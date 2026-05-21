"""Phase B — source acquisition (ONTOLOGY_PLAN §4.1).

Fetches the arXiv e-print (``https://arxiv.org/e-print/<id>``) into
``corpus/<id>/`` and records a *fidelity tier*, since extraction
confidence (§4.2, §9.2) depends on whether we got real LaTeX:

    source   > text          > pdf            > metadata
    (.tex)     (plain text)     (pdf only)       (abstract only / offline)

Resumable per paper (``corpus/<id>/meta.json`` is the done-marker).
Offline / fetch failure degrades to the ``metadata`` tier and continues,
so a partial run is safe.
"""

from __future__ import annotations

import gzip
import io
import json
import tarfile
import urllib.request
from pathlib import Path
from typing import Callable

from .store import Store

ARXIV_EPRINT = "https://arxiv.org/e-print/"


def arxiv_dir_name(arxiv_id: str) -> str:
    """``math/0703206`` -> ``math_0703206`` (filesystem-safe, reversible)."""
    return arxiv_id.replace("/", "_")


def _http_get(url: str, timeout: float = 60.0) -> bytes:
    req = urllib.request.Request(
        url, headers={"User-Agent": "symdyn-ontology/0.1 (research)"}
    )
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def _unpack(blob: bytes) -> tuple[str, dict[str, bytes]]:
    """Return (tier, {filename: bytes}). Handles tar.gz, single gzipped
    tex, raw tex, and pdf-only submissions."""
    if blob[:4] == b"%PDF":
        return "pdf", {"paper.pdf": blob}
    # tar (possibly gzipped)
    try:
        with tarfile.open(fileobj=io.BytesIO(blob), mode="r:*") as tf:
            files = {}
            for m in tf.getmembers():
                if m.isfile():
                    fh = tf.extractfile(m)
                    if fh is not None:
                        files[m.name] = fh.read()
            if files:
                return "source", files
    except (tarfile.TarError, OSError):
        pass
    # single gzipped file (often one .tex)
    try:
        raw = gzip.decompress(blob)
        if raw[:4] == b"%PDF":
            return "pdf", {"paper.pdf": raw}
        return "source", {"main.tex": raw}
    except OSError:
        pass
    # raw bytes — assume tex/text
    if blob.strip():
        return "source", {"main.tex": blob}
    return "metadata", {}


def acquire_paper(
    arxiv_id: str,
    corpus_dir: Path,
    *,
    fetch: Callable[[str], bytes] = _http_get,
    force: bool = False,
) -> str:
    """Fetch + unpack one paper. Returns the fidelity tier."""
    out = Path(corpus_dir) / arxiv_dir_name(arxiv_id)
    meta_path = out / "meta.json"
    if meta_path.exists() and not force:
        return json.loads(meta_path.read_text()).get("fidelity_tier", "")

    out.mkdir(parents=True, exist_ok=True)
    try:
        blob = fetch(f"{ARXIV_EPRINT}{arxiv_id}")
        tier, files = _unpack(blob)
    except Exception:  # noqa: BLE001 - offline/HTTP failure is expected
        tier, files = "metadata", {}

    written = []
    for name, data in files.items():
        # flatten nested paths safely under out/
        safe = name.replace("..", "_").lstrip("/")
        dest = out / safe
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        written.append(safe)
    meta_path.write_text(
        json.dumps(
            {
                "arxiv_id": arxiv_id,
                "fidelity_tier": tier,
                "files": sorted(written),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return tier


def run_acquire(
    store: Store,
    corpus_dir: Path,
    *,
    fetch: Callable[[str], bytes] = _http_get,
    min_relevance: int = 2,
    only: list[str] | None = None,
    force: bool = False,
    log: Callable[[str], None] = print,
) -> dict:
    """Acquire sources for G1-approved core papers (relevance ≥
    ``min_relevance``), or an explicit ``only`` id list (the pilot path)."""
    if only:
        targets = [
            store.papers[pid] for pid in only if pid in store.papers
        ]
    else:
        targets = [
            p for p in store.papers.values() if (p.relevance or 0) >= min_relevance
        ]
    tiers: dict[str, int] = {}
    for i, p in enumerate(sorted(targets, key=lambda p: p.id)):
        arxiv_id = p.id.split("arxiv:", 1)[-1]
        tier = acquire_paper(arxiv_id, corpus_dir, fetch=fetch, force=force)
        p.fidelity_tier = tier
        tiers[tier] = tiers.get(tier, 0) + 1
        log(f"  [{i+1}/{len(targets)}] {p.id}: {tier}")
    return {"acquired": len(targets), "by_tier": tiers}
