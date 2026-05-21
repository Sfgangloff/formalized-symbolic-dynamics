"""Phase A — paper harvesting (ONTOLOGY_PLAN §3).

Talks to the public arXiv Atom API directly (stdlib only) rather than the
``math-search`` MCP, which is in-session-agent-only; see ../README.md
"Design refinement". Harvest is sharded by (year × category × keyword)
and fully resumable: shard state is canonical (``snapshots/shards.jsonl``).

The relevance gate (§3.3) is behind :class:`RelevanceScorer`; the default
is a deterministic keyword scorer (no model) so harvest is reproducible.
A model-backed scorer is swapped in at the pilot.

Output is reviewed at gate **G1** before any downstream phase runs.
"""

from __future__ import annotations

import datetime as _dt
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from typing import Callable, Protocol, runtime_checkable

from .schema import Paper, Shard, paper_id
from .store import Store

ARXIV_API = "http://export.arxiv.org/api/query"
_ATOM = "{http://www.w3.org/2005/Atom}"
_ARXIV = "{http://arxiv.org/schemas/atom}"

# §3.2 query matrix.
CORE_CATEGORIES = ["math.DS", "cs.DM", "cs.FL", "cs.CC", "math.LO", "math.CO"]
LEGACY_CATEGORIES = ["chao-dyn", "comp-gas", "nlin.CG", "nlin.CD"]

KEYWORDS = [
    "symbolic dynamics",
    "subshift",
    "shift of finite type",
    "sofic shift",
    "Wang tiles",
    "Wang tiling",
    "domino problem",
    "aperiodic tiling",
    "multidimensional shift",
    "cellular automata",
    "topological entropy",
    "factor complexity",
    "block gluing",
    "minimal subshift",
    "substitution subshift",
    "S-adic",
]

ARXIV_MATH_START_YEAR = 1992


def current_year() -> int:
    return _dt.datetime.now(_dt.timezone.utc).year


def categories_for_year(year: int) -> list[str]:
    """Legacy archives only carry the early years (modern math.DS ~1998)."""
    cats = list(CORE_CATEGORIES)
    if year < 1998:
        cats += LEGACY_CATEGORIES
    return cats


@runtime_checkable
class RelevanceScorer(Protocol):
    def score(self, title: str, abstract: str) -> int:
        """0 drop · 1 borderline (human at G1) · 2-3 core."""
        ...


class KeywordRelevanceScorer:
    """Deterministic core-scope scorer (§3.3). Conservative on
    ``cellular automata`` (heavy false-positive source in physics)."""

    CORE = (
        "subshift", "shift of finite type", "sofic", "wang tile",
        "domino problem", "symbolic dynam", "aperiodic", "tiling",
        "topological entropy", "minimal shift", "substitution",
    )
    SUPPORT = ("entropy", "automaton", "automata", "lattice", "ergodic")

    def score(self, title: str, abstract: str) -> int:
        t = f"{title}\n{abstract}".lower()
        core_hits = sum(1 for w in self.CORE if w in t)
        sup_hits = sum(1 for w in self.SUPPORT if w in t)
        if "cellular automat" in t and core_hits == 0:
            return 1  # CA alone -> borderline, human decides at G1
        if core_hits >= 2:
            return 3
        if core_hits == 1:
            return 2
        if sup_hits >= 1 and ("shift" in t or "tiling" in t):
            return 1
        return 0


def _http_get(url: str, timeout: float = 30.0) -> bytes:
    req = urllib.request.Request(
        url, headers={"User-Agent": "symdyn-ontology/0.1 (research)"}
    )
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def _build_query(category: str, keyword: str, year: int) -> str:
    kw = keyword.replace('"', "")
    field = f'(ti:"{kw}" OR abs:"{kw}")'
    date = f"submittedDate:[{year}01010000 TO {year}12312359]"
    q = f"cat:{category} AND {field} AND {date}"
    return urllib.parse.urlencode(
        {
            "search_query": q,
            "start": 0,
            "max_results": 100,
            "sortBy": "submittedDate",
            "sortOrder": "ascending",
        }
    )


def _parse_atom(xml_bytes: bytes) -> list[dict]:
    root = ET.fromstring(xml_bytes)
    out = []
    for e in root.findall(f"{_ATOM}entry"):
        raw_id = (e.findtext(f"{_ATOM}id") or "").strip()
        # http://arxiv.org/abs/2401.01234v2  ->  2401.01234 , v2
        tail = raw_id.split("/abs/")[-1]
        version = ""
        bare = tail
        if "v" in tail.rsplit("/", 1)[-1]:
            idx = tail.rfind("v")
            if tail[idx + 1 :].isdigit():
                bare, version = tail[:idx], tail[idx:]
        published = (e.findtext(f"{_ATOM}published") or "")[:4]
        authors = [
            (a.findtext(f"{_ATOM}name") or "").strip()
            for a in e.findall(f"{_ATOM}author")
        ]
        cats = [
            c.get("term", "")
            for c in e.findall(f"{_ATOM}category")
            if c.get("term")
        ]
        out.append(
            {
                "arxiv_id": bare,
                "version": version,
                "title": " ".join((e.findtext(f"{_ATOM}title") or "").split()),
                "abstract": " ".join(
                    (e.findtext(f"{_ATOM}summary") or "").split()
                ),
                "authors": authors,
                "year": int(published) if published.isdigit() else None,
                "categories": cats,
            }
        )
    return out


def build_shards(store: Store, year_from: int | None = None) -> int:
    """Populate any missing shards in the (year×category×keyword) matrix.
    Returns the number of new shards added. Existing shard state is kept
    (resumability)."""
    y_to = current_year()
    y_from = year_from or ARXIV_MATH_START_YEAR
    added = 0
    for year in range(y_to, y_from - 1, -1):
        for cat in categories_for_year(year):
            for kw in KEYWORDS:
                key = (year, cat, kw)
                if key not in store.shards:
                    store.shards[key] = Shard(year=year, category=cat, keyword=kw)
                    added += 1
    return added


def _upsert_paper(store: Store, rec: dict, relevance: int) -> None:
    pid = paper_id(rec["arxiv_id"])
    existing = store.papers.get(pid)
    if existing is None:
        store.papers[pid] = Paper(
            id=pid,
            title=rec["title"],
            authors=rec["authors"],
            year=rec["year"],
            categories=rec["categories"],
            abstract=rec["abstract"],
            relevance=relevance,
            latest_version=rec["version"],
        )
        return
    # Same paper seen via another shard: keep richest metadata.
    existing.relevance = max(existing.relevance or 0, relevance)
    existing.categories = sorted(set(existing.categories) | set(rec["categories"]))
    if rec["version"] > (existing.latest_version or ""):
        existing.latest_version = rec["version"]


def run_harvest(
    store: Store,
    *,
    scorer: RelevanceScorer | None = None,
    fetch: Callable[[str], bytes] = _http_get,
    max_shards: int | None = None,
    delay: float = 3.0,
    log: Callable[[str], None] = print,
) -> dict:
    """Process pending shards. Network/parse failures leave a shard
    ``pending`` and continue, so a partial/offline run is safe and
    resumable. Returns a summary dict."""
    scorer = scorer or KeywordRelevanceScorer()
    pending = [s for s in store.shards.values() if s.status != "done"]
    pending.sort(key=lambda s: (-s.year, s.category, s.keyword))
    if max_shards is not None:
        pending = pending[:max_shards]

    processed = errors = new_papers = 0
    before = len(store.papers)
    for i, sh in enumerate(pending):
        url = f"{ARXIV_API}?{_build_query(sh.category, sh.keyword, sh.year)}"
        try:
            recs = _parse_atom(fetch(url))
        except Exception as ex:  # noqa: BLE001 - resilience by design
            errors += 1
            log(f"  shard {sh.key} failed ({ex.__class__.__name__}); left pending")
            continue
        kept = 0
        for rec in recs:
            rel = scorer.score(rec["title"], rec["abstract"])
            if rel >= 1:  # 0 dropped (logged via count diff only)
                _upsert_paper(store, rec, rel)
                kept += 1
        sh.count = len(recs)
        sh.status = "done"
        sh.ts = _dt.datetime.now(_dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        processed += 1
        log(f"  [{i+1}/{len(pending)}] {sh.key}: {len(recs)} hits, {kept} kept")
        if delay and i + 1 < len(pending):
            time.sleep(delay)
    new_papers = len(store.papers) - before
    return {
        "shards_processed": processed,
        "shards_pending": len([s for s in store.shards.values() if s.status != "done"]),
        "shard_errors": errors,
        "new_papers": new_papers,
        "total_papers": len(store.papers),
    }


def write_g1_artifacts(store: Store, reviews_dir) -> tuple[str, str]:
    """Write the G1 master list (md + csv) for human sign-off (§3.6)."""
    import csv
    import io
    from pathlib import Path

    reviews_dir = Path(reviews_dir)
    reviews_dir.mkdir(parents=True, exist_ok=True)
    papers = sorted(
        store.papers.values(),
        key=lambda p: (-(p.relevance or 0), -(p.year or 0), p.id),
    )

    md = io.StringIO()
    md.write("# G1 — master paper list\n\n")
    md.write(f"{len(papers)} papers. Relevance: 3/2 core · 1 borderline (decide).\n\n")
    md.write("Sign off when reviewed: `onto gate sign G1`\n\n")
    md.write("| id | year | rel | title |\n|----|------|-----|-------|\n")
    for p in papers:
        md.write(
            f"| {p.id} | {p.year or ''} | {p.relevance or 0} | "
            f"{p.title.replace('|', '/')} |\n"
        )
    md_path = reviews_dir / "G1_master_list.md"
    md_path.write_text(md.getvalue(), encoding="utf-8")

    csv_path = reviews_dir / "G1_master_list.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["id", "year", "relevance", "title", "authors", "categories"])
        for p in papers:
            w.writerow(
                [
                    p.id, p.year or "", p.relevance or 0, p.title,
                    "; ".join(p.authors), " ".join(p.categories),
                ]
            )
    return str(md_path), str(csv_path)
