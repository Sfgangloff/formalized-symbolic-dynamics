"""Pluggable embeddings + nearest-neighbour search for dedup L2 (§5.1).

The §11 open decision (which embedding model) is deliberately *not*
hard-wired. The default :class:`HashingEmbedder` is zero-dependency and
fully deterministic, so the pipeline and its tests are reproducible
without a model download. Semantic quality is poor by design — it is a
placeholder; a real local sentence-encoder is swapped in at the pilot by
implementing the :class:`Embedder` protocol, nothing else changes.

FAISS is an optional accelerator (``pip install '.[faiss]'``); without it
a pure-Python exact cosine search is used.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
from pathlib import Path
from typing import Protocol, runtime_checkable

_TOKEN = re.compile(r"[a-z0-9ℤℕℝℚσΣ→↦×≤≥·∞∅⊆]+")


@runtime_checkable
class Embedder(Protocol):
    dim: int

    def embed(self, text: str) -> list[float]:
        ...


class HashingEmbedder:
    """Deterministic feature-hashing embedder (words + char trigrams)."""

    def __init__(self, dim: int = 256):
        self.dim = dim

    def _features(self, text: str) -> list[str]:
        t = text.lower()
        words = _TOKEN.findall(t)
        feats = list(words)
        joined = " ".join(words)
        feats += [joined[i : i + 3] for i in range(max(0, len(joined) - 2))]
        return feats

    def embed(self, text: str) -> list[float]:
        vec = [0.0] * self.dim
        for f in self._features(text):
            h = int(hashlib.sha1(f.encode()).hexdigest(), 16)
            idx = h % self.dim
            sign = 1.0 if (h >> 8) & 1 else -1.0
            vec[idx] += sign
        norm = math.sqrt(sum(x * x for x in vec))
        if norm > 0:
            vec = [x / norm for x in vec]
        return vec


def cosine(a: list[float], b: list[float]) -> float:
    return sum(x * y for x, y in zip(a, b))


def cosine_topk(
    query: list[float], corpus: dict[str, list[float]], k: int
) -> list[tuple[str, float]]:
    """Exact top-k by cosine (vectors assumed L2-normalized)."""
    scored = [(nid, cosine(query, v)) for nid, v in corpus.items()]
    scored.sort(key=lambda x: x[1], reverse=True)
    return scored[:k]


class VectorIndex:
    """Persisted node-embedding index under ``build/``.

    Stores vectors in ``build/embeddings.json`` (deterministic,
    git-ignored). If ``faiss`` is installed it is used for search; the
    JSON remains the portable source so the index is rebuildable.
    """

    def __init__(self, build_dir: Path, embedder: Embedder | None = None):
        self.build_dir = Path(build_dir)
        self.embedder = embedder or HashingEmbedder()
        self.vectors: dict[str, list[float]] = {}
        self._path = self.build_dir / "embeddings.json"

    def build(self, items: dict[str, str]) -> None:
        """``items``: node_id -> text to embed (typically statement_text)."""
        self.vectors = {
            nid: self.embedder.embed(txt) for nid, txt in items.items() if txt
        }
        self.build_dir.mkdir(parents=True, exist_ok=True)
        self._path.write_text(
            json.dumps(
                {"dim": self.embedder.dim, "vectors": self.vectors},
                sort_keys=True,
            )
        )

    def load(self) -> bool:
        if not self._path.exists():
            return False
        data = json.loads(self._path.read_text())
        self.vectors = {k: list(map(float, v)) for k, v in data["vectors"].items()}
        return True

    def query_text(self, text: str, k: int = 5) -> list[tuple[str, float]]:
        return cosine_topk(self.embedder.embed(text), self.vectors, k)

    def query_node(self, node_id: str, k: int = 5) -> list[tuple[str, float]]:
        q = self.vectors.get(node_id)
        if q is None:
            return []
        out = cosine_topk(q, self.vectors, k + 1)
        return [(nid, s) for nid, s in out if nid != node_id][:k]
