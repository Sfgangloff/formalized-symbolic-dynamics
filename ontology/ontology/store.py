"""Canonical JSONL store + manifest + derived SQLite build.

Canonical state lives in ``snapshots/*.jsonl`` (git-tracked, diffable,
sorted, stable key order). ``build/ontology.db`` is a *derived* artifact
rebuilt from the snapshots; deleting it loses nothing.

A ``Store`` is loaded, mutated in memory by a phase, then ``save()``d
atomically. Re-running any phase is idempotent because every collection
is keyed by a content-derived id (schema §1.5).
"""

from __future__ import annotations

import datetime as _dt
import hashlib
import json
import os
import sqlite3
from pathlib import Path
from typing import Iterable

from .schema import DDL, SCHEMA_VERSION, Edge, Merge, Node, Paper, Shard

_SNAPSHOT_FILES = {
    "papers": "papers.jsonl",
    "nodes": "nodes.jsonl",
    "edges": "edges.jsonl",
    "merges": "merges.jsonl",
    "shards": "shards.jsonl",
}


def _now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def _atomic_write(path: Path, text: str) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)


def _dump_jsonl(rows: Iterable[dict]) -> str:
    return "".join(
        json.dumps(r, sort_keys=True, ensure_ascii=False) + "\n" for r in rows
    )


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


class Store:
    """In-memory view of the ontology, backed by JSONL snapshots."""

    def __init__(self, root: Path):
        self.root = Path(root)
        self.snap = self.root / "snapshots"
        self.build_dir = self.root / "build"
        self.papers: dict[str, Paper] = {}
        self.nodes: dict[str, Node] = {}
        self.edges: dict[str, Edge] = {}
        self.merges: list[Merge] = []
        self.shards: dict[tuple[int, str, str], Shard] = {}

    # -- load / save -------------------------------------------------------

    @classmethod
    def load(cls, root: Path) -> "Store":
        s = cls(root)
        s.snap.mkdir(parents=True, exist_ok=True)
        s.build_dir.mkdir(parents=True, exist_ok=True)
        for line in s._read("papers"):
            p = Paper.from_dict(line)
            s.papers[p.id] = p
        for line in s._read("nodes"):
            n = Node.from_dict(line)
            s.nodes[n.id] = n
        for line in s._read("edges"):
            e = Edge.from_dict(line)
            s.edges[e.id] = e
        for line in s._read("merges"):
            s.merges.append(Merge.from_dict(line))
        for line in s._read("shards"):
            sh = Shard.from_dict(line)
            s.shards[sh.key] = sh
        return s

    def _read(self, name: str) -> list[dict]:
        path = self.snap / _SNAPSHOT_FILES[name]
        if not path.exists():
            return []
        out = []
        for raw in path.read_text(encoding="utf-8").splitlines():
            raw = raw.strip()
            if raw:
                out.append(json.loads(raw))
        return out

    def save(self, run_id: str = "") -> None:
        """Write all snapshots atomically + refresh the manifest."""
        self.snap.mkdir(parents=True, exist_ok=True)
        papers = [self.papers[k].to_dict() for k in sorted(self.papers)]
        nodes = [self.nodes[k].to_dict() for k in sorted(self.nodes)]
        edges = [self.edges[k].to_dict() for k in sorted(self.edges)]
        merges = [
            m.to_dict()
            for m in sorted(self.merges, key=lambda m: (m.ts, m.losing_id))
        ]
        shards = [
            self.shards[k].to_dict() for k in sorted(self.shards)
        ]
        payload = {
            "papers": papers,
            "nodes": nodes,
            "edges": edges,
            "merges": merges,
            "shards": shards,
        }
        hashes = {}
        for name, rows in payload.items():
            text = _dump_jsonl(rows)
            _atomic_write(self.snap / _SNAPSHOT_FILES[name], text)
            hashes[name] = _sha256_text(text)
        manifest = {
            "schema_version": SCHEMA_VERSION,
            "generated": _now(),
            "run_id": run_id,
            "counts": {k: len(v) for k, v in payload.items()},
            "hashes": hashes,
            "snapshot_hash": _sha256_text(json.dumps(hashes, sort_keys=True)),
        }
        _atomic_write(
            self.snap / "manifest.json",
            json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        )

    # -- manifest / staleness ---------------------------------------------

    def manifest(self) -> dict:
        p = self.snap / "manifest.json"
        return json.loads(p.read_text()) if p.exists() else {}

    def snapshot_hash(self) -> str:
        return self.manifest().get("snapshot_hash", "")

    def is_build_stale(self) -> bool:
        db = self.build_dir / "ontology.db"
        if not db.exists():
            return True
        try:
            con = sqlite3.connect(db)
            cur = con.execute("SELECT value FROM meta WHERE key='snapshot_hash'")
            row = cur.fetchone()
            con.close()
        except sqlite3.Error:
            return True
        return (not row) or row[0] != self.snapshot_hash()

    # -- graph helpers (used by lints / Phase E) --------------------------

    def out_edges(self, node_id: str) -> list[Edge]:
        return [e for e in self.edges.values() if e.src == node_id]

    def in_edges(self, node_id: str) -> list[Edge]:
        return [e for e in self.edges.values() if e.dst == node_id]

    def resolve(self, node_id: str) -> str:
        """Follow merge redirect tombstones to the survivor (§5.2)."""
        seen = set()
        cur = node_id
        while cur in self.nodes and self.nodes[cur].is_tombstone:
            if cur in seen:
                break
            seen.add(cur)
            cur = self.nodes[cur].canonical_id
        return cur

    # -- derived SQLite build ---------------------------------------------

    def build(self) -> Path:
        """Rebuild ``build/ontology.db`` from the in-memory snapshots."""
        self.build_dir.mkdir(parents=True, exist_ok=True)
        db = self.build_dir / "ontology.db"
        if db.exists():
            db.unlink()
        con = sqlite3.connect(db)
        con.executescript(DDL)
        con.execute(
            "INSERT OR REPLACE INTO meta VALUES ('schema_version', ?)",
            (str(SCHEMA_VERSION),),
        )
        con.execute(
            "INSERT OR REPLACE INTO meta VALUES ('snapshot_hash', ?)",
            (self.snapshot_hash(),),
        )
        for p in self.papers.values():
            con.execute(
                "INSERT INTO papers VALUES (?,?,?,?,?,?,?,?,?)",
                (
                    p.id, p.title, json.dumps(p.authors), p.year,
                    json.dumps(p.categories), p.abstract, p.relevance,
                    p.fidelity_tier, p.latest_version,
                ),
            )
        for n in self.nodes.values():
            con.execute(
                "INSERT INTO nodes VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (
                    n.id, n.kind, n.name, n.statement_latex, n.statement_text,
                    json.dumps(n.hypotheses), n.conclusion,
                    json.dumps(n.parameters), json.dumps(n.tags), n.status,
                    n.content_hash, n.structural_sig, n.lean_decl,
                    n.lean_status, n.canonical_id, json.dumps(n.merged_from),
                    json.dumps(n.aliases), n.created_run, n.updated_run,
                ),
            )
            for pv in n.provenance:
                con.execute(
                    "INSERT INTO provenance VALUES (?,?,?,?,?,?,?,?,?)",
                    (
                        n.id, pv.paper, pv.label, pv.env_name, pv.section,
                        pv.char_span, pv.run_id, pv.confidence,
                        int(pv.human_verified),
                    ),
                )
        for e in self.edges.values():
            con.execute(
                "INSERT INTO edges VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                (
                    e.id, e.type, e.src, e.dst, e.regime, e.where_, e.proved,
                    e.confidence, int(e.human_verified), int(e.in_lean),
                    e.notes,
                ),
            )
            for ep in e.provenance:
                con.execute(
                    "INSERT INTO edge_provenance VALUES (?,?,?,?)",
                    (e.id, ep.paper, ep.char_span, ep.run_id),
                )
        for m in self.merges:
            con.execute(
                "INSERT INTO merges VALUES (?,?,?,?,?,?,?)",
                (
                    m.losing_id, m.canonical_id, m.verdict, m.confidence,
                    m.run_id, m.justification, m.ts,
                ),
            )
        for sh in self.shards.values():
            con.execute(
                "INSERT INTO shards VALUES (?,?,?,?,?,?,?)",
                (
                    sh.year, sh.category, sh.keyword, sh.status,
                    sh.last_offset, sh.count, sh.ts,
                ),
            )
        con.commit()
        con.close()
        return db
