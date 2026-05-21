"""Core data model + SQLite DDL for the symbolic-dynamics ontology.

Mirrors ../ONTOLOGY_PLAN.md §1 (data model) and Appendix A (DDL). The
canonical store is JSONL (see ``store.py``); SQLite is a derived artifact.

Design choices:

* Dataclasses, not an ORM: the canonical store is plain JSONL, so a
  schema is just (de)serialization + validation. Keeps deps at zero.
* Lists/dicts live natively on the dataclass; ``store.py`` JSON-encodes
  them into the TEXT columns of Appendix A when materializing SQLite.
* IDs are content-derived (§1.5) so re-extraction is idempotent.
"""

from __future__ import annotations

import datetime as _dt
import hashlib
from dataclasses import asdict, dataclass, field
from enum import Enum
from typing import Any

# Bump when the on-disk JSONL/SQLite shape changes; ``store.build`` checks
# this against the ``meta`` table and refuses a mismatched stale build.
SCHEMA_VERSION = 1


class NodeKind(str, Enum):
    """§1.1 node kinds."""

    PAPER = "Paper"
    DEFINITION = "Definition"
    THEOREM = "Theorem"
    LEMMA = "Lemma"
    PROPOSITION = "Proposition"
    COROLLARY = "Corollary"
    CLAIM = "Claim"
    CONJECTURE = "Conjecture"
    OPEN_PROBLEM = "OpenProblem"
    EXAMPLE = "Example"
    COUNTEREXAMPLE = "Counterexample"
    CONSTRUCTION = "Construction"
    CONCEPT = "Concept"
    ALIAS = "Alias"  # redirect tombstone left behind by a merge (§5.2)


# Kinds whose identity is the (normalized) statement text.
STATEMENT_KINDS = {
    NodeKind.DEFINITION,
    NodeKind.THEOREM,
    NodeKind.LEMMA,
    NodeKind.PROPOSITION,
    NodeKind.COROLLARY,
    NodeKind.CLAIM,
    NodeKind.CONJECTURE,
    NodeKind.OPEN_PROBLEM,
    NodeKind.EXAMPLE,
    NodeKind.COUNTEREXAMPLE,
}
# Kinds that get a curated slug instead of a statement hash.
SLUG_KINDS = {NodeKind.CONSTRUCTION, NodeKind.CONCEPT}


class EdgeType(str, Enum):
    """§1.3 edge kinds. All directed."""

    DEFINES = "defines"
    STATES = "states"
    DEPENDS_ON = "depends_on"
    USES_DEFINITION = "uses_definition"
    SPECIALIZES = "specializes"
    EQUIVALENT_TO = "equivalent_to"
    SAME_AS = "same_as"
    RESOLVES = "resolves"
    REFUTES = "refutes"
    IMPROVES = "improves"
    COROLLARY_OF = "corollary_of"
    INSTANCE_OF = "instance_of"
    CITES = "cites"
    ATTRIBUTED_TO = "attributed_to"


# Edges that constrain formalization order (Phase E topo sort, §6.1).
ORDERING_EDGES = {EdgeType.USES_DEFINITION, EdgeType.DEPENDS_ON}


def new_run_id() -> str:
    """UTC-timestamped, sortable, collision-resistant run id."""
    now = _dt.datetime.now(_dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return f"run-{now}"


def paper_id(arxiv_id: str) -> str:
    """``arxiv:2401.01234`` / ``arxiv:math/0703206``."""
    return f"arxiv:{arxiv_id.strip()}"


def node_id(kind: NodeKind, key: str) -> str:
    """Content-derived stable id (§1.5).

    Statement kinds hash their normalized statement; slug kinds use the
    caller-supplied curated slug verbatim.
    """
    if kind in SLUG_KINDS:
        return f"{kind.value.lower()}:{key}"
    if kind == NodeKind.PAPER:
        return paper_id(key)
    h = hashlib.sha256(f"{kind.value}\x1f{key}".encode()).hexdigest()[:20]
    return f"{kind.value.lower()}:{h}"


@dataclass
class Provenance:
    """Where a node was seen (§1.2). A node may have many."""

    paper: str
    label: str = ""          # the paper's \label or environment name
    env_name: str = ""       # the LaTeX environment it came from
    section: str = ""
    char_span: str = ""      # "start:end" into the source
    run_id: str = ""
    confidence: float = 1.0
    human_verified: bool = False


@dataclass
class EdgeProvenance:
    paper: str
    char_span: str = ""
    run_id: str = ""


@dataclass
class Paper:
    """§1.1 Paper node + Appendix A ``papers`` row."""

    id: str
    title: str = ""
    authors: list[str] = field(default_factory=list)
    year: int | None = None
    categories: list[str] = field(default_factory=list)
    abstract: str = ""
    relevance: int | None = None       # 0-3, §3.3
    fidelity_tier: str = ""            # source | text | pdf | metadata
    latest_version: str = ""

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    @staticmethod
    def from_dict(d: dict[str, Any]) -> "Paper":
        return Paper(**d)


@dataclass
class Node:
    """§1.2 node properties."""

    id: str
    kind: str                          # NodeKind value
    name: str = ""
    statement_latex: str = ""
    statement_text: str = ""
    hypotheses: list[str] = field(default_factory=list)
    conclusion: str = ""
    parameters: list[str] = field(default_factory=list)
    tags: list[str] = field(default_factory=list)
    status: str = ""
    aliases: list[str] = field(default_factory=list)
    provenance: list[Provenance] = field(default_factory=list)
    content_hash: str = ""
    structural_sig: str = ""
    lean_decl: str = ""
    lean_status: str = ""              # stated | proved | axiomatized | sorry
    canonical_id: str = ""            # set on a tombstone -> its survivor
    merged_from: list[str] = field(default_factory=list)
    created_run: str = ""
    updated_run: str = ""

    @property
    def is_tombstone(self) -> bool:
        return self.kind == NodeKind.ALIAS.value and bool(self.canonical_id)

    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d["provenance"] = [asdict(p) for p in self.provenance]
        return d

    @staticmethod
    def from_dict(d: dict[str, Any]) -> "Node":
        d = dict(d)
        d["provenance"] = [Provenance(**p) for p in d.get("provenance", [])]
        return Node(**d)


@dataclass
class Edge:
    """§1.3 edge properties."""

    id: str
    type: str                          # EdgeType value
    src: str
    dst: str
    regime: str = ""
    where_: str = ""                   # in_statement | in_proof (depends_on)
    proved: str = ""                   # claimed | lean-proved (equivalent_to)
    confidence: float = 1.0
    human_verified: bool = False
    in_lean: bool = False
    notes: str = ""
    provenance: list[EdgeProvenance] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d["provenance"] = [asdict(p) for p in self.provenance]
        return d

    @staticmethod
    def from_dict(d: dict[str, Any]) -> "Edge":
        d = dict(d)
        d["provenance"] = [EdgeProvenance(**p) for p in d.get("provenance", [])]
        return Edge(**d)


def edge_id(etype: EdgeType, src: str, dst: str, regime: str = "") -> str:
    """Deterministic so re-extracting the same relation is idempotent."""
    h = hashlib.sha256(f"{etype.value}\x1f{src}\x1f{dst}\x1f{regime}".encode()).hexdigest()[:16]
    return f"e:{h}"


@dataclass
class Merge:
    """§5.2 reversible merge log row."""

    losing_id: str
    canonical_id: str
    verdict: str = "same"
    confidence: float = 1.0
    run_id: str = ""
    justification: str = ""
    ts: str = ""

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    @staticmethod
    def from_dict(d: dict[str, Any]) -> "Merge":
        return Merge(**d)


@dataclass
class Shard:
    """§3.5 harvest shard (resumable unit of Phase A)."""

    year: int
    category: str
    keyword: str
    status: str = "pending"            # pending | done
    last_offset: int = 0
    count: int = 0
    ts: str = ""

    @property
    def key(self) -> tuple[int, str, str]:
        return (self.year, self.category, self.keyword)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    @staticmethod
    def from_dict(d: dict[str, Any]) -> "Shard":
        return Shard(**d)


# --------------------------------------------------------------------------
# SQLite DDL (Appendix A). Derived store only; rebuilt by ``store.build``.
# --------------------------------------------------------------------------

DDL = """
CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT);

CREATE TABLE IF NOT EXISTS papers (
  id TEXT PRIMARY KEY, title TEXT, authors TEXT, year INT, categories TEXT,
  abstract TEXT, relevance INT, fidelity_tier TEXT, latest_version TEXT
);
CREATE TABLE IF NOT EXISTS nodes (
  id TEXT PRIMARY KEY, kind TEXT, name TEXT,
  statement_latex TEXT, statement_text TEXT,
  hypotheses TEXT, conclusion TEXT, parameters TEXT, tags TEXT,
  status TEXT, content_hash TEXT, structural_sig TEXT,
  lean_decl TEXT, lean_status TEXT, canonical_id TEXT,
  merged_from TEXT, aliases TEXT, created_run TEXT, updated_run TEXT
);
CREATE TABLE IF NOT EXISTS provenance (
  node_id TEXT, paper TEXT, label TEXT, env_name TEXT,
  section TEXT, char_span TEXT, run_id TEXT,
  confidence REAL, human_verified INT
);
CREATE TABLE IF NOT EXISTS edges (
  id TEXT PRIMARY KEY, type TEXT, src TEXT, dst TEXT,
  regime TEXT, where_ TEXT, proved TEXT, confidence REAL,
  human_verified INT, in_lean INT, notes TEXT
);
CREATE TABLE IF NOT EXISTS edge_provenance (
  edge_id TEXT, paper TEXT, char_span TEXT, run_id TEXT
);
CREATE TABLE IF NOT EXISTS embeddings (node_id TEXT PRIMARY KEY, vec BLOB);
CREATE TABLE IF NOT EXISTS merges (
  losing_id TEXT, canonical_id TEXT, verdict TEXT,
  confidence REAL, run_id TEXT, justification TEXT, ts TEXT
);
CREATE TABLE IF NOT EXISTS shards (
  year INT, category TEXT, keyword TEXT,
  status TEXT, last_offset INT, count INT, ts TEXT,
  PRIMARY KEY (year, category, keyword)
);
CREATE INDEX IF NOT EXISTS nodes_kind ON nodes(kind);
CREATE INDEX IF NOT EXISTS nodes_hash ON nodes(content_hash);
CREATE INDEX IF NOT EXISTS edges_src  ON edges(src);
CREATE INDEX IF NOT EXISTS edges_dst  ON edges(dst);
"""
