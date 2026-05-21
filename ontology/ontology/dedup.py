"""Phase D — dedup ladder (ONTOLOGY_PLAN §5.1).

L0 exact content hash → L1 structural bucket → L2 embedding top-k → L3
LLM identity judge → L4 Lean identity (late repair). The deterministic
rungs (L0–L2) run now; L3/L4 are protocols.

Critical correctness rule (§1.4, §5.4): the default judge **never
auto-merges on similarity** — only an exact L0 hash auto-merges. Anything
ambiguous is added *unmerged* and pushed to gate **G3**; a false merge is
the worst failure mode, a transient duplicate is cheap.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Protocol, runtime_checkable

from .embed import HashingEmbedder, VectorIndex
from .schema import EdgeType, Node
from .store import Store


@dataclass
class Verdict:
    verdict: str          # same|specializes|generalizes|equivalent|improves|related|unrelated
    confidence: float
    justification: str = ""


@runtime_checkable
class IdentityJudge(Protocol):
    """L3 (§5.1). Returns the §1.4 relation between two candidate nodes."""

    def judge(self, incoming: Node, existing: Node) -> Verdict:
        ...


class ConservativeJudge:
    """No-model default: refuses every similarity-based merge. L0 exact
    matches are handled before the judge runs, so this never fabricates a
    merge or a relation edge — it routes ambiguity to G3."""

    def judge(self, incoming: Node, existing: Node) -> Verdict:
        return Verdict("unrelated", 0.0, "conservative no-model judge")


@runtime_checkable
class LeanIdentityProbe(Protocol):
    """L4 (§5.1) — only meaningful once *both* nodes have ``lean_decl``;
    a late repair pass, never the primary gate (the §5.1 design note)."""

    def probe(self, a: Node, b: Node) -> Verdict | None:
        ...


class NoopLeanProbe:
    def probe(self, a, b):  # noqa: D102
        return None


_RELATION_EDGE = {
    "specializes": (EdgeType.SPECIALIZES, "fwd"),
    "generalizes": (EdgeType.SPECIALIZES, "rev"),
    "equivalent": (EdgeType.EQUIVALENT_TO, "fwd"),
    "improves": (EdgeType.IMPROVES, "fwd"),
}


@dataclass
class PlanItem:
    incoming_id: str
    action: str                       # "merge" | "new"
    canonical_id: str = ""
    verdict: str = ""
    confidence: float = 0.0
    justification: str = ""
    relation: tuple[str, str, str] | None = None  # (etype, src_id, dst_id)
    review: bool = False
    candidates: list[tuple[str, float]] = field(default_factory=list)


@dataclass
class MergePlan:
    items: list[PlanItem] = field(default_factory=list)
    id_map: dict[str, str] = field(default_factory=dict)  # incoming id -> store id

    @property
    def n_merge(self) -> int:
        return sum(1 for i in self.items if i.action == "merge")

    @property
    def n_new(self) -> int:
        return sum(1 for i in self.items if i.action == "new")

    @property
    def n_review(self) -> int:
        return sum(1 for i in self.items if i.review)


def _bucket(store: Store, nd: Node) -> list[Node]:
    out = []
    for sn in store.nodes.values():
        if sn.is_tombstone or sn.kind != nd.kind:
            continue
        if nd.structural_sig and sn.structural_sig and \
                sn.structural_sig != nd.structural_sig:
            continue
        out.append(sn)
    return out


def plan_merge(
    store: Store,
    subgraph_nodes: list[Node],
    *,
    judge: IdentityJudge | None = None,
    tau_high: float = 0.92,
    tau_low: float = 0.55,
    k: int = 5,
) -> MergePlan:
    """Compute (but do not apply) the merge plan for one paper's nodes."""
    judge = judge or ConservativeJudge()
    plan = MergePlan()

    # L0: exact content-hash index over live store nodes.
    by_hash: dict[tuple[str, str], str] = {}
    for sn in store.nodes.values():
        if not sn.is_tombstone and sn.content_hash:
            by_hash.setdefault((sn.kind, sn.content_hash), sn.id)

    # L2 retrieval index over live store nodes (statement_text).
    emb = HashingEmbedder()
    idx = VectorIndex(store.build_dir, emb)
    idx.vectors = {
        sn.id: emb.embed(sn.statement_text or sn.statement_latex)
        for sn in store.nodes.values()
        if not sn.is_tombstone
    }

    for nd in subgraph_nodes:
        # L0 exact
        hit = by_hash.get((nd.kind, nd.content_hash)) if nd.content_hash else None
        if hit and hit != nd.id:
            plan.items.append(
                PlanItem(nd.id, "merge", canonical_id=hit, verdict="same",
                         confidence=1.0, justification="L0 exact content hash")
            )
            plan.id_map[nd.id] = hit
            continue
        if hit == nd.id:  # same id already present (idempotent re-extract)
            plan.items.append(PlanItem(nd.id, "merge", canonical_id=nd.id,
                                       verdict="same", confidence=1.0,
                                       justification="idempotent re-extract"))
            plan.id_map[nd.id] = nd.id
            continue

        # L1 + L2: cosine within the structural bucket only.
        from .embed import cosine

        bucket_ids = {n.id for n in _bucket(store, nd)}
        q = emb.embed(nd.statement_text or nd.statement_latex)
        scored = sorted(
            ((cid, cosine(q, idx.vectors[cid])) for cid in bucket_ids
             if cid in idx.vectors),
            key=lambda x: x[1],
            reverse=True,
        )[:k]

        decided = False
        review = False
        for cid, score in scored:
            other = store.nodes[cid]
            v = judge.judge(nd, other)
            if v.verdict == "same" and v.confidence >= tau_high:
                plan.items.append(
                    PlanItem(nd.id, "merge", canonical_id=cid, verdict="same",
                             confidence=v.confidence, justification=v.justification,
                             candidates=scored)
                )
                plan.id_map[nd.id] = cid
                decided = True
                break
            if v.verdict in _RELATION_EDGE and v.confidence >= tau_high:
                etype, direction = _RELATION_EDGE[v.verdict]
                src, dst = (nd.id, cid) if direction == "fwd" else (cid, nd.id)
                plan.items.append(
                    PlanItem(nd.id, "new", verdict=v.verdict,
                             confidence=v.confidence, justification=v.justification,
                             relation=(etype.value, src, dst), candidates=scored)
                )
                plan.id_map[nd.id] = nd.id
                decided = True
                break
            if (v.verdict == "same" and tau_low <= v.confidence < tau_high) or \
                    score >= tau_low:
                review = True

        if not decided:
            plan.items.append(
                PlanItem(nd.id, "new", review=review,
                         justification="no confident match",
                         candidates=scored)
            )
            plan.id_map[nd.id] = nd.id

    return plan
