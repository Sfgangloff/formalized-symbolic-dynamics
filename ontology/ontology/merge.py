"""Phase D — non-destructive merge into the global graph (§5.2–5.4).

Applies a :class:`~ontology.dedup.MergePlan`:

* merged duplicates fold their provenance/aliases into the survivor and
  leave a redirect **tombstone** (kept, never deleted → reversible, and
  re-extraction stays idempotent);
* every merge is appended to ``merges.jsonl`` with its justification;
* subgraph edges are rewired onto canonical ids with the §5.2 rule —
  an equivalent edge already present is *not* duplicated (its provenance
  is unioned); otherwise the edge is added;
* ambiguous items are added **unmerged** and queued for gate **G3**.
"""

from __future__ import annotations

import datetime as _dt
import json
from pathlib import Path

from .dedup import MergePlan
from .schema import (
    Edge,
    EdgeProvenance,
    EdgeType,
    Merge,
    Node,
    NodeKind,
    edge_id,
)
from .store import Store


def load_subgraph(path: Path) -> tuple[str, list[Node], list[Edge], list[dict]]:
    sg = json.loads(Path(path).read_text())
    nodes = [Node.from_dict(n) for n in sg.get("nodes", [])]
    edges = [Edge.from_dict(e) for e in sg.get("edges", [])]
    return sg["paper"], nodes, edges, sg.get("citations", [])


def _now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def _prov_key(p) -> tuple:
    return (p.paper, p.label, p.env_name, p.char_span)


def _fold_provenance(dst: Node, src: Node) -> None:
    have = {_prov_key(p) for p in dst.provenance}
    for p in src.provenance:
        if _prov_key(p) not in have:
            dst.provenance.append(p)
            have.add(_prov_key(p))
    dst.aliases = sorted(set(dst.aliases) | set(src.aliases)
                         | ({src.name} if src.name else set()))
    dst.tags = sorted(set(dst.tags) | set(src.tags))
    dst.parameters = sorted(set(dst.parameters) | set(src.parameters))
    if not dst.lean_decl and src.lean_decl:
        dst.lean_decl = src.lean_decl
        dst.lean_status = src.lean_status


def _resolve(store: Store, id_map: dict[str, str], nid: str) -> str:
    return store.resolve(id_map.get(nid, nid))


def apply_plan(
    store: Store,
    paper_id: str,
    sg_nodes: list[Node],
    sg_edges: list[Edge],
    plan: MergePlan,
    *,
    run_id: str,
    reviews_dir: Path | None = None,
) -> dict:
    by_id = {n.id: n for n in sg_nodes}
    g3: list[dict] = []
    added_nodes = merged = added_edges = deduped_edges = 0

    for item in plan.items:
        nd = by_id.get(item.incoming_id)
        if nd is None:
            continue

        if item.action == "merge" and item.canonical_id != item.incoming_id:
            canonical = store.nodes.get(item.canonical_id)
            if canonical is None:
                continue
            _fold_provenance(canonical, nd)
            if item.incoming_id not in canonical.merged_from:
                canonical.merged_from.append(item.incoming_id)
            canonical.updated_run = run_id
            # redirect tombstone (kept forever; §5.2)
            if item.incoming_id not in store.nodes:
                store.nodes[item.incoming_id] = Node(
                    id=item.incoming_id,
                    kind=NodeKind.ALIAS.value,
                    canonical_id=item.canonical_id,
                    created_run=run_id,
                    updated_run=run_id,
                )
            store.merges.append(
                Merge(
                    losing_id=item.incoming_id,
                    canonical_id=item.canonical_id,
                    verdict=item.verdict or "same",
                    confidence=item.confidence,
                    run_id=run_id,
                    justification=item.justification,
                    ts=_now(),
                )
            )
            merged += 1
            continue

        # action == "new" (or idempotent self-merge): upsert the node
        existing = store.nodes.get(nd.id)
        if existing is not None and not existing.is_tombstone:
            _fold_provenance(existing, nd)      # same node, another paper
            existing.updated_run = run_id
        else:
            nd.created_run = nd.created_run or run_id
            nd.updated_run = run_id
            store.nodes[nd.id] = nd
            added_nodes += 1

        if item.relation:
            etype, rsrc, rdst = item.relation
            _add_edge(
                store,
                EdgeType(etype),
                _resolve(store, plan.id_map, rsrc),
                _resolve(store, plan.id_map, rdst),
                paper_id,
                run_id,
                proved="claimed" if etype == EdgeType.EQUIVALENT_TO.value else "",
            )
            added_edges += 1

        if item.review:
            g3.append(
                {
                    "incoming_id": item.incoming_id,
                    "paper": paper_id,
                    "statement": nd.statement_text[:500],
                    "kind": nd.kind,
                    "candidates": item.candidates,
                    "justification": item.justification,
                    "run_id": run_id,
                }
            )

    # rewire + add subgraph edges (§5.2 step 3)
    for e in sg_edges:
        src = e.src if e.src.startswith("arxiv:") else _resolve(store, plan.id_map, e.src)
        dst = e.dst if e.dst.startswith("arxiv:") else _resolve(store, plan.id_map, e.dst)
        if not _endpoint_ok(store, src) or not _endpoint_ok(store, dst):
            continue
        if _add_edge(
            store, EdgeType(e.type), src, dst, paper_id, run_id,
            where_=e.where_, regime=e.regime, proved=e.proved,
            existing_prov=e.provenance,
        ):
            added_edges += 1
        else:
            deduped_edges += 1

    if g3 and reviews_dir is not None:
        enqueue_g3(reviews_dir, g3)

    return {
        "added_nodes": added_nodes,
        "merged": merged,
        "added_edges": added_edges,
        "deduped_edges": deduped_edges,
        "g3_queued": len(g3),
    }


def _endpoint_ok(store: Store, nid: str) -> bool:
    return nid.startswith("arxiv:") or nid in store.nodes


def _add_edge(
    store: Store,
    etype: EdgeType,
    src: str,
    dst: str,
    paper_id: str,
    run_id: str,
    *,
    where_: str = "",
    regime: str = "",
    proved: str = "",
    existing_prov: list | None = None,
) -> bool:
    """Add an edge, or union provenance into the equivalent existing one
    (§5.2: same type+endpoints+regime is not duplicated). Returns True iff
    a new edge was created."""
    eid = edge_id(etype, src, dst, regime)
    prov = list(existing_prov or []) or [
        EdgeProvenance(paper=paper_id, run_id=run_id)
    ]
    if eid in store.edges:
        ex = store.edges[eid]
        have = {(p.paper, p.char_span) for p in ex.provenance}
        for p in prov:
            if (p.paper, p.char_span) not in have:
                ex.provenance.append(p)
        # in_statement is the binding constraint for Phase E ordering;
        # upgrade deterministically so the kept edge is order-independent.
        if where_ == "in_statement" and ex.where_ == "in_proof":
            ex.where_ = "in_statement"
        return False
    store.edges[eid] = Edge(
        id=eid, type=etype.value, src=src, dst=dst, regime=regime,
        where_=where_, proved=proved, provenance=prov,
    )
    return True


def enqueue_g3(reviews_dir: Path, records: list[dict]) -> str:
    reviews_dir = Path(reviews_dir)
    reviews_dir.mkdir(parents=True, exist_ok=True)
    path = reviews_dir / "G3_merge_queue.jsonl"
    with open(path, "a", encoding="utf-8") as fh:
        for r in records:
            fh.write(json.dumps(r, sort_keys=True) + "\n")
    return str(path)


def canonicalize_components(store: Store) -> int:
    """§5.3: union-find the ``same_as`` closure, repoint edges to the
    component representative, tombstone the rest. Returns #collapsed."""
    parent: dict[str, str] = {}

    def find(x: str) -> str:
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a: str, b: str) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            # deterministic representative: lexicographically smallest id
            lo, hi = sorted((ra, rb))
            parent[hi] = lo

    for e in list(store.edges.values()):
        if e.type == EdgeType.SAME_AS.value:
            union(e.src, e.dst)

    collapsed = 0
    for nid in list(store.nodes):
        rep = find(nid)
        if rep != nid and not store.nodes[nid].is_tombstone:
            _fold_provenance(store.nodes[rep], store.nodes[nid])
            store.nodes[nid] = Node(
                id=nid, kind=NodeKind.ALIAS.value, canonical_id=rep,
            )
            collapsed += 1
    if collapsed:
        for e in list(store.edges.values()):
            ns, nd = find(e.src), find(e.dst)
            if (ns, nd) != (e.src, e.dst):
                del store.edges[e.id]
                _add_edge(
                    store, EdgeType(e.type), ns, nd, "", "",
                    where_=e.where_, regime=e.regime, proved=e.proved,
                    existing_prov=e.provenance,
                )
    return collapsed
