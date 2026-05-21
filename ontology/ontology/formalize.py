"""Phase E — formalization driver (ONTOLOGY_PLAN §6).

The graph *orders* formalization. Ordering edges are
``uses_definition`` ∪ ``depends_on`` restricted to ``in_statement``
(``in_proof`` deps don't block *stating* a node — matching the existing
axiomatize-then-derive practice). ``onto next`` returns the ready,
not-yet-formalized nodes nearest the roots, optionally restricted to the
dependency closure of a target subgraph.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .schema import EdgeType, NodeKind
from .store import Store

_FORMALIZABLE = {
    NodeKind.DEFINITION.value, NodeKind.THEOREM.value, NodeKind.LEMMA.value,
    NodeKind.PROPOSITION.value, NodeKind.COROLLARY.value,
    NodeKind.CONSTRUCTION.value, NodeKind.CONJECTURE.value,
    NodeKind.OPEN_PROBLEM.value,
}
# A node is "formalized" when its Lean status indicates the work is done.
# Two regimes:
#   * Terminal-at-stated kinds (definitions, constructions, **open
#     problems**, conjectures): a Lean def of the object / statement
#     either exists or it doesn't. An open problem stated in Lean IS its
#     Lean-side formalization — there's nothing further to prove (proving
#     it would resolve it, after which it's a theorem, not an open
#     problem).
#   * Result kinds (theorem, lemma, proposition, corollary): ``stated``
#     means the statement is in Lean but the proof is still missing
#     (sorry / not_started); only ``proved`` / ``axiomatized`` count.
_FORMALIZED_FOR_STATED_TERMINAL = {"proved", "axiomatized", "stated"}
_FORMALIZED_FOR_RESULT = {"proved", "axiomatized"}
_STATED_TERMINAL_KINDS = {
    NodeKind.DEFINITION.value,
    NodeKind.CONSTRUCTION.value,
    NodeKind.OPEN_PROBLEM.value,
    NodeKind.CONJECTURE.value,
}


def _is_formalized(node) -> bool:
    if node.kind in _STATED_TERMINAL_KINDS:
        return node.lean_status in _FORMALIZED_FOR_STATED_TERMINAL
    return node.lean_status in _FORMALIZED_FOR_RESULT


def _is_ordering_edge(e) -> bool:
    if e.type == EdgeType.USES_DEFINITION.value:
        return True
    return e.type == EdgeType.DEPENDS_ON.value and e.where_ == "in_statement"


def dependencies(store: Store) -> dict[str, set[str]]:
    """node -> set of statement-prerequisite nodes (resolved through
    merge tombstones)."""
    deps: dict[str, set[str]] = {
        nid: set() for nid, n in store.nodes.items()
        if not n.is_tombstone and n.kind in _FORMALIZABLE
    }
    for e in store.edges.values():
        if not _is_ordering_edge(e):
            continue
        src, dst = store.resolve(e.src), store.resolve(e.dst)
        if src in deps and dst in deps and src != dst:
            deps[src].add(dst)
    return deps


def target_closure(store: Store, targets: list[str]) -> set[str]:
    """All nodes a target transitively depends on (the §6.1 subgraph)."""
    deps = dependencies(store)
    seen: set[str] = set()
    frontier = [store.resolve(t) for t in targets]
    while frontier:
        cur = frontier.pop()
        if cur in seen or cur not in deps:
            continue
        seen.add(cur)
        frontier.extend(deps[cur])
    return seen


def topo_order(store: Store, restrict: set[str] | None = None) -> list[str]:
    """Kahn topological order, roots (no prerequisites) first.
    Determics ties by id. A residual cycle is appended sorted (the §8.3
    lint is what flags it as an error)."""
    deps = dependencies(store)
    if restrict is not None:
        deps = {k: (v & restrict) for k, v in deps.items() if k in restrict}
    indeg = {k: len(v) for k, v in deps.items()}
    succ: dict[str, list[str]] = {k: [] for k in deps}
    for k, vs in deps.items():
        for v in vs:
            succ.setdefault(v, []).append(k)
    ready = sorted(k for k, d in indeg.items() if d == 0)
    order: list[str] = []
    while ready:
        n = ready.pop(0)
        order.append(n)
        for m in sorted(succ.get(n, [])):
            indeg[m] -= 1
            if indeg[m] == 0:
                ready.append(m)
                ready.sort()
    leftover = sorted(k for k in deps if k not in set(order))
    return order + leftover


@dataclass
class NextTarget:
    id: str
    kind: str
    name: str
    statement_text: str
    deps: list[str] = field(default_factory=list)
    unformalized_deps: list[str] = field(default_factory=list)


def next_targets(
    store: Store,
    *,
    target: list[str] | None = None,
    limit: int = 5,
) -> list[NextTarget]:
    """Ready, not-yet-formalized nodes in root→leaf order (§6.1)."""
    restrict = target_closure(store, target) if target else None
    deps = dependencies(store)
    out: list[NextTarget] = []
    for nid in topo_order(store, restrict):
        node = store.nodes.get(nid)
        if node is None or _is_formalized(node):
            continue
        unfo = sorted(
            d for d in deps.get(nid, ())
            if store.nodes.get(d) is not None
            and not _is_formalized(store.nodes[d])
        )
        if unfo:
            continue  # not ready: a statement-dependency is unformalized
        out.append(
            NextTarget(
                id=nid,
                kind=node.kind,
                name=node.name,
                statement_text=node.statement_text[:300],
                deps=sorted(deps.get(nid, ())),
            )
        )
        if len(out) >= limit:
            break
    return out
