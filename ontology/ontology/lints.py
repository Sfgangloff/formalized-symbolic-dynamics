"""Graph lints (ONTOLOGY_PLAN §8.1–8.4).

These are *not* part of the proof obligation; they guard graph integrity.
``run_lints`` returns issues per lint; the CLI exits non-zero if any
ERROR-level issue is present (WARN does not fail CI).
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .formalize import dependencies
from .schema import EdgeType, NodeKind
from .store import Store

_VALID_KINDS = {k.value for k in NodeKind}
_VALID_ETYPES = {t.value for t in EdgeType}


@dataclass
class LintReport:
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.errors

    def merge(self, other: "LintReport") -> None:
        self.errors += other.errors
        self.warnings += other.warnings


def lint_schema(store: Store) -> LintReport:
    """§8.1 — kinds/types valid; tombstones well-formed."""
    r = LintReport()
    for n in store.nodes.values():
        if n.kind not in _VALID_KINDS:
            r.errors.append(f"node {n.id}: invalid kind {n.kind!r}")
        if n.is_tombstone:
            tgt = n.canonical_id
            if tgt not in store.nodes:
                r.errors.append(f"tombstone {n.id} -> missing {tgt}")
            elif store.nodes[tgt].is_tombstone and store.resolve(n.id) == n.id:
                r.errors.append(f"tombstone {n.id}: unresolved redirect chain")
    for e in store.edges.values():
        if e.type not in _VALID_ETYPES:
            r.errors.append(f"edge {e.id}: invalid type {e.type!r}")
    return r


def lint_dangling(store: Store) -> LintReport:
    """§8.2 — every edge endpoint resolves to a node or a paper."""
    r = LintReport()
    for e in store.edges.values():
        for role, endp in (("src", e.src), ("dst", e.dst)):
            if endp.startswith("arxiv:"):
                if endp not in store.papers:
                    r.warnings.append(
                        f"edge {e.id} {role} {endp}: paper not in store"
                    )
                continue
            resolved = store.resolve(endp)
            if resolved not in store.nodes:
                r.errors.append(
                    f"edge {e.id} {role} {endp} -> {resolved}: dangling"
                )
    return r


def lint_acyclicity(store: Store) -> LintReport:
    """§8.3 — the ordering graph is a DAG; report one offending cycle."""
    r = LintReport()
    deps = dependencies(store)
    color: dict[str, int] = {}  # 0 white, 1 gray, 2 black
    stack: list[str] = []

    def dfs(u: str) -> list[str] | None:
        color[u] = 1
        stack.append(u)
        for v in sorted(deps.get(u, ())):
            if color.get(v, 0) == 1:
                i = stack.index(v)
                return stack[i:] + [v]
            if color.get(v, 0) == 0:
                cyc = dfs(v)
                if cyc:
                    return cyc
        stack.pop()
        color[u] = 2
        return None

    for node in sorted(deps):
        if color.get(node, 0) == 0:
            cyc = dfs(node)
            if cyc:
                r.errors.append("ordering cycle: " + " -> ".join(cyc))
                break
    return r


def lint_lean_sync(store: Store) -> LintReport:
    """§8.4 (partial) — sanity-check ``lean_decl`` shape. Full resolution
    against live Lean declarations is deferred to the Lean-side lint
    (ROADMAP §7) to keep this cheap; here we only flag malformed decls."""
    r = LintReport()
    for n in store.nodes.values():
        if n.lean_decl and (" " in n.lean_decl or n.lean_decl.startswith(".")):
            r.warnings.append(f"node {n.id}: suspicious lean_decl {n.lean_decl!r}")
        if n.lean_decl and not n.lean_status:
            r.warnings.append(f"node {n.id}: lean_decl set but lean_status empty")
    return r


def run_lints(store: Store) -> LintReport:
    report = LintReport()
    for fn in (lint_schema, lint_dangling, lint_acyclicity, lint_lean_sync):
        report.merge(fn(store))
    return report
