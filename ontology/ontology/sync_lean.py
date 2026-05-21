"""``onto sync-lean`` — reconcile ontology nodes with the Lean repo.

Implements the back-annotation half of ONTOLOGY_PLAN §6.4. A Lean
declaration is back-linked to a graph node by a doc-comment marker
immediately above (or in the docstring of) the declaration:

    -- @ontology: hm:thm:3.1
    theorem topEntropy_rightRE ...

    -- @ontology: hm:thm:1.1 [sorry]    (explicit status override)
    theorem SFT_entropy_iff_rightRE ...

This module reads every ``.lean`` file under a configured ``lean_root``
(default ``../SymbolicDynamics``), pairs each annotation with the next
declaration, infers ``lean_status`` from the declaration keyword plus a
sorry-scan, resolves the slug against ``node.id`` or ``node.aliases``,
and writes back ``lean_decl`` + ``lean_status`` onto the matched node.

Idempotent. Re-running with no Lean changes touches nothing.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable

from .store import Store

# A doc-comment marker — its own line, anywhere within the comment block
# before a declaration. Optional ``[status]`` overrides the inference.
ANNOTATION_RE = re.compile(
    r"^\s*--\s*@ontology:\s*(?P<slug>[^\s\[\]]+)"
    r"(?:\s*\[(?P<status>[^\]]+)\])?\s*$"
)

# Top-level declaration head. Tolerates attributes + visibility modifiers.
DECL_RE = re.compile(
    r"^(?:\s*@\[[^\]]*\]\s*)*"
    r"(?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+)*"
    r"(?P<kw>theorem|lemma|def|abbrev|structure|class|instance|axiom)\b"
    r"\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
)

_KW_TO_STATUS_DEFAULT = {
    "axiom": "axiomatized",
    "def": "stated", "abbrev": "stated", "structure": "stated",
    "class": "stated", "instance": "stated",
}


@dataclass
class Annotation:
    slug: str
    status_override: str
    file_rel: str
    line: int
    lean_name: str
    kw: str
    has_sorry: bool


@dataclass
class SyncReport:
    files_scanned: int = 0
    annotations: int = 0
    updated: int = 0
    unchanged: int = 0
    unresolved: list[str] = field(default_factory=list)
    no_decl: list[str] = field(default_factory=list)
    stale_lean_decl: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not (self.unresolved or self.no_decl)


def default_status_for(kw: str, has_sorry: bool) -> str:
    if kw in ("theorem", "lemma"):
        return "sorry" if has_sorry else "proved"
    return _KW_TO_STATUS_DEFAULT.get(kw, "")


def module_path(file_rel: str) -> str:
    """``papers/HM/HM.lean`` -> ``papers.HM.HM``."""
    p = file_rel.replace("\\", "/")
    if p.endswith(".lean"):
        p = p[:-5]
    return p.replace("/", ".")


def _strip_comments(text: str) -> str:
    """Remove ``/- … -/`` blocks (nesting aware) and ``--`` line comments.
    Used so the sorry scan doesn't trip on ``-- TODO: sorry``."""
    out: list[str] = []
    i, L = 0, len(text)
    depth = 0
    while i < L:
        if text[i:i + 2] == "/-":
            depth += 1
            i += 2
            continue
        if depth > 0:
            if text[i:i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if text[i:i + 2] == "--":
            j = text.find("\n", i)
            if j == -1:
                break
            i = j
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


_NAMESPACE_OPEN_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
_SECTION_OPEN_RE = re.compile(r"^\s*section\b(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
_END_RE = re.compile(r"^\s*end\b(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")


def _namespace_at_line(lines: list[str], target_line: int) -> str:
    """Return the dotted namespace path effective at ``target_line``
    (0-indexed), tracking ``namespace``/``section`` opens and ``end``
    closes. Sections do not contribute to the namespace path."""
    stack: list[tuple[str, str]] = []  # (kind, name); kind ∈ {"ns", "sec"}
    for i in range(min(target_line, len(lines))):
        ln = lines[i]
        if (m := _NAMESPACE_OPEN_RE.match(ln)):
            stack.append(("ns", m.group(1)))
            continue
        if (m := _SECTION_OPEN_RE.match(ln)):
            stack.append(("sec", m.group(1) or ""))
            continue
        if (m := _END_RE.match(ln)):
            name = m.group(1) or ""
            if not stack:
                continue
            if not name:
                stack.pop()
                continue
            for j in range(len(stack) - 1, -1, -1):
                if stack[j][1] == name:
                    del stack[j:]
                    break
    return ".".join(n for (kind, n) in stack if kind == "ns" and n)


def parse_file(path: Path, file_rel: str | None = None) -> list[Annotation]:
    """Pair every ``-- @ontology:`` annotation in ``path`` with the next
    top-level declaration, scanning its body for ``sorry``. Tracks the
    enclosing ``namespace`` so the recorded ``lean_name`` is the fully
    namespace-qualified identifier (e.g. ``Pattern.GloballyAdmissible``
    when the decl is inside ``namespace Pattern``)."""
    file_rel = file_rel or str(path)
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    decls: list[tuple[int, str, str]] = []
    for idx, ln in enumerate(lines):
        m = DECL_RE.match(ln)
        if m:
            ns = _namespace_at_line(lines, idx)
            bare = m.group("name")
            qualified = f"{ns}.{bare}" if ns else bare
            decls.append((idx, m.group("kw"), qualified))

    out: list[Annotation] = []
    for idx, ln in enumerate(lines):
        m = ANNOTATION_RE.match(ln)
        if not m:
            continue
        slug = m.group("slug").strip()
        status = (m.group("status") or "").strip()
        # next decl strictly after this line
        target = next(((di, kw, nm) for (di, kw, nm) in decls if di > idx), None)
        if target is None:
            out.append(Annotation(slug, status, file_rel, idx + 1, "", "", False))
            continue
        decl_line, kw, name = target
        # body span = decl line .. next decl line (or EOF)
        nxt = next((di for (di, _, _) in decls if di > decl_line), len(lines))
        body = "\n".join(lines[decl_line:nxt])
        has_sorry = bool(re.search(r"\bsorry\b", _strip_comments(body)))
        out.append(
            Annotation(slug, status, file_rel, decl_line + 1, name, kw, has_sorry)
        )
    return out


def resolve_slug(store: Store, slug: str) -> str | None:
    """Resolve a doc-comment slug to a node id. Exact id beats alias
    match; an alias matching multiple nodes is unresolvable
    (ambiguous -> caller surfaces a warning)."""
    if slug in store.nodes and not store.nodes[slug].is_tombstone:
        return slug
    hits = [
        n.id for n in store.nodes.values()
        if not n.is_tombstone and slug in n.aliases
    ]
    return hits[0] if len(hits) == 1 else None


def sync(
    store: Store,
    lean_root: Path,
    *,
    log: Callable[[str], None] = lambda _: None,
) -> SyncReport:
    """Walk ``lean_root`` for ``.lean`` files, harvest annotations, and
    push them into the graph. ``store.save`` is the caller's job."""
    r = SyncReport()
    lean_root = Path(lean_root).resolve()
    if not lean_root.exists():
        raise FileNotFoundError(f"lean_root {lean_root} does not exist")
    for path in sorted(lean_root.rglob("*.lean")):
        if any(part in (".lake", "build") for part in path.parts):
            continue
        rel = str(path.relative_to(lean_root))
        r.files_scanned += 1
        for a in parse_file(path, file_rel=rel):
            r.annotations += 1
            if not a.lean_name:
                r.no_decl.append(f"{rel}:{a.line}: @ontology {a.slug!r} with no following decl")
                continue
            nid = resolve_slug(store, a.slug)
            if nid is None:
                r.unresolved.append(f"{rel}:{a.line}: slug {a.slug!r} not in graph")
                continue
            n = store.nodes[nid]
            lean_decl = f"{module_path(rel)}.{a.lean_name}"
            status = a.status_override or default_status_for(a.kw, a.has_sorry)
            if n.lean_decl and n.lean_decl != lean_decl:
                r.stale_lean_decl.append(
                    f"{nid}: lean_decl was {n.lean_decl!r}, now {lean_decl!r}"
                )
            if n.lean_decl == lean_decl and n.lean_status == status:
                r.unchanged += 1
            else:
                n.lean_decl = lean_decl
                n.lean_status = status
                r.updated += 1
                log(f"  {rel}:{a.line}  {a.slug}  ->  {lean_decl}  [{status}]")
    return r
