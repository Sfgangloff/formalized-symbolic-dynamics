"""Phase C — per-paper subgraph extraction (ONTOLOGY_PLAN §4.2).

A deterministic LaTeX pass does the structural work that needs no model:

* learn ``\\newtheorem`` env → kind map (env names are per-paper);
* capture every theorem-like / definition / proof environment with its
  ``\\label`` and source span;
* resolve in-paper ``\\ref``/``\\cref`` into ``depends_on`` edges, tagged
  ``in_statement`` vs ``in_proof`` by where the ref occurs;
* collect ``\\cite`` keys for the deferred cross-paper resolver.

The model-driven passes the plan also calls for — prose definitions not
in an environment, proof-mining, subtle relation extraction (§4.2 steps
2–4) — sit behind :class:`Extractor`. The default :class:`NullExtractor`
adds nothing, so the structural baseline is exact and reproducible; the
LLM extractor is wired at the pilot (Milestone 2).

Output: ``corpus/<id>/subgraph.json`` (validated, NOT yet merged — Phase
D does the merge). A per-batch sample is written for gate **G2**.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Callable, Protocol, runtime_checkable

from .acquire import arxiv_dir_name
from .normalize import content_hash, structural_sig
from .schema import (
    Edge,
    EdgeProvenance,
    EdgeType,
    Node,
    NodeKind,
    Provenance,
    edge_id,
    new_run_id,
    node_id,
)
from .store import Store

_COMMENT = re.compile(r"(?<!\\)%.*?$", re.MULTILINE)
_NEWTHM = re.compile(
    r"\\newtheorem\*?\s*\{(?P<env>[^}]+)\}\s*(?:\[[^\]]*\])?\s*\{(?P<disp>[^}]+)\}"
)
_LABEL = re.compile(r"\\label\s*\{([^}]+)\}")
_REF = re.compile(r"\\(?:eqref|autoref|cref|Cref|ref)\s*\{([^}]+)\}")
_CITE = re.compile(r"\\(?:cite[a-zA-Z]*)\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}")
_SECTION = re.compile(r"\\(?:sub)*section\*?\s*\{([^}]+)\}")

# Display-name → node kind. Matched case-insensitively on the second
# \newtheorem argument; falls back to the env token itself.
_DISPLAY_KIND = {
    "theorem": NodeKind.THEOREM,
    "lemma": NodeKind.LEMMA,
    "proposition": NodeKind.PROPOSITION,
    "corollary": NodeKind.COROLLARY,
    "definition": NodeKind.DEFINITION,
    "conjecture": NodeKind.CONJECTURE,
    "problem": NodeKind.OPEN_PROBLEM,
    "question": NodeKind.OPEN_PROBLEM,
    "open problem": NodeKind.OPEN_PROBLEM,
    "claim": NodeKind.CLAIM,
    "example": NodeKind.EXAMPLE,
    "counterexample": NodeKind.COUNTEREXAMPLE,
}
_DEFAULT_ENV_KIND = {
    "thm": NodeKind.THEOREM, "theorem": NodeKind.THEOREM,
    "lem": NodeKind.LEMMA, "lemma": NodeKind.LEMMA,
    "prop": NodeKind.PROPOSITION, "proposition": NodeKind.PROPOSITION,
    "cor": NodeKind.COROLLARY, "corollary": NodeKind.COROLLARY,
    "defn": NodeKind.DEFINITION, "dfn": NodeKind.DEFINITION,
    "def": NodeKind.DEFINITION, "definition": NodeKind.DEFINITION,
    "conj": NodeKind.CONJECTURE, "conjecture": NodeKind.CONJECTURE,
    "prob": NodeKind.OPEN_PROBLEM, "problem": NodeKind.OPEN_PROBLEM,
    "ques": NodeKind.OPEN_PROBLEM, "question": NodeKind.OPEN_PROBLEM,
    "claim": NodeKind.CLAIM,
    "ex": NodeKind.EXAMPLE, "example": NodeKind.EXAMPLE,
}


@runtime_checkable
class Extractor(Protocol):
    """Model-driven supplement to the structural pass (§4.2 steps 2–4)."""

    name: str

    def extract(
        self, paper_id: str, tex: str, base_nodes: list[Node]
    ) -> tuple[list[Node], list[Edge]]:
        ...


class NullExtractor:
    """Default: structural-only. Reproducible, no model."""

    name = "structural"

    def extract(self, paper_id, tex, base_nodes):  # noqa: D102
        return [], []


def strip_comments(tex: str) -> str:
    return _COMMENT.sub("", tex)


def read_paper_tex(corpus_dir: Path, arxiv_id: str) -> str:
    """Concatenate all .tex under corpus/<id>/ (sorted; \\input order is
    a known approximation — good enough for env/label/ref extraction)."""
    base = Path(corpus_dir) / arxiv_dir_name(arxiv_id)
    if not base.exists():
        return ""
    parts = []
    for p in sorted(base.rglob("*.tex")):
        try:
            parts.append(p.read_text(encoding="utf-8", errors="replace"))
        except OSError:
            continue
    return "\n".join(parts)


def learn_theorem_map(tex: str) -> dict[str, NodeKind]:
    m = dict(_DEFAULT_ENV_KIND)
    for mo in _NEWTHM.finditer(tex):
        env = mo.group("env").strip()
        disp = mo.group("disp").strip().lower()
        kind = _DISPLAY_KIND.get(disp)
        if kind is None:
            for key, k in _DISPLAY_KIND.items():
                if key in disp:
                    kind = k
                    break
        if kind is not None:
            m[env] = kind
    return m


def _find_envs(tex: str, env: str):
    """Yield (name_opt, body, start, end) for each \\begin{env}..\\end{env}.
    Non-greedy; same-env nesting is rare in math papers and tolerated."""
    pat = re.compile(
        r"\\begin\s*\{" + re.escape(env) + r"\}\s*(\[[^\]]*\])?(.*?)\\end\s*\{"
        + re.escape(env) + r"\}",
        re.DOTALL,
    )
    for mo in pat.finditer(tex):
        name = (mo.group(1) or "").strip("[]").strip()
        yield name, mo.group(2), mo.start(), mo.end()


def _section_at(tex: str, pos: int) -> str:
    last = ""
    for mo in _SECTION.finditer(tex):
        if mo.start() > pos:
            break
        last = mo.group(1).strip()
    return last


def extract_paper(
    paper_id: str,
    tex: str,
    run_id: str,
    extractors: list[Extractor] | None = None,
) -> dict:
    """Produce a per-paper subgraph dict (not merged)."""
    tex = strip_comments(tex)
    tmap = learn_theorem_map(tex)
    nodes: list[Node] = []
    edges: list[Edge] = []
    label_to_node: dict[str, str] = {}
    citations: list[dict] = []

    # 1. statement-bearing environments
    stmt_spans: list[tuple[int, int, str]] = []  # (start, end, node_id)
    for env, kind in tmap.items():
        for name, body, start, end in _find_envs(tex, env):
            nid = node_id(kind, body)
            labels = _LABEL.findall(body)
            n = Node(
                id=nid,
                kind=kind.value,
                name=name,
                statement_latex=body.strip(),
                statement_text=" ".join(body.split())[:2000],
                content_hash=content_hash(kind.value, body),
                created_run=run_id,
                updated_run=run_id,
                provenance=[
                    Provenance(
                        paper=paper_id,
                        label=labels[0] if labels else "",
                        env_name=env,
                        section=_section_at(tex, start),
                        char_span=f"{start}:{end}",
                        run_id=run_id,
                    )
                ],
            )
            n.structural_sig = structural_sig(
                kind.value, n.tags, n.hypotheses, n.parameters
            )
            nodes.append(n)
            for lb in labels:
                label_to_node[lb] = nid
            stmt_spans.append((start, end, nid))
            # paper -> node provenance edge
            etype = (
                EdgeType.DEFINES
                if kind == NodeKind.DEFINITION
                else EdgeType.STATES
            )
            edges.append(
                Edge(
                    id=edge_id(etype, paper_id, nid),
                    type=etype.value,
                    src=paper_id,
                    dst=nid,
                    provenance=[EdgeProvenance(paper=paper_id, run_id=run_id)],
                )
            )
            # in-statement \ref dependencies
            for ref in _REF.findall(body):
                _add_dep(edges, nid, ref, "in_statement", paper_id, run_id)
            for ck in _CITE.findall(body):
                for key in ck.split(","):
                    citations.append(
                        {"key": key.strip(), "from_node": nid, "where": "in_statement"}
                    )

    stmt_spans.sort()

    # 2. proofs -> attach to nearest preceding statement (proof-mining of
    #    explicit refs; deep proof-mining is the LLM extractor's job)
    for _name, body, start, _end in _find_envs(tex, "proof"):
        owner = None
        for s, e, nid in stmt_spans:
            if e <= start:
                owner = nid
            else:
                break
        if owner is None:
            continue
        for ref in _REF.findall(body):
            _add_dep(edges, owner, ref, "in_proof", paper_id, run_id)
        for ck in _CITE.findall(body):
            for key in ck.split(","):
                citations.append(
                    {"key": key.strip(), "from_node": owner, "where": "in_proof"}
                )

    # 3. rewrite \ref edges (dst was a label) to node ids now all known
    for e in edges:
        if e.type == EdgeType.DEPENDS_ON.value and e.dst.startswith("label:"):
            lbl = e.dst[len("label:") :]
            e.dst = label_to_node.get(lbl, e.dst)

    # 4. model-driven supplements (prose defs / relations / proof-mining)
    for ex in extractors or []:
        en, ee = ex.extract(paper_id, tex, nodes)
        nodes.extend(en)
        edges.extend(ee)

    # drop unresolved label refs (dangling) — they'd fail the §8.2 lint
    edges = [
        e for e in edges if not e.dst.startswith("label:")
    ]
    return {
        "paper": paper_id,
        "run_id": run_id,
        "extractors": ["structural"] + [e.name for e in (extractors or [])],
        "nodes": [n.to_dict() for n in nodes],
        "edges": [e.to_dict() for e in edges],
        "citations": citations,
    }


def _add_dep(edges, src, ref_label, where, paper_id, run_id):
    dst = f"label:{ref_label}"
    eid = edge_id(EdgeType.DEPENDS_ON, src, dst, where)
    edges.append(
        Edge(
            id=eid,
            type=EdgeType.DEPENDS_ON.value,
            src=src,
            dst=dst,
            where_=where,
            provenance=[EdgeProvenance(paper=paper_id, run_id=run_id)],
        )
    )


def validate_subgraph(sg: dict) -> list[str]:
    """Schema-shape validation (§8.1) of a per-paper subgraph."""
    errs: list[str] = []
    ids = set()
    valid_kinds = {k.value for k in NodeKind}
    valid_etypes = {t.value for t in EdgeType}
    for nd in sg.get("nodes", []):
        if nd["id"] in ids:
            errs.append(f"duplicate node id {nd['id']}")
        ids.add(nd["id"])
        if nd["kind"] not in valid_kinds:
            errs.append(f"bad kind {nd['kind']} on {nd['id']}")
    known = ids | {sg["paper"]}
    for ed in sg.get("edges", []):
        if ed["type"] not in valid_etypes:
            errs.append(f"bad edge type {ed['type']}")
        for endp in (ed["src"], ed["dst"]):
            # Only flag unresolved extraction placeholders. Cross-subgraph
            # references (to concepts or to nodes in another paper's gold)
            # are normal — the merger resolves them against the global store.
            if endp.startswith("label:") and endp not in known:
                errs.append(f"edge {ed['id']} endpoint {endp} unresolved label")
    return errs


def run_extract(
    store: Store,
    corpus_dir: Path,
    *,
    only: list[str] | None = None,
    run_id: str | None = None,
    extractors: list[Extractor] | None = None,
    log: Callable[[str], None] = print,
) -> dict:
    """Extract subgraphs for the given papers (or all acquired ones)."""
    run_id = run_id or new_run_id()
    if only:
        pids = [p for p in only if p in store.papers]
    else:
        pids = [
            p.id for p in store.papers.values() if p.fidelity_tier in
            ("source", "text")
        ]
    summary = {"papers": 0, "nodes": 0, "edges": 0, "invalid": 0}
    for i, pid in enumerate(sorted(pids)):
        arxiv_id = pid.split("arxiv:", 1)[-1]
        tex = read_paper_tex(corpus_dir, arxiv_id)
        if not tex.strip():
            log(f"  [{i+1}/{len(pids)}] {pid}: no source, skipped")
            continue
        sg = extract_paper(pid, tex, run_id, extractors)
        errs = validate_subgraph(sg)
        out = Path(corpus_dir) / arxiv_dir_name(arxiv_id) / "subgraph.json"
        out.write_text(json.dumps(sg, indent=2, sort_keys=True))
        summary["papers"] += 1
        summary["nodes"] += len(sg["nodes"])
        summary["edges"] += len(sg["edges"])
        if errs:
            summary["invalid"] += 1
            log(f"  [{i+1}/{len(pids)}] {pid}: {len(sg['nodes'])} nodes "
                f"({len(errs)} validation errors)")
        else:
            log(f"  [{i+1}/{len(pids)}] {pid}: {len(sg['nodes'])} nodes, "
                f"{len(sg['edges'])} edges")
    return summary


def write_g2_sample(
    corpus_dir: Path, reviews_dir: Path, batch: str, sample_ids: list[str]
) -> str:
    """Write a G2 review sheet for a batch sample (§4.2 step 6)."""
    reviews_dir = Path(reviews_dir)
    reviews_dir.mkdir(parents=True, exist_ok=True)
    lines = [f"# G2 — extraction sample (batch {batch})\n",
             "Check node recall / edge correctness / regime tags vs the PDF.\n",
             "Sign off: `onto gate sign G2:" + batch + "`\n"]
    for pid in sample_ids:
        arxiv_id = pid.split("arxiv:", 1)[-1]
        sgp = Path(corpus_dir) / arxiv_dir_name(arxiv_id) / "subgraph.json"
        if not sgp.exists():
            continue
        sg = json.loads(sgp.read_text())
        lines.append(f"\n## {pid} — {len(sg['nodes'])} nodes, "
                     f"{len(sg['edges'])} edges\n")
        for nd in sg["nodes"][:40]:
            lines.append(f"- **{nd['kind']}** {nd.get('name') or ''} "
                         f"`{nd['id']}` — {nd['statement_text'][:160]}")
    path = reviews_dir / f"G2_sample_{batch}.md"
    path.write_text("\n".join(lines), encoding="utf-8")
    return str(path)
