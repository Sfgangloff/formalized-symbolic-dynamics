"""Bootstrap gold — Kari–Culik / open-problems Lean assets.

Batch-1 of the §6.5 cycle: every formalized line in the Kari–Culik
neighborhood (deps + axioms + the three open problems + the partial
right-r.e. trajectory result) becomes a back-linked graph node. After
this lands and `onto sync-lean` runs, the graph mirrors *all* the
already-formalized assets in the repo, not just the HM spine.

Per §6.5: bootstrap is the *same* operation as the steady-state cycle —
this file curates Lean back-links the same way the HM gold did, just
for nodes that don't all live in a single paper.

Run::

    uv run python gold/build_kari_culik_bootstrap.py
"""

from __future__ import annotations

import json
from pathlib import Path

from ontology.extract import validate_subgraph
from ontology.normalize import content_hash, structural_sig
from ontology.schema import (
    Edge,
    EdgeProvenance,
    EdgeType,
    Node,
    NodeKind,
    Provenance,
    edge_id,
    node_id,
)

# Primary paper for the bootstrap = DGG 2013 (where the 14-tile variant
# + positive-entropy theorem in our codebase originate). Per-node
# attribution to other papers via `attributed_to` edges below.
PAPER = "arxiv:1312.4126"
RUN = "gold-kc-bootstrap-2026-05-20"

nodes: list[Node] = []
edges: list[Edge] = []
_seen: set[str] = set()


def N(kind, slug, *, name, latex, text, tags=None, parameters=None,
      status="", lean_decl="", lean_status="", section="", env_name="prose"):
    nid = node_id(kind, slug)
    if nid in _seen:
        raise ValueError(f"duplicate id {nid}")
    _seen.add(nid)
    aliases = [slug] if slug != nid else []
    n = Node(
        id=nid, kind=kind.value, name=name,
        statement_latex=latex, statement_text=text,
        tags=tags or [], parameters=parameters or [], status=status,
        aliases=aliases,
        content_hash=content_hash(kind.value, latex) if latex else "",
        structural_sig=structural_sig(kind.value, tags or [], [], parameters or []),
        lean_decl=lean_decl, lean_status=lean_status,
        provenance=[
            Provenance(paper=PAPER, section=section, env_name=env_name,
                       run_id=RUN, human_verified=True)
        ] if kind != NodeKind.CONCEPT else [],
        created_run=RUN, updated_run=RUN,
    )
    nodes.append(n)
    return nid


def E(etype, src, dst, *, where_="", regime="", notes=""):
    eid = edge_id(etype, src, dst, regime)
    edges.append(
        Edge(id=eid, type=etype.value, src=src, dst=dst,
             where_=where_, regime=regime, notes=notes, human_verified=True,
             provenance=[EdgeProvenance(paper=PAPER, run_id=RUN)])
    )


# -------------------------------------------------------------------------
# The named mathematical object: the Kari–Culik shift (DGG 14-tile variant).
# -------------------------------------------------------------------------
KC_TILES = N(
    NodeKind.CONSTRUCTION, "kari-culik-tile-set",
    name="Kari–Culik 14-tile Wang set (DGG variant)",
    latex=r"A Wang tileset of $|T|=14$ tiles whose horizontal alphabet is $\mathbb{F}_3$ and vertical alphabet is $\mathbb{F}_6=\mathbb{F}_2\times\mathbb{F}_3$, defined explicitly via the maps $\mathrm{kcN},\mathrm{kcS}:T\to\mathbb{F}_3$ and $\mathrm{kcE},\mathrm{kcW}:T\to\mathbb{F}_6$.",
    text="The DGG 14-tile Wang set that defines the Kari–Culik shift.",
    section="DGG 2013 §2", tags=["wang", "kari-culik", "construction"],
    lean_decl="dependencies.KariCulik.KCTile", lean_status="stated",
)
KC_SHIFT = N(
    NodeKind.CONSTRUCTION, "kari-culik-shift",
    name="Kari–Culik shift (2D SFT, DGG variant)",
    latex=r"$X_{\mathrm{KC}}\subseteq T^{\mathbb{Z}^2}$, the SFT defined by the 14-tile syntax (north–south matching on $\mathbb{F}_3$ and east–west matching on $\mathbb{F}_6$).",
    text="The aperiodic 2D SFT defined by the 14-tile Kari–Culik Wang set.",
    section="DGG 2013 §2", tags=["sft", "kari-culik", "aperiodic"],
    parameters=["dimension d=2"],
    lean_decl="dependencies.KariCulik.kariCulikShift", lean_status="stated",
)

# The infrastructure used by Weiss conjecture.
DEF_HAS_EP_COVER = N(
    NodeKind.DEFINITION, "kc:def:has-entropy-preserving-cover",
    name="Has entropy-preserving SFT cover",
    latex=r"A subshift $Y$ has an entropy-preserving SFT cover if there exists an SFT $X$ and a factor map $\pi:X\to Y$ with $h(X)=h(Y)$.",
    text="Existence of an SFT cover with equal topological entropy.",
    tags=["sofic", "sft", "factor", "cover"],
    lean_decl="dependencies.FactorMap.HasEntropyPreservingSFTCover",
    lean_status="stated",
)

# -------------------------------------------------------------------------
# Axiomatized facts about the Kari–Culik shift.
# -------------------------------------------------------------------------
THM_KC_NONEMPTY = N(
    NodeKind.THEOREM, "kc:thm:nonempty",
    name="Kari–Culik shift is non-empty",
    latex=r"$X_{\mathrm{KC}}\neq\varnothing$.",
    text="The Kari–Culik 14-tile set admits a tiling of the plane.",
    tags=["kari-culik", "wang", "tileability"],
    lean_decl="axioms.KariCulik.kariCulikShift_carrier_nonempty",
    lean_status="axiomatized",
)
THM_KC_ENTROPY_POS = N(
    NodeKind.THEOREM, "kc:thm:positive-entropy",
    name="Kari–Culik shift has positive entropy (DGG 2013)",
    latex=r"$h(X_{\mathrm{KC}})>0$.",
    text="The topological entropy of the Kari–Culik shift is strictly positive.",
    tags=["kari-culik", "entropy", "main"],
    parameters=["dimension d=2"],
    lean_decl="axioms.KariCulik.kariCulikShift_entropy_pos",
    lean_status="axiomatized",
)

# -------------------------------------------------------------------------
# Open problems (each formalised as a Lean def/statement).
# -------------------------------------------------------------------------
OP_WEISS = N(
    NodeKind.OPEN_PROBLEM, "op:weiss-conjecture",
    name="Weiss conjecture: entropy-preserving SFT cover of sofic shifts",
    latex=r"For every $d$, every finite alphabet, every sofic $\mathbb{Z}^d$-shift admits an entropy-preserving SFT cover.",
    text="Every sofic Z^d-shift has an SFT cover of the same entropy (d=1 known, d≥2 open).",
    tags=["sofic", "sft", "entropy", "cover", "open"],
    parameters=["d>=2"],
    status="open",
    lean_decl="openProblems.WeissConjecture.WeissConjecture.WeissConjectureStatement",
    lean_status="stated",
)
OP_ODDSHIFT = N(
    NodeKind.OPEN_PROBLEM, "op:odd-shift-soficity",
    name="Is the multidimensional odd shift sofic?",
    latex=r"For $d\geq 3$, is the $d$-dim odd shift $Y_d\subseteq\{0,1\}^{\mathbb{Z}^d}$ (configurations whose finite connected components of occupied sites have odd cardinality) sofic?",
    text="Multidimensional odd shift soficity (d=1 solved; d≥3 open).",
    tags=["sofic", "percolation", "open"],
    parameters=["d>=3"],
    status="open",
    lean_decl="openProblems.OddShiftSoficity.OddShiftSoficity.OddShiftSoficityStatement",
    lean_status="stated",
)
OP_KC_ENTROPY = N(
    NodeKind.OPEN_PROBLEM, "op:kari-culik-entropy-value",
    name="What is the topological entropy of the Kari–Culik shift?",
    latex=r"Determine $h(X_{\mathrm{KC}})\in(0,\log 14]$ exactly; is it computable, algebraic, ...?",
    text="The value h(X_KC) is positive (DGG) and right-r.e. (HM 3.1); the exact value is open.",
    tags=["kari-culik", "entropy", "computability", "open"],
    status="open",
    lean_decl="openProblems.KariCulikEntropy.KariCulikEntropy.kariCulikEntropy",
    lean_status="stated",
)

# -------------------------------------------------------------------------
# Partial trajectory result.
# -------------------------------------------------------------------------
THM_KC_ENT_RIGHTRE = N(
    NodeKind.THEOREM, "kc:thm:entropy-right-re",
    name="kariCulikEntropy is right r.e. (Attempt_1)",
    latex=r"$h(X_{\mathrm{KC}})$ is right recursively enumerable.",
    text="The entropy of the Kari–Culik shift is right r.e. (special case of HM Thm 3.1).",
    tags=["kari-culik", "entropy", "right-re", "partial"],
    lean_decl=(
        "trajectories.KariCulikEntropyComputableStatement."
        "Attempt_1_rightRE_via_HM.kariCulikEntropy_isRightRE"
    ),
    lean_status="proved",
)

# -------------------------------------------------------------------------
# Edges.
# -------------------------------------------------------------------------
# The kari-culik construction is an SFT.
E(EdgeType.INSTANCE_OF, KC_SHIFT, "concept:sft")
E(EdgeType.INSTANCE_OF, KC_SHIFT, "concept:subshift")

# Axiomatized facts about the construction depend on the construction.
E(EdgeType.USES_DEFINITION, THM_KC_NONEMPTY, KC_SHIFT, where_="in_statement")
E(EdgeType.USES_DEFINITION, THM_KC_ENTROPY_POS, KC_SHIFT, where_="in_statement")
E(EdgeType.USES_DEFINITION, THM_KC_ENTROPY_POS, "concept:topological-entropy",
  where_="in_statement")

# Weiss conjecture statement uses the predicate + sofic concept.
E(EdgeType.USES_DEFINITION, OP_WEISS, DEF_HAS_EP_COVER, where_="in_statement")
E(EdgeType.USES_DEFINITION, OP_WEISS, "concept:sofic-shift", where_="in_statement")

# OddShift statement uses sofic concept.
E(EdgeType.USES_DEFINITION, OP_ODDSHIFT, "concept:sofic-shift", where_="in_statement")

# Kari–Culik entropy open problem uses the construction + entropy concept,
# and depends *in proof* on its two known partial results.
E(EdgeType.USES_DEFINITION, OP_KC_ENTROPY, KC_SHIFT, where_="in_statement")
E(EdgeType.USES_DEFINITION, OP_KC_ENTROPY, "concept:topological-entropy",
  where_="in_statement")
E(EdgeType.DEPENDS_ON, OP_KC_ENTROPY, THM_KC_ENTROPY_POS, where_="in_proof",
  notes="positivity (DGG) is the only proved value information so far")

# Partial trajectory result depends on HM Thm 3.1 (it lifts topEntropy_rightRE
# to the specific shift) and resolves the open problem partially.
E(EdgeType.USES_DEFINITION, THM_KC_ENT_RIGHTRE, KC_SHIFT, where_="in_statement")
E(EdgeType.USES_DEFINITION, THM_KC_ENT_RIGHTRE, "concept:topological-entropy",
  where_="in_statement")
# Cross-paper dependency on HM Theorem 3.1. The id is content-derived so
# we compute it the same way the HM gold did (slug 'hm:thm:3.1'); the
# edge then resolves directly without relying on alias lookup.
HM_THM_3_1_ID = node_id(NodeKind.THEOREM, "hm:thm:3.1")
E(EdgeType.DEPENDS_ON, THM_KC_ENT_RIGHTRE, HM_THM_3_1_ID, where_="in_proof",
  notes="lifts HM Theorem 3.1 to the specific shift")
E(EdgeType.RESOLVES, THM_KC_ENT_RIGHTRE, OP_KC_ENTROPY,
  regime="partial:right-re",
  notes="right-r.e. half of the computability question")

# Cross-paper attribution to the originating papers.
E(EdgeType.ATTRIBUTED_TO, KC_TILES, "arxiv:kari1996")
E(EdgeType.ATTRIBUTED_TO, KC_TILES, "arxiv:culik1996")
E(EdgeType.ATTRIBUTED_TO, KC_SHIFT, "arxiv:kari1996")
E(EdgeType.ATTRIBUTED_TO, KC_SHIFT, "arxiv:culik1996")
E(EdgeType.ATTRIBUTED_TO, THM_KC_ENTROPY_POS, PAPER)              # DGG
E(EdgeType.ATTRIBUTED_TO, OP_WEISS, "arxiv:weiss1973")
E(EdgeType.ATTRIBUTED_TO, OP_ODDSHIFT, "arxiv:hochman2009")

# Paper edges from the primary paper.
for src in (KC_TILES, KC_SHIFT, THM_KC_NONEMPTY, THM_KC_ENTROPY_POS,
            DEF_HAS_EP_COVER, OP_WEISS, OP_ODDSHIFT, OP_KC_ENTROPY,
            THM_KC_ENT_RIGHTRE):
    if "construction" in src or "definition:" in src:
        E(EdgeType.DEFINES, PAPER, src)
    else:
        E(EdgeType.STATES, PAPER, src)


def main() -> None:
    sg = {
        "paper": PAPER,
        "run_id": RUN,
        "extractors": ["gold-hand-curated-bootstrap"],
        "source": "lean-bootstrap (no single paper)",
        "nodes": [n.to_dict() for n in nodes],
        "edges": [e.to_dict() for e in edges],
        "citations": [],
    }
    errs = validate_subgraph(sg)
    out = Path(__file__).resolve().parent / "1312.4126_kc_bootstrap.subgraph.json"
    out.write_text(json.dumps(sg, indent=2, sort_keys=True))
    n_proved = sum(1 for n in nodes if n.lean_status == "proved")
    n_stated = sum(1 for n in nodes if n.lean_status == "stated")
    n_axiom = sum(1 for n in nodes if n.lean_status == "axiomatized")
    print(f"wrote {out.name}: {len(nodes)} nodes, {len(edges)} edges, "
          f"{len(errs)} validation errors")
    print(f"  Lean back-links: {n_proved} proved · {n_stated} stated · "
          f"{n_axiom} axiomatized")
    if errs:
        for e in errs[:10]:
            print(f"  ! {e}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
