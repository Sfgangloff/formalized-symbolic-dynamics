r"""Gold subgraph for arXiv:1312.4126 (Durand–Gamard–Grandjean 2013).

This curates the paper's *mathematical* content (theorems, lemmas,
constructions, open problems) — complementing
``1312.4126_kc_bootstrap.subgraph.json`` (which curated the Lean
assets in the repo concerning the Kari–Culik shift).

Cross-paper integration demo: the DGG main theorem here is rendered
with the canonical LaTeX ``$h(X_{\mathrm{KC}})>0$`` — *the same string*
the bootstrap used for ``kc:thm:positive-entropy`` — so it should
**L0-merge** with the bootstrap node. After merge the resulting
canonical node carries:

* DGG's per-paper provenance + in_proof dependency edges to the §3
  lemmas curated below;
* the Lean back-link the bootstrap set
  (``axioms.KariCulik.kariCulikShift_entropy_pos``);
* attribution to both Kari/Culik 1996 (origin of the tileset) and DGG
  1312.4126 (origin of the positive-entropy proof).

Run::

    uv run python gold/build_dgg_gold.py
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

PAPER = "arxiv:1312.4126"
RUN = "gold-dgg-2026-05-20"
SOURCE = "article_entropie_kari.tex"

nodes: list[Node] = []
edges: list[Edge] = []
_seen: set[str] = set()


def N(kind, slug, *, name, latex, text, section="", env_name="prose",
      tags=None, parameters=None, status="", lean_decl="", lean_status=""):
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


# Cross-references to ids established by earlier gold subgraphs.
# Recomputed via the same slug → node_id deterministic mapping the
# other builders use, so the edges resolve directly against the merged
# global graph without alias lookup.
KC_SHIFT_ID = node_id(NodeKind.CONSTRUCTION, "kari-culik-shift")

# -------------------------------------------------------------------------
# Definitions introduced by the paper.
# -------------------------------------------------------------------------
DEF_F = N(
    NodeKind.DEFINITION, "dgg:def:kc-function-f",
    name="Kari–Culik base function f",
    latex=r"$f:[\tfrac13,2]\to[\tfrac13,2]$ defined by $f(x)=2x$ for $x\in[\tfrac13,1]$ and $f(x)=x/3$ for $x\in[1,2]$.",
    text="Piecewise-linear base function underlying the Kari–Culik construction; conjugate to an irrational rotation of angle log2/(log2+log3).",
    section="§3.2", env_name="prose", tags=["kari-culik", "dynamics", "rotation"],
)
DEF_SUBST_PAIR = N(
    NodeKind.DEFINITION, "dgg:def:substitutive-pair",
    name="Substitutive pair",
    latex=r"A \emph{substitutive pair} is a couple of different patterns with the same borders.",
    text="Two distinct Wang patterns with identical boundary colors (a swap one for the other in any tiling).",
    section="§3.1", env_name="prose", tags=["wang", "patterns", "substitution"],
)
CONSTR_AA = N(
    NodeKind.CONSTRUCTION, "dgg:constr:dgg-substitutive-pairs",
    name="DGG substitutive pairs (A_1, A'_1) and (A_2, A'_2)",
    latex=r"Two explicit pairs of $2\times 2$ Wang patterns over the 14-tile DGG alphabet, each pair sharing identical north/south/east/west boundary colours.",
    text="Two explicit 2x2 substitutive pairs in the 14-tile Kari–Culik tileset.",
    section="§3.1", tags=["wang", "kari-culik", "construction", "substitution"],
)
DEF_CYLINDRICITY = N(
    NodeKind.DEFINITION, "dgg:def:cylindricity",
    name="Cylindricity function (Monteil)",
    latex=r"For an aperiodic tileset, the \emph{cylindricity function} maps $n$ to the smallest growing bound on the vertical size of a tilable portion of a horizontal cylinder of perimeter $n$.",
    text="Maximal tilable vertical height of a horizontal cylinder of given perimeter (Monteil 2012).",
    section="§4", env_name="prose", tags=["tilings", "complexity", "cited"],
)

# -------------------------------------------------------------------------
# Section 3 — the proof of positive entropy.
# -------------------------------------------------------------------------
LEM_DENSE_F = N(
    NodeKind.LEMMA, "dgg:lem:dense-f",
    name="Orbits of f are dense",
    latex=r"The orbits of $f$ are dense in $[\tfrac13,2]$.",
    text="The base function f has dense orbits; via the log-coordinate the dynamics is an irrational rotation.",
    section="§3.2", env_name="lemma", tags=["kari-culik", "dynamics"],
)
PROP_DENSE2 = N(
    NodeKind.PROPOSITION, "dgg:prop:dense2",
    name="Bounded return time of f in any interval",
    latex=r"Given any interval $I\subseteq[\tfrac13,2]$, the maximal number of iterations of $f$ between two consecutive occurrences in $I$ is bounded.",
    text="Bounded gap between consecutive returns of an orbit of f to any fixed interval.",
    section="§3.2", env_name="prop", tags=["kari-culik", "dynamics"],
)
PROP_AVERAGE = N(
    NodeKind.PROPOSITION, "dgg:prop:line-average",
    name="Every horizontal line has an average",
    latex=r"Every horizontal line in any tiling by the DGG 14-tile set has an average (in the sense of frequencies).",
    text="In any Kari–Culik tiling, each horizontal line of bottom labels has a well-defined frequency.",
    section="§3.2", env_name="prop", tags=["kari-culik", "tilings", "frequency"],
)
LEM_LINEAR_DENSITY = N(
    NodeKind.LEMMA, "dgg:lem:linear-pattern-density",
    name="Family 01^α0 appears with positive density",
    latex=r"The family of patterns $\{01^\alpha 0 \mid \alpha>3\}$ appears with positive density on every horizontal line whose density lies in $(\tfrac45,\tfrac9{10})$.",
    text="Linear-pattern density on lines whose 1-density lies in the gap interval (4/5, 9/10).",
    section="§3.3", env_name="lemma", tags=["kari-culik", "tilings", "density"],
)

# DGG's main theorem — rendered with the SAME canonical LaTeX as the
# bootstrap's `kc:thm:positive-entropy` so L0 merges across papers.
THM_DGG_MAIN = N(
    NodeKind.THEOREM, "dgg:thm:positive-entropy",
    name="Theorem [MAIN] — Kari–Culik tileset has positive entropy",
    latex=r"$h(X_{\mathrm{KC}})>0$.",   # identical to bootstrap → L0 merge
    text="The topological entropy of the Kari–Culik shift is strictly positive (DGG 2013).",
    section="§3.4", env_name="theorem",
    tags=["kari-culik", "entropy", "main"],
    parameters=["dimension d=2"],
)

# -------------------------------------------------------------------------
# Section 4 — cylindricity and the Monteil conjecture (refuted by DGG).
# -------------------------------------------------------------------------
CONJ_MONTEIL = N(
    NodeKind.CONJECTURE, "dgg:conj:monteil-linear-complexity",
    name="Monteil's linear-complexity conjecture (refuted)",
    latex=r"The 2D pattern complexity of the Kari–Culik shift satisfies $\log p(n,n)=O(n)$ (conjectured by Monteil 2012).",
    text="Conjecture (Monteil) that the Kari–Culik pattern count grows only sub-exponentially in n^2.",
    section="§4", env_name="prose", tags=["complexity", "cited", "refuted"],
    status="refuted",
)
THM_REFUTES_MONTEIL = N(
    NodeKind.COROLLARY, "dgg:cor:refutes-monteil",
    name="DGG main theorem refutes Monteil's conjecture",
    latex=r"Positivity of $h(X_{\mathrm{KC}})$ implies $\log p(n,n)\in\Theta(n^2)$, refuting the Monteil conjecture.",
    text="Positive entropy on a 2D SFT means n^2 growth, contradicting Monteil's O(n) conjecture.",
    section="§4", env_name="prose", tags=["kari-culik", "complexity", "refutation"],
)

# -------------------------------------------------------------------------
# Open problems from §3 conclusion.
# -------------------------------------------------------------------------
OP_SINGLE_PAIR = N(
    NodeKind.OPEN_PROBLEM, "dgg:op:single-pair-dense",
    name="Is one substitutive pair alone dense?",
    latex=r"Is one of the two DGG substitutive pairs dense alone in some tiling?",
    text="Whether one of A_i,A'_i (rather than the joint family) is dense by itself.",
    section="§3.5", env_name="prose", tags=["kari-culik", "open"], status="open",
)
OP_FORBID_PATTERN = N(
    NodeKind.OPEN_PROBLEM, "dgg:op:forbid-pattern",
    name="Forbidding one pattern of each pair: entropy still positive?",
    latex=r"Forbidding one pattern from each substitutive pair gives a sub-tileset. Is its entropy still positive? More generally, can finitely many forbidden patterns force entropy zero?",
    text="Sub-SFT obtained by forbidding one pattern from each DGG pair — positive entropy?",
    section="§3.5", env_name="prose", tags=["kari-culik", "entropy", "open"], status="open",
)

# -------------------------------------------------------------------------
# Edges.
# -------------------------------------------------------------------------
# instance_of: this paper's notions hang off the shared concepts seeded
# by HM (concept:topological-entropy etc.).
E(EdgeType.INSTANCE_OF, DEF_CYLINDRICITY, "concept:topological-entropy")

# Statement-dependencies of the DGG main theorem.
for d in (KC_SHIFT_ID, "concept:topological-entropy"):
    E(EdgeType.USES_DEFINITION, THM_DGG_MAIN, d, where_="in_statement")

# Proof-mining: which §3 lemmas the main theorem invokes.
for src, dst, where in [
    (LEM_DENSE_F, DEF_F, "in_statement"),
    (PROP_DENSE2, LEM_DENSE_F, "in_proof"),
    (PROP_AVERAGE, KC_SHIFT_ID, "in_statement"),
    (LEM_LINEAR_DENSITY, PROP_AVERAGE, "in_proof"),
    (THM_DGG_MAIN, DEF_SUBST_PAIR, "in_statement"),
    (THM_DGG_MAIN, CONSTR_AA, "in_proof"),
    (THM_DGG_MAIN, LEM_LINEAR_DENSITY, "in_proof"),
    (THM_DGG_MAIN, PROP_DENSE2, "in_proof"),
    (THM_DGG_MAIN, PROP_AVERAGE, "in_proof"),
]:
    if where == "in_statement":
        E(EdgeType.USES_DEFINITION, src, dst, where_="in_statement")
    else:
        E(EdgeType.DEPENDS_ON, src, dst, where_="in_proof")

# §4: DGG main theorem refutes Monteil's conjecture (via the corollary).
E(EdgeType.DEPENDS_ON, THM_REFUTES_MONTEIL, THM_DGG_MAIN, where_="in_proof")
E(EdgeType.REFUTES, THM_REFUTES_MONTEIL, CONJ_MONTEIL)
E(EdgeType.USES_DEFINITION, CONJ_MONTEIL, DEF_CYLINDRICITY, where_="in_statement")

# Cross-paper attribution.
E(EdgeType.ATTRIBUTED_TO, CONSTR_AA, "arxiv:kari1996")
E(EdgeType.ATTRIBUTED_TO, CONSTR_AA, "arxiv:culik1996")
E(EdgeType.ATTRIBUTED_TO, DEF_CYLINDRICITY, "arxiv:pavlovSchraudner")   # placeholder for Monteil 2012 (not on arxiv)

# Paper-source edges.
for src in (DEF_F, DEF_SUBST_PAIR, CONSTR_AA, DEF_CYLINDRICITY,
            LEM_DENSE_F, PROP_DENSE2, PROP_AVERAGE, LEM_LINEAR_DENSITY,
            THM_DGG_MAIN, CONJ_MONTEIL, THM_REFUTES_MONTEIL,
            OP_SINGLE_PAIR, OP_FORBID_PATTERN):
    if "definition:" in src or "construction:" in src:
        E(EdgeType.DEFINES, PAPER, src)
    else:
        E(EdgeType.STATES, PAPER, src)


def main() -> None:
    sg = {
        "paper": PAPER,
        "run_id": RUN,
        "extractors": ["gold-hand-curated"],
        "source": SOURCE,
        "nodes": [n.to_dict() for n in nodes],
        "edges": [e.to_dict() for e in edges],
        "citations": [
            {"key": k, "from_node": PAPER, "where": "bibliography"}
            for k in ["Kari", "Culik", "Wang", "BergerPhD", "Robinson",
                      "thierry", "ollinger", "DBLP:journals/jcss/DurandRS12"]
        ],
    }
    errs = validate_subgraph(sg)
    out = Path(__file__).resolve().parent / "1312.4126_dgg_paper.subgraph.json"
    out.write_text(json.dumps(sg, indent=2, sort_keys=True))
    print(f"wrote {out.name}: {len(nodes)} nodes, {len(edges)} edges, "
          f"{len(errs)} validation errors")
    if errs:
        for e in errs[:10]:
            print(f"  ! {e}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
