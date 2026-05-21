"""Hand-curated gold subgraph for arXiv:math/0703206 (Hochman–Meyerovitch).

This is the **template** for Milestone 2 gold curation. It captures the
spine of the paper (its three main theorems, the supporting Section-3
results, the key definitions, and the prior-art it cites) and
back-links every node that the repo has already formalized to the
existing Lean declaration (per ONTOLOGY_PLAN §6.4).

Not in scope: §4–§8 construction details (the sufficiency proof of
Theorem 1.1, which the repo has not yet started). Those will be added
in a later curation pass when their Lean targets exist.

Run::

    uv run python gold/build_hm_gold.py

The script writes ``gold/math_0703206.subgraph.json``, validated against
the §1 schema. ``onto merge`` consumes that JSON the same way it
consumes any other per-paper subgraph.
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
    paper_id,
)

PAPER = paper_id("math/0703206")
RUN = "gold-hm-2026-05-20"
SOURCE = "entropies-of-SFTs.arxiv.tex"
LEAN_HM = "papers.HochmanMeyerovitch.HochmanMeyerovitch"

nodes: list[Node] = []
edges: list[Edge] = []
_seen: set[str] = set()


def N(
    kind: NodeKind,
    slug: str,
    *,
    name: str,
    latex: str,
    text: str,
    section: str = "",
    label: str = "",
    env_name: str = "",
    tags: list[str] | None = None,
    parameters: list[str] | None = None,
    status: str = "",
    lean_decl: str = "",
    lean_status: str = "",
) -> str:
    """Create a Node and return its id. ``slug`` keys the id (statement
    kinds hash it, concept/construction use it verbatim)."""
    nid = node_id(kind, slug)
    if nid in _seen:
        raise ValueError(f"duplicate id {nid}")
    _seen.add(nid)
    # The curated slug is appended to aliases so `onto sync-lean` can
    # resolve human-readable doc-comments like `-- @ontology: hm:thm:1.1`
    # to the (hashed) statement-kind node id.
    aliases = [slug] if slug != nid else []
    n = Node(
        id=nid,
        kind=kind.value,
        name=name,
        statement_latex=latex,
        statement_text=text,
        tags=tags or [],
        parameters=parameters or [],
        status=status,
        aliases=aliases,
        content_hash=content_hash(kind.value, latex) if latex else "",
        structural_sig=structural_sig(
            kind.value, tags or [], [], parameters or []
        ),
        lean_decl=lean_decl,
        lean_status=lean_status,
        provenance=[
            Provenance(
                paper=PAPER, label=label, env_name=env_name,
                section=section, run_id=RUN, human_verified=True,
            )
        ] if kind not in (NodeKind.CONCEPT,) else [],
        created_run=RUN, updated_run=RUN,
    )
    nodes.append(n)
    return nid


def E(etype: EdgeType, src: str, dst: str, *, where_: str = "",
      regime: str = "", proved: str = "", notes: str = "") -> None:
    eid = edge_id(etype, src, dst, regime)
    edges.append(
        Edge(
            id=eid, type=etype.value, src=src, dst=dst,
            where_=where_, regime=regime, proved=proved, notes=notes,
            human_verified=True,
            provenance=[EdgeProvenance(paper=PAPER, run_id=RUN)],
        )
    )


# -------------------------------------------------------------------------
# Concepts (umbrella nodes; bridge to ROADMAP §4 dictionary).
# -------------------------------------------------------------------------
C_SUBSHIFT  = N(NodeKind.CONCEPT, "subshift",                 name="subshift",                  latex="", text="closed shift-invariant subset of a full shift")
C_SFT       = N(NodeKind.CONCEPT, "sft",                      name="shift of finite type",      latex="", text="subshift defined by a finite local syntax")
C_SOFIC     = N(NodeKind.CONCEPT, "sofic-shift",              name="sofic shift",               latex="", text="continuous shift-commuting factor of an SFT")
C_ENTROPY   = N(NodeKind.CONCEPT, "topological-entropy",      name="topological entropy",       latex="", text="asymptotic growth rate of admissible patterns")
C_RIGHTRE   = N(NodeKind.CONCEPT, "right-recursively-enumerable", name="right r.e. real",       latex="", text="real with a computable rational upper-approximation sequence")
C_COMPUTABLE= N(NodeKind.CONCEPT, "computable-real",          name="computable real",           latex="", text="real with a computable two-sided rational approximation sequence")
C_IRR       = N(NodeKind.CONCEPT, "irreducible-shift",        name="irreducible subshift",      latex="", text="globally admissible far-apart patterns can be glued")
C_FACTOR    = N(NodeKind.CONCEPT, "factor-map",               name="factor map",                latex="", text="continuous surjection commuting with the shift action")

# -------------------------------------------------------------------------
# Definitions (Section 2 of the paper).
# -------------------------------------------------------------------------
D_SUBSHIFT = N(
    NodeKind.DEFINITION, "hm:def:subshift",
    name="Subshift (Hochman–Meyerovitch §2.1)",
    latex=r"A closed shift-invariant subset $X\subseteq \Sigma^{\mathbb{Z}^d}$ is a $\mathbb{Z}^d$-subshift.",
    text="A closed, shift-invariant subset of the full shift.",
    section="Preliminaries §2.1", env_name="prose",
    tags=["subshift"], parameters=["dimension d", "finite alphabet"],
    lean_decl="dependencies.Subshift.Subshift", lean_status="stated",
)
D_SFT = N(
    NodeKind.DEFINITION, "hm:def:sft",
    name="Shift of finite type (Hochman–Meyerovitch §2.1)",
    latex=r"An SFT is defined by a finite alphabet $\Sigma$, a finite $F\subseteq \mathbb{Z}^d$ and a syntax $L\subseteq \Sigma^F$; the carrier is the set of $x\in\Sigma^{\mathbb{Z}^d}$ all of whose translated $F$-patterns lie in $L$.",
    text="Subshift defined by a finite local syntax.",
    section="Preliminaries §2.1", env_name="prose",
    tags=["sft"], parameters=["dimension d", "finite alphabet"],
    lean_decl="dependencies.Subshift.mkSFT", lean_status="stated",
)
D_LOC_ADM = N(
    NodeKind.DEFINITION, "hm:def:locally-admissible",
    name="Locally admissible pattern (§2.1)",
    latex=r"$a\in\Sigma^E$ is locally admissible for the syntax $L$ if $a|_{F+u}$ is congruent to a pattern in $L$ whenever $F+u\subseteq E$.",
    text="Every translate of the syntax window contained in the domain matches some allowed pattern.",
    section="§2.1", env_name="prose", tags=["sft", "patterns"],
    lean_decl="dependencies.LocallyAdmissible.locallyAdmissible", lean_status="stated",
)
D_GLOB_ADM = N(
    NodeKind.DEFINITION, "hm:def:globally-admissible",
    name="Globally admissible pattern (§2.1)",
    latex=r"A finite pattern $a$ is globally admissible for $X$ if it appears in some $x\in X$.",
    text="Pattern that occurs in some point of the subshift.",
    section="§2.1", env_name="prose", tags=["sft", "patterns"],
    lean_decl="dependencies.GloballyAdmissible.Pattern.GloballyAdmissible", lean_status="stated",
)
D_IRR_SFT = N(
    NodeKind.DEFINITION, "hm:def:irreducible-sft",
    name="Irreducible SFT (§2.1)",
    latex=r"An SFT $X$ is irreducible if there is a gap $r>0$ such that for every $A,B\subseteq\mathbb{Z}^d$ with $\|u-v\|_\infty\geq r$ for $u\in A,v\in B$ and every globally admissible $a\in\Sigma^A,\ b\in\Sigma^B$, the union $a\cup b$ is globally admissible.",
    text="Far-apart globally admissible patterns can always be glued.",
    section="§2.1", env_name="prose", tags=["sft", "irreducibility"],
    parameters=["gap r", "dimension d"],
    lean_decl="dependencies.LocallyAdmissible.IsIrreducibleShift", lean_status="stated",
)
D_TOP_ENT = N(
    NodeKind.DEFINITION, "hm:def:top-entropy",
    name="Topological entropy of a subshift (§2.2)",
    latex=r"$h(X)=\lim_{n\to\infty}\frac{1}{|F_n|}\log N_X(F_n)$ where $F_n=\{1,\dots,n\}^d$.",
    text="Asymptotic growth rate of the number of admissible patterns on cubes.",
    section="§2.2", env_name="prose", tags=["entropy"],
    parameters=["dimension d", "finite alphabet"],
    lean_decl="dependencies.Subshift.topEntropy", lean_status="stated",
)
D_FACTOR_MAP = N(
    NodeKind.DEFINITION, "hm:def:factor-map",
    name="Factor map / one-block map (§2.3)",
    latex=r"A factor map $\varphi:X\to Y$ is a continuous surjection commuting with the shift action; equivalently it is a block code arising from $\varphi_0:\Sigma^F\to\Delta$. It is one-block if $|F|=1$.",
    text="Continuous shift-commuting surjection.",
    section="§2.3", env_name="prose", tags=["factor"],
    lean_decl="dependencies.FactorMap.FactorMap", lean_status="stated",
)
D_SOFIC = N(
    NodeKind.DEFINITION, "hm:def:sofic-shift",
    name="Sofic shift (§2.3)",
    latex=r"A subshift $Y$ is sofic if it is a factor of some SFT.",
    text="Factor of a shift of finite type.",
    section="§2.3", env_name="prose", tags=["sofic"],
    parameters=["dimension d"],
    lean_decl="dependencies.FactorMap.IsSofic", lean_status="stated",
)
D_INV_MEAS = N(
    NodeKind.DEFINITION, "hm:def:invariant-measure",
    name="Shift-invariant Borel probability measure (§2.4)",
    latex=r"$\mathcal{M}(X)$ denotes the set of $\sigma$-invariant Borel probability measures on $X$, with the weak-$*$ topology.",
    text="Borel probability measure invariant under the shift action.",
    section="§2.4", env_name="prose", tags=["measure"],
    lean_decl="dependencies.InvariantMeasure.InvMeasure", lean_status="stated",
)
D_MEAS_ENT = N(
    NodeKind.DEFINITION, "hm:def:measure-entropy",
    name="Measure-theoretic entropy h(μ) (§2.4, cited)",
    latex=r"For $\mu\in\mathcal{M}(X)$, $h(\mu)$ denotes its Kolmogorov–Sinai entropy.",
    text="Kolmogorov–Sinai entropy of a shift-invariant measure.",
    section="§2.4", env_name="prose", tags=["measure", "entropy"],
    lean_decl="axioms.InvariantMeasure.measureEntropy", lean_status="axiomatized",
)
D_COMPUTABLE = N(
    NodeKind.DEFINITION, "hm:def:computable-real",
    name="Computable real (§1)",
    latex=r"$h\in\mathbb{R}$ is computable if there is an algorithm that, given $n\in\mathbb{N}$, produces a rational $r(n)$ with $|h-r(n)|<1/n$.",
    text="Real with a computable rational approximation to arbitrary precision.",
    section="§1", env_name="prose", tags=["computability"],
    lean_decl="dependencies.Computable.IsComputableReal", lean_status="stated",
)
D_RIGHT_RE = N(
    NodeKind.DEFINITION, "hm:def:right-re",
    name="Right recursively enumerable real (§1)",
    latex=r"$h\in\mathbb{R}$ is right recursively enumerable (upper semi-recursive) if there is a computable $r(n)\geq h$ with $r(n)\to h$, equivalently the right Dedekind cut $\{q\in\mathbb{Q}\mid q>h\}$ is recursive.",
    text="Real with a computable monotone rational approximation from above.",
    section="§1", env_name="prose", tags=["computability"],
    lean_decl="dependencies.Computable.IsRightRE", lean_status="stated",
)

# instance_of: definitions -> concepts (the §0.1 dictionary bridge)
for d, c in [
    (D_SUBSHIFT, C_SUBSHIFT), (D_SFT, C_SFT), (D_SFT, C_SUBSHIFT),
    (D_SOFIC, C_SOFIC), (D_SOFIC, C_SUBSHIFT),
    (D_TOP_ENT, C_ENTROPY), (D_IRR_SFT, C_IRR),
    (D_FACTOR_MAP, C_FACTOR), (D_RIGHT_RE, C_RIGHTRE),
    (D_COMPUTABLE, C_COMPUTABLE),
]:
    E(EdgeType.INSTANCE_OF, d, c)

# -------------------------------------------------------------------------
# Main theorems (§1).
# -------------------------------------------------------------------------
T_1_1 = N(
    NodeKind.THEOREM, "hm:thm:1.1",
    name="Theorem 1.1 [MAIN]",
    latex=r"For $d\geq 2$ the class of entropies of $d$-dimensional SFTs is exactly the class of non-negative right recursively enumerable real numbers.",
    text="In dimension d ≥ 2, the entropies of SFTs are exactly the non-negative right r.e. reals.",
    section="§1", label="thm:main", env_name="thm",
    tags=["main", "sft", "entropy", "computability"],
    parameters=["d>=2"],
    lean_decl="", lean_status="",  # NOT YET formalized (sufficiency I2 missing)
)
T_1_2 = N(
    NodeKind.THEOREM, "hm:thm:1.2",
    name="Theorem 1.2 [MAIN]",
    latex=r"For $d\geq 2$, the class of entropies of $d$-dimensional sofic shifts is the same as that of $d$-dimensional SFTs.",
    text="For d ≥ 2 the entropy set of sofic shifts equals that of SFTs.",
    section="§1", label="thm:sofic", env_name="thm",
    tags=["main", "sofic", "sft", "entropy"],
    parameters=["d>=2"],
    lean_decl="", lean_status="",
)
T_1_3 = N(
    NodeKind.THEOREM, "hm:thm:1.3",
    name="Theorem 1.3 [MAIN]",
    latex=r"The topological entropy of a non-empty irreducible SFT is computable.",
    text="Entropy of an irreducible SFT is a computable real.",
    section="§1", label="thm:irreducible", env_name="thm",
    tags=["main", "sft", "entropy", "irreducibility", "computability"],
    lean_decl=f"{LEAN_HM}.topEntropy_irreducible_computable", lean_status="proved",
)

# -------------------------------------------------------------------------
# Section 3 — computability of entropies.
# -------------------------------------------------------------------------
T_3_1 = N(
    NodeKind.THEOREM, "hm:thm:3.1",
    name="Theorem 3.1 (= necessity half of 1.1)",
    latex=r"For an SFT $X$ defined by syntax $L$ and $\tilde N_n=\#\{\text{locally admissible }F_n\text{-patterns}\}$, $\frac{1}{n^d}\log\tilde N_n\to h(X)$ from above; consequently $h(X)$ is right r.e.",
    text="Locally admissible counts give a computable upper-approximation; SFT entropy is right r.e.",
    section="§3", label="thm:SFT-entropies-are-co-RE", env_name="thm",
    tags=["sft", "entropy", "right-re"],
    lean_decl=f"{LEAN_HM}.topEntropy_rightRE", lean_status="proved",
)
T_3_2 = N(
    NodeKind.THEOREM, "hm:thm:3.2",
    name="Theorem (sofic version of 3.1)",
    latex=r"Let $Y$ be a sofic shift, factor of an SFT $X$ via the one-block map $\varphi_0$, and $\tilde M_n=\#\{\varphi(a):a\in W_n\}$. Then $\frac{1}{|F_n|}\log\tilde M_n\to h(Y)$ from above; consequently $h(Y)$ is right r.e.",
    text="Sofic shifts admit a computable upper-approximation of entropy via image counts.",
    section="§3", label="thm:sofic-entropies-are-co-RE", env_name="thm",
    tags=["sofic", "entropy", "right-re"],
    lean_decl="", lean_status="",
)
C_3_SOFIC = N(
    NodeKind.COROLLARY, "hm:cor:sofic-right-re",
    name="Corollary (sofic entropies are right r.e.)",
    latex=r"The topological entropy of every sofic shift is right recursively enumerable.",
    text="Every sofic shift entropy is right r.e.",
    section="§3", label="cor:sofic-entropies", env_name="cor",
    tags=["sofic", "entropy", "right-re"],
)
L_3_4 = N(
    NodeKind.LEMMA, "hm:lem:3.4",
    name="Lemma 3.4 (irreducibility dichotomy)",
    latex=r"Let $X$ be a non-empty irreducible SFT and $a\in\Sigma^{Q_k}$. Then exactly one of: (1) $a$ is not a sub-pattern of any locally admissible $b\in\Sigma^{Q_N}$ for large $N$ (so $a$ is not globally admissible); or (2) $a$ and every locally admissible $b\in\Sigma^{Q_N}$ are $\sqrt N$-compatible for large $N$ (so $a$ is globally admissible).",
    text="For an irreducible SFT, every cube pattern either fails to extend or extends with compatibility on all large cubes.",
    section="§3", env_name="lem",
    tags=["sft", "irreducibility", "patterns"],
    lean_decl=f"{LEAN_HM}.Lemma_3_4", lean_status="proved",
)
C_3_5 = N(
    NodeKind.COROLLARY, "hm:cor:3.5",
    name="Corollary 3.5 (decidable global admissibility)",
    latex=r"For a non-empty irreducible SFT $X$ it is decidable whether a finite pattern $a$ is globally admissible.",
    text="Global admissibility is decidable for nonempty irreducible SFTs.",
    section="§3", env_name="cor",
    tags=["sft", "irreducibility", "decidability"],
)

# -------------------------------------------------------------------------
# Cited prior-art results that the proofs use.
# -------------------------------------------------------------------------
AX_VP = N(
    NodeKind.THEOREM, "hm:cited:variational-principle",
    name="Variational principle (cited, Misiurewicz 1976)",
    latex=r"$h(X)=\sup_{\mu\in\mathcal{M}(X)}h(\mu)$, achieved at some equilibrium measure.",
    text="Topological entropy equals the supremum of measure-theoretic entropies.",
    section="§2.4", env_name="prose", tags=["entropy", "measure", "cited"],
    lean_decl="axioms.InvariantMeasure.variationalPrinciple", lean_status="axiomatized",
)
AX_USC = N(
    NodeKind.THEOREM, "hm:cited:usc-entropy",
    name="Upper semi-continuity of measure entropy (cited)",
    latex=r"$\mu\mapsto h(\mu)$ is upper semi-continuous on $\mathcal{M}(X)$ with the weak-$*$ topology.",
    text="Measure entropy is upper semi-continuous in the weak-* topology.",
    section="§2.4", env_name="prose", tags=["entropy", "measure", "cited"],
    lean_decl="axioms.InvariantMeasure.measureEntropy_uppersemicontinuous", lean_status="axiomatized",
)
AX_LEFTRE_IRR = N(
    NodeKind.THEOREM, "hm:lean:leftRE-irreducible",
    name="topEntropy_leftRE_irreducible (left-r.e. half of 1.3)",
    latex=r"For a non-empty irreducible SFT, $h(X)$ is left recursively enumerable.",
    text="Left-r.e. counterpart for irreducible SFTs.",
    section="(Lean axiomatization derived from Lemma 3.4)", env_name="lean-axiom",
    tags=["sft", "entropy", "left-re", "irreducibility"],
    lean_decl="dependencies.IrreducibleConsequences.topEntropy_leftRE_irreducible",
    lean_status="axiomatized",
)
LEAN_COMP_IFF = N(
    NodeKind.THEOREM, "hm:lean:computable-iff",
    name="computable_iff_leftRE_and_rightRE (Lean)",
    latex=r"A real is computable iff it is both left and right recursively enumerable.",
    text="Computable ⇔ left-r.e. ∧ right-r.e.",
    section="(Lean dependency)", env_name="lean-thm",
    tags=["computability"],
    lean_decl="dependencies.Computable.computable_iff_leftRE_and_rightRE",
    lean_status="proved",
)

# -------------------------------------------------------------------------
# Open problems noted in the paper.
# -------------------------------------------------------------------------
OP_IRR_CONVERSE = N(
    NodeKind.OPEN_PROBLEM, "hm:op:irr-converse",
    name="Open: is irreducibility necessary for computability?",
    latex=r"Does $h(X)$ computable imply $X$ irreducible? (Theorem 1.3 gives one direction; the converse is open per §1.)",
    text="Converse of Theorem 1.3; raised explicitly in §1 after Theorem 1.3.",
    section="§1", env_name="prose",
    tags=["entropy", "computability", "irreducibility", "open"],
    status="open",
)
OP_SOFIC_COVER = N(
    NodeKind.OPEN_PROBLEM, "hm:op:sofic-covering",
    name="Open: SFT cover of sofic shifts of equal entropy (d ≥ 2)",
    latex=r"For $d\geq 2$, does every sofic shift have an SFT extension of the same entropy? (Coven–Paul covering theorem in $d=1$.)",
    text="Multidimensional analog of the Coven–Paul covering theorem; partial result by Desai 2006.",
    section="§1", env_name="prose",
    tags=["sofic", "sft", "entropy", "open"],
    parameters=["d>=2"],
    status="open",
)

# -------------------------------------------------------------------------
# Paper edges: defines / states
# -------------------------------------------------------------------------
for d in (D_SUBSHIFT, D_SFT, D_LOC_ADM, D_GLOB_ADM, D_IRR_SFT, D_TOP_ENT,
          D_FACTOR_MAP, D_SOFIC, D_INV_MEAS, D_MEAS_ENT,
          D_COMPUTABLE, D_RIGHT_RE):
    E(EdgeType.DEFINES, PAPER, d)
for t in (T_1_1, T_1_2, T_1_3, T_3_1, T_3_2, C_3_SOFIC, L_3_4, C_3_5,
          AX_VP, AX_USC, OP_IRR_CONVERSE, OP_SOFIC_COVER):
    E(EdgeType.STATES, PAPER, t)

# -------------------------------------------------------------------------
# Dependency edges (uses_definition + depends_on).
# -------------------------------------------------------------------------
# Statement dependencies of the main theorems
for t, deps in [
    (T_1_1, [D_SFT, D_TOP_ENT, D_RIGHT_RE]),
    (T_1_2, [D_SFT, D_SOFIC, D_TOP_ENT]),
    (T_1_3, [D_SFT, D_IRR_SFT, D_TOP_ENT, D_COMPUTABLE]),
    (T_3_1, [D_SFT, D_LOC_ADM, D_TOP_ENT, D_RIGHT_RE]),
    (T_3_2, [D_SOFIC, D_FACTOR_MAP, D_LOC_ADM, D_TOP_ENT, D_RIGHT_RE]),
    (C_3_SOFIC, [D_SOFIC, D_TOP_ENT, D_RIGHT_RE]),
    (L_3_4, [D_SFT, D_IRR_SFT, D_LOC_ADM, D_GLOB_ADM]),
    (C_3_5, [D_SFT, D_IRR_SFT, D_GLOB_ADM]),
    (AX_VP, [D_TOP_ENT, D_MEAS_ENT, D_INV_MEAS]),
    (AX_USC, [D_MEAS_ENT, D_INV_MEAS]),
    (AX_LEFTRE_IRR, [D_SFT, D_IRR_SFT, D_TOP_ENT]),
]:
    for d in deps:
        E(EdgeType.USES_DEFINITION, t, d, where_="in_statement")

# Proof-mining: which prior results each proof invokes
for src, dst, where in [
    (T_3_1, AX_VP, "in_proof"),
    (T_3_1, AX_USC, "in_proof"),
    (T_3_2, AX_VP, "in_proof"),
    (T_3_2, AX_USC, "in_proof"),
    (T_3_2, T_3_1, "in_proof"),         # "identical to the proof of ... at the end of Theorem 3.1"
    (C_3_SOFIC, T_3_2, "in_proof"),
    (C_3_SOFIC, D_SOFIC, "in_proof"),   # "every sofic is a factor of an SFT"
    (T_1_3, T_3_1, "in_proof"),          # right-r.e. half
    (T_1_3, L_3_4, "in_proof"),          # via irreducibility-gluing
    (T_1_3, AX_LEFTRE_IRR, "in_proof"),  # left-r.e. half (Lean axiom)
    (T_1_3, LEAN_COMP_IFF, "in_proof"),  # computable ⇔ left+right r.e.
    (C_3_5, L_3_4, "in_proof"),
    (T_1_2, C_3_SOFIC, "in_proof"),
    (T_1_2, T_1_1, "in_proof"),
]:
    E(EdgeType.DEPENDS_ON, src, dst, where_=where)

# Higher-level structural edges
E(EdgeType.COROLLARY_OF, C_3_SOFIC, T_3_2)
E(EdgeType.COROLLARY_OF, C_3_5, L_3_4)
# T_3_1 is the right-r.e. *necessity* half of T_1_1; record as partial resolution.
E(EdgeType.RESOLVES, T_3_1, T_1_1, regime="d>=2", notes="partial:necessity")

# Cross-paper attribution to the metadata-only classics
for src, paper in [
    (D_SOFIC, "arxiv:weiss1973"),
    (T_1_1, "arxiv:berger1966"),      # undecidability backdrop cited in §1
    (T_1_1, "arxiv:robinson1971"),
    (T_3_1, "arxiv:friedland1997"),   # "follows from the work of Friedland"
    (AX_VP, "arxiv:mozes1989"),       # Misiurewicz cited but also Mozes is in §1 backdrop
]:
    E(EdgeType.ATTRIBUTED_TO, src, paper)

# -------------------------------------------------------------------------
# Emit + validate.
# -------------------------------------------------------------------------

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
            for k in ["friedland1997", "B66", "robinson71", "W73", "mozes89",
                      "M76", "LM95", "CP75", "D06"]
        ],
    }
    errs = validate_subgraph(sg)
    out = Path(__file__).resolve().parent / "math_0703206.subgraph.json"
    out.write_text(json.dumps(sg, indent=2, sort_keys=True))
    n_proved = sum(1 for n in nodes if n.lean_status == "proved")
    n_stated = sum(1 for n in nodes if n.lean_status == "stated")
    n_axiom = sum(1 for n in nodes if n.lean_status == "axiomatized")
    n_unform = sum(1 for n in nodes
                   if not n.lean_status and n.kind != NodeKind.CONCEPT.value)
    print(f"wrote {out.name}: {len(nodes)} nodes, {len(edges)} edges, "
          f"{len(errs)} validation errors")
    print(f"  Lean back-links: {n_proved} proved · {n_stated} stated · "
          f"{n_axiom} axiomatized · {n_unform} unformalized")
    if errs:
        for e in errs[:10]:
            print(f"  ! {e}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
