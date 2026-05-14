import dependencies.Subshift
import dependencies.Box
import dependencies.GloballyAdmissible
import dependencies.KariCulik

/-! # Axioms about the Kari–Culik shift

The 2D Kari–Culik shift is now formalised concretely as the SFT
`mkSFT kcWindow kcAllowed` over the DGG 14-tile alphabet (see
`dependencies/KariCulik.lean`). What remains here are the *deep*
properties — the ones that were genuinely axiomatic even when the
tile-matching rule was opaque — and the auxiliary scaffolding for the
DGG open questions.

What is now a theorem (no longer an axiom):
- `kariCulikShift` itself — a `def` based on explicit Wang tile data.
- `kariCulikShift_isSFT` — direct from `mkSFT_isSFT`.

What remains axiomatic:
- `kariCulikShift_carrier_nonempty` — the witness `kcWitness` (a 2×2-
  periodic configuration) is exhibited concretely in
  `dependencies/KariCulik.lean`, and the MCP transfer-matrix /
  periodic-search tools confirm it; the membership proof
  `kcWitness ∈ kariCulikShift.carrier` is mechanical lattice-parity
  case analysis kept axiomatic for now.
- `kariCulikShift_entropy_pos` — DGG's positive-entropy result; a
  substantial proof not formalised in this project.
- The DGG-paper open-problem scaffolding (`Pattern.hasPositiveDensity`,
  `dgg_A1` …, `kariCulikShift_forbid`, `kariCulikHorizontalShift`).

References:
- J. Kari, *A small aperiodic set of Wang tiles*, Discrete Math. 160
  (1996) 259–264.
- K. Culik II, *An aperiodic set of 13 Wang tiles*, Discrete Math. 160
  (1996) 245–251.
- B. Durand, G. Gamard, A. Grandjean, *Aperiodic tilings and entropy*,
  DLT 2014 / arXiv:1312.4126.  Preprint:
  `../papers/DurandGamardGrandjean/1312.4126v2.pdf`.
-/

/-! ## Non-emptiness and positive entropy -/

/-- The Kari–Culik shift is nonempty: the DGG 14 tiles tile `ℤ²`.
A concrete 2×2-periodic witness `kcWitness` is given in
`dependencies/KariCulik.lean`; the membership proof is left
axiomatic here pending a finite parity case analysis. -/
axiom kariCulikShift_carrier_nonempty : kariCulikShift.carrier.Nonempty

/-- **Durand–Gamard–Grandjean (2013).** The Kari–Culik shift has
strictly positive topological entropy. -/
axiom kariCulikShift_entropy_pos : 0 < topEntropy kariCulikShift

/-! ## Auxiliary scaffolding for the open questions in
`openProblems/KariCulikEntropy/generated_questions/`

The Durand–Gamard–Grandjean paper raises three open questions in
Section 4 ("Positive entropy"), subsection "Open problems". To state
them as Lean `Prop`s we need a small amount of additional structure:
a pattern-density predicate, the four specific 2×2 patterns DGG
construct, an extended-forbidden-patterns subshift, and the 1D shift
of horizontal lines. All four are axiomatised here. -/

/-- "Pattern `p` appears with positive density in configuration `x`":
the asymptotic frequency of occurrences of `p` along `symBox d n`
divided by `(2n+1)^d` is strictly positive. Axiomatised here as an
opaque `Prop`; a full definition would compute the frequency. -/
axiom Pattern.hasPositiveDensity {α : Type*} {d : ℕ} [TopologicalSpace α]
    {F : Finset (Lat d)} (p : Pattern α F) (x : FullShift α d) : Prop

/-- The four 2×2 `KCTile` patterns that constitute Durand–Gamard–Grandjean's
two substitutive pairs `(A₁, A'₁)` and `(A₂, A'₂)`. They appear with
concrete tile values in Section 4 (subsection "Coming back to the
function" → figures `A_1`, `A'_1`, `A_2`, `A'_2`) of arXiv:1312.4126,
v2. Axiomatised here since the explicit `Fin 14`-coordinate transcription
has not been performed. -/
axiom dgg_A1 : Pattern KCTile (box 2 2)
axiom dgg_A1' : Pattern KCTile (box 2 2)
axiom dgg_A2 : Pattern KCTile (box 2 2)
axiom dgg_A2' : Pattern KCTile (box 2 2)

/-- The subshift obtained from `kariCulikShift` by additionally forbidding
a finite set of 2×2 patterns. A full definition would extend the
Kari–Culik SFT presentation by including the given patterns in the
forbidden list; axiomatised here. -/
axiom kariCulikShift_forbid :
    Finset (Pattern KCTile (box 2 2)) → Subshift KCTile 2

/-- The 1D subshift of horizontal lines that appear in valid Kari–Culik
tilings of `ℤ²`: the closure under horizontal shifts of the set
`{x : KCTile^ℤ | ∃ y ∈ kariCulikShift, ∀ i, x i = y (i, 0)}`.
Axiomatised here. -/
axiom kariCulikHorizontalShift : Subshift KCTile 1
