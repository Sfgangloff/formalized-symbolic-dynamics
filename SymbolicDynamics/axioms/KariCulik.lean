import dependencies.Subshift
import dependencies.Box
import dependencies.GloballyAdmissible
import dependencies.KariCulik

/-! # Axioms about the Kari–Culik shift

The 2D Kari–Culik shift is the SFT defined by the 13 Wang tiles of
Kari–Culik (1995): the smallest known aperiodic tile set. We do not
formalise the construction of the tile set or any deep facts about it;
this file records the existence of the shift, a single known
non-trivial property (positive entropy, Durand–Gamard–Grandjean 2013),
and a small amount of auxiliary scaffolding used by the open questions
in `openProblems/KariCulikEntropy/generated_questions/`.

References:
- J. Kari, *A small aperiodic set of Wang tiles*, Discrete Math. 160
  (1996) 259–264.
- K. Culik II, *An aperiodic set of 13 Wang tiles*, Discrete Math. 160
  (1996) 245–251.
- B. Durand, G. Gamard, A. Grandjean, *Aperiodic tilings and entropy*,
  DLT 2014 / arXiv:1312.4126.  Preprint:
  `../papers/DurandGamardGrandjean/1312.4126v2.pdf`.
-/

/-! ## The shift itself -/

/-- The Kari–Culik 2D shift: a subshift of `(KCTile)^{ℤ²}` whose
configurations are the valid Wang tilings of `ℤ²` by the 13 Kari–Culik
tiles. -/
axiom kariCulikShift : Subshift KCTile 2

/-- The Kari–Culik shift is a shift of finite type (it is presented by
a finite local rule — the tile-matching constraint at each pair of
adjacent positions). -/
axiom kariCulikShift_isSFT : IsSFT kariCulikShift

/-- The Kari–Culik shift is nonempty: the 13 tiles do tile `ℤ²`. -/
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
v2. Axiomatised here since the Kari–Culik tile encoding `KCTile ≃ Fin 13`
is not specified. -/
axiom dgg_A1  : Pattern KCTile (box 2 2)
axiom dgg_A1' : Pattern KCTile (box 2 2)
axiom dgg_A2  : Pattern KCTile (box 2 2)
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
