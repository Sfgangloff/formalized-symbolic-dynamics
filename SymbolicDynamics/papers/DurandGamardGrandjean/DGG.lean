import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import dependencies.Subshift
import dependencies.KariCulik
import dependencies.LocallyAdmissible
import dependencies.DGG
import axioms.KariCulik
import axioms.DGG

/-! # Durand–Gamard–Grandjean (arXiv:1312.4126) — paper stubs

Statements only. Definitions, lemmas, propositions, theorem, corollary,
conjecture, and open problems from the body of the DGG paper, each
recorded with an `@ontology` marker so the ontology graph back-links to
the Lean source. Proofs are placeholders (`theorem … := by sorry`);
opaque DGG constants live in `axioms/DGG.lean` and `axioms/KariCulik.lean`.

References: Durand, Gamard, Grandjean. *Aperiodic tilings and entropy.*
arXiv:1312.4126v2.
-/

/-! ## §2 — The Kari–Culik base function `f` -/

/-- **Definition (DGG, §2).** The Kari–Culik base function
`f : [1/3, 2] → [1/3, 2]`, given by `f(x) = 2x` on `[1/3, 1]` and
`f(x) = x/3` on `[1, 2]`. -/
-- @ontology: dgg:def:kc-function-f
noncomputable def kcF (x : ℝ) : ℝ :=
  if x ≤ 1 then 2 * x else x / 3

/-- **Lemma (DGG, §2).** The forward orbits of `kcF` are dense in
`[1/3, 2]`. -/
-- @ontology: dgg:lem:dense-f
theorem kcF_orbits_dense :
    ∀ x ∈ Set.Icc ((1 : ℝ) / 3) 2,
      closure (Set.range (fun n : ℕ => kcF^[n] x)) ⊇ Set.Icc ((1 : ℝ) / 3) 2 := by
  sorry

/-- **Proposition (DGG, §2).** For every interval `I ⊆ [1/3, 2]`, the
maximal number of iterations of `kcF` between two consecutive visits to
`I` is bounded. -/
-- @ontology: dgg:prop:dense2
theorem kcF_bounded_return_time
    (I : Set ℝ) (_hI : I ⊆ Set.Icc ((1 : ℝ) / 3) 2)
    (_hI_ne : I.Nonempty) :
    ∃ N : ℕ, ∀ x ∈ Set.Icc ((1 : ℝ) / 3) 2,
      ∀ n : ℕ, kcF^[n] x ∈ I →
        ∃ k, k ≤ N ∧ 0 < k ∧ kcF^[n + k] x ∈ I := by
  sorry

/-! ## §3 — Substitutive pairs and the DGG construction

`SubstitutivePair` (§3 definition) lives in `dependencies/DGG.lean`; the
existence axiom `dggSubstitutivePairs` (§3 construction) lives in
`axioms/DGG.lean`. -/

/-! ## §4 — Monteil cylindricity and the line-average proposition

`cylindricityFunction` (§4 definition, Monteil 2012) lives in
`axioms/DGG.lean`. -/

/-- **Proposition (DGG, §4).** Every horizontal line in any tiling by
the DGG 14-tile set has an average, in the sense of frequencies of
symbols. The average is encoded as an opaque `ℝ` per point of the
shift; the proposition asserts existence of this limit. -/
-- @ontology: dgg:prop:line-average
theorem dggLine_has_average (x : FullShift KCTile 2) (_hx : x ∈ kariCulikShift)
    (row : ℤ) :
    ∃ avg : ℝ,
      Filter.Tendsto
        (fun N : ℕ =>
          ((Finset.Ico (-(N : ℤ)) (N : ℤ)).card : ℝ)⁻¹ *
          (Finset.Ico (-(N : ℤ)) (N : ℤ)).sum (fun col =>
            ((x ![col, row]).val : ℝ)))
        Filter.atTop (nhds avg) := by
  sorry

/-- **Lemma (DGG, §4).** Along any horizontal line whose density lies in
`(4/5, 9/10)`, the family of patterns `0 1^α 0` for `α > 3` appears
with positive density. Stated abstractly here. -/
-- @ontology: dgg:lem:linear-pattern-density
theorem dggLine_density_01alpha0 (x : FullShift KCTile 2)
    (_hx : x ∈ kariCulikShift) (row : ℤ) (density : ℝ)
    (_h_density_lo : (4 : ℝ) / 5 < density)
    (_h_density_hi : density < (9 : ℝ) / 10) :
    ∃ c : ℝ, 0 < c ∧
      ∀ α : ℕ, 3 < α → True := by
  sorry

/-! ## §5 — Main theorem and refutation of Monteil's conjecture -/

/-- **Monteil's linear-complexity conjecture (2012, refuted).** The 2D
pattern complexity of the Kari–Culik shift satisfies
`log p(n, n) = O(n)`. Stated as a `Prop` here; refuted by `dgg:cor:refutes-monteil`
via positivity of `topEntropy kariCulikShift`. -/
-- @ontology: dgg:conj:monteil-linear-complexity
def Monteil_LinearComplexity_Conjecture : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, Real.log
      ((Finset.univ : Finset (Pattern KCTile (box 2 n))).card.succ : ℝ)
    ≤ C * (n : ℝ)

/-- **Corollary (DGG, §5).** The DGG main theorem — positivity of
`topEntropy kariCulikShift` — implies `log p(n, n) ∈ Θ(n²)`, hence
refutes Monteil's linear-complexity conjecture. -/
-- @ontology: dgg:cor:refutes-monteil
theorem dgg_refutes_monteil
    (_h_pos : 0 < topEntropy kariCulikShift) :
    ¬ Monteil_LinearComplexity_Conjecture := by
  sorry

/-! ## §6 — Open problems -/

/-- **Open problem (DGG, §6).** Is one of the two DGG substitutive pairs
dense by itself in some tiling? -/
-- @ontology: dgg:op:single-pair-dense
def DGG_OpenProblem_singlePairDense : Prop :=
  ∃ (x : FullShift KCTile 2) (W B : Finset (Lat 2)) (_hB : B ⊆ W)
    (p q : Pattern KCTile W),
      x ∈ kariCulikShift ∧ SubstitutivePair W B _hB p q ∧
      (∀ N : ℕ, ∃ u v : Lat 2,
        Lat.supNorm u ≤ N ∧ Lat.supNorm v ≤ N ∧
        Pattern.AppearsAt p x u ∧ Pattern.AppearsAt q x v)

/-- **Open problem (DGG, §6).** Forbidding one pattern from each
substitutive pair produces a sub-tileset; is its topological entropy
still positive? More generally: can finitely many forbidden patterns
force entropy zero? -/
-- @ontology: dgg:op:forbid-pattern
def DGG_OpenProblem_forbidPattern : Prop :=
  ∀ (forbid₁ forbid₂ : Pattern KCTile (box 2 2)),
    ∀ X : Subshift KCTile 2,
      X.carrier ⊆ kariCulikShift.carrier →
      (∀ x ∈ X, ¬ Pattern.AppearsAt forbid₁ x 0) →
      (∀ x ∈ X, ¬ Pattern.AppearsAt forbid₂ x 0) →
      0 < topEntropy X
