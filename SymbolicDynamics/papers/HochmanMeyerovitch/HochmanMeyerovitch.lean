import Mathlib.Analysis.SpecialFunctions.Log.Basic
import dependencies.Subshift
import dependencies.Box
import dependencies.LocallyAdmissible
import dependencies.GloballyAdmissible
import dependencies.Entropy
import dependencies.Computable
import dependencies.NbarComputable
import dependencies.IrreducibleConsequences
import dependencies.FactorMap
import axioms.Computability

/-! # Hochman–Meyerovitch — main theorems

The three main theorems from Hochman–Meyerovitch (arXiv:math/0703206):

- **Theorem 3.1** = necessity half of Theorem 1.1: the topological entropy
  of a nonempty SFT is right recursively enumerable (`topEntropy_rightRE`).
- **Lemma 3.4**: compactness dichotomy for irreducible SFTs (`Lemma_3_4`).
- **Theorem 1.3**: the topological entropy of a nonempty irreducible SFT
  is computable (`topEntropy_irreducible_computable`).

All auxiliary lemmas, supporting definitions and axioms used by these
proofs live in `dependencies/` and `axioms/`; this file contains only
the paper's stated theorems and their direct proofs.
-/

/-- **Theorem 3.1** (necessity half of Theorem 1.1). The topological entropy
of a nonempty SFT is right recursively enumerable.

Combines `topEntropy_le_log_N_bar_div_pow` (upper bound),
`log_N_bar_div_pow_tendsto_topEntropy` (convergence axiom, deep
ergodic-theory content), and `rationalUpperApprox_log_N_bar` (computable
rational upper approximation). -/
-- @ontology: hm:thm:3.1
theorem topEntropy_rightRE {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    [Encodable α] [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty) :
    IsRightRE (topEntropy (mkSFT F L)) := by
  obtain ⟨q, hq_comp, hq_upper, hq_gap⟩ := rationalUpperApprox_log_N_bar F L
  refine ⟨q, hq_comp, ?_, ?_⟩
  · intro n
    have h_upper :=
      topEntropy_le_log_N_bar_div_pow F L hX (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    exact h_upper.trans (hq_upper n)
  · have h_conv := log_N_bar_div_pow_tendsto_topEntropy F L hX
    have h_sum := hq_gap.add h_conv
    have h_target :
        (fun n : ℕ =>
          ((q n : ℝ) - Real.log (N_bar F L (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ d) +
            Real.log (N_bar F L (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ d)
          = fun n : ℕ => (q n : ℝ) := by
      funext n; ring
    rw [h_target, zero_add] at h_sum
    exact h_sum

/-- **Lemma 3.4** (Hochman–Meyerovitch). For a nonempty `r`-irreducible SFT
`X = mkSFT F L` and a pattern `a` on the symmetric cube `symBox d k`, the
dichotomy holds: either `a` is not globally admissible (case 1) or `a` is
globally admissible (case 2), with the corresponding effective consequence.

The two cases (`Lemma_3_4_case_notGA` proved by compactness of the full
shift, `Lemma_3_4_case_GA` proved via the irreducibility-gluing axiom)
live in `dependencies/IrreducibleConsequences.lean`. -/
-- @ontology: hm:lem:3.4
theorem Lemma_3_4 {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty)
    (h_irr : IsIrreducibleShift (mkSFT F L))
    {k : ℕ} (a : Pattern α (symBox d k)) :
    (¬ Pattern.GloballyAdmissible (mkSFT F L) a ∧
      ∃ N₀, ∀ N ≥ N₀, ∀ b : Pattern α (symBox d N),
        locallyAdmissible F L b →
        ∀ h : symBox d k ⊆ symBox d N,
          (Pattern.restrict (symBox d k) h b) ≠ a)
    ∨
    (Pattern.GloballyAdmissible (mkSFT F L) a ∧
      ∃ N₀, ∀ N ≥ N₀, ∀ b : Pattern α (symBox d N),
        locallyAdmissible F L b → Pattern.rCompatible (mkSFT F L) (Nat.sqrt N) a b) := by
  by_cases h_ga : Pattern.GloballyAdmissible (mkSFT F L) a
  · exact Or.inr ⟨h_ga, Lemma_3_4_case_GA F L hX h_irr a h_ga⟩
  · exact Or.inl ⟨h_ga, Lemma_3_4_case_notGA F L hX h_irr a h_ga⟩

/-- **Theorem 1.3.** The topological entropy of a nonempty irreducible SFT is
computable, derived from the right-r.e. (Theorem 3.1, `topEntropy_rightRE`) and
left-r.e. (`topEntropy_leftRE_irreducible`, in
`dependencies/IrreducibleConsequences.lean`) approximations via
`computable_iff_leftRE_and_rightRE`. -/
-- @ontology: hm:thm:1.3
theorem topEntropy_irreducible_computable {α : Type*} {d : ℕ}
    [Fintype α] [DecidableEq α] [Encodable α] [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty)
    (h_irr : IsIrreducibleShift (mkSFT F L)) :
    IsComputableReal (topEntropy (mkSFT F L)) :=
  (computable_iff_leftRE_and_rightRE).mpr
    ⟨topEntropy_leftRE_irreducible F L hX h_irr,
     topEntropy_rightRE F L hX⟩

/-! ## Main theorems — statements only

The following are HM's main results stated as `theorem … := by sorry`.
Their proofs are not yet formalized; they connect the right-r.e. content
of `topEntropy_rightRE`, the gluing constructions sketched in §4–§5 of the
paper, and the sofic factor reduction. Each carries an `@ontology` marker
so the back-link from the ontology graph survives renames. -/

/-- The set of entropies realized by nonempty `d`-dimensional SFTs. -/
def entropySetSFT (d : ℕ) : Set ℝ :=
  { h | ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α)
          (_ : Encodable α) (_ : TopologicalSpace α) (_ : T1Space α)
          (F : Finset (Lat d)) (L : Finset (Pattern α F)),
      (mkSFT F L).carrier.Nonempty ∧ topEntropy (mkSFT F L) = h }

/-- The set of entropies realized by nonempty `d`-dimensional sofic shifts. -/
def entropySetSofic (d : ℕ) : Set ℝ :=
  { h | ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α)
          (_ : Encodable α) (_ : TopologicalSpace α) (_ : T1Space α)
          (X : Subshift α d),
      X.carrier.Nonempty ∧ IsSofic X ∧ topEntropy X = h }

/-- The set of non-negative right recursively enumerable real numbers. -/
def nonnegRightREs : Set ℝ := { h | 0 ≤ h ∧ IsRightRE h }

/-- **Theorem 1.1** (HM main). For `d ≥ 2`, the class of entropies of
`d`-dimensional SFTs is exactly the class of non-negative right
recursively enumerable real numbers. -/
-- @ontology: hm:thm:1.1
theorem HM_Theorem_1_1 {d : ℕ} (_hd : 2 ≤ d) :
    entropySetSFT d = nonnegRightREs := by
  sorry

/-- **Theorem 1.2** (HM main). For `d ≥ 2`, the class of entropies of
`d`-dimensional sofic shifts equals that of `d`-dimensional SFTs. -/
-- @ontology: hm:thm:1.2
theorem HM_Theorem_1_2 {d : ℕ} (_hd : 2 ≤ d) :
    entropySetSofic d = entropySetSFT d := by
  sorry

/-- **Theorem 3.2** (sofic version of 3.1). The topological entropy of a
nonempty sofic shift is right recursively enumerable. The proof factors
through a one-block SFT cover and counts image patterns. -/
-- @ontology: hm:thm:3.2
theorem HM_Theorem_3_2 {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    [Encodable α] [TopologicalSpace α] [T1Space α]
    (Y : Subshift α d) (_hY : Y.carrier.Nonempty) (_hSof : IsSofic Y) :
    IsRightRE (topEntropy Y) := by
  sorry

/-- **Corollary** (HM). The topological entropy of every sofic shift is
right recursively enumerable. Direct consequence of `HM_Theorem_3_2`. -/
-- @ontology: hm:cor:sofic-right-re
theorem HM_Corollary_sofic_right_re {α : Type*} {d : ℕ} [Fintype α]
    [DecidableEq α] [Encodable α] [TopologicalSpace α] [T1Space α]
    (Y : Subshift α d) (hY : Y.carrier.Nonempty) (hSof : IsSofic Y) :
    IsRightRE (topEntropy Y) :=
  HM_Theorem_3_2 Y hY hSof

/-- **Corollary 3.5** (HM). For a nonempty irreducible SFT `X`, global
admissibility of finite patterns is decidable. Stated as a `Nonempty`
of `Decidable` to keep the conclusion in `Prop`. -/
-- @ontology: hm:cor:3.5
theorem HM_Corollary_3_5 {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    [Encodable α] [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (_hX : (mkSFT F L).carrier.Nonempty)
    (_h_irr : IsIrreducibleShift (mkSFT F L))
    {E : Finset (Lat d)} (_a : Pattern α E) :
    Nonempty (Decidable (Pattern.GloballyAdmissible (mkSFT F L) _a)) := by
  sorry
