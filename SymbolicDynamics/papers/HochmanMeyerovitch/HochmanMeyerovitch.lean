import Mathlib.Analysis.SpecialFunctions.Log.Basic
import dependencies.Subshift
import dependencies.Box
import dependencies.LocallyAdmissible
import dependencies.GloballyAdmissible
import dependencies.Entropy
import dependencies.Computable
import dependencies.NbarComputable
import dependencies.IrreducibleConsequences
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
theorem topEntropy_irreducible_computable {α : Type*} {d : ℕ}
    [Fintype α] [DecidableEq α] [Encodable α] [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty)
    (h_irr : IsIrreducibleShift (mkSFT F L)) :
    IsComputableReal (topEntropy (mkSFT F L)) :=
  (computable_iff_leftRE_and_rightRE).mpr
    ⟨topEntropy_leftRE_irreducible F L hX h_irr,
     topEntropy_rightRE F L hX⟩
