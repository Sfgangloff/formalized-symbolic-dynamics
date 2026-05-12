import Mathlib.Computability.Partrec
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import dependencies.Subshift
import dependencies.Box
import dependencies.LocallyAdmissible
import dependencies.GloballyAdmissible
import dependencies.Computable

/-! # Computability axioms for Hochman–Meyerovitch

Axioms covering the computability content used in the proof of
Theorems 1.1 / 1.3:

- `primrec_admPredDigit`: the digit-level local-admissibility predicate
  `admPredDigit F L n k` is primitive-recursive in `(n, k)` (a
  meta-mathematically obvious fact, pending a `Primcodable` /
  `Finset` infrastructure pass).
- `log_N_bar_div_pow_tendsto_topEntropy`: convergence of
  `log (N_bar F L (n+1)) / (n+1)^d` to `topEntropy` (deep ergodic-theory
  content; uses the axioms in `axioms/InvariantMeasure.lean`).
- `rationalApprox_log_div_pow_of_computable`: simultaneous computable
  rational bracket of `Real.log (f n) / (n+1)^d` for any Computable
  `f : ℕ → ℕ` (pure computable real analysis).

This file contains *only axioms*. Theorems derived from them
(`N_bar_computable`, `rationalUpperApprox_log_div_pow_of_computable`,
`rationalLowerApprox_log_div_pow_of_computable`, `rationalUpperApprox_log_N_bar`)
live in `dependencies/NbarComputable.lean`.
-/

/-- `admPredDigit F L n k` is built from `digit`, comparison with constants
in `L`, and iteration over the constant Finsets `relevantOffsets F (box d n)`,
`L`, `F`. It is Primrec₂ in principle, but a full proof needs Primcodable
infrastructure for `Finset (Lat d)` and primrec encodings of `Finset.image`,
`Finset.filter`, `Fintype.piFinset`, `Finset.Ico` on `ℤ`. We axiomatize the
result here. -/
axiom primrec_admPredDigit {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    {d : ℕ} (F : Finset (Lat d)) (L : Finset (Pattern α F)) :
    Primrec₂ (fun n k : ℕ => decide (admPredDigit F L n k))

/-- For a nonempty SFT, `Real.log (N_bar F L (n+1)) / ((n+1) : ℝ)^d → topEntropy (mkSFT F L)`
as `n → ∞`. Combines the i.i.d. uniform measure on locally admissible patterns
with the variational principle, upper semi-continuity of measure entropy, and
compactness of `M(X)`. -/
axiom log_N_bar_div_pow_tendsto_topEntropy {α : Type*} {d : ℕ}
    [Fintype α] [DecidableEq α] [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty) :
    Filter.Tendsto
      (fun n : ℕ => Real.log (N_bar F L (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ d)
      Filter.atTop (nhds (topEntropy (mkSFT F L)))

/-- For any Computable `f : ℕ → ℕ`, simultaneous Computable rational bracket
of `Real.log (f n) / ((n+1) : ℝ)^d` whose width tends to zero. -/
axiom rationalApprox_log_div_pow_of_computable {d : ℕ}
    {f : ℕ → ℕ} (hf : Computable f) :
    ∃ qU qL : ℕ → ℚ, Computable qU ∧ Computable qL ∧
      (∀ n : ℕ,
        (qL n : ℝ) ≤ Real.log (f n) / ((n + 1 : ℕ) : ℝ) ^ d ∧
        Real.log (f n) / ((n + 1 : ℕ) : ℝ) ^ d ≤ (qU n : ℝ)) ∧
      Filter.Tendsto
        (fun n : ℕ => (qU n : ℝ) - (qL n : ℝ))
        Filter.atTop (nhds 0)
