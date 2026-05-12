import Mathlib.Computability.Partrec
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import dependencies.Subshift
import dependencies.Box
import dependencies.LocallyAdmissible
import dependencies.GloballyAdmissible
import dependencies.Computable
import axioms.Computability

/-! # Consequences of the computability axioms

Theorems derived from the axioms in `axioms/Computability.lean`:

- `N_bar_computable` — `Computable (fun n => N_bar F L n)`, by combining
  `N_bar_eq_count_digit`, `primrec_admPredDigit`, and primitive recursion.
- `rationalUpperApprox_log_div_pow_of_computable` /
  `rationalLowerApprox_log_div_pow_of_computable` — extract the upper /
  lower side of the bracket axiom `rationalApprox_log_div_pow_of_computable`.
- `rationalUpperApprox_log_N_bar` — specialised upper approximation for
  `Real.log (N_bar F L (n+1)) / ((n+1) : ℝ)^d` (combines `N_bar_computable`
  with `rationalUpperApprox_log_div_pow_of_computable`).
-/

/-- `N_bar F L` is computable: derived from `N_bar_eq_count_digit`,
`primrec_admPredDigit`, and primitive recursion on the bound `(card α)^(n^d)`. -/
theorem N_bar_computable {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    {d : ℕ} (F : Finset (Lat d)) (L : Finset (Pattern α F)) :
    Computable (fun n => N_bar F L n) := by
  let countAux : ℕ → ℕ → ℕ := fun n m =>
    Nat.rec 0 (fun i IH => IH + (if admPredDigit F L n i then 1 else 0)) m
  have h_count : Primrec₂ countAux := by
    have h_pred_at : Primrec (fun q : ℕ × ℕ × ℕ =>
        decide (admPredDigit F L q.1 q.2.1)) :=
      (primrec_admPredDigit F L).comp Primrec.fst (Primrec.fst.comp Primrec.snd)
    have h_one_or_zero : Primrec (fun q : ℕ × ℕ × ℕ =>
        if admPredDigit F L q.1 q.2.1 then 1 else 0) := by
      have : ∀ q : ℕ × ℕ × ℕ,
          (if admPredDigit F L q.1 q.2.1 then 1 else 0) =
          (if decide (admPredDigit F L q.1 q.2.1) = true then 1 else 0) := by
        intro q
        simp
      refine Primrec.of_eq ?_ (fun q => (this q).symm)
      exact Primrec.ite (Primrec.eq.comp h_pred_at (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0)
    have h_step : Primrec₂ (fun (n : ℕ) (p : ℕ × ℕ) =>
        p.2 + if admPredDigit F L n p.1 then 1 else 0) :=
      Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) h_one_or_zero
    exact Primrec.nat_rec (f := fun _ : ℕ => (0 : ℕ)) (Primrec.const 0) h_step
  have h_eq : ∀ n m, countAux n m = Nat.count (admPredDigit F L n) m := by
    intro n m
    induction m with
    | zero => simp [countAux, Nat.count_zero]
    | succ m ih =>
      show countAux n m + _ = Nat.count (admPredDigit F L n) (m + 1)
      rw [Nat.count_succ, ih]
  have h_bound : Primrec (fun n : ℕ => (Fintype.card α)^(n^d)) :=
    primrec_const_pow_pow _ d
  have h_comp : Primrec (fun n : ℕ =>
      countAux n ((Fintype.card α)^(n^d))) := by
    have := h_count.comp Primrec.id h_bound
    exact this
  have h_eq_N_bar : ∀ n, N_bar F L n = countAux n ((Fintype.card α)^(n^d)) := by
    intro n
    rw [N_bar_eq_count_digit, ← h_eq]
  have h_primrec : Primrec (fun n => N_bar F L n) := by
    refine Primrec.of_eq h_comp ?_
    intro n
    exact (h_eq_N_bar n).symm
  exact h_primrec.to_comp

/-- Extract a Computable rational *upper* approximation from the bracket axiom. -/
theorem rationalUpperApprox_log_div_pow_of_computable {d : ℕ}
    {f : ℕ → ℕ} (hf : Computable f) :
    ∃ q : ℕ → ℚ, Computable q ∧
      (∀ n : ℕ, Real.log (f n) / ((n + 1 : ℕ) : ℝ) ^ d ≤ (q n : ℝ)) ∧
      Filter.Tendsto
        (fun n : ℕ => (q n : ℝ) - Real.log (f n) / ((n + 1 : ℕ) : ℝ) ^ d)
        Filter.atTop (nhds 0) := by
  obtain ⟨qU, qL, hqU_comp, _hqL_comp, h_bracket, h_gap⟩ :=
    rationalApprox_log_div_pow_of_computable (d := d) hf
  refine ⟨qU, hqU_comp, fun n => (h_bracket n).2, ?_⟩
  refine squeeze_zero (fun n => sub_nonneg.mpr (h_bracket n).2)
    (fun n => ?_) h_gap
  have h_lower := (h_bracket n).1
  linarith

/-- Extract a Computable rational *lower* approximation from the bracket axiom. -/
theorem rationalLowerApprox_log_div_pow_of_computable {d : ℕ}
    {f : ℕ → ℕ} (hf : Computable f) :
    ∃ q : ℕ → ℚ, Computable q ∧
      (∀ n : ℕ, (q n : ℝ) ≤ Real.log (f n) / ((n + 1 : ℕ) : ℝ) ^ d) ∧
      Filter.Tendsto
        (fun n : ℕ => Real.log (f n) / ((n + 1 : ℕ) : ℝ) ^ d - (q n : ℝ))
        Filter.atTop (nhds 0) := by
  obtain ⟨qU, qL, _hqU_comp, hqL_comp, h_bracket, h_gap⟩ :=
    rationalApprox_log_div_pow_of_computable (d := d) hf
  refine ⟨qL, hqL_comp, fun n => (h_bracket n).1, ?_⟩
  refine squeeze_zero (fun n => sub_nonneg.mpr (h_bracket n).1)
    (fun n => ?_) h_gap
  have h_upper := (h_bracket n).2
  linarith

/-- Computable rational upper approximation of
`Real.log (N_bar F L (n+1)) / ((n+1) : ℝ)^d`. Specialises the abstract
bracket axiom to `f := fun n => N_bar F L (n+1)`. -/
theorem rationalUpperApprox_log_N_bar {α : Type*} [Fintype α] [DecidableEq α]
    [Encodable α] {d : ℕ} (F : Finset (Lat d)) (L : Finset (Pattern α F)) :
    ∃ q : ℕ → ℚ, Computable q ∧
      (∀ n : ℕ,
        Real.log (N_bar F L (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ d ≤ (q n : ℝ)) ∧
      Filter.Tendsto
        (fun n : ℕ =>
          (q n : ℝ) - Real.log (N_bar F L (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ d)
        Filter.atTop (nhds 0) := by
  have h_shift : Computable (fun n : ℕ => N_bar F L (n + 1)) :=
    (N_bar_computable F L).comp (Primrec.succ.to_comp)
  exact rationalUpperApprox_log_div_pow_of_computable (d := d) h_shift
