import Mathlib.Computability.Partrec
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Nat.Count
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import dependencies.ComputableRat
import dependencies.Subshift
import dependencies.Box
import dependencies.LocallyAdmissible
import dependencies.GloballyAdmissible

/-! # Computable / r.e. reals and computability of `N_bar`

Predicates `IsRightRE`, `IsLeftRE`, `IsComputableReal` for real numbers
plus the equivalence `computable ↔ leftRE ∧ rightRE`; primitive-recursive
helpers (digit extraction, base-`m` decoding, pattern encoding); and a
computable, digit-level form of local admissibility used to express
`N_bar` as a primitive-recursive count.

Originally lived in `papers/HochmanMeyerovitch/HochmanMeyerovitch.lean`;
moved here for reuse.
-/

/-! ## Recursively enumerable / computable reals -/

/-- `h : ℝ` is right recursively enumerable if it is the limit of a computable sequence
    of rationals approaching from above. -/
-- @ontology: hm:def:right-re
def IsRightRE (h : ℝ) : Prop :=
  ∃ r : ℕ → ℚ, Computable r ∧ (∀ n, h ≤ (r n : ℝ)) ∧
    Filter.Tendsto (fun n => (r n : ℝ)) Filter.atTop (nhds h)

/-- `h : ℝ` is left recursively enumerable if it is the limit of a computable sequence
    of rationals approaching from below. -/
def IsLeftRE (h : ℝ) : Prop :=
  ∃ r : ℕ → ℚ, Computable r ∧ (∀ n, (r n : ℝ) ≤ h) ∧
    Filter.Tendsto (fun n => (r n : ℝ)) Filter.atTop (nhds h)

/-- `h : ℝ` is computable if there is a computable sequence of rationals
    approximating it with effective rate `1/(n+1)`. -/
-- @ontology: hm:def:computable-real
def IsComputableReal (h : ℝ) : Prop :=
  ∃ q : ℕ → ℚ, Computable q ∧ ∀ n, |((q n : ℝ)) - h| ≤ 1 / (n + 1)

theorem computable_imp_leftRE {h : ℝ} (hcomp : IsComputableReal h) : IsLeftRE h := by
  obtain ⟨q, hq_comp, hq_close⟩ := hcomp
  refine ⟨fun n => q n - (1 : ℚ) / ((n : ℚ) + 1),
    ComputableRat.computable_sub_one_div_succ hq_comp, ?_, ?_⟩
  · intro n
    have habs := hq_close n
    have h1 := (abs_le.mp habs).2
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    push_cast
    linarith
  · have h_bias : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have hbase := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
      refine hbase.congr (fun n => ?_)
      simp [Function.comp]
    have h_q : Filter.Tendsto (fun n : ℕ => (q n : ℝ)) Filter.atTop (nhds h) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h_bias) ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hb := hN n hn
      have hclose := hq_close n
      rw [Real.dist_eq] at hb ⊢
      have h_bias_eq : (1 : ℝ) / ((n : ℝ) + 1) - 0 = 1 / ((n : ℝ) + 1) := by ring
      rw [h_bias_eq] at hb
      have h_bias_nn : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      have h_bias_abs : |(1 : ℝ) / ((n : ℝ) + 1)| = 1 / ((n : ℝ) + 1) := abs_of_nonneg h_bias_nn
      rw [h_bias_abs] at hb
      calc |((q n : ℝ)) - h| ≤ 1 / ((n : ℝ) + 1) := hclose
        _ < ε := hb
    have hsum : Filter.Tendsto (fun n : ℕ => (q n : ℝ) - 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds (h - 0)) := h_q.sub h_bias
    rw [sub_zero] at hsum
    convert hsum using 1
    ext n
    push_cast
    ring

theorem computable_imp_rightRE {h : ℝ} (hcomp : IsComputableReal h) : IsRightRE h := by
  obtain ⟨q, hq_comp, hq_close⟩ := hcomp
  refine ⟨fun n => q n + (1 : ℚ) / ((n : ℚ) + 1),
    ComputableRat.computable_add_one_div_succ hq_comp, ?_, ?_⟩
  · intro n
    have habs := hq_close n
    have h1 := (abs_le.mp habs).1
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    push_cast
    linarith
  · have h_bias : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have hbase := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
      refine hbase.congr (fun n => ?_)
      simp [Function.comp]
    have h_q : Filter.Tendsto (fun n : ℕ => (q n : ℝ)) Filter.atTop (nhds h) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h_bias) ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hb := hN n hn
      have hclose := hq_close n
      rw [Real.dist_eq] at hb ⊢
      have h_bias_eq : (1 : ℝ) / ((n : ℝ) + 1) - 0 = 1 / ((n : ℝ) + 1) := by ring
      rw [h_bias_eq] at hb
      have h_bias_nn : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      have h_bias_abs : |(1 : ℝ) / ((n : ℝ) + 1)| = 1 / ((n : ℝ) + 1) := abs_of_nonneg h_bias_nn
      rw [h_bias_abs] at hb
      calc |((q n : ℝ)) - h| ≤ 1 / ((n : ℝ) + 1) := hclose
        _ < ε := hb
    have hsum : Filter.Tendsto (fun n : ℕ => (q n : ℝ) + 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds (h + 0)) := h_q.add h_bias
    rw [add_zero] at hsum
    convert hsum using 1
    ext n
    push_cast
    ring

-- @ontology: hm:lean:computable-iff
theorem computable_iff_leftRE_and_rightRE {h : ℝ} :
    IsComputableReal h ↔ IsLeftRE h ∧ IsRightRE h := by
  refine ⟨fun hcomp => ⟨computable_imp_leftRE hcomp, computable_imp_rightRE hcomp⟩, ?_⟩
  rintro ⟨⟨ℓ, hℓ_comp, hℓ_below, hℓ_lim⟩, ⟨r, hr_comp, hr_above, hr_lim⟩⟩
  set P : ℕ → ℕ → Bool :=
    fun n k => decide (r k ≤ ℓ k + (1 : ℚ) / ((n : ℚ) + 1)) with hP_def
  have hP_comp : Computable₂ P := by
    have h_le_pr : Primrec₂ (fun (a b : ℚ) => decide (a ≤ b)) :=
      PrimrecRel.decide ComputableRat.primrec_rat_le
    have h_le : Computable₂ (fun (a b : ℚ) => decide (a ≤ b)) := h_le_pr.to_comp
    have h_add : Computable₂ (fun (q' : ℚ) (n : ℕ) => q' + (1 : ℚ) / ((n : ℚ) + 1)) :=
      ComputableRat.primrec_add_one_div_succ.to_comp
    have h_lk : Computable₂ (fun (_ k : ℕ) => ℓ k) :=
      hℓ_comp.comp Computable.snd
    have h_rk : Computable₂ (fun (_ k : ℕ) => r k) :=
      hr_comp.comp Computable.snd
    have h_n_proj : Computable₂ (fun (n _ : ℕ) => n) := Computable.fst
    have h_lkadd : Computable₂ (fun (n k : ℕ) => ℓ k + (1 : ℚ) / ((n : ℚ) + 1)) :=
      h_add.comp₂ h_lk h_n_proj
    exact h_le.comp₂ h_rk h_lkadd
  have hP_exists : ∀ n : ℕ, ∃ k : ℕ, P n k = true := by
    intro n
    have hr_sub_l : Filter.Tendsto (fun k : ℕ => (r k : ℝ) - (ℓ k : ℝ))
        Filter.atTop (nhds 0) := by
      have hsub := hr_lim.sub hℓ_lim
      simpa using hsub
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [Metric.tendsto_atTop] at hr_sub_l
    obtain ⟨K, hK⟩ := hr_sub_l (1 / ((n : ℝ) + 1)) hpos
    refine ⟨K, ?_⟩
    rw [hP_def]
    apply decide_eq_true
    have hK_val := hK K (le_refl K)
    rw [Real.dist_eq] at hK_val
    have h_diff_nn : (0 : ℝ) ≤ (r K : ℝ) - (ℓ K : ℝ) := by
      linarith [hr_above K, hℓ_below K]
    have hK_val' : (r K : ℝ) - (ℓ K : ℝ) < 1 / ((n : ℝ) + 1) := by
      have heq : (r K : ℝ) - (ℓ K : ℝ) - 0 = (r K : ℝ) - (ℓ K : ℝ) := by ring
      rw [heq] at hK_val
      rw [abs_of_nonneg h_diff_nn] at hK_val
      exact hK_val
    have h_cast : ((ℓ K + (1 : ℚ) / ((n : ℚ) + 1) : ℚ) : ℝ) =
        (ℓ K : ℝ) + 1 / ((n : ℝ) + 1) := by push_cast; ring
    have h_real : (r K : ℝ) ≤ ((ℓ K + (1 : ℚ) / ((n : ℚ) + 1) : ℚ) : ℝ) := by
      rw [h_cast]; linarith
    exact_mod_cast h_real
  let f : ℕ → ℕ := fun n => Nat.find (hP_exists n)
  have hf_comp : Computable f := by
    have h_partrec : Partrec (fun n : ℕ => Nat.rfind (fun k : ℕ => (P n k : Part Bool))) :=
      Partrec.rfind hP_comp.partrec₂
    refine Partrec.of_eq_tot h_partrec ?_
    intro n
    rw [Nat.mem_rfind]
    refine ⟨?_, ?_⟩
    · have hspec : P n (Nat.find (hP_exists n)) = true := Nat.find_spec (hP_exists n)
      exact Part.mem_some_iff.mpr hspec.symm
    · intro m hm
      have hnot : ¬ P n m = true := Nat.find_min (hP_exists n) hm
      have hfalse : P n m = false := by
        cases hcase : P n m
        · rfl
        · exact absurd hcase hnot
      rw [hfalse]
      exact Part.mem_some_iff.mpr rfl
  refine ⟨fun n => ℓ (f n), hℓ_comp.comp hf_comp, fun n => ?_⟩
  have hf_spec : P n (f n) = true := Nat.find_spec (hP_exists n)
  rw [hP_def] at hf_spec
  have hf_rat : r (f n) ≤ ℓ (f n) + (1 : ℚ) / ((n : ℚ) + 1) := of_decide_eq_true hf_spec
  have h_cast : ((ℓ (f n) + (1 : ℚ) / ((n : ℚ) + 1) : ℚ) : ℝ) =
      (ℓ (f n) : ℝ) + 1 / ((n : ℝ) + 1) := by push_cast; ring
  have hf_real : (r (f n) : ℝ) ≤ (ℓ (f n) : ℝ) + 1 / ((n : ℝ) + 1) := by
    have : ((r (f n) : ℚ) : ℝ) ≤ ((ℓ (f n) + (1 : ℚ) / ((n : ℚ) + 1) : ℚ) : ℝ) := by
      exact_mod_cast hf_rat
    rw [h_cast] at this; exact this
  have hℓ_le : (ℓ (f n) : ℝ) ≤ h := hℓ_below (f n)
  have hr_ge : h ≤ (r (f n) : ℝ) := hr_above (f n)
  have hh_le : h ≤ (ℓ (f n) : ℝ) + 1 / ((n : ℝ) + 1) := hr_ge.trans hf_real
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-! ## Primrec helpers: powers of constants -/

/-- `Primrec₂ HPow.hPow : Primrec₂ (· ^ · : ℕ → ℕ → ℕ)`, derived from
`Nat.Primrec.pow` via `Primrec.nat_iff`. -/
theorem primrec_nat_pow : Primrec₂ (fun a b : ℕ => a ^ b) :=
  Primrec.nat_iff.mpr Nat.Primrec.pow

/-- `n ↦ n^d` is Primrec for fixed `d`. -/
theorem primrec_pow_const (d : ℕ) : Primrec (fun n : ℕ => n ^ d) :=
  primrec_nat_pow.comp Primrec.id (Primrec.const d)

/-- `n ↦ m^(n^d)` is Primrec for fixed `m`, `d`. -/
theorem primrec_const_pow_pow (m d : ℕ) : Primrec (fun n : ℕ => m ^ (n ^ d)) :=
  primrec_nat_pow.comp (Primrec.const m) (primrec_pow_const d)

/-! ## Base-`m` digit extraction -/

/-- The `i`-th digit of `k` in base `m`: `(k / m^i) % m`. -/
def digit (m k i : ℕ) : ℕ := (k / m ^ i) % m

/-- For fixed `m`, `(k, i) ↦ digit m k i` is Primrec₂. -/
theorem primrec_digit (m : ℕ) : Primrec₂ (fun k i : ℕ => digit m k i) := by
  unfold digit
  have h_pow : Primrec (fun p : ℕ × ℕ => m ^ p.2) :=
    primrec_nat_pow.comp (Primrec.const m) Primrec.snd
  have h_div : Primrec (fun p : ℕ × ℕ => p.1 / m ^ p.2) :=
    Primrec.nat_div.comp Primrec.fst h_pow
  exact Primrec.nat_mod.comp h_div (Primrec.const m)

theorem digit_lt {m : ℕ} (hm : 0 < m) (k i : ℕ) : digit m k i < m :=
  Nat.mod_lt _ hm

/-- Digit-extraction: `digit m (a * m^i + r) i = a` when `a < m` and `r < m^i`. -/
theorem digit_extract {m : ℕ} (hm : 0 < m) {a r i : ℕ} (ha : a < m) (hr : r < m ^ i) :
    digit m (a * m ^ i + r) i = a := by
  unfold digit
  have h_pow_pos : 0 < m ^ i := Nat.pow_pos hm
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ h_pow_pos,
      Nat.div_eq_of_lt hr, zero_add]
  exact Nat.mod_eq_of_lt ha

theorem digit_succ (m k i : ℕ) : digit m k (i + 1) = digit m (k / m) i := by
  unfold digit
  congr 1
  rw [pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

@[simp]
theorem digit_zero (m k : ℕ) : digit m k 0 = k % m := by
  unfold digit; simp

/-- Sum-of-digits decomposition: for `k < m^len`,
`Σ_{i < len} digit m k i * m^i = k`. The base-m positional formula. -/
theorem sum_digits_pow_eq {m : ℕ} (hm : 0 < m) :
    ∀ (len k : ℕ), k < m ^ len →
    (Finset.range len).sum (fun i => digit m k i * m ^ i) = k := by
  intro len
  induction len with
  | zero =>
    intro k hk
    rw [pow_zero, Nat.lt_one_iff] at hk
    subst hk
    simp
  | succ len ih =>
    intro k hk
    rw [Finset.sum_range_succ']
    have h_term : ∀ i, digit m k (i + 1) * m ^ (i + 1) = m * (digit m (k / m) i * m ^ i) := by
      intro i
      rw [digit_succ, pow_succ]
      ring
    rw [Finset.sum_congr rfl (fun i _ => h_term i), ← Finset.mul_sum]
    have h_kdiv : k / m < m ^ len := by
      rw [Nat.div_lt_iff_lt_mul hm]
      rwa [pow_succ] at hk
    rw [ih (k / m) h_kdiv, digit_zero, pow_zero, Nat.mul_one]
    exact Nat.div_add_mod k m

theorem sum_pow_lt {m : ℕ} (hm : 0 < m) :
    ∀ (len : ℕ) {f : ℕ → ℕ}, (∀ i < len, f i < m) →
    (Finset.range len).sum (fun i => f i * m ^ i) < m ^ len := by
  intro len
  induction len with
  | zero => intro f _; simp
  | succ len ih =>
    intro f hf
    rw [Finset.sum_range_succ, pow_succ]
    have h_pow_pos : 0 < m ^ len := Nat.pow_pos hm
    have h_rest : (Finset.range len).sum (fun i => f i * m ^ i) < m ^ len :=
      ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have h_last_lt : f len < m := hf len (Nat.lt_succ_self _)
    have key : (Finset.range len).sum (fun i => f i * m ^ i) + f len * m ^ len
                < (1 + f len) * m ^ len := by
      have : (1 + f len) * m ^ len = m ^ len + f len * m ^ len := by ring
      rw [this]
      exact Nat.add_lt_add_right h_rest _
    calc (Finset.range len).sum (fun i => f i * m ^ i) + f len * m ^ len
        < (1 + f len) * m ^ len := key
      _ ≤ m * m ^ len := Nat.mul_le_mul_right _ (by omega)
      _ = m ^ len * m := by ring

/-! ## Decoding into a list of digits -/

/-- Decode `k` as a list of `len` digits in base `m`. -/
def decodeList (m k len : ℕ) : List ℕ :=
  (List.range len).map (digit m k)

@[simp]
theorem decodeList_length (m k len : ℕ) : (decodeList m k len).length = len := by
  simp [decodeList]

theorem decodeList_get {m k len i : ℕ} (h : i < len) :
    (decodeList m k len).get ⟨i, by simp [h]⟩ = digit m k i := by
  simp [decodeList]

theorem decodeList_lt {m : ℕ} (hm : 0 < m) (k len i : ℕ) (h : i < len) :
    (decodeList m k len).get ⟨i, by simp [h]⟩ < m := by
  rw [decodeList_get h]
  exact digit_lt hm _ _

/-- For fixed `m`, `(k, len) ↦ decodeList m k len` is Primrec₂. -/
theorem primrec_decodeList (m : ℕ) : Primrec₂ (fun k len : ℕ => decodeList m k len) := by
  unfold decodeList
  have h_range : Primrec (fun p : ℕ × ℕ => List.range p.2) :=
    Primrec.list_range.comp Primrec.snd
  have h_digit : Primrec (fun pq : (ℕ × ℕ) × ℕ => digit m pq.1.1 pq.2) :=
    (primrec_digit m).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map h_range h_digit

/-! ## Encoding patterns as natural numbers -/

/-- `(Fin (n^d) → α) ≃ Fin ((Fintype.card α)^(n^d))` — the uniform-shape encoding
of patterns as natural numbers. -/
def fnFinEquiv (α : Type*) [Fintype α] [DecidableEq α] [Encodable α] (n d : ℕ) :
    (Fin (n^d) → α) ≃ Fin ((Fintype.card α)^(n^d)) :=
  (Equiv.arrowCongr (Equiv.refl _) Encodable.fintypeEquivFin).trans finFunctionFinEquiv

/-- Full chain: `Pattern α (box d n) ≃ Fin ((Fintype.card α)^(n^d))`. -/
def patternFinEquiv (α : Type*) [Fintype α] [DecidableEq α] [Encodable α] (d n : ℕ) :
    Pattern α (box d n) ≃ Fin ((Fintype.card α)^(n^d)) :=
  (patternFnEquiv α d n).trans (fnFinEquiv α n d)

theorem patternFinEquiv_symm_apply {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    {d n : ℕ} (k : Fin ((Fintype.card α)^(n^d))) (w : ↥(box d n)) :
    (patternFinEquiv α d n).symm k w =
    Encodable.fintypeEquivFin.symm
      ((finFunctionFinEquiv.symm k) ((boxIxEquiv d n) w)) := by
  rfl

theorem patternFinEquiv_symm_val_eq_digit {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    {d n : ℕ} (k : Fin ((Fintype.card α) ^ (n ^ d))) (w : ↥(box d n)) :
    (Encodable.fintypeEquivFin ((patternFinEquiv α d n).symm k w)).val =
    digit (Fintype.card α) k.val (boxIndexInv d n w.val) := by
  rw [patternFinEquiv_symm_apply]
  rw [Encodable.fintypeEquivFin.apply_symm_apply]
  rw [finFunctionFinEquiv_symm_apply_val]
  rw [boxIxEquiv_val]
  rfl

/-- `N_bar` as a count over `Fin (m^(n^d))` — the most direct uniform-encoding form. -/
theorem N_bar_eq_fintype_card_fin {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α] [Encodable α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) :
    N_bar F L n =
      Fintype.card { k : Fin ((Fintype.card α)^(n^d)) //
        locallyAdmissible F L ((patternFinEquiv α d n).symm k) } := by
  rw [N_bar_eq_fintype_card_subtype]
  refine Fintype.card_congr (Equiv.subtypeEquiv (patternFinEquiv α d n) ?_)
  intro p
  rw [Equiv.symm_apply_apply]

/-- The decode predicate on ℕ: `k < (card α)^(n^d)` and the corresponding pattern
is locally admissible. -/
def admPredNat {α : Type*} [Fintype α] [DecidableEq α] [Encodable α] {d : ℕ}
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n k : ℕ) : Prop :=
  ∃ h : k < (Fintype.card α)^(n^d),
    locallyAdmissible F L ((patternFinEquiv α d n).symm ⟨k, h⟩)

instance decidable_admPredNat {α : Type*} [Fintype α] [DecidableEq α] [Encodable α] {d : ℕ}
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n k : ℕ) :
    Decidable (admPredNat F L n k) := by
  unfold admPredNat
  exact inferInstance

theorem admPredNat_lt {α : Type*} [Fintype α] [DecidableEq α] [Encodable α] {d : ℕ}
    {F : Finset (Lat d)} {L : Finset (Pattern α F)} {n k : ℕ}
    (h : admPredNat F L n k) : k < (Fintype.card α)^(n^d) :=
  h.choose

/-- Digit-level admissibility predicate on ℕ, expressed without `patternFinEquiv`.
Has a clear path to `Primrec₂`: a `∧` of a primrec bound with a universal-existential
quantifier over fixed Finsets, with the inner check being a comparison of digits
and constants. -/
def admPredDigit {α : Type*} [Fintype α] [DecidableEq α] [Encodable α] {d : ℕ}
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n k : ℕ) : Prop :=
  k < (Fintype.card α) ^ (n ^ d) ∧
  ∀ u ∈ relevantOffsets F (box d n), ∃ ℓ ∈ L, ∀ v : F,
    digit (Fintype.card α) k (boxIndexInv d n (v.val + u)) =
      (Encodable.fintypeEquivFin (ℓ v)).val

instance decidable_admPredDigit {α : Type*} [Fintype α] [DecidableEq α] [Encodable α] {d : ℕ}
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n k : ℕ) :
    Decidable (admPredDigit F L n k) := by
  unfold admPredDigit
  exact inferInstance

theorem admPredNat_iff_admPredDigit {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    {d : ℕ} (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n k : ℕ) :
    admPredNat F L n k ↔ admPredDigit F L n k := by
  constructor
  · rintro ⟨hk, hloc⟩
    refine ⟨hk, ?_⟩
    rw [locallyAdmissible_iff_relevantOffsets] at hloc
    intro u hu
    have h_v : ∀ v : F, v.val + u ∈ box d n := by
      intro v
      simp only [relevantOffsets] at hu
      by_cases hF : F = ∅
      · exact absurd v.property (Finset.eq_empty_iff_forall_notMem.mp hF v.val)
      · rw [if_neg hF] at hu
        exact (Finset.mem_filter.mp hu).2 v.val v.property
    let ℓ : Pattern α F :=
      fun v => (patternFinEquiv α d n).symm ⟨k, hk⟩ ⟨v.val + u, h_v v⟩
    refine ⟨ℓ, hloc u hu h_v, ?_⟩
    intro v
    have := patternFinEquiv_symm_val_eq_digit (α := α) (d := d) (n := n)
      ⟨k, hk⟩ ⟨v.val + u, h_v v⟩
    simpa [ℓ] using this.symm
  · rintro ⟨hk, hdigit⟩
    refine ⟨hk, ?_⟩
    rw [locallyAdmissible_iff_relevantOffsets]
    intro u hu h_v
    obtain ⟨ℓ, hℓ_mem, hdig⟩ := hdigit u hu
    have hpat_eq : (fun v : F =>
        (patternFinEquiv α d n).symm ⟨k, hk⟩ ⟨v.val + u, h_v v⟩) = ℓ := by
      funext v
      have hbridge := patternFinEquiv_symm_val_eq_digit (α := α) (d := d) (n := n)
        ⟨k, hk⟩ ⟨v.val + u, h_v v⟩
      have heq_val :
          (Encodable.fintypeEquivFin
              ((patternFinEquiv α d n).symm ⟨k, hk⟩ ⟨v.val + u, h_v v⟩)).val =
          (Encodable.fintypeEquivFin (ℓ v)).val := by
        rw [hbridge]; exact hdig v
      have heq_fin :
          Encodable.fintypeEquivFin
              ((patternFinEquiv α d n).symm ⟨k, hk⟩ ⟨v.val + u, h_v v⟩) =
          Encodable.fintypeEquivFin (ℓ v) := Fin.ext heq_val
      exact Encodable.fintypeEquivFin.injective heq_fin
    rw [hpat_eq]; exact hℓ_mem

/-- `N_bar` as `Nat.count admPredNat`: the count of admissible pattern-encodings
in `[0, (card α)^(n^d))`. -/
theorem N_bar_eq_count {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    {d : ℕ} (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) :
    N_bar F L n = Nat.count (admPredNat F L n) ((Fintype.card α)^(n^d)) := by
  rw [N_bar_eq_fintype_card_fin, Nat.count_eq_card_filter_range]
  set bound := (Fintype.card α)^(n^d) with hbound
  let P : Fin bound → Prop := fun k => locallyAdmissible F L ((patternFinEquiv α d n).symm k)
  have hSubCard : Fintype.card { k : Fin bound // P k } =
      ((Finset.univ : Finset (Fin bound)).filter P).card :=
    Fintype.subtype_card _ (fun _ => by simp [Finset.mem_filter])
  rw [hSubCard]
  rw [← Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  ext k
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, Finset.mem_range, true_and]
  constructor
  · rintro ⟨k', hP, rfl⟩
    exact ⟨k'.is_lt, k'.is_lt, hP⟩
  · rintro ⟨hk_lt, hpred⟩
    exact ⟨⟨k, hk_lt⟩, hpred.choose_spec, rfl⟩

/-- N_bar via the digit-level predicate. -/
theorem N_bar_eq_count_digit {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    {d : ℕ} (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) :
    N_bar F L n = Nat.count (admPredDigit F L n) ((Fintype.card α)^(n^d)) := by
  rw [N_bar_eq_count]
  congr 1
  funext k
  exact propext (admPredNat_iff_admPredDigit F L n k)

/-! ## Bool-valued admissibility on encoded form (legacy / alternative shape) -/

/-- Admissibility check at the encoded level: given `(n, k)` with `m = Fintype.card α`,
the natural number `k` corresponds (via base-`m` digits + `Encodable.decode`) to a
function `Fin (n^d) → α`, hence to a pattern on `box d n`. -/
def admissibleEncoded {α : Type*} [Fintype α] [DecidableEq α] [Encodable α] {d : ℕ}
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n k : ℕ) : Prop :=
  ∀ u ∈ relevantOffsets F (box d n),
    ∃ ℓ ∈ L, ∀ v : F,
      digit (Fintype.card α) k (boxIndexInv d n (v.val + u)) = Encodable.encode (ℓ v)

instance decidable_admissibleEncoded {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    {d : ℕ} (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n k : ℕ) :
    Decidable (admissibleEncoded F L n k) := by
  unfold admissibleEncoded
  exact inferInstance

/-- `N_bar F L n` equals the cardinality of admissible functions `Fin (n^d) → α`
(under the transferred predicate via `patternFnEquiv`). -/
theorem N_bar_eq_fin_arrow_card {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) :
    N_bar F L n =
      Fintype.card { f : Fin (n^d) → α //
        locallyAdmissible F L ((patternFnEquiv α d n).symm f) } := by
  rw [N_bar_eq_fintype_card_subtype]
  refine Fintype.card_congr (Equiv.subtypeEquiv (patternFnEquiv α d n) ?_)
  intro p
  rw [Equiv.symm_apply_apply]
