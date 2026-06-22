import dependencies.ComputableRat
import dependencies.Computable
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.IntervalCases

/-! # Computable rational bracket of `log (f n) / (n+1)^d`

This module proves `rationalApprox_log_div_pow_of_computable` (formerly an
axiom in `axioms/Computability.lean`): for any `Computable f : ℕ → ℕ`, the
real `Real.log (f n) / (n+1)^d` admits simultaneous computable rational upper
and lower approximations whose gap tends to `0`.

The construction is a `Computable` rational `K`-term partial sum `logApprox m K`
of the Mercator series for `log m`, with `K = m²(n+1)` chosen so the truncation
error (bounded via `Real.abs_log_sub_add_sum_range_le` and an exp/Bernoulli tail)
is `≤ 1/(n+1)`. Numerator/denominator are computed entirely in `ℕ`/`ℤ`; the only
`ℚ` primitive used is division of an integer by a natural (`computable_divInt`).

Depends only on the standard Mathlib axioms (`propext`, `Classical.choice`,
`Quot.sound`). -/

namespace RatLogApprox
open ComputableRat

/-- Encoded form of `(a : ℚ) / (b : ℚ)` for `a : ℤ` (given by its encoding `ea`)
and `b : ℕ`, in the structured `Primcodable ℚ` encoding. -/
def divIntEnc (ea b : ℕ) : ℕ :=
  if b = 0 then Nat.pair 0 1
  else
    let aAbs := (ea + 1) / 2
    let g := Nat.gcd aAbs b
    Nat.pair (if ea % 2 = 0 then 2 * (aAbs / g) else 2 * (aAbs / g - 1) + 1) (b / g)

theorem primrec_divIntEnc : Primrec₂ divIntEnc := by
  unfold divIntEnc
  have hb0 : PrimrecPred (fun p : ℕ × ℕ => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have haAbs : Primrec (fun p : ℕ × ℕ => (p.1 + 1) / 2) :=
    Primrec.nat_div.comp (Primrec.succ.comp Primrec.fst) (Primrec.const 2)
  have hg : Primrec (fun p : ℕ × ℕ => Nat.gcd ((p.1 + 1) / 2) p.2) :=
    primrec_nat_gcd.comp haAbs Primrec.snd
  have heaEven : PrimrecPred (fun p : ℕ × ℕ => p.1 % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 0)
  have hquot : Primrec (fun p : ℕ × ℕ => (p.1 + 1) / 2 / Nat.gcd ((p.1 + 1) / 2) p.2) :=
    Primrec.nat_div.comp haAbs hg
  have hnumEnc : Primrec (fun p : ℕ × ℕ =>
      if p.1 % 2 = 0 then 2 * ((p.1 + 1) / 2 / Nat.gcd ((p.1 + 1) / 2) p.2)
      else 2 * ((p.1 + 1) / 2 / Nat.gcd ((p.1 + 1) / 2) p.2 - 1) + 1) :=
    Primrec.ite heaEven
      (Primrec.nat_mul.comp (Primrec.const 2) hquot)
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_sub.comp hquot (Primrec.const 1)))
        (Primrec.const 1))
  have hden : Primrec (fun p : ℕ × ℕ => p.2 / Nat.gcd ((p.1 + 1) / 2) p.2) :=
    Primrec.nat_div.comp Primrec.snd hg
  exact Primrec.ite hb0 (Primrec.const (Nat.pair 0 1))
    (Primrec₂.natPair.comp hnumEnc hden)

/-- (Re-proved from `ComputableRat`'s private version.) Encoding of `z / (g:ℤ)` for
exact division. -/
theorem encode_int_div_exact (z : ℤ) (g : ℕ) (hg_pos : 0 < g) (hg_dvd : g ∣ z.natAbs) :
    Encodable.encode (z / (g : ℤ)) =
      if Encodable.encode z % 2 = 0 then 2 * (z.natAbs / g) else 2 * (z.natAbs / g - 1) + 1 := by
  cases z with
  | ofNat k =>
    rw [show (Encodable.encode (Int.ofNat k) : ℕ) = 2 * k from rfl,
        if_pos (Nat.mul_mod_right 2 k)]
    rfl
  | negSucc k =>
    rw [show (Encodable.encode (Int.negSucc k) : ℕ) = 2 * k + 1 from rfl,
        if_neg (by omega : (2 * k + 1) % 2 ≠ 0)]
    have hnat : Int.natAbs (Int.negSucc k) = k + 1 := rfl
    rw [hnat] at hg_dvd
    have hge : g ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) hg_dvd
    have hquot_pos : 0 < (k + 1) / g := Nat.div_pos hge hg_pos
    have h_div : (Int.negSucc k : ℤ) / (g : ℤ) = Int.negSucc ((k + 1) / g - 1) := by
      have h1 : (Int.negSucc k : ℤ) = -((↑k + 1 : ℤ)) := by rw [Int.negSucc_eq]
      rw [h1, Int.neg_ediv]
      have hdvd_int : ((g : ℤ)) ∣ (↑k + 1 : ℤ) := by exact_mod_cast hg_dvd
      rw [if_pos hdvd_int]
      simp only [sub_zero]
      rw [show ((↑k + 1 : ℤ) / (g : ℤ)) = (((k + 1) / g : ℕ) : ℤ) from rfl]
      rw [Int.negSucc_eq, Nat.cast_sub hquot_pos]
      push_cast; ring
    rw [h_div]
    rfl

/-- The encoding equation: `divIntEnc` computes the encoding of `(a:ℚ)/(b:ℚ)`. -/
theorem divInt_encode_eq (a : ℤ) (b : ℕ) :
    Encodable.encode ((a : ℚ) / (b : ℚ)) = divIntEnc (Encodable.encode a) b := by
  by_cases hb : b = 0
  · subst hb
    simp only [Nat.cast_zero, div_zero, divIntEnc, if_pos rfl]
    rfl
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    have hbz : (b : ℤ) ≠ 0 := by exact_mod_cast hb
    have hg_pos : 0 < Nat.gcd b a.natAbs := Nat.gcd_pos_of_pos_left _ hbpos
    have hg_dvd : Nat.gcd b a.natAbs ∣ a.natAbs := Nat.gcd_dvd_right b a.natAbs
    have hq : (a : ℚ) / (b : ℚ) = Rat.divInt a (b : ℤ) := by
      rw [Rat.divInt_eq_div]; push_cast; ring
    have hgcd : (b : ℤ).gcd a = Nat.gcd b a.natAbs := by
      rw [Int.gcd, Int.natAbs_natCast]
    have hsign : (b : ℤ).sign = 1 := Int.sign_eq_one_of_pos (by exact_mod_cast hbpos)
    rw [hq, rat_encode_eq, Rat.num_divInt, Rat.den_divInt, if_neg hbz, hsign, one_mul,
        hgcd, Int.natAbs_natCast, encode_int_div_exact a _ hg_pos hg_dvd]
    simp only [divIntEnc, if_neg hb, ← natAbs_eq_encode_div a, Nat.gcd_comm a.natAbs b]

/-- `(a:ℚ)/(b:ℚ)` is `Computable` in `(a : ℤ, b : ℕ)`. -/
theorem computable_divInt : Computable₂ (fun (a : ℤ) (b : ℕ) => (a : ℚ) / (b : ℚ)) := by
  have h : Primrec (fun p : ℤ × ℕ => (p.1 : ℚ) / (p.2 : ℚ)) := by
    refine Primrec.encode_iff.mp ?_
    refine Primrec.of_eq ?_ (fun p => (divInt_encode_eq p.1 p.2).symm)
    exact primrec_divIntEnc.comp (Primrec.encode.comp Primrec.fst) Primrec.snd
  exact h.to_comp

/-! ## Step 2: the ℕ-valued log series and its computable rational value -/

theorem primrec_factorial : Primrec Nat.factorial := by
  refine Primrec.of_eq (Primrec.nat_rec₁ (1 : ℕ)
    (show Primrec₂ (fun k ih : ℕ => (k + 1) * ih) from
      Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)) (fun n => ?_)
  induction n with
  | zero => rfl
  | succ k ih =>
    show (k + 1) * Nat.rec 1 (fun k ih => (k + 1) * ih) k = Nat.factorial (k + 1)
    rw [ih, Nat.factorial_succ]

theorem primrec_int_ofNat : Primrec (fun n : ℕ => (n : ℤ)) := by
  refine Primrec.encode_iff.mp ?_
  exact Primrec.of_eq (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (fun n => rfl)

/-- The `i`-th series term `(m-1)^(i+1) * m^(K-1-i) * (K!/(i+1))`. -/
def seriesTerm (m K i : ℕ) : ℕ := (m - 1) ^ (i + 1) * m ^ (K - 1 - i) * (Nat.factorial K / (i + 1))

theorem primrec_seriesTerm : Primrec (fun q : (ℕ × ℕ) × ℕ => seriesTerm q.1.1 q.1.2 q.2) := by
  unfold seriesTerm
  have hm : Primrec (fun q : (ℕ × ℕ) × ℕ => q.1.1) := Primrec.fst.comp Primrec.fst
  have hK : Primrec (fun q : (ℕ × ℕ) × ℕ => q.1.2) := Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun q : (ℕ × ℕ) × ℕ => q.2) := Primrec.snd
  have h1 := primrec_nat_pow.comp (Primrec.nat_sub.comp hm (Primrec.const 1)) (Primrec.succ.comp hi)
  have h2 := primrec_nat_pow.comp hm
    (Primrec.nat_sub.comp (Primrec.nat_sub.comp hK (Primrec.const 1)) hi)
  have h3 := Primrec.nat_div.comp (primrec_factorial.comp hK) (Primrec.succ.comp hi)
  exact Primrec.nat_mul.comp (Primrec.nat_mul.comp h1 h2) h3

/-- Numerator of the `K`-term series for `log m`, over the common denominator `m^K * K!`. -/
def seriesNum (m K : ℕ) : ℕ := Nat.rec 0 (fun i acc => acc + seriesTerm m K i) K

/-- Common denominator `m^K * K!`. -/
def seriesDen (m K : ℕ) : ℕ := m ^ K * Nat.factorial K

theorem primrec_seriesNum : Primrec₂ seriesNum := by
  unfold seriesNum
  refine Primrec.nat_rec'
    (f := fun p : ℕ × ℕ => p.2)
    (g := fun _ : ℕ × ℕ => (0 : ℕ))
    (h := fun (p : ℕ × ℕ) (q : ℕ × ℕ) => q.2 + seriesTerm p.1 p.2 q.1)
    Primrec.snd (Primrec.const (0 : ℕ)) ?_
  exact Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
    (primrec_seriesTerm.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))

theorem primrec_seriesDen : Primrec₂ seriesDen := by
  unfold seriesDen
  exact Primrec.nat_mul.comp primrec_nat_pow (primrec_factorial.comp Primrec.snd)

/-- The computable rational `K`-term approximation of `log m`. -/
def logApprox (m K : ℕ) : ℚ := ((seriesNum m K : ℤ) : ℚ) / ((seriesDen m K : ℕ) : ℚ)

attribute [irreducible] seriesNum seriesDen divIntEnc

theorem primrec_divInt : Primrec (fun p : ℤ × ℕ => (p.1 : ℚ) / (p.2 : ℚ)) := by
  refine Primrec.encode_iff.mp ?_
  refine Primrec.of_eq ?_ (fun p => (divInt_encode_eq p.1 p.2).symm)
  exact primrec_divIntEnc.comp (Primrec.encode.comp Primrec.fst) Primrec.snd

set_option maxHeartbeats 1000000 in
theorem primrec_logApprox : Primrec₂ logApprox := by
  unfold logApprox
  exact primrec_divInt.comp
    ((primrec_int_ofNat.comp primrec_seriesNum).pair primrec_seriesDen)

theorem computable_logApprox : Computable₂ logApprox := primrec_logApprox.to_comp

/-! ## Step 3a: the integer fraction equals the real partial sum -/

theorem natRec_add_eq_sum (t : ℕ → ℕ) (n : ℕ) :
    Nat.rec 0 (fun i acc => acc + t i) n = ∑ i ∈ Finset.range n, t i := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ← ih]

theorem seriesNum_eq_sum (m K : ℕ) :
    seriesNum m K = ∑ i ∈ Finset.range K, seriesTerm m K i := by
  unfold seriesNum
  exact natRec_add_eq_sum (seriesTerm m K) K

set_option maxHeartbeats 800000 in
theorem logApprox_eq_sum (m K : ℕ) (hm : 1 ≤ m) :
    (logApprox m K : ℝ)
      = ∑ i ∈ Finset.range K, ((m : ℝ) - 1) ^ (i + 1) / ((m : ℝ) ^ (i + 1) * ((i : ℝ) + 1)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  unfold logApprox
  rw [Rat.cast_div]
  rw [show ((((seriesNum m K : ℤ)) : ℚ) : ℝ) = (seriesNum m K : ℝ) by push_cast; ring,
      show (((seriesDen m K : ℕ) : ℚ) : ℝ) = (seriesDen m K : ℝ) by push_cast; ring,
      seriesNum_eq_sum, seriesDen]
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  unfold seriesTerm
  have hdvd : (i + 1) ∣ Nat.factorial K := Nat.dvd_factorial (Nat.succ_pos i) hi
  have hKfac : (0 : ℝ) < (Nat.factorial K : ℝ) := by exact_mod_cast Nat.factorial_pos K
  have hexp : K - 1 - i + (i + 1) = K := by omega
  have hmpow : (m : ℝ) ^ (K - 1 - i) * (m : ℝ) ^ (i + 1) = (m : ℝ) ^ K := by
    rw [← pow_add, hexp]
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hKf : (Nat.factorial K : ℝ) ≠ 0 := ne_of_gt hKfac
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_sub hm, Nat.cast_div_charZero hdvd, Nat.cast_one,
      Nat.cast_mul, Nat.cast_pow, ← hmpow, Nat.cast_add, Nat.cast_one]
  field_simp

/-! ## Step 3b: the approximation error bound -/

theorem logApprox_sub_log_le (m K : ℕ) (hm : 2 ≤ m) :
    |(logApprox m K : ℝ) - Real.log m| ≤ ((m : ℝ) - 1) ^ (K + 1) / (m : ℝ) ^ K := by
  have hmpos : 0 < m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  set x : ℝ := ((m : ℝ) - 1) / m with hx
  have hxnn : 0 ≤ x := by rw [hx]; apply div_nonneg (by linarith) (le_of_lt hm0)
  have hx1 : x < 1 := by rw [hx, div_lt_one hm0]; linarith
  have hxabs : |x| < 1 := abs_lt.mpr ⟨by linarith, hx1⟩
  have h1x : (1 : ℝ) - x = 1 / m := by rw [hx]; field_simp; ring
  have hlog : Real.log (1 - x) = - Real.log m := by
    rw [h1x, Real.log_div one_ne_zero (ne_of_gt hm0), Real.log_one, zero_sub]
  have hsum : (logApprox m K : ℝ) = ∑ i ∈ Finset.range K, x ^ (i + 1) / ((i : ℝ) + 1) := by
    rw [logApprox_eq_sum m K (by omega)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hx, div_pow, div_div]
  have key : |(∑ i ∈ Finset.range K, x ^ (i + 1) / ((i : ℝ) + 1)) - Real.log m|
      ≤ |x| ^ (K + 1) / (1 - |x|) := by
    have hb := Real.abs_log_sub_add_sum_range_le hxabs K
    rw [hlog, ← sub_eq_add_neg] at hb
    exact hb
  rw [hsum]
  refine le_trans key (le_of_eq ?_)
  rw [abs_of_nonneg hxnn, h1x, hx, div_pow]
  field_simp
  ring

/-! ## Step 4: explicit tail estimate -/

theorem powDiv_le (m K : ℕ) (hm : 2 ≤ m) (hK : 1 ≤ K) :
    ((m : ℝ) - 1) ^ (K + 1) / (m : ℝ) ^ K ≤ (m : ℝ) ^ 2 / (K : ℝ) := by
  have hmpos : 0 < m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set x : ℝ := ((m : ℝ) - 1) / m with hx
  have hxnn : 0 ≤ x := by rw [hx]; exact div_nonneg (by linarith) (le_of_lt hm0)
  have hxe : x ≤ Real.exp (-(1 / (m : ℝ))) := by
    have h := Real.add_one_le_exp (-(1 / (m : ℝ)))
    have hxeq : x = -(1 / (m : ℝ)) + 1 := by rw [hx]; field_simp; ring
    rw [hxeq]; exact h
  have hxK : x ^ K ≤ Real.exp (-((K : ℝ) / (m : ℝ))) := by
    calc x ^ K ≤ (Real.exp (-(1 / (m : ℝ)))) ^ K := pow_le_pow_left₀ hxnn hxe K
      _ = Real.exp (-((K : ℝ) / (m : ℝ))) := by
            rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hKm : (0 : ℝ) < (K : ℝ) / (m : ℝ) := by positivity
  have hexpK : Real.exp (-((K : ℝ) / (m : ℝ))) ≤ (m : ℝ) / K := by
    rw [Real.exp_neg, ← one_div]
    have h1 : (K : ℝ) / (m : ℝ) ≤ Real.exp ((K : ℝ) / (m : ℝ)) := by
      have := Real.add_one_le_exp ((K : ℝ) / (m : ℝ)); linarith
    calc 1 / Real.exp ((K : ℝ) / (m : ℝ)) ≤ 1 / ((K : ℝ) / (m : ℝ)) :=
            one_div_le_one_div_of_le hKm h1
      _ = (m : ℝ) / K := by rw [one_div_div]
  have hLHS : ((m : ℝ) - 1) ^ (K + 1) / (m : ℝ) ^ K = ((m : ℝ) - 1) * x ^ K := by
    rw [hx, div_pow]; field_simp; ring
  rw [hLHS]
  calc ((m : ℝ) - 1) * x ^ K ≤ (m : ℝ) * x ^ K :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hxnn K)
    _ ≤ (m : ℝ) * ((m : ℝ) / K) := mul_le_mul_of_nonneg_left (le_trans hxK hexpK) (le_of_lt hm0)
    _ = (m : ℝ) ^ 2 / K := by ring

/-! ## Step 4b: combined error bound for `K = m²(n+1)` -/

theorem logApprox_one (K : ℕ) : logApprox 1 K = 0 := by
  unfold logApprox
  have h : seriesNum 1 K = 0 := by
    rw [seriesNum_eq_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    unfold seriesTerm
    simp
  rw [h]; simp

theorem logApprox_zero : logApprox 0 0 = 0 := by
  unfold logApprox
  have h : seriesNum 0 0 = 0 := by rw [seriesNum_eq_sum]; simp
  rw [h]; simp

theorem logApprox_err (m n : ℕ) :
    |(logApprox m (m ^ 2 * (n + 1)) : ℝ) - Real.log m| ≤ 1 / ((n : ℝ) + 1) := by
  rcases lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [show (0 : ℕ) ^ 2 * (n + 1) = 0 by simp, logApprox_zero]
      simp only [Rat.cast_zero, Nat.cast_zero, Real.log_zero, sub_zero, abs_zero]
      positivity
    · rw [show (1 : ℕ) ^ 2 * (n + 1) = n + 1 by ring, logApprox_one]
      simp only [Rat.cast_zero, Nat.cast_one, Real.log_one, sub_zero, abs_zero]
      positivity
  · have hK : 1 ≤ m ^ 2 * (n + 1) := by
      have h0 : 0 < m := by omega
      have hpos : 0 < m ^ 2 * (n + 1) := by positivity
      omega
    refine le_trans (logApprox_sub_log_le m (m ^ 2 * (n + 1)) hm) ?_
    refine le_trans (powDiv_le m (m ^ 2 * (n + 1)) hm hK) (le_of_eq ?_)
    have hm2 : ((m : ℝ)) ^ 2 ≠ 0 := by
      have : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      positivity
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp

/-! ## Step 5: assembly -/

/-- `q / (k : ℚ)` as a named function (so computability composition does not
mis-decompose the `/` as raw `HDiv` during higher-order unification). -/
def ratDivNat (q : ℚ) (k : ℕ) : ℚ := q / (k : ℚ)

theorem computable_ratDivNat : Computable₂ ratDivNat := by
  have heq : ∀ (q : ℚ) (k : ℕ), ratDivNat q k = ((q.num : ℤ) : ℚ) / ((q.den * k : ℕ) : ℚ) := by
    intro q k; rw [ratDivNat, Nat.cast_mul, ← div_div, Rat.num_div_den]
  have hP : Primrec (fun p : ℚ × ℕ => ((p.1.num : ℤ) : ℚ) / ((p.1.den * p.2 : ℕ) : ℚ)) :=
    primrec_divInt.comp ((primrec_rat_num.comp Primrec.fst).pair
      (Primrec.nat_mul.comp (primrec_rat_den.comp Primrec.fst) Primrec.snd))
  exact (hP.of_eq (fun p => (heq p.1 p.2).symm)).to_comp

attribute [irreducible] logApprox

set_option maxHeartbeats 400000 in
/-- ★ DISCHARGE: simultaneous computable rational bracket of
`Real.log (f n) / (n+1)^d` with vanishing width, for any computable `f : ℕ → ℕ`.
This is exactly the statement of the axiom `rationalApprox_log_div_pow_of_computable`. -/
theorem rationalApprox_log_div_pow_of_computable {d : ℕ} {f : ℕ → ℕ} (hf : Computable f) :
    ∃ qU qL : ℕ → ℚ, Computable qU ∧ Computable qL ∧
      (∀ n : ℕ,
        (qL n : ℝ) ≤ Real.log (f n) / ((n + 1 : ℕ) : ℝ) ^ d ∧
        Real.log (f n) / ((n + 1 : ℕ) : ℝ) ^ d ≤ (qU n : ℝ)) ∧
      Filter.Tendsto (fun n : ℕ => (qU n : ℝ) - (qL n : ℝ)) Filter.atTop (nhds 0) := by
  have hK : Computable (fun n => f n ^ 2 * (n + 1)) :=
    Computable₂.comp (Primrec.nat_mul.to_comp)
      (((primrec_pow_const 2).to_comp).comp hf) (Primrec.succ.to_comp)
  have hA : Computable (fun n => logApprox (f n) (f n ^ 2 * (n + 1))) :=
    Computable₂.comp computable_logApprox hf hK
  have hAU := ComputableRat.computable_add_one_div_succ hA
  have hAL := ComputableRat.computable_sub_one_div_succ hA
  have hpd : Computable (fun n => (n + 1) ^ d) := ((primrec_pow_const d).comp Primrec.succ).to_comp
  set qU : ℕ → ℚ := fun n =>
    ratDivNat (logApprox (f n) (f n ^ 2 * (n + 1)) + (1 : ℚ) / ((n : ℚ) + 1)) ((n + 1) ^ d)
    with hqU_def
  set qL : ℕ → ℚ := fun n =>
    ratDivNat (logApprox (f n) (f n ^ 2 * (n + 1)) - (1 : ℚ) / ((n : ℚ) + 1)) ((n + 1) ^ d)
    with hqL_def
  have hqUc : Computable qU := Computable₂.comp computable_ratDivNat hAU hpd
  have hqLc : Computable qL := Computable₂.comp computable_ratDivNat hAL hpd
  have hUR : ∀ n, (qU n : ℝ)
      = ((logApprox (f n) (f n ^ 2 * (n + 1)) : ℝ) + 1 / ((n : ℝ) + 1)) / ((n + 1 : ℕ) : ℝ) ^ d := by
    intro n; simp only [hqU_def, ratDivNat]; push_cast; ring
  have hLR : ∀ n, (qL n : ℝ)
      = ((logApprox (f n) (f n ^ 2 * (n + 1)) : ℝ) - 1 / ((n : ℝ) + 1)) / ((n + 1 : ℕ) : ℝ) ^ d := by
    intro n; simp only [hqL_def, ratDivNat]; push_cast; ring
  refine ⟨qU, qL, hqUc, hqLc, ?_, ?_⟩
  · intro n
    have herr := logApprox_err (f n) n
    have hD : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ d := by positivity
    obtain ⟨h1, h2⟩ := abs_le.mp herr
    refine ⟨?_, ?_⟩
    · rw [hLR n]; gcongr; linarith
    · rw [hUR n]; gcongr; linarith
  · have hbias : Filter.Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
        have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
          (Filter.tendsto_add_atTop_nat 1)
        refine h.congr (fun n => ?_); simp [Function.comp]
      have h2 := h0.const_mul 2
      simpa using h2
    have hwidth : ∀ n, (qU n : ℝ) - (qL n : ℝ)
        = (2 / ((n : ℝ) + 1)) / ((n + 1 : ℕ) : ℝ) ^ d := by
      intro n; rw [hUR n, hLR n, div_sub_div_same]; congr 1; ring
    rw [show (fun n : ℕ => (qU n : ℝ) - (qL n : ℝ))
          = (fun n : ℕ => (2 / ((n : ℝ) + 1)) / ((n + 1 : ℕ) : ℝ) ^ d) from funext hwidth]
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hbias
    have hd1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ d := by
      apply one_le_pow₀
      have : (1 : ℕ) ≤ n + 1 := by omega
      exact_mod_cast this
    exact div_le_self (by positivity) hd1

end RatLogApprox


/-- **Discharged** (formerly the axiom `rationalApprox_log_div_pow_of_computable`).
For any `Computable f : ℕ → ℕ`, simultaneous computable rational bracket of
`Real.log (f n) / ((n+1) : ℝ)^d` whose width tends to zero. -/
theorem rationalApprox_log_div_pow_of_computable {d : ℕ} {f : ℕ → ℕ} (hf : Computable f) :
    ∃ qU qL : ℕ → ℚ, Computable qU ∧ Computable qL ∧
      (∀ n : ℕ,
        (qL n : ℝ) ≤ Real.log (f n) / ((n + 1 : ℕ) : ℝ) ^ d ∧
        Real.log (f n) / ((n + 1 : ℕ) : ℝ) ^ d ≤ (qU n : ℝ)) ∧
      Filter.Tendsto
        (fun n : ℕ => (qU n : ℝ) - (qL n : ℝ))
        Filter.atTop (nhds 0) :=
  RatLogApprox.rationalApprox_log_div_pow_of_computable hf
