import Mathlib.Computability.Partrec
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Ring.Int

/-! # Computability infrastructure for `ℚ`

This file establishes a `Primcodable ℚ` instance whose underlying encoding is the
*structured* `(num, den)` form

  `encode q = Nat.pair (Encodable.encode q.num) q.den`,

and uses it to derive computability of basic rational operations needed for the
Hochman–Meyerovitch formalization (F-section of the implementation list).

Mathlib already provides `Primcodable ℚ` indirectly via `Rat.instDenumerable`
(through `Denumerable.ofEncodableOfInfinite`), but that instance re-indexes the
encoding to be a bijection `ℕ ↔ ℚ`, which is *not* the structured form above.
We override it here at higher priority so that downstream computability proofs
can use the simple `Nat.pair (encode num) den` shape directly.

The bridge requires three primitive-recursive prerequisites that Mathlib does
not ship: `Int.natAbs`, `Nat.gcd`, and the predicate `0 < d ∧ n.natAbs.Coprime d`
on `ℤ × ℕ`. Each is established below.
-/

namespace ComputableRat

/-! ## `Int.natAbs` is `Primrec` -/

/-- `Int.natAbs` factors through the standard ℤ encoding: encoding sends
`Int.ofNat k ↦ 2k` and `Int.negSucc k ↦ 2k+1`, so `n.natAbs = (encode n + 1) / 2`. -/
theorem natAbs_eq_encode_div (n : ℤ) :
    n.natAbs = (Encodable.encode n + 1) / 2 := by
  cases n with
  | ofNat k => change k = (2 * k + 1) / 2; omega
  | negSucc k => change (k + 1) = (2 * k + 1 + 1) / 2; omega

theorem primrec_natAbs : Primrec Int.natAbs := by
  refine Primrec.of_eq ?_ (fun n => (natAbs_eq_encode_div n).symm)
  exact Primrec.nat_div.comp
    (Primrec.succ.comp (Primrec.encode (α := ℤ))) (Primrec.const 2)

/-! ## `Nat.gcd` is `Primrec` (via `Nat.findGreatest`) -/

/-- The combined divisibility predicate `d ∣ p.1 ∧ d ∣ p.2` on `(ℕ × ℕ) × ℕ`
is `PrimrecRel`. Used to unlock `Nat.findGreatest` for `Nat.gcd`. -/
theorem primrec_dvd_pair :
    PrimrecRel (fun (p : ℕ × ℕ) (d : ℕ) => d ∣ p.1 ∧ d ∣ p.2) := by
  refine PrimrecPred.of_eq
    (p := fun (q : (ℕ × ℕ) × ℕ) => q.1.1 % q.2 = 0 ∧ q.1.2 % q.2 = 0) ?_ ?_
  · exact PrimrecPred.and
      (Primrec.eq.comp
        (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.const (0 : ℕ)))
      (Primrec.eq.comp
        (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
        (Primrec.const (0 : ℕ)))
  · intro q
    change (q.1.1 % q.2 = 0 ∧ q.1.2 % q.2 = 0) ↔ (q.2 ∣ q.1.1 ∧ q.2 ∣ q.1.2)
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]

/-- `Nat.gcd a b` equals the greatest `d ≤ max a b` dividing both `a` and `b`. -/
theorem nat_gcd_eq_findGreatest (a b : ℕ) :
    Nat.gcd a b = Nat.findGreatest (fun d => d ∣ a ∧ d ∣ b) (max a b) := by
  refine (Nat.findGreatest_eq_iff.mpr ?_).symm
  refine ⟨?_, ?_, ?_⟩
  · by_cases ha : a = 0
    · subst ha; simp [Nat.gcd_zero_left]
    · exact le_trans (Nat.gcd_le_left _ (Nat.pos_of_ne_zero ha)) (le_max_left _ _)
  · intro _; exact ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩
  · intro k hk hkmax ⟨hk_dvd_a, hk_dvd_b⟩
    have hk_dvd_gcd : k ∣ Nat.gcd a b := Nat.dvd_gcd hk_dvd_a hk_dvd_b
    by_cases h : Nat.gcd a b = 0
    · rw [Nat.gcd_eq_zero_iff] at h
      obtain ⟨ha, hb⟩ := h
      subst ha; subst hb; simp at hkmax; omega
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h) hk_dvd_gcd)
        (Nat.not_le_of_lt hk)

theorem primrec_nat_gcd : Primrec₂ Nat.gcd := by
  have hbound : Primrec (fun p : ℕ × ℕ => max p.1 p.2) :=
    Primrec.nat_max.comp Primrec.fst Primrec.snd
  have hfg : Primrec (fun p : ℕ × ℕ =>
      Nat.findGreatest (fun d => d ∣ p.1 ∧ d ∣ p.2) (max p.1 p.2)) :=
    Primrec.nat_findGreatest hbound primrec_dvd_pair
  refine Primrec₂.mk (Primrec.of_eq hfg ?_)
  intro p; exact (nat_gcd_eq_findGreatest p.1 p.2).symm

/-! ## The (num, den)-validity predicate is `PrimrecPred` -/

/-- The predicate `0 < d ∧ n.natAbs.Coprime d` on `ℤ × ℕ`, which characterizes
canonical (numerator, denominator) pairs for rationals. -/
theorem primrec_rat_pred :
    PrimrecPred (fun (p : ℤ × ℕ) => 0 < p.2 ∧ p.1.natAbs.Coprime p.2) := by
  refine PrimrecPred.and ?_ ?_
  · refine PrimrecPred.of_eq (p := fun (p : ℤ × ℕ) => 0 < p.2) ?_ (fun _ => Iff.rfl)
    exact Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd
  · refine PrimrecPred.of_eq
      (p := fun (p : ℤ × ℕ) => Nat.gcd p.1.natAbs p.2 = 1) ?_ (fun _ => Iff.rfl)
    have h_natAbs : Primrec (fun p : ℤ × ℕ => p.1.natAbs) :=
      primrec_natAbs.comp Primrec.fst
    have h_gcd : Primrec (fun p : ℤ × ℕ => Nat.gcd p.1.natAbs p.2) :=
      primrec_nat_gcd.comp h_natAbs Primrec.snd
    exact Primrec.eq.comp h_gcd (Primrec.const 1)

/-! ## `Primcodable ℚ` via the structured `(num, den)` encoding -/

/-- Bijection between `ℚ` and the subtype of `(num, den) : ℤ × ℕ` pairs with
`0 < den` and `gcd |num| den = 1`. -/
def ratSubtypeEquiv : ℚ ≃ {p : ℤ × ℕ // 0 < p.2 ∧ p.1.natAbs.Coprime p.2} where
  toFun q := ⟨(q.num, q.den), q.pos, q.reduced⟩
  invFun := fun ⟨(n, d), hd_pos, hcop⟩ => Rat.mk' n d hd_pos.ne' hcop
  left_inv q := by cases q; rfl
  right_inv := by rintro ⟨⟨n, d⟩, hd_pos, hcop⟩; rfl

instance primcodableRatSubtype :
    Primcodable {p : ℤ × ℕ // 0 < p.2 ∧ p.1.natAbs.Coprime p.2} :=
  Primcodable.subtype primrec_rat_pred

/-- High-priority `Primcodable ℚ` whose encoding is the structured
`Nat.pair (encode q.num) q.den` form. Overrides the default
`Primcodable.ofDenumerable ℚ` so that downstream computability proofs can use
the structured encoding identities. -/
instance (priority := 1100) primcodableRat : Primcodable ℚ :=
  Primcodable.ofEquiv _ ratSubtypeEquiv

/-! ## Encoding identities under the structured `Primcodable ℚ` -/

theorem rat_encode_eq (q : ℚ) :
    Encodable.encode q = Nat.pair (Encodable.encode q.num) q.den := rfl

theorem one_div_succ_num (n : ℕ) : ((1 : ℚ) / ((n : ℚ) + 1)).num = 1 := by
  rw [one_div, ← Nat.cast_succ]
  exact Rat.inv_natCast_num_of_pos (Nat.succ_pos _)

theorem one_div_succ_den (n : ℕ) : ((1 : ℚ) / ((n : ℚ) + 1)).den = n + 1 := by
  rw [one_div, ← Nat.cast_succ]
  exact Rat.inv_natCast_den_of_pos (Nat.succ_pos _)

theorem encode_one_div_succ (n : ℕ) :
    Encodable.encode ((1 : ℚ) / ((n : ℚ) + 1)) = Nat.pair 2 (n + 1) := by
  rw [rat_encode_eq, one_div_succ_num, one_div_succ_den]
  rfl

/-! ## Identity, constants, and basic compositions -/

theorem computable_id : Computable (id : ℚ → ℚ) := Computable.id

theorem computable_const (q : ℚ) : Computable (fun _ : ℕ => q) := Computable.const q

theorem computable_comp_nat {q : ℕ → ℚ} (hq : Computable q) {g : ℕ → ℕ}
    (hg : Primrec g) : Computable (fun n => q (g n)) :=
  hq.comp hg.to_comp

/-! ## `Primrec` / `Computable` for `n ↦ 1/(↑n + 1)` -/

theorem primrec_one_div_succ : Primrec (fun n : ℕ => (1 : ℚ) / ((n : ℚ) + 1)) := by
  apply Primrec.encode_iff.mp
  refine Primrec.of_eq ?_ (fun n => (encode_one_div_succ n).symm)
  exact Primrec₂.natPair.comp (Primrec.const 2) Primrec.succ

theorem computable_one_div_succ : Computable (fun n : ℕ => (1 : ℚ) / ((n : ℚ) + 1)) :=
  primrec_one_div_succ.to_comp

/-! ## Encoded helper for `q + 1/(n+1)`

We need `Computable (fun n => q n + 1/(↑n + 1))` for any computable
`q : ℕ → ℚ`. Mathlib does not ship `Primrec` rational addition (it would
require `Primrec` Int operations that are also missing), so we construct a
single-purpose encoded helper `addOneOverSuccEnc` that mimics the operation
at the level of structured `Primcodable ℚ` encodings, prove it is `Primrec`,
and bridge to the actual rational sum via the encoding identity.
-/

/-- Encoded form of `q + 1/(n+1)` computed directly from the structured
encoding `encQ` of `q` and the natural number `n`. -/
def addOneOverSuccEnc (encQ n : ℕ) : ℕ :=
  let encNum := encQ.unpair.fst
  let den := encQ.unpair.snd
  let np1 := n + 1
  let mulEnc := if encNum % 2 = 0 then encNum * np1 else (encNum + 1) * np1 - 1
  let rawNumEnc :=
    if mulEnc % 2 = 0 then mulEnc + 2 * den
    else if 2 * den > mulEnc then 2 * den - mulEnc - 1
    else mulEnc - 2 * den
  let rawNumAbs := (rawNumEnc + 1) / 2
  let rawDen := den * np1
  let g := Nat.gcd rawDen rawNumAbs
  let newNumEnc :=
    if rawNumEnc % 2 = 0 then 2 * (rawNumAbs / g)
    else 2 * (rawNumAbs / g - 1) + 1
  Nat.pair newNumEnc (rawDen / g)

theorem primrec_addOneOverSuccEnc : Primrec₂ addOneOverSuccEnc := by
  have hencNum : Primrec (fun p : ℕ × ℕ => p.1.unpair.fst) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hden : Primrec (fun p : ℕ × ℕ => p.1.unpair.snd) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hnp1 : Primrec (fun p : ℕ × ℕ => p.2 + 1) :=
    Primrec.succ.comp Primrec.snd
  have hencNum_even : PrimrecPred (fun p : ℕ × ℕ => p.1.unpair.fst % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hencNum (Primrec.const 2)) (Primrec.const 0)
  have hmulEnc : Primrec (fun p : ℕ × ℕ =>
      if p.1.unpair.fst % 2 = 0 then p.1.unpair.fst * (p.2 + 1)
      else (p.1.unpair.fst + 1) * (p.2 + 1) - 1) :=
    Primrec.ite hencNum_even
      (Primrec.nat_mul.comp hencNum hnp1)
      (Primrec.nat_sub.comp
        (Primrec.nat_mul.comp (Primrec.succ.comp hencNum) hnp1)
        (Primrec.const 1))
  have hmulEnc_even : PrimrecPred (fun p : ℕ × ℕ =>
      (if p.1.unpair.fst % 2 = 0 then p.1.unpair.fst * (p.2 + 1)
       else (p.1.unpair.fst + 1) * (p.2 + 1) - 1) % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hmulEnc (Primrec.const 2)) (Primrec.const 0)
  have h2den : Primrec (fun p : ℕ × ℕ => 2 * p.1.unpair.snd) :=
    Primrec.nat_mul.comp (Primrec.const 2) hden
  have h2den_gt : PrimrecPred (fun p : ℕ × ℕ =>
      2 * p.1.unpair.snd >
        if p.1.unpair.fst % 2 = 0 then p.1.unpair.fst * (p.2 + 1)
        else (p.1.unpair.fst + 1) * (p.2 + 1) - 1) :=
    Primrec.nat_lt.comp hmulEnc h2den
  have hrawNumEnc : Primrec (fun p : ℕ × ℕ =>
      let mulEnc := if p.1.unpair.fst % 2 = 0 then p.1.unpair.fst * (p.2 + 1)
                    else (p.1.unpair.fst + 1) * (p.2 + 1) - 1
      if mulEnc % 2 = 0 then mulEnc + 2 * p.1.unpair.snd
      else if 2 * p.1.unpair.snd > mulEnc then 2 * p.1.unpair.snd - mulEnc - 1
      else mulEnc - 2 * p.1.unpair.snd) :=
    Primrec.ite hmulEnc_even
      (Primrec.nat_add.comp hmulEnc h2den)
      (Primrec.ite h2den_gt
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp h2den hmulEnc) (Primrec.const 1))
        (Primrec.nat_sub.comp hmulEnc h2den))
  have hrawNumAbs : Primrec (fun p : ℕ × ℕ =>
      let mulEnc := if p.1.unpair.fst % 2 = 0 then p.1.unpair.fst * (p.2 + 1)
                    else (p.1.unpair.fst + 1) * (p.2 + 1) - 1
      let rawNumEnc := if mulEnc % 2 = 0 then mulEnc + 2 * p.1.unpair.snd
                       else if 2 * p.1.unpair.snd > mulEnc then 2 * p.1.unpair.snd - mulEnc - 1
                       else mulEnc - 2 * p.1.unpair.snd
      (rawNumEnc + 1) / 2) :=
    Primrec.nat_div.comp (Primrec.succ.comp hrawNumEnc) (Primrec.const 2)
  have hrawDen : Primrec (fun p : ℕ × ℕ => p.1.unpair.snd * (p.2 + 1)) :=
    Primrec.nat_mul.comp hden hnp1
  have hg : Primrec (fun p : ℕ × ℕ =>
      Nat.gcd (p.1.unpair.snd * (p.2 + 1))
        (let mulEnc := if p.1.unpair.fst % 2 = 0 then p.1.unpair.fst * (p.2 + 1)
                       else (p.1.unpair.fst + 1) * (p.2 + 1) - 1
         let rawNumEnc := if mulEnc % 2 = 0 then mulEnc + 2 * p.1.unpair.snd
                          else if 2 * p.1.unpair.snd > mulEnc then 2 * p.1.unpair.snd - mulEnc - 1
                          else mulEnc - 2 * p.1.unpair.snd
         (rawNumEnc + 1) / 2)) :=
    primrec_nat_gcd.comp hrawDen hrawNumAbs
  have hrawNumEnc_even : PrimrecPred (fun p : ℕ × ℕ =>
      (let mulEnc := if p.1.unpair.fst % 2 = 0 then p.1.unpair.fst * (p.2 + 1)
                     else (p.1.unpair.fst + 1) * (p.2 + 1) - 1
       if mulEnc % 2 = 0 then mulEnc + 2 * p.1.unpair.snd
       else if 2 * p.1.unpair.snd > mulEnc then 2 * p.1.unpair.snd - mulEnc - 1
       else mulEnc - 2 * p.1.unpair.snd) % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hrawNumEnc (Primrec.const 2)) (Primrec.const 0)
  have habsDivG : Primrec (fun p : ℕ × ℕ =>
      (let mulEnc := if p.1.unpair.fst % 2 = 0 then p.1.unpair.fst * (p.2 + 1)
                     else (p.1.unpair.fst + 1) * (p.2 + 1) - 1
       let rawNumEnc := if mulEnc % 2 = 0 then mulEnc + 2 * p.1.unpair.snd
                        else if 2 * p.1.unpair.snd > mulEnc then 2 * p.1.unpair.snd - mulEnc - 1
                        else mulEnc - 2 * p.1.unpair.snd
       (rawNumEnc + 1) / 2) /
      (Nat.gcd (p.1.unpair.snd * (p.2 + 1))
        (let mulEnc := if p.1.unpair.fst % 2 = 0 then p.1.unpair.fst * (p.2 + 1)
                       else (p.1.unpair.fst + 1) * (p.2 + 1) - 1
         let rawNumEnc := if mulEnc % 2 = 0 then mulEnc + 2 * p.1.unpair.snd
                          else if 2 * p.1.unpair.snd > mulEnc then 2 * p.1.unpair.snd - mulEnc - 1
                          else mulEnc - 2 * p.1.unpair.snd
         (rawNumEnc + 1) / 2))) :=
    Primrec.nat_div.comp hrawNumAbs hg
  have hnewNumEnc : Primrec (fun p : ℕ × ℕ =>
      let mulEnc := if p.1.unpair.fst % 2 = 0 then p.1.unpair.fst * (p.2 + 1)
                    else (p.1.unpair.fst + 1) * (p.2 + 1) - 1
      let rawNumEnc := if mulEnc % 2 = 0 then mulEnc + 2 * p.1.unpair.snd
                       else if 2 * p.1.unpair.snd > mulEnc then 2 * p.1.unpair.snd - mulEnc - 1
                       else mulEnc - 2 * p.1.unpair.snd
      let rawNumAbs := (rawNumEnc + 1) / 2
      let rawDen := p.1.unpair.snd * (p.2 + 1)
      let g := Nat.gcd rawDen rawNumAbs
      if rawNumEnc % 2 = 0 then 2 * (rawNumAbs / g)
      else 2 * (rawNumAbs / g - 1) + 1) :=
    Primrec.ite hrawNumEnc_even
      (Primrec.nat_mul.comp (Primrec.const 2) habsDivG)
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_sub.comp habsDivG (Primrec.const 1)))
        (Primrec.const 1))
  have hdenDivG : Primrec (fun p : ℕ × ℕ =>
      (p.1.unpair.snd * (p.2 + 1)) /
      Nat.gcd (p.1.unpair.snd * (p.2 + 1))
        (let mulEnc := if p.1.unpair.fst % 2 = 0 then p.1.unpair.fst * (p.2 + 1)
                       else (p.1.unpair.fst + 1) * (p.2 + 1) - 1
         let rawNumEnc := if mulEnc % 2 = 0 then mulEnc + 2 * p.1.unpair.snd
                          else if 2 * p.1.unpair.snd > mulEnc then 2 * p.1.unpair.snd - mulEnc - 1
                          else mulEnc - 2 * p.1.unpair.snd
         (rawNumEnc + 1) / 2)) :=
    Primrec.nat_div.comp hrawDen hg
  exact Primrec₂.natPair.comp hnewNumEnc hdenDivG

/-! ## Encoding identities for `z * (n+1)` and `x + (D : ℤ)` -/

/-- Encoding of `z * (↑(n+1)) : ℤ` in the structured form. -/
private theorem encode_int_mul_succ (z : ℤ) (n : ℕ) :
    Encodable.encode (z * ((n + 1 : ℕ) : ℤ)) =
      if Encodable.encode z % 2 = 0 then Encodable.encode z * (n + 1)
      else (Encodable.encode z + 1) * (n + 1) - 1 := by
  cases z with
  | ofNat k =>
    rw [show (Encodable.encode (Int.ofNat k) : ℕ) = 2 * k from rfl,
        if_pos (Nat.mul_mod_right 2 k)]
    have h1 : (Int.ofNat k : ℤ) * ((n + 1 : ℕ) : ℤ) = Int.ofNat (k * (n + 1)) := by simp
    rw [h1]
    change 2 * (k * (n + 1)) = 2 * k * (n + 1)
    ring
  | negSucc k =>
    rw [show (Encodable.encode (Int.negSucc k) : ℕ) = 2 * k + 1 from rfl,
        if_neg (by omega : (2 * k + 1) % 2 ≠ 0)]
    have hpos : 0 < (k + 1) * (n + 1) := Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos n)
    have h1 : (Int.negSucc k : ℤ) * ((n + 1 : ℕ) : ℤ) = Int.negSucc ((k + 1) * (n + 1) - 1) := by
      rw [Int.negSucc_eq, Int.negSucc_eq, Nat.cast_sub hpos]
      push_cast; ring
    rw [h1]
    change 2 * ((k + 1) * (n + 1) - 1) + 1 = (2 * k + 1 + 1) * (n + 1) - 1
    have h_expand : (2 * k + 1 + 1) * (n + 1) = 2 * ((k + 1) * (n + 1)) := by ring
    rw [h_expand]
    omega

/-- Encoding of `x + (D : ℤ)` in the structured form (case-split on parity of `encode x`). -/
private theorem encode_int_add_nat (x : ℤ) (D : ℕ) :
    Encodable.encode (x + (D : ℤ)) =
      (if Encodable.encode x % 2 = 0 then Encodable.encode x + 2 * D
       else if 2 * D > Encodable.encode x then 2 * D - Encodable.encode x - 1
       else Encodable.encode x - 2 * D) := by
  cases x with
  | ofNat a =>
    rw [show (Encodable.encode (Int.ofNat a) : ℕ) = 2 * a from rfl,
        if_pos (Nat.mul_mod_right 2 a)]
    have h1 : (Int.ofNat a : ℤ) + (D : ℤ) = Int.ofNat (a + D) := by simp
    rw [h1]
    change 2 * (a + D) = 2 * a + 2 * D
    ring
  | negSucc a =>
    rw [show (Encodable.encode (Int.negSucc a) : ℕ) = 2 * a + 1 from rfl,
        if_neg (by omega : (2 * a + 1) % 2 ≠ 0)]
    by_cases hcase : 2 * D > 2 * a + 1
    · rw [if_pos hcase]
      have hge : a + 1 ≤ D := by omega
      have h1 : (Int.negSucc a : ℤ) + (D : ℤ) = ((D - (a + 1) : ℕ) : ℤ) := by
        rw [Int.negSucc_eq, Nat.cast_sub hge]
        push_cast; ring
      rw [h1]
      change 2 * (D - (a + 1)) = 2 * D - (2 * a + 1) - 1
      omega
    · rw [if_neg hcase]
      push_neg at hcase
      have hle : D ≤ a := by omega
      have h1 : (Int.negSucc a : ℤ) + (D : ℤ) = (Int.negSucc (a - D) : ℤ) := by
        rw [Int.negSucc_eq, Int.negSucc_eq, Nat.cast_sub hle]
        ring
      rw [h1]
      change 2 * (a - D) + 1 = 2 * a + 1 - 2 * D
      omega

/-! ## The "raw numerator" stage matches `q.num * (n+1) + q.den` -/

private theorem rawNumEnc_eq (q : ℚ) (n : ℕ) :
    (let mulEnc := if Encodable.encode q.num % 2 = 0
                    then Encodable.encode q.num * (n + 1)
                    else (Encodable.encode q.num + 1) * (n + 1) - 1
     if mulEnc % 2 = 0 then mulEnc + 2 * q.den
     else if 2 * q.den > mulEnc then 2 * q.den - mulEnc - 1
     else mulEnc - 2 * q.den) =
    Encodable.encode (q.num * ((n + 1 : ℕ) : ℤ) + (q.den : ℤ)) := by
  rw [encode_int_add_nat, encode_int_mul_succ]

/-! ## Encoding identity for `z / (g : ℤ)` when `g ∣ z.natAbs` and `g > 0` -/

private theorem encode_int_div_exact (z : ℤ) (g : ℕ) (hg_pos : 0 < g)
    (hg_dvd : g ∣ z.natAbs) :
    Encodable.encode (z / (g : ℤ)) =
      if Encodable.encode z % 2 = 0 then 2 * (z.natAbs / g)
      else 2 * (z.natAbs / g - 1) + 1 := by
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

/-! ## Full semantic equation: `addOneOverSuccEnc` matches `encode (q + 1/(n+1))` -/

theorem encode_addOneOverSucc (q : ℚ) (n : ℕ) :
    Encodable.encode (q + (1 : ℚ) / ((n : ℚ) + 1)) =
    addOneOverSuccEnc (Encodable.encode q) n := by
  have hsum : q + (1 : ℚ) / ((n : ℚ) + 1) =
      mkRat (q.num * ((n + 1 : ℕ) : ℤ) + (q.den : ℤ)) (q.den * (n + 1)) := by
    rw [Rat.add_def', one_div_succ_num, one_div_succ_den, one_mul]
  rw [hsum]
  set A : ℤ := q.num * ((n + 1 : ℕ) : ℤ) + (q.den : ℤ) with hA_def
  set B : ℕ := q.den * (n + 1) with hB_def
  have hB_ne : B ≠ 0 := Nat.mul_ne_zero q.pos.ne' (Nat.succ_ne_zero _)
  have hB_pos : 0 < B := Nat.pos_of_ne_zero hB_ne
  set g : ℕ := Nat.gcd B A.natAbs with hg_def
  have hg_dvd : g ∣ A.natAbs := Nat.gcd_dvd_right B A.natAbs
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ hB_pos
  -- LHS reduction
  rw [rat_encode_eq, Rat.num_mkRat, Rat.den_mkRat]
  simp only [hB_ne, if_false, ← hg_def]
  -- RHS unfolding
  unfold addOneOverSuccEnc
  -- Replace (encode q).unpair.fst and .snd with their values.
  rw [rat_encode_eq]
  simp only [Nat.unpair_pair]
  -- Replace the inner mulEnc/rawNumEnc block with `encode A`.
  rw [show (let mulEnc := if Encodable.encode q.num % 2 = 0
                          then Encodable.encode q.num * (n + 1)
                          else (Encodable.encode q.num + 1) * (n + 1) - 1
            if mulEnc % 2 = 0 then mulEnc + 2 * q.den
            else if 2 * q.den > mulEnc then 2 * q.den - mulEnc - 1
            else mulEnc - 2 * q.den) = Encodable.encode A from
    rawNumEnc_eq q n]
  -- After rewrite: rawNumAbs = (encode A + 1) / 2 = A.natAbs.
  rw [show ((Encodable.encode A) + 1) / 2 = A.natAbs from (natAbs_eq_encode_div A).symm]
  -- Now g (in helper) = Nat.gcd (q.den * (n+1)) A.natAbs = Nat.gcd B A.natAbs.
  -- And outer if-block reduces to encode (A / g) by encode_int_div_exact.
  rw [show q.den * (n + 1) = B from rfl]
  rw [← hg_def]
  rw [show (if Encodable.encode A % 2 = 0 then 2 * (A.natAbs / g)
            else 2 * (A.natAbs / g - 1) + 1) = Encodable.encode (A / (g : ℤ)) from
    (encode_int_div_exact A g hg_pos hg_dvd).symm]

/-! ## Primrec / Computable for `(q, n) ↦ q + 1/(n+1)` -/

theorem primrec_add_one_div_succ :
    Primrec₂ (fun (q : ℚ) (n : ℕ) => q + (1 : ℚ) / ((n : ℚ) + 1)) := by
  refine Primrec.encode_iff.mp ?_
  refine Primrec.of_eq ?_ (fun p => (encode_addOneOverSucc p.1 p.2).symm)
  exact Primrec₂.comp primrec_addOneOverSuccEnc
    (Primrec.encode.comp Primrec.fst) Primrec.snd

theorem computable_add_one_div_succ {q : ℕ → ℚ} (hq : Computable q) :
    Computable (fun n : ℕ => q n + (1 : ℚ) / ((n : ℚ) + 1)) :=
  (Computable₂.comp (f := fun (q' : ℚ) (n' : ℕ) => q' + (1 : ℚ) / ((n' : ℚ) + 1))
    primrec_add_one_div_succ.to_comp hq Computable.id : _)

/-! ## Computable / Primrec for `Neg.neg : ℚ → ℚ` -/

/-- Sign-flip on the structured encoding: maps `2k` to `2k - 1` (with `0 ↦ 0`)
and `2k + 1` to `2k + 2`, then re-pairs with the unchanged denominator. -/
def negEnc (encQ : ℕ) : ℕ :=
  let encNum := encQ.unpair.fst
  let den := encQ.unpair.snd
  let newNumEnc := if encNum % 2 = 0 then encNum - 1 else encNum + 1
  Nat.pair newNumEnc den

theorem primrec_negEnc : Primrec negEnc := by
  have hencNum : Primrec (fun e : ℕ => e.unpair.fst) :=
    Primrec.fst.comp Primrec.unpair
  have hden : Primrec (fun e : ℕ => e.unpair.snd) :=
    Primrec.snd.comp Primrec.unpair
  have hpar : PrimrecPred (fun e : ℕ => e.unpair.fst % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hencNum (Primrec.const 2)) (Primrec.const 0)
  have hnewNum : Primrec (fun e : ℕ =>
      if e.unpair.fst % 2 = 0 then e.unpair.fst - 1 else e.unpair.fst + 1) :=
    Primrec.ite hpar
      (Primrec.nat_sub.comp hencNum (Primrec.const 1))
      (Primrec.succ.comp hencNum)
  exact Primrec₂.natPair.comp hnewNum hden

theorem encode_neg (q : ℚ) : Encodable.encode (-q) = negEnc (Encodable.encode q) := by
  rw [rat_encode_eq, rat_encode_eq]
  unfold negEnc
  simp only [Nat.unpair_pair]
  congr 1
  · -- encode (-q.num) = if encode q.num % 2 = 0 then encode q.num - 1 else encode q.num + 1
    cases hnum : q.num with
    | ofNat k =>
      rw [show (-q).num = -q.num from rfl, hnum]
      cases k with
      | zero =>
        show (Encodable.encode (0 : ℤ) : ℕ) =
          if (Encodable.encode (Int.ofNat 0) : ℕ) % 2 = 0
          then (Encodable.encode (Int.ofNat 0) : ℕ) - 1
          else (Encodable.encode (Int.ofNat 0) : ℕ) + 1
        rfl
      | succ m =>
        rw [show (-(Int.ofNat (m + 1)) : ℤ) = Int.negSucc m from rfl]
        rw [show (Encodable.encode (Int.negSucc m) : ℕ) = 2 * m + 1 from rfl,
            show (Encodable.encode (Int.ofNat (m + 1)) : ℕ) = 2 * (m + 1) from rfl]
        rw [if_pos (by omega : (2 * (m + 1)) % 2 = 0)]
        omega
    | negSucc k =>
      rw [show (-q).num = -q.num from rfl, hnum]
      rw [show (-Int.negSucc k : ℤ) = Int.ofNat (k + 1) from rfl]
      rw [show (Encodable.encode (Int.ofNat (k + 1)) : ℕ) = 2 * (k + 1) from rfl,
          show (Encodable.encode (Int.negSucc k) : ℕ) = 2 * k + 1 from rfl]
      rw [if_neg (by omega : (2 * k + 1) % 2 ≠ 0)]
      omega

theorem primrec_rat_neg : Primrec (fun q : ℚ => -q) := by
  refine Primrec.encode_iff.mp ?_
  refine Primrec.of_eq ?_ (fun q => (encode_neg q).symm)
  exact primrec_negEnc.comp Primrec.encode

theorem computable_rat_neg : Computable (fun q : ℚ => -q) := primrec_rat_neg.to_comp

theorem computable_neg_comp {q : ℕ → ℚ} (hq : Computable q) : Computable (fun n => -(q n)) :=
  computable_rat_neg.comp hq

theorem computable_sub_one_div_succ {q : ℕ → ℚ} (hq : Computable q) :
    Computable (fun n : ℕ => q n - (1 : ℚ) / ((n : ℚ) + 1)) := by
  have h1 : Computable (fun n : ℕ => -(q n) + (1 : ℚ) / ((n : ℚ) + 1)) :=
    computable_add_one_div_succ (computable_neg_comp hq)
  have h2 : Computable (fun n : ℕ => -(-(q n) + (1 : ℚ) / ((n : ℚ) + 1))) :=
    computable_rat_neg.comp h1
  refine h2.of_eq (fun n => ?_)
  ring

/-! ## Primrec / PrimrecRel for `(· ≤ ·) : ℚ → ℚ → Prop`

Bypasses the lack of Primrec ℤ multiplication by deciding the comparison
directly on the structured `Nat.pair (encode num) den` encoding via
case-analysis on the parities of the encoded numerators (sign bits). -/

/-- Decide `a ≤ b` for rationals `a`, `b` directly on their structured encodings
`encA`, `encB`. Implemented via case-split on numerator signs. -/
def ratLeEnc (encA encB : ℕ) : Bool :=
  let A_e := encA.unpair.fst
  let A_d := encA.unpair.snd
  let B_e := encB.unpair.fst
  let B_d := encB.unpair.snd
  let a_abs := (A_e + 1) / 2
  let b_abs := (B_e + 1) / 2
  if A_e % 2 = 0 then
    if B_e % 2 = 0 then decide (a_abs * B_d ≤ b_abs * A_d)
    else false
  else
    if B_e % 2 = 0 then true
    else decide (b_abs * A_d ≤ a_abs * B_d)

theorem primrec_ratLeEnc : Primrec₂ ratLeEnc := by
  have hAE : Primrec (fun p : ℕ × ℕ => p.1.unpair.fst) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hAD : Primrec (fun p : ℕ × ℕ => p.1.unpair.snd) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hBE : Primrec (fun p : ℕ × ℕ => p.2.unpair.fst) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hBD : Primrec (fun p : ℕ × ℕ => p.2.unpair.snd) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have h_aabs : Primrec (fun p : ℕ × ℕ => (p.1.unpair.fst + 1) / 2) :=
    Primrec.nat_div.comp (Primrec.succ.comp hAE) (Primrec.const 2)
  have h_babs : Primrec (fun p : ℕ × ℕ => (p.2.unpair.fst + 1) / 2) :=
    Primrec.nat_div.comp (Primrec.succ.comp hBE) (Primrec.const 2)
  have h_aE_even : PrimrecPred (fun p : ℕ × ℕ => p.1.unpair.fst % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hAE (Primrec.const 2)) (Primrec.const 0)
  have h_bE_even : PrimrecPred (fun p : ℕ × ℕ => p.2.unpair.fst % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hBE (Primrec.const 2)) (Primrec.const 0)
  have h_aabs_BD : Primrec (fun p : ℕ × ℕ =>
      (p.1.unpair.fst + 1) / 2 * p.2.unpair.snd) :=
    Primrec.nat_mul.comp h_aabs hBD
  have h_babs_AD : Primrec (fun p : ℕ × ℕ =>
      (p.2.unpair.fst + 1) / 2 * p.1.unpair.snd) :=
    Primrec.nat_mul.comp h_babs hAD
  have h_pos_pos : PrimrecPred (fun p : ℕ × ℕ =>
      (p.1.unpair.fst + 1) / 2 * p.2.unpair.snd ≤
      (p.2.unpair.fst + 1) / 2 * p.1.unpair.snd) :=
    Primrec.nat_le.comp h_aabs_BD h_babs_AD
  have h_neg_neg : PrimrecPred (fun p : ℕ × ℕ =>
      (p.2.unpair.fst + 1) / 2 * p.1.unpair.snd ≤
      (p.1.unpair.fst + 1) / 2 * p.2.unpair.snd) :=
    Primrec.nat_le.comp h_babs_AD h_aabs_BD
  have h_inner_a : Primrec (fun p : ℕ × ℕ =>
      (if p.2.unpair.fst % 2 = 0 then
        decide ((p.1.unpair.fst + 1) / 2 * p.2.unpair.snd ≤
                (p.2.unpair.fst + 1) / 2 * p.1.unpair.snd)
       else false : Bool)) :=
    Primrec.ite h_bE_even h_pos_pos.decide (Primrec.const false)
  have h_inner_b : Primrec (fun p : ℕ × ℕ =>
      (if p.2.unpair.fst % 2 = 0 then true
       else decide ((p.2.unpair.fst + 1) / 2 * p.1.unpair.snd ≤
                    (p.1.unpair.fst + 1) / 2 * p.2.unpair.snd) : Bool)) :=
    Primrec.ite h_bE_even (Primrec.const true) h_neg_neg.decide
  exact Primrec₂.mk (Primrec.ite h_aE_even h_inner_a h_inner_b)

theorem ratLeEnc_iff (a b : ℚ) :
    ratLeEnc (Encodable.encode a) (Encodable.encode b) = decide (a ≤ b) := by
  rw [Bool.decide_congr (Rat.le_iff a b)]
  rw [rat_encode_eq, rat_encode_eq]
  unfold ratLeEnc
  simp only [Nat.unpair_pair]
  rw [show ((Encodable.encode a.num) + 1) / 2 = a.num.natAbs from
        (natAbs_eq_encode_div a.num).symm,
      show ((Encodable.encode b.num) + 1) / 2 = b.num.natAbs from
        (natAbs_eq_encode_div b.num).symm]
  have ha_pos : (0 : ℤ) < (a.den : ℤ) := by exact_mod_cast a.pos
  have hb_pos : (0 : ℤ) < (b.den : ℤ) := by exact_mod_cast b.pos
  cases ha : a.num with
  | ofNat ka =>
    rw [show (Encodable.encode (Int.ofNat ka) : ℕ) = 2 * ka from rfl,
        if_pos (Nat.mul_mod_right 2 ka)]
    rw [show (Int.ofNat ka).natAbs = ka from rfl]
    have hAcast : (Int.ofNat ka : ℤ) = (ka : ℤ) := rfl
    cases hb : b.num with
    | ofNat kb =>
      rw [show (Encodable.encode (Int.ofNat kb) : ℕ) = 2 * kb from rfl,
          if_pos (Nat.mul_mod_right 2 kb)]
      rw [show (Int.ofNat kb).natAbs = kb from rfl]
      apply Bool.decide_congr
      rw [hAcast, show (Int.ofNat kb : ℤ) = (kb : ℤ) from rfl]
      exact_mod_cast Iff.rfl
    | negSucc kb =>
      rw [show (Encodable.encode (Int.negSucc kb) : ℕ) = 2 * kb + 1 from rfl,
          if_neg (by omega : (2 * kb + 1) % 2 ≠ 0)]
      symm
      apply decide_eq_false
      rw [hAcast, show (Int.negSucc kb : ℤ) = -((kb + 1 : ℕ) : ℤ) from rfl]
      intro h
      have hL : (0 : ℤ) ≤ (ka : ℤ) * b.den := mul_nonneg (Int.natCast_nonneg _) hb_pos.le
      have hRpos : (0 : ℤ) < ((kb + 1 : ℕ) : ℤ) * a.den :=
        mul_pos (by exact_mod_cast Nat.succ_pos _) ha_pos
      linarith
  | negSucc ka =>
    rw [show (Encodable.encode (Int.negSucc ka) : ℕ) = 2 * ka + 1 from rfl,
        if_neg (by omega : (2 * ka + 1) % 2 ≠ 0)]
    rw [show (Int.negSucc ka).natAbs = ka + 1 from rfl]
    have hAcast : (Int.negSucc ka : ℤ) = -((ka + 1 : ℕ) : ℤ) := rfl
    cases hb : b.num with
    | ofNat kb =>
      rw [show (Encodable.encode (Int.ofNat kb) : ℕ) = 2 * kb from rfl,
          if_pos (Nat.mul_mod_right 2 kb)]
      symm
      apply decide_eq_true
      rw [hAcast, show (Int.ofNat kb : ℤ) = (kb : ℤ) from rfl]
      have hL : (0 : ℤ) ≤ (kb : ℤ) * a.den := mul_nonneg (Int.natCast_nonneg _) ha_pos.le
      have hRpos : (0 : ℤ) < ((ka + 1 : ℕ) : ℤ) * b.den :=
        mul_pos (by exact_mod_cast Nat.succ_pos _) hb_pos
      linarith
    | negSucc kb =>
      rw [show (Encodable.encode (Int.negSucc kb) : ℕ) = 2 * kb + 1 from rfl,
          if_neg (by omega : (2 * kb + 1) % 2 ≠ 0)]
      rw [show (Int.negSucc kb).natAbs = kb + 1 from rfl]
      apply Bool.decide_congr
      rw [hAcast, show (Int.negSucc kb : ℤ) = -((kb + 1 : ℕ) : ℤ) from rfl]
      constructor
      · intro h
        have h_int : ((kb + 1 : ℕ) : ℤ) * (a.den : ℤ) ≤ ((ka + 1 : ℕ) : ℤ) * (b.den : ℤ) := by
          exact_mod_cast h
        linarith
      · intro h
        have h_int : ((kb + 1 : ℕ) : ℤ) * (a.den : ℤ) ≤ ((ka + 1 : ℕ) : ℤ) * (b.den : ℤ) := by
          linarith
        exact_mod_cast h_int

theorem primrec_rat_le : PrimrecRel ((· ≤ ·) : ℚ → ℚ → Prop) := by
  refine Primrec₂.primrecRel ?_
  refine Primrec.of_eq ?_ (fun p => ratLeEnc_iff p.1 p.2)
  exact Primrec₂.comp primrec_ratLeEnc
    (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)

/-! ## `Primrec` / `Computable` for `n ↦ (n : ℚ)` (nat-cast to ℚ)

Encoded form: `(n : ℚ)` has `.num = n` (as Int) and `.den = 1`. Under the
standard ℤ encoding `Int.ofNat n ↦ 2 * n`, the rat-encoding becomes
`Nat.pair (2 * n) 1`. -/

theorem rat_natCast_num (n : ℕ) : ((n : ℚ).num) = (n : ℤ) := by
  simp [Rat.num_natCast]

theorem rat_natCast_den (n : ℕ) : ((n : ℚ).den) = 1 := by
  simp [Rat.den_natCast]

theorem encode_rat_natCast (n : ℕ) :
    Encodable.encode ((n : ℚ)) = Nat.pair (2 * n) 1 := by
  rw [rat_encode_eq, rat_natCast_num, rat_natCast_den]
  rfl

theorem primrec_rat_natCast : Primrec (fun n : ℕ => (n : ℚ)) := by
  apply Primrec.encode_iff.mp
  refine Primrec.of_eq ?_ (fun n => (encode_rat_natCast n).symm)
  exact Primrec₂.natPair.comp
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
    (Primrec.const 1)

theorem computable_rat_natCast : Computable (fun n : ℕ => (n : ℚ)) :=
  primrec_rat_natCast.to_comp

/-! ## `Primrec` projections `q ↦ q.num` and `q ↦ q.den`

Under the structured encoding `encode q = Nat.pair (encode q.num) q.den`,
both projections are `Primrec` by direct composition with `Nat.unpair`. -/

theorem primrec_rat_num : Primrec (fun q : ℚ => q.num) := by
  apply Primrec.encode_iff.mp
  refine Primrec.of_eq
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.encode (α := ℚ))))
    (fun q => ?_)
  show (Nat.unpair (Encodable.encode q)).1 = Encodable.encode q.num
  conv_lhs => rw [rat_encode_eq q]
  rw [Nat.unpair_pair]

theorem primrec_rat_den : Primrec (fun q : ℚ => q.den) := by
  refine Primrec.of_eq
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.encode (α := ℚ))))
    (fun q => ?_)
  show (Nat.unpair (Encodable.encode q)).2 = q.den
  conv_lhs => rw [rat_encode_eq q]
  rw [Nat.unpair_pair]

theorem computable_rat_num : Computable (fun q : ℚ => q.num) :=
  primrec_rat_num.to_comp

theorem computable_rat_den : Computable (fun q : ℚ => q.den) :=
  primrec_rat_den.to_comp

/-! ## Encoded Int multiplication by a positive Nat

`intMulNatEnc encInt k` computes the encoding of `(decoded encInt) * k` where
`k : ℕ`. Used as a building block for rational addition: `(a/b) + (c/d) =
(a*d + c*b) / (b*d)` requires multiplying numerators by denominators. -/

/-- Multiply an encoded Int by a Nat. For `encInt = 2m` (positive), result is
`2 * m * k = encInt * k`. For `encInt = 2m + 1` (negative `-(m+1)`), result is
encoded `-(k * (m+1))`, which is `2 * (k * (m+1)) - 1 = (encInt + 1) * k - 1`
provided `k ≥ 1`; for `k = 0`, result is `0` (zero). -/
def intMulNatEnc (encInt k : ℕ) : ℕ :=
  if k = 0 then 0
  else if encInt % 2 = 0 then encInt * k
  else (encInt + 1) * k - 1

theorem primrec_intMulNatEnc : Primrec₂ intMulNatEnc := by
  -- Decompose the if-then-else into Primrec building blocks.
  have h_kEq0 : PrimrecPred (fun p : ℕ × ℕ => p.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have h_encEven : PrimrecPred (fun p : ℕ × ℕ => p.1 % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2))
      (Primrec.const 0)
  have h_branch_pos : Primrec (fun p : ℕ × ℕ => p.1 * p.2) :=
    Primrec.nat_mul.comp Primrec.fst Primrec.snd
  have h_branch_neg : Primrec (fun p : ℕ × ℕ => (p.1 + 1) * p.2 - 1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)
      (Primrec.const 1)
  exact Primrec.ite h_kEq0 (Primrec.const 0)
    (Primrec.ite h_encEven h_branch_pos h_branch_neg)

/-! ## Encoded Int addition `intAddEnc`

For two encoded Ints `e1, e2`, computes the encoding of their sum.
Handles four sign cases:
- Both even (≥ 0): `e1 + e2`.
- Both odd (< 0, magnitudes m1+1, m2+1): `e1 + e2 + 1`
  (encodes `-(m1+m2+2)` as `2(m1+m2+1)+1 = e1+e2+1`).
- Mixed signs: subtract magnitudes; sign tracks the larger magnitude. -/

/-- Encoded Int addition. -/
def intAddEnc (e1 e2 : ℕ) : ℕ :=
  if e1 % 2 = 0 then
    if e2 % 2 = 0 then e1 + e2
    else if e1 > e2 then e1 - e2 - 1 else e2 - e1
  else
    if e2 % 2 = 0 then
      if e2 > e1 then e2 - e1 - 1 else e1 - e2
    else e1 + e2 + 1

theorem primrec_intAddEnc : Primrec₂ intAddEnc := by
  have h_e1Even : PrimrecPred (fun p : ℕ × ℕ => p.1 % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2))
      (Primrec.const 0)
  have h_e2Even : PrimrecPred (fun p : ℕ × ℕ => p.2 % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
      (Primrec.const 0)
  have h_e1gt : PrimrecPred (fun p : ℕ × ℕ => p.1 > p.2) :=
    Primrec.nat_lt.comp Primrec.snd Primrec.fst
  have h_e2gt : PrimrecPred (fun p : ℕ × ℕ => p.2 > p.1) :=
    Primrec.nat_lt.comp Primrec.fst Primrec.snd
  have h_sum : Primrec (fun p : ℕ × ℕ => p.1 + p.2) :=
    Primrec.nat_add.comp Primrec.fst Primrec.snd
  have h_sumPlus1 : Primrec (fun p : ℕ × ℕ => p.1 + p.2 + 1) :=
    Primrec.succ.comp h_sum
  have h_e1subE2sub1 : Primrec (fun p : ℕ × ℕ => p.1 - p.2 - 1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_sub.comp Primrec.fst Primrec.snd) (Primrec.const 1)
  have h_e2subE1 : Primrec (fun p : ℕ × ℕ => p.2 - p.1) :=
    Primrec.nat_sub.comp Primrec.snd Primrec.fst
  have h_e2subE1sub1 : Primrec (fun p : ℕ × ℕ => p.2 - p.1 - 1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1)
  have h_e1subE2 : Primrec (fun p : ℕ × ℕ => p.1 - p.2) :=
    Primrec.nat_sub.comp Primrec.fst Primrec.snd
  -- Outer if (e1 even):
  --   inner if (e2 even): h_sum, else if (e1 > e2): h_e1subE2sub1, else h_e2subE1.
  -- Outer else (e1 odd):
  --   inner if (e2 even): if (e2 > e1): h_e2subE1sub1, else h_e1subE2;
  --   else (both odd): h_sumPlus1.
  exact Primrec.ite h_e1Even
    (Primrec.ite h_e2Even h_sum
      (Primrec.ite h_e1gt h_e1subE2sub1 h_e2subE1))
    (Primrec.ite h_e2Even
      (Primrec.ite h_e2gt h_e2subE1sub1 h_e1subE2)
      h_sumPlus1)

end ComputableRat
