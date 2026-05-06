import Mathlib.Computability.Partrec
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring

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

end ComputableRat
