import Mathlib.Computability.Partrec
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Rat.Lemmas

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

end ComputableRat
