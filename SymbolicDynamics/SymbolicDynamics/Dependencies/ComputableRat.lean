import Mathlib.Computability.Partrec
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Rat.Lemmas

/-! # Computability infrastructure for `ℚ`

This file builds up the `Computable` / `Primrec` infrastructure for
operations on the rationals that the Hochman–Meyerovitch formalization
needs in its computability section (F-section of the implementation list).

## Two encodings of `ℚ`

There are TWO `Encodable ℚ` instances in Mathlib:

1.  `Rat.instEncodable` (`Mathlib.Data.Rat.Encodable`): the *structured* encoding
    via `Σ n : ℤ, {d : ℕ // 0 < d ∧ n.natAbs.Coprime d}`. With this instance,

      `@Encodable.encode ℚ Rat.instEncodable q = Nat.pair (encode q.num) q.den`

    (where `encode q.num` is the standard `Equiv.intEquivNat` encoding of `ℤ`),
    and this identity is `rfl`. In particular, for `q = 1/(↑n+1)`:

      `encode (1/(↑n+1) : ℚ) = Nat.pair 2 (n+1)`.

2.  `(Primcodable.ofDenumerable ℚ).toEncodable`, which `Primrec` and
    `Computable` use. This goes through `Denumerable.ofEncodableOfInfinite`,
    which RE-INDEXES the encoding to be a bijection `ℕ ↔ ℚ` — different from
    `Rat.instEncodable.encode`, and the two are NOT definitionally equal.

The fact `Primrec (fun n : ℕ => (1 : ℚ) / (↑n + 1))` requires the *Primcodable*
encoding to be primitive recursive, which in turn requires computing the
re-indexed encoding — significantly harder than the structured `Rat.instEncodable`
case.

## Path forward (TODO)

Concrete options for unblocking F4 (`computable_imp_rightRE`):

  (a) Prove that the structured `Rat.instEncodable` encoding *is* primitive
      recursive (i.e., that `fun n : ℕ => encode (decode n : Option ℚ)` is
      `Nat.Primrec` for that encoding), then provide a higher-priority
      `Primcodable ℚ` instance that uses it. This makes
      `encode (1/(↑n+1)) = Nat.pair 2 (n+1)` available to `Primrec`.

  (b) Work with the existing re-indexed Primcodable encoding directly,
      computing it concretely via the `equivRangeEncode` bijection. Tedious.

  (c) Build computable rational arithmetic via a custom intermediate type
      (e.g., `(num, den) : ℤ × ℕ⁺` with no coprimality requirement), prove
      operations there, then bridge.

(a) seems most promising — the Primcodable check `Nat.Primrec (fun n => encode (decode n))`
for the structured encoding boils down to: gcd is Primrec (yes, in Mathlib).

The explicit encoding identities below are stated and proven for
`Rat.instEncodable`; they will be the "true content" once option (a) is in place.
-/

namespace ComputableRat

/-! ## Identity, constants, and basic compositions -/

/-- The identity on `ℚ` is computable. -/
theorem computable_id : Computable (id : ℚ → ℚ) := Computable.id

/-- A constant rational sequence is computable. -/
theorem computable_const (q : ℚ) : Computable (fun _ : ℕ => q) := Computable.const q

/-- A `Computable q : ℕ → ℚ` composed with a `Primrec g : ℕ → ℕ` is `Computable`. -/
theorem computable_comp_nat {q : ℕ → ℚ} (hq : Computable q) {g : ℕ → ℕ} (hg : Primrec g) :
    Computable (fun n => q (g n)) :=
  hq.comp hg.to_comp

/-! ## Encoding identities for `Rat.instEncodable`

These give the explicit form of `Encodable.encode` (under the structured
sigma encoding) in terms of `Rat.num` and `Rat.den`. They are `rfl`,
so they will compose cleanly once we have a `Primcodable ℚ` instance
matching this encoding. -/

/-- `Rat.instEncodable.encode` factors as `Nat.pair (encode num) den`. -/
theorem rat_encode_eq (q : ℚ) :
    @Encodable.encode ℚ Rat.instEncodable q
      = Nat.pair (@Encodable.encode ℤ _ q.num) q.den := rfl

/-- Numerator of `1/(↑n + 1)` is `1`. -/
theorem one_div_succ_num (n : ℕ) : ((1 : ℚ) / ((n : ℚ) + 1)).num = 1 := by
  rw [one_div, ← Nat.cast_succ]
  exact Rat.inv_natCast_num_of_pos (Nat.succ_pos _)

/-- Denominator of `1/(↑n + 1)` is `n + 1`. -/
theorem one_div_succ_den (n : ℕ) : ((1 : ℚ) / ((n : ℚ) + 1)).den = n + 1 := by
  rw [one_div, ← Nat.cast_succ]
  exact Rat.inv_natCast_den_of_pos (Nat.succ_pos _)

/-- `Rat.instEncodable.encode (1/(↑n+1)) = Nat.pair 2 (n+1)`. -/
theorem encode_one_div_succ (n : ℕ) :
    @Encodable.encode ℚ Rat.instEncodable ((1 : ℚ) / ((n : ℚ) + 1))
      = Nat.pair 2 (n + 1) := by
  rw [rat_encode_eq, one_div_succ_num, one_div_succ_den]
  rfl

end ComputableRat
