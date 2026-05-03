import Mathlib.Computability.Partrec
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Rat.Defs

/-! # Computability infrastructure for `ℚ`

This file builds up the `Computable` / `Primrec` infrastructure for
operations on the rationals that the Hochman–Meyerovitch formalization
needs in its computability section (F-section of the implementation list).

`ℚ` is `Denumerable` (hence `Primcodable`) via `ofEncodableOfInfinite`;
the `Encodable` instance goes through the sigma-type
`Σ n : ℤ, {d : ℕ // 0 < d ∧ n.natAbs.Coprime d}` (see `Mathlib.Data.Rat.Encodable`),
so for a rational `q : ℚ` we have

  `encode q = Nat.pair (encode (q.num : ℤ)) (encode (q.den : ℕ))`
            = `Nat.pair (encode (q.num : ℤ)) q.den`

(the second equality uses that `Nat`'s encoding is the identity).

## Downstream goal (F-section of HochmanMeyerovitch.lean)

The target is `theorem computable_imp_rightRE` (F4): given a `Computable q : ℕ → ℚ`
with `|q n - h| ≤ 1/(n+1)`, the function `r n := q n + 1/(n+1)` is `Computable`
and witnesses `IsRightRE h`.

This requires:

  (i)   `Computable (fun n : ℕ => (1 : ℚ) / (↑n + 1))` — the rate function.
  (ii)  `Computable₂ ((· + ·) : ℚ → ℚ → ℚ)` — rational addition.
  (iii) Compose `q` and (i) under (ii).

For (i), the encoding identity above gives
`encode (1 / (↑n + 1) : ℚ) = Nat.pair (encode (1 : ℤ)) (n + 1) = Nat.pair 2 (n+1)`,
which is `Nat.Primrec`. Bridging the abstract `encode` and this explicit form
requires unfolding `Encodable.ofEquiv`, sigma encoding, subtype encoding, and
the specific `Equiv.intEquivNat 1 = 2` computation; this is the next item to add.

For (ii), rational addition is `(a + b).num = a.num * b.den + b.num * a.den`
and `(a + b).den = a.den * b.den / gcd ...`; on the encoding side this is a
`Primrec₂` function of `(encode a, encode b)`. The `gcd` reduction makes this
the hardest of the three.

## Status

- ✓ Identity and constants (`Computable.id`, `Computable.const`)
- ☐ `Computable (Nat.cast : ℕ → ℚ)`
- ☐ `Computable (fun n : ℕ => (1 : ℚ) / (↑n + 1))`
- ☐ `Computable₂ ((· + ·) : ℚ → ℚ → ℚ)`
- ☐ `Computable.rat_shift_above q : Computable q → Computable (fun n => q n + 1/(↑n+1))`
-/

namespace ComputableRat

/-! ## Identity, constants, and basic compositions -/

/-- The identity on `ℚ` is computable. -/
theorem computable_id : Computable (id : ℚ → ℚ) := Computable.id

/-- A constant rational sequence is computable. -/
theorem computable_const (q : ℚ) : Computable (fun _ : ℕ => q) := Computable.const q

/-- A `Computable q : ℕ → ℚ` composed with a `Primrec g : ℕ → ℕ` is `Computable`.
    A handy reusable form of `Computable.comp`. -/
theorem computable_comp_nat {q : ℕ → ℚ} (hq : Computable q) {g : ℕ → ℕ} (hg : Primrec g) :
    Computable (fun n => q (g n)) :=
  hq.comp hg.to_comp

end ComputableRat
