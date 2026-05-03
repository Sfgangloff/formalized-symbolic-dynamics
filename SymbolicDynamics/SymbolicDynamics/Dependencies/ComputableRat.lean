import Mathlib.Computability.Partrec
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Rat.Defs

/-! # Computability infrastructure for `ℚ`

This file builds up the `Computable` / `Primrec` infrastructure for
operations on the rationals that the Hochman–Meyerovitch formalization
needs in its computability section (F-section of the implementation list).

`ℚ` is `Denumerable` (hence `Primcodable`) via `ofEncodableOfInfinite`;
the encoding goes through the sigma-type
`Σ n : ℤ, {d : ℕ // 0 < d ∧ n.natAbs.Coprime d}`.

The downstream goal is to prove enough rational arithmetic is `Computable`
to support `theorem computable_imp_rightRE` (F4): given a computable
rational approximation `q : ℕ → ℚ` of a real `h` with rate `1/(n+1)`,
the function `r n := q n + 1/(n+1)` is computable and bounds `h` from above.

## Status

- ✓ Identity and constants (trivial via `Computable.id` / `Computable.const`)
- ☐ `Computable (Nat.cast : ℕ → ℚ)`
- ☐ `Computable₂ ((· + ·) : ℚ → ℚ → ℚ)`
- ☐ `Computable (fun n : ℕ => (1 : ℚ) / (n + 1))`
- ☐ `Computable.rat_shift_above`: `Computable q → Computable (fun n => q n + 1/(n+1))`

These will be added incrementally; each commit adds a working block.
-/

namespace ComputableRat

/-! ## Identity and constants -/

/-- The identity on `ℚ` is computable. -/
theorem computable_id : Computable (id : ℚ → ℚ) := Computable.id

/-- A constant rational sequence is computable. -/
theorem computable_const (q : ℚ) : Computable (fun _ : ℕ => q) := Computable.const q

end ComputableRat
