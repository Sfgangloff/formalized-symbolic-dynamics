import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Action.Defs

/-! ## 0.1  Lat d — the group ℤ^d -/

/-- The additive group ℤ^d, used as the index lattice. -/
abbrev Lat (d : ℕ) := Fin d → ℤ

namespace Lat

/-! ## 0.2  supNorm — the ℓ∞ norm on ℤ^d -/

/-- The ℓ∞ (sup) norm on ℤ^d: max of absolute values of coordinates.
    Returns 0 for d = 0. -/
def supNorm {d : ℕ} (u : Lat d) : ℤ :=
  ↑(Finset.univ.sup (fun i => (u i).natAbs))

/-! ## 0.3  supNorm_zero -/

@[simp]
theorem supNorm_zero {d : ℕ} : supNorm (0 : Lat d) = 0 := by
  simp only [supNorm, Pi.zero_apply, Int.natAbs_zero]
  norm_cast
  exact Finset.sup_bot Finset.univ

/-! ## 0.4  supNorm_nonneg -/

theorem supNorm_nonneg {d : ℕ} (u : Lat d) : 0 ≤ supNorm u := by
  simp only [supNorm]
  exact_mod_cast Nat.zero_le _

end Lat

/-! ## 0.5  FullShift — α^{ℤ^d} -/

/-- The full shift: the set of all colorings of ℤ^d by alphabet α. -/
abbrev FullShift (α : Type*) (d : ℕ) := Lat d → α

namespace FullShift

/-! ## 0.5b  ext lemma -/

@[ext]
lemma ext {α : Type*} {d : ℕ} {x y : FullShift α d} (h : ∀ v, x v = y v) : x = y :=
  funext h

/-! ## 0.6  shiftMap — the shift action σ^u -/

/-- Shift a coloring by lattice vector `u`: `(shiftMap u x) v = x (v + u)`. -/
def shiftMap {α : Type*} {d : ℕ} (u : Lat d) (x : FullShift α d) : FullShift α d :=
  fun v => x (v + u)

/-! ## 0.7  shiftMap_zero -/

@[simp]
theorem shiftMap_zero {α : Type*} {d : ℕ} (x : FullShift α d) : shiftMap 0 x = x := by
  ext v; simp only [shiftMap]; exact congr_arg x (add_zero v)

/-! ## 0.8  shiftMap_add -/

@[simp]
theorem shiftMap_add {α : Type*} {d : ℕ} (u v : Lat d) (x : FullShift α d) :
    shiftMap (u + v) x = shiftMap u (shiftMap v x) := by
  ext w; simp only [shiftMap]; exact congr_arg x (add_assoc w u v).symm

/-! ## 0.9  instAddAction — ℤ^d acts on FullShift α d by shifts -/

instance instAddAction {α : Type*} {d : ℕ} : AddAction (Lat d) (FullShift α d) where
  vadd u x := shiftMap u x
  zero_vadd x := shiftMap_zero x
  add_vadd u v x := shiftMap_add u v x

/-! ## 0.10  vadd_eq_shiftMap -/

@[simp]
theorem vadd_eq_shiftMap {α : Type*} {d : ℕ} (u : Lat d) (x : FullShift α d) :
    u +ᵥ x = shiftMap u x := rfl

end FullShift
