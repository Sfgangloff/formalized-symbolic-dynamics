import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Homeomorph.Defs

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

/-! ## 0.11  shiftMap_bijective -/

theorem shiftMap_bijective {α : Type*} {d : ℕ} (u : Lat d) :
    Function.Bijective (shiftMap u (α := α)) := by
  constructor
  · intro x y h
    ext v
    have := congr_fun h (v - u)
    simp only [shiftMap, sub_add_cancel] at this
    exact this
  · intro x
    exact ⟨shiftMap (-u) x, by ext v; simp [shiftMap]⟩

/-! ## 0.12  Topology instances on FullShift -/

instance instTopologicalSpace {α : Type*} {d : ℕ} [TopologicalSpace α] :
    TopologicalSpace (FullShift α d) := inferInstance

instance instCompactSpace {α : Type*} {d : ℕ} [TopologicalSpace α] [CompactSpace α] :
    CompactSpace (FullShift α d) := inferInstance

instance instT2Space {α : Type*} {d : ℕ} [TopologicalSpace α] [T2Space α] :
    T2Space (FullShift α d) := inferInstance

/-! ## 0.13  shiftMap_continuous -/

theorem shiftMap_continuous {α : Type*} {d : ℕ} [TopologicalSpace α] (u : Lat d) :
    Continuous (shiftMap u (α := α)) :=
  continuous_pi fun v => continuous_apply (v + u)

/-! ## A1  shiftMap_homeomorph — σ^u is a homeomorphism -/

def shiftMap_homeomorph {α : Type*} {d : ℕ} [TopologicalSpace α] (u : Lat d) :
    FullShift α d ≃ₜ FullShift α d where
  toFun := shiftMap u
  invFun := shiftMap (-u)
  left_inv x := by rw [← shiftMap_add]; simp [neg_add_cancel]
  right_inv x := by rw [← shiftMap_add]; simp [add_neg_cancel]
  continuous_toFun := shiftMap_continuous u
  continuous_invFun := shiftMap_continuous (-u)

end FullShift

/-! ## 0.14  Pattern — a finite window coloring -/

/-- A pattern over alphabet `α` with support `F ⊆ ℤ^d`. -/
abbrev Pattern (α : Type*) {d : ℕ} (F : Finset (Lat d)) := F → α

namespace Pattern

/-! ## 0.15  ofColoring — restrict a full coloring to a finite window -/

/-- Restrict a coloring to a finite support. -/
def ofColoring {α : Type*} {d : ℕ} (F : Finset (Lat d)) (x : FullShift α d) : Pattern α F :=
  fun v => x v.val

/-! ## 0.16  restrict — restrict a pattern to a sub-window -/

/-- Restrict a pattern on `F` to a sub-finset `G ⊆ F`. -/
def restrict {α : Type*} {d : ℕ} {F : Finset (Lat d)} (G : Finset (Lat d)) (hGF : G ⊆ F)
    (p : Pattern α F) : Pattern α G :=
  fun v => p ⟨v.val, hGF v.property⟩

end Pattern
