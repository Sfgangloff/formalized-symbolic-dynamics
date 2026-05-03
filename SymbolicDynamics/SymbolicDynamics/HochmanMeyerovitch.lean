import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval

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

/-! ## 0.17  translateFinset — shift a finite support by u -/

/-- Translate the support `F` by lattice vector `u`. -/
def translateFinset {d : ℕ} (u : Lat d) (F : Finset (Lat d)) : Finset (Lat d) :=
  F.image (· + u)

/-! ## 0.18  mem_translateFinset -/

@[simp]
theorem mem_translateFinset {d : ℕ} {u : Lat d} {F : Finset (Lat d)} {v : Lat d} :
    v ∈ translateFinset u F ↔ v - u ∈ F := by
  simp [translateFinset, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using hw
  · intro hv; exact ⟨v - u, hv, by simp⟩

/-! ## 0.19  AppearsAt — pattern p occurs at position u in coloring x -/

def AppearsAt {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F)
    (x : FullShift α d) (u : Lat d) : Prop :=
  ∀ v : F, x (v.val + u) = p v

/-! ## 0.20  Appears — pattern p occurs somewhere in x -/

def Appears {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F)
    (x : FullShift α d) : Prop :=
  ∃ u : Lat d, AppearsAt p x u

/-! ## 0.21  cylinder — the clopen set of colorings extending p at offset u -/

def cylinder {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F) (u : Lat d) :
    Set (FullShift α d) :=
  {x | AppearsAt p x u}

/-! ## 0.22  mem_cylinder_iff -/

@[simp]
theorem mem_cylinder_iff {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F)
    (u : Lat d) (x : FullShift α d) :
    x ∈ cylinder p u ↔ ∀ v : F, x (v.val + u) = p v :=
  Iff.rfl

/-! ## 0.23  cylinder_isOpen -/

theorem cylinder_isOpen {α : Type*} {d : ℕ} {F : Finset (Lat d)} [TopologicalSpace α]
    [DiscreteTopology α] (p : Pattern α F) (u : Lat d) :
    IsOpen (cylinder p u) := by
  simp only [cylinder, AppearsAt, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro v
  change IsOpen ((fun x : FullShift α d => x (v.val + u)) ⁻¹' {p v})
  exact (continuous_apply (v.val + u)).isOpen_preimage _ (isOpen_discrete _)

/-! ## 0.24  cylinder_isClosed -/

theorem cylinder_isClosed {α : Type*} {d : ℕ} {F : Finset (Lat d)} [TopologicalSpace α]
    [T1Space α] (p : Pattern α F) (u : Lat d) :
    IsClosed (cylinder p u) := by
  simp only [cylinder, AppearsAt, Set.setOf_forall]
  apply isClosed_iInter
  intro v
  change IsClosed ((fun x : FullShift α d => x (v.val + u)) ⁻¹' {p v})
  exact IsClosed.preimage (continuous_apply (v.val + u)) isClosed_singleton

end Pattern

/-! ## 0.25  Subshift — closed shift-invariant subset of FullShift α d -/

structure Subshift (α : Type*) (d : ℕ) [TopologicalSpace α] where
  carrier : Set (FullShift α d)
  isClosed : IsClosed carrier
  isInvariant : ∀ (u : Lat d) (x : FullShift α d), x ∈ carrier → FullShift.shiftMap u x ∈ carrier

namespace Subshift

/-! ## 0.26  Membership -/

instance instMembership {α : Type*} {d : ℕ} [TopologicalSpace α] :
    Membership (FullShift α d) (Subshift α d) where
  mem (X : Subshift α d) (x : FullShift α d) := x ∈ X.carrier

/-! ## 0.27  mem_iff -/

@[simp]
theorem mem_iff {α : Type*} {d : ℕ} [TopologicalSpace α]
    (X : Subshift α d) (x : FullShift α d) :
    x ∈ X ↔ x ∈ X.carrier :=
  Iff.rfl

/-! ## 0.28  univ — the full shift as a subshift -/

def univ (α : Type*) (d : ℕ) [TopologicalSpace α] : Subshift α d where
  carrier := Set.univ
  isClosed := isClosed_univ
  isInvariant := fun _ _ _ => Set.mem_univ _

/-! ## A2  bot — the empty subshift -/

def bot (α : Type*) (d : ℕ) [TopologicalSpace α] : Subshift α d where
  carrier := ∅
  isClosed := isClosed_empty
  isInvariant := fun _ _ hx => absurd hx (Set.notMem_empty _)

/-! ## A3  inter — intersection of two subshifts -/

def inter {α : Type*} {d : ℕ} [TopologicalSpace α]
    (X Y : Subshift α d) : Subshift α d where
  carrier := X.carrier ∩ Y.carrier
  isClosed := X.isClosed.inter Y.isClosed
  isInvariant := fun u x ⟨hxX, hxY⟩ =>
    ⟨X.isInvariant u x hxX, Y.isInvariant u x hxY⟩

/-! ## A4  iInter — arbitrary indexed intersection of subshifts -/

def iInter {α : Type*} {d : ℕ} [TopologicalSpace α] {ι : Type*}
    (Xs : ι → Subshift α d) : Subshift α d where
  carrier := ⋂ i, (Xs i).carrier
  isClosed := isClosed_iInter (fun i => (Xs i).isClosed)
  isInvariant := fun u x hx =>
    Set.mem_iInter.mpr (fun i => (Xs i).isInvariant u x (Set.mem_iInter.mp hx i))

end Subshift

/-! ## 0.29  SFT_admissible — coloring x is admissible for window F and allowed patterns L -/

/-- A coloring `x` is admissible for the syntax `(F, L)` if the F-pattern at every offset is in L.
-/
def SFT_admissible {α : Type*} {d : ℕ} (F : Finset (Lat d))
    (L : Finset (Pattern α F)) (x : FullShift α d) : Prop :=
  ∀ u : Lat d, Pattern.ofColoring F (FullShift.shiftMap u x) ∈ L

/-! ## 0.30  SFT_carrier -/

/-- The carrier set of the SFT with window `F` and syntax `L`. -/
def SFT_carrier {α : Type*} {d : ℕ} (F : Finset (Lat d))
    (L : Finset (Pattern α F)) : Set (FullShift α d) :=
  {x | SFT_admissible F L x}

/-! ## 0.31  SFT_carrier_isInvariant -/

theorem SFT_carrier_isInvariant {α : Type*} {d : ℕ} (F : Finset (Lat d))
    (L : Finset (Pattern α F)) :
    ∀ (u : Lat d) (x : FullShift α d), x ∈ SFT_carrier F L →
      FullShift.shiftMap u x ∈ SFT_carrier F L := by
  intro u x hx w
  simp only [SFT_carrier, Set.mem_setOf_eq, SFT_admissible] at hx ⊢
  show Pattern.ofColoring F (FullShift.shiftMap w (FullShift.shiftMap u x)) ∈ L
  rw [← FullShift.shiftMap_add]
  exact hx (w + u)

/-! ## 0.32  SFT_carrier_isClosed -/

theorem SFT_carrier_isClosed {α : Type*} {d : ℕ} [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) :
    IsClosed (SFT_carrier F L) := by
  have heq : SFT_carrier F L =
      ⋂ u : Lat d, (fun x => Pattern.ofColoring F (FullShift.shiftMap u x)) ⁻¹' ↑L := by
    ext x
    simp only [SFT_carrier, SFT_admissible, Set.mem_setOf_eq,
               Set.mem_iInter, Set.mem_preimage, Finset.mem_coe]
  rw [heq]
  apply isClosed_iInter
  intro u
  apply IsClosed.preimage
  · apply continuous_pi; intro v; exact continuous_apply (v.val + u)
  · exact L.finite_toSet.isClosed

/-! ## 0.33  mkSFT -/

/-- The SFT with window `F` and allowed patterns `L`. -/
def mkSFT {α : Type*} {d : ℕ} [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) : Subshift α d where
  carrier   := SFT_carrier F L
  isClosed  := SFT_carrier_isClosed F L
  isInvariant := SFT_carrier_isInvariant F L

/-! ## 0.34  mem_mkSFT -/

@[simp]
theorem mem_mkSFT {α : Type*} {d : ℕ} [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (x : FullShift α d) :
    x ∈ mkSFT F L ↔ SFT_admissible F L x :=
  Iff.rfl

/-! ## 0.35  locallyAdmissible — finite pattern is locally admissible for (F, L) -/

/-- Pattern `a` over `E` is locally admissible for syntax `(F, L)` if for every
    translate `F + u ⊆ E` the de-translated restriction lands in `L`. -/
def locallyAdmissible {α : Type*} {d : ℕ} {E : Finset (Lat d)}
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (a : Pattern α E) : Prop :=
  ∀ u : Lat d, ∀ (h : ∀ v : F, v.val + u ∈ E),
    (fun v : F => a ⟨v.val + u, h v⟩) ∈ L

/-! ## 0.36  ShiftIrreducible — X is r-irreducible -/

/-- Subshift `X` is `r`-irreducible if every two globally admissible patterns on
    supports that are at least `r` apart (in ℓ∞) can be simultaneously realized. -/
def ShiftIrreducible {α : Type*} {d : ℕ} [TopologicalSpace α]
    (X : Subshift α d) (r : ℕ) : Prop :=
  ∀ (A B : Finset (Lat d)),
    (∀ u ∈ A, ∀ v ∈ B, (r : ℤ) ≤ Lat.supNorm (u - v)) →
    ∀ (a : Pattern α A) (b : Pattern α B),
      (∃ x ∈ X, Pattern.AppearsAt a x 0) →
      (∃ x ∈ X, Pattern.AppearsAt b x 0) →
      ∃ x ∈ X, Pattern.AppearsAt a x 0 ∧ Pattern.AppearsAt b x 0

/-! ## 0.37  IsIrreducibleShift -/

/-- A subshift is irreducible if it is `r`-irreducible for some `r > 0`. -/
def IsIrreducibleShift {α : Type*} {d : ℕ} [TopologicalSpace α]
    (X : Subshift α d) : Prop :=
  ∃ r : ℕ, 0 < r ∧ ShiftIrreducible X r

namespace Pattern

/-! ## B1  GloballyAdmissible — pattern appears in some point of X -/

/-- Pattern `p` is globally admissible for `X` if it appears somewhere in some point of `X`. -/
def GloballyAdmissible {α : Type*} {d : ℕ} [TopologicalSpace α]
    {F : Finset (Lat d)} (X : Subshift α d) (p : Pattern α F) : Prop :=
  ∃ x ∈ X, Appears p x

/-! ## B2  globallyAdmissible_iff_exists_offset -/

@[simp]
theorem globallyAdmissible_iff_exists_offset {α : Type*} {d : ℕ} [TopologicalSpace α]
    {F : Finset (Lat d)} (X : Subshift α d) (p : Pattern α F) :
    GloballyAdmissible X p ↔ ∃ x ∈ X, ∃ u : Lat d, AppearsAt p x u :=
  Iff.rfl

/-! ## B3  globally_imp_locally — global admissibility implies local admissibility -/

theorem globally_imp_locally {α : Type*} {d : ℕ} [TopologicalSpace α] [T1Space α]
    {E : Finset (Lat d)} (F : Finset (Lat d)) (L : Finset (Pattern α F)) (p : Pattern α E)
    (hp : GloballyAdmissible (mkSFT F L) p) : locallyAdmissible F L p := by
  obtain ⟨x, hxX, offset, happ⟩ := hp
  intro u hu
  have hadm : SFT_admissible F L x := (mem_mkSFT F L x).mp hxX
  have key : ofColoring F (FullShift.shiftMap (u + offset) x) ∈ L := hadm (u + offset)
  have heq : ofColoring F (FullShift.shiftMap (u + offset) x) =
      fun v : F => p ⟨v.val + u, hu v⟩ := by
    ext v
    simp only [ofColoring, FullShift.shiftMap, ← add_assoc]
    exact happ ⟨v.val + u, hu v⟩
  rwa [heq] at key

end Pattern

/-! ## B4  N_X — number of globally admissible F-patterns in a subshift -/

/-- The number of globally admissible `F`-patterns in subshift `X`. -/
noncomputable def N_X {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) (F : Finset (Lat d)) : ℕ :=
  Set.ncard {p : Pattern α F | Pattern.GloballyAdmissible X p}

/-! ## B5  N_X_pos_of_nonempty — N_X is positive when X has a point -/

theorem N_X_pos_of_nonempty {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) (F : Finset (Lat d)) (hX : X.carrier.Nonempty) :
    0 < N_X X F := by
  obtain ⟨x, hx⟩ := hX
  rw [N_X, Set.ncard_pos]
  refine ⟨Pattern.ofColoring F x, x, hx, 0, ?_⟩
  intro v
  simp [Pattern.ofColoring]

/-! ## C1  box — the cube {0,...,n-1}^d in ℤ^d -/

/-- The discrete cube `{0,...,n-1}^d ⊆ ℤ^d`. -/
def box (d n : ℕ) : Finset (Lat d) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) (n : ℤ))
