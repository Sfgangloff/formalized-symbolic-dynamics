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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Subadditive
import Mathlib.Computability.Partrec
import Mathlib.Data.Rat.Denumerable

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
  simp only [translateFinset, Finset.mem_image]
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

/-! ## C2  box_card -/

@[simp]
theorem box_card (d n : ℕ) : (box d n).card = n ^ d := by
  simp [box, Fintype.card_piFinset, Int.card_Ico]

/-! ## C3  box_mono -/

theorem box_mono {d m n : ℕ} (hmn : m ≤ n) : box d m ⊆ box d n :=
  Fintype.piFinset_subset _ _ (fun _ => Finset.Ico_subset_Ico_right (by exact_mod_cast hmn))

/-! ## C4  box_zero -/

theorem box_zero {d : ℕ} (hd : 0 < d) : box d 0 = ∅ := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  simp [box]

/-! ## D1  N_X_submultiplicative — N_X is submultiplicative on disjoint unions -/

theorem N_X_submultiplicative {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) {F G : Finset (Lat d)} :
    N_X X (F ∪ G) ≤ N_X X F * N_X X G := by
  unfold N_X
  rw [← Set.ncard_prod]
  refine Set.ncard_le_ncard_of_injOn
    (fun p : Pattern α (F ∪ G) =>
      ((fun v : F => p ⟨v.val, Finset.mem_union_left _ v.property⟩),
       (fun v : G => p ⟨v.val, Finset.mem_union_right _ v.property⟩)))
    ?_ ?_ (Set.toFinite _)
  · rintro p ⟨x, hxX, u, happ⟩
    exact ⟨⟨x, hxX, u, fun v => happ ⟨v.val, _⟩⟩,
           ⟨x, hxX, u, fun v => happ ⟨v.val, _⟩⟩⟩
  · intro p _ q _ hpq
    ext ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvF | hvG
    · exact congr_fun (congr_arg Prod.fst hpq) ⟨v, hvF⟩
    · exact congr_fun (congr_arg Prod.snd hpq) ⟨v, hvG⟩

/-! ## D2  logN — log of the box pattern count -/

/-- `logN X n` is `log (N_X X (box d n))`, the log of the count of globally admissible
    patterns on the box `F_n = {0,...,n-1}^d`. -/
noncomputable def logN {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) (n : ℕ) : ℝ :=
  Real.log (N_X X (box d n))

/-! ## D3  logN_subadditive — 1D subadditivity of logN -/

/-- In one dimension, `logN X` is a subadditive sequence. -/
theorem logN_subadditive {α : Type*} [Fintype α] [TopologicalSpace α]
    (X : Subshift α 1) :
    Subadditive (logN X) := by
  intro m n
  -- The shift vector with single coordinate `m`.
  set vm : Lat 1 := fun _ => (m : ℤ) with hvm_def
  have hbox_mem : ∀ {k : ℕ} (v : Lat 1), v ∈ box 1 k ↔ 0 ≤ v 0 ∧ v 0 < (k : ℤ) := by
    intro k v
    simp only [box, Fintype.mem_piFinset, Finset.mem_Ico]
    refine ⟨fun h => h 0, fun h i => ?_⟩
    rw [Fin.eq_zero i]; exact h
  have hshift_box : ∀ v ∈ box 1 n, v + vm ∈ box 1 (m + n) := by
    intro v hv
    rw [hbox_mem] at hv
    rw [hbox_mem]
    have hadd : (v + vm) 0 = v 0 + (m : ℤ) := by simp [vm]
    rw [hadd]
    obtain ⟨h1, h2⟩ := hv
    have hm_nonneg : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    push_cast
    exact ⟨by linarith, by linarith⟩
  have hN : N_X X (box 1 (m + n)) ≤ N_X X (box 1 m) * N_X X (box 1 n) := by
    unfold N_X
    rw [← Set.ncard_prod]
    refine Set.ncard_le_ncard_of_injOn
      (fun p : Pattern α (box 1 (m + n)) =>
        ((fun v : box 1 m => p ⟨v.val, box_mono (Nat.le_add_right _ _) v.property⟩),
         (fun v : box 1 n => p ⟨v.val + vm, hshift_box v.val v.property⟩)))
      ?_ ?_ (Set.toFinite _)
    · rintro p ⟨x, hxX, w, happ⟩
      refine ⟨⟨x, hxX, w, fun v => ?_⟩, ⟨x, hxX, w + vm, fun v => ?_⟩⟩
      · exact happ ⟨v.val, box_mono (Nat.le_add_right _ _) v.property⟩
      · have h := happ ⟨v.val + vm, hshift_box v.val v.property⟩
        change x (v.val + (w + vm)) = p ⟨v.val + vm, hshift_box v.val v.property⟩
        have heq : v.val + (w + vm) = (v.val + vm) + w := by ring
        rw [heq]; exact h
    · intro p _ q _ hpq
      ext ⟨v, hv_orig⟩
      have hv : 0 ≤ v 0 ∧ v 0 < ((m + n : ℕ) : ℤ) := (hbox_mem v).mp hv_orig
      by_cases hvm : v 0 < (m : ℤ)
      · have hv_m : v ∈ box 1 m := (hbox_mem v).mpr ⟨hv.1, hvm⟩
        exact congr_fun (congr_arg Prod.fst hpq) ⟨v, hv_m⟩
      · push_neg at hvm
        have hv_n : v - vm ∈ box 1 n := by
          rw [hbox_mem]
          have hsub : (v - vm) 0 = v 0 - (m : ℤ) := by simp [vm]
          rw [hsub]
          obtain ⟨_, h2⟩ := hv
          push_cast at h2
          exact ⟨by linarith, by linarith⟩
        have heq : (v - vm) + vm = v := by ext i; simp [vm]
        have key : (⟨v, hv_orig⟩ : { x : Lat 1 // x ∈ box 1 (m + n) }) =
                   ⟨(v - vm) + vm, hshift_box (v - vm) hv_n⟩ :=
          Subtype.ext heq.symm
        rw [key]
        exact congr_fun (congr_arg Prod.snd hpq) ⟨v - vm, hv_n⟩
  unfold logN
  by_cases hb : N_X X (box 1 m) = 0
  · have ha : N_X X (box 1 (m + n)) = 0 := Nat.le_zero.mp (by simpa [hb] using hN)
    rw [ha, hb]
    push_cast
    rw [Real.log_zero]
    have : (0 : ℝ) ≤ Real.log (N_X X (box 1 n)) := Real.log_natCast_nonneg _
    linarith
  by_cases hc : N_X X (box 1 n) = 0
  · have ha : N_X X (box 1 (m + n)) = 0 := Nat.le_zero.mp (by simpa [hc] using hN)
    rw [ha, hc]
    push_cast
    rw [Real.log_zero]
    have : (0 : ℝ) ≤ Real.log (N_X X (box 1 m)) := Real.log_natCast_nonneg _
    linarith
  have hb' : (0 : ℝ) < (N_X X (box 1 m) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb
  have hc' : (0 : ℝ) < (N_X X (box 1 n) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc
  by_cases ha : N_X X (box 1 (m + n)) = 0
  · rw [ha]
    push_cast
    rw [Real.log_zero]
    have hpos1 : (0 : ℝ) ≤ Real.log (N_X X (box 1 m)) := Real.log_natCast_nonneg _
    have hpos2 : (0 : ℝ) ≤ Real.log (N_X X (box 1 n)) := Real.log_natCast_nonneg _
    linarith
  have ha' : (0 : ℝ) < (N_X X (box 1 (m + n)) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hN' : (N_X X (box 1 (m + n)) : ℝ) ≤
      (N_X X (box 1 m) : ℝ) * (N_X X (box 1 n) : ℝ) := by exact_mod_cast hN
  rw [← Real.log_mul (ne_of_gt hb') (ne_of_gt hc')]
  exact Real.log_le_log ha' hN'

/-! ## D4  Fekete_1d — Fekete's lemma in 1D (wrapper for Mathlib) -/

/-- Fekete's lemma in one dimension: a subadditive sequence bounded below has `u n / n`
    converging to `Subadditive.lim`. Wraps `Subadditive.tendsto_lim`. -/
theorem Fekete_1d {u : ℕ → ℝ} (h : Subadditive u)
    (hbdd : BddBelow (Set.range fun n => u n / n)) :
    Filter.Tendsto (fun n => u n / n) Filter.atTop (nhds h.lim) :=
  h.tendsto_lim hbdd

/-! ## D5  logN_div_pow_tendsto — `logN X n / n` converges in 1D -/

/-- For a 1D subshift `X` over a finite alphabet, `logN X n / n` converges to
    `(logN_subadditive X).lim`. -/
theorem logN_div_pow_tendsto {α : Type*} [Fintype α] [TopologicalSpace α]
    (X : Subshift α 1) :
    Filter.Tendsto (fun n => logN X n / n) Filter.atTop
      (nhds (logN_subadditive X).lim) := by
  apply Fekete_1d (logN_subadditive X)
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst hn; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    apply div_nonneg
    · exact Real.log_natCast_nonneg _
    · exact hn'.le

/-! ## E1  topEntropy — topological entropy of a subshift -/

/-- Topological entropy: the infimum of `logN X n / n^d` over `n ≥ 1`.
    For 1D subshifts, this equals `(logN_subadditive X).lim` by Fekete's lemma. -/
noncomputable def topEntropy {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) : ℝ :=
  sInf ((fun n : ℕ => logN X n / (n : ℝ) ^ d) '' Set.Ici 1)

/-! ## E2  topEntropy_nonneg -/

theorem topEntropy_nonneg {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) :
    0 ≤ topEntropy X := by
  apply le_csInf
  · exact Set.Nonempty.image _ ⟨1, Set.mem_Ici.mpr le_rfl⟩
  · rintro x ⟨n, hn, rfl⟩
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply div_nonneg (Real.log_natCast_nonneg _)
    positivity

/-! ## E3  topEntropy_fullShift -/

theorem topEntropy_fullShift {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α] :
    topEntropy (Subshift.univ α d) = Real.log (Fintype.card α) := by
  classical
  unfold topEntropy
  have hcount : ∀ n : ℕ, 1 ≤ n →
      N_X (Subshift.univ α d) (box d n) = (Fintype.card α) ^ (n ^ d) := by
    intro n hn
    unfold N_X
    by_cases hα : Nonempty α
    · have heq : {p : Pattern α (box d n) |
                  Pattern.GloballyAdmissible (Subshift.univ α d) p} = Set.univ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        refine ⟨fun v => if h : v ∈ box d n then p ⟨v, h⟩ else Classical.arbitrary α,
                Set.mem_univ _, 0, fun v => ?_⟩
        change (fun w => if h : w ∈ box d n then p ⟨w, h⟩ else Classical.arbitrary α)
                 (v.val + 0) = p v
        simp [v.property]
      rw [heq, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
          Fintype.card_coe, box_card]
    · rw [not_nonempty_iff] at hα
      haveI := hα
      have hb : (box d n).Nonempty := by
        rw [← Finset.card_pos, box_card]; positivity
      haveI : Nonempty ↥(box d n) := hb.coe_sort
      haveI : IsEmpty (Pattern α (box d n)) := inferInstance
      have hN : ({p : Pattern α (box d n) |
                  Pattern.GloballyAdmissible (Subshift.univ α d) p}).ncard = 0 := by
        rw [Set.ncard_eq_zero (Set.toFinite _)]
        ext p
        exact (IsEmpty.false p).elim
      rw [hN, Fintype.card_eq_zero, zero_pow (by positivity : n ^ d ≠ 0)]
  have hlogN : ∀ n ≥ 1,
      logN (Subshift.univ α d) n / (n : ℝ) ^ d = Real.log (Fintype.card α) := by
    intro n hn
    unfold logN
    rw [hcount n hn]
    have hnd_pos : (0 : ℝ) < (n : ℝ) ^ d := by
      have : (0 : ℝ) < n := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn |>.bot_lt
      positivity
    have hnd_ne : ((n : ℝ) ^ d) ≠ 0 := ne_of_gt hnd_pos
    push_cast
    rw [Real.log_pow]
    push_cast
    field_simp
  have himg : (fun n : ℕ => logN (Subshift.univ α d) n / (n : ℝ) ^ d) '' Set.Ici 1
            = {Real.log (Fintype.card α)} := by
    ext y
    simp only [Set.mem_image, Set.mem_Ici, Set.mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨n, hn, rfl⟩; exact hlogN n hn
    · intro hy; exact ⟨1, le_rfl, by rw [hlogN 1 le_rfl]; exact hy.symm⟩
  rw [himg]
  exact csInf_singleton _

/-! ## E4  topEntropy_antitone — entropy is monotone in subshift inclusion -/

theorem topEntropy_antitone {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    {X Y : Subshift α d} (hXY : X.carrier ⊆ Y.carrier) :
    topEntropy X ≤ topEntropy Y := by
  unfold topEntropy
  have hbdd : BddBelow ((fun n : ℕ => logN X n / (n : ℝ) ^ d) '' Set.Ici 1) := by
    refine ⟨0, ?_⟩
    rintro x ⟨k, hk, rfl⟩
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    apply div_nonneg (Real.log_natCast_nonneg _)
    positivity
  apply le_csInf
  · exact Set.Nonempty.image _ ⟨1, Set.mem_Ici.mpr le_rfl⟩
  rintro y ⟨n, hn, rfl⟩
  have hN : N_X X (box d n) ≤ N_X Y (box d n) := by
    unfold N_X
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro p ⟨x, hxX, u, happ⟩
    exact ⟨x, hXY hxX, u, happ⟩
  have hlog : logN X n ≤ logN Y n := by
    unfold logN
    by_cases hX_zero : N_X X (box d n) = 0
    · rw [hX_zero]; push_cast; rw [Real.log_zero]
      exact Real.log_natCast_nonneg _
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hX_zero
    · exact_mod_cast hN
  have hX_in : logN X n / (n : ℝ) ^ d ∈
      (fun n : ℕ => logN X n / (n : ℝ) ^ d) '' Set.Ici 1 := ⟨n, hn, rfl⟩
  calc sInf _ ≤ logN X n / (n : ℝ) ^ d := csInf_le hbdd hX_in
    _ ≤ logN Y n / (n : ℝ) ^ d := by gcongr

/-! ## F1  IsRightRE — right recursively enumerable real -/

/-- `h : ℝ` is right recursively enumerable if it is the limit of a computable sequence
    of rationals approaching from above. -/
def IsRightRE (h : ℝ) : Prop :=
  ∃ r : ℕ → ℚ, Computable r ∧ (∀ n, h ≤ (r n : ℝ)) ∧
    Filter.Tendsto (fun n => (r n : ℝ)) Filter.atTop (nhds h)

/-! ## F2  IsLeftRE — left recursively enumerable real -/

/-- `h : ℝ` is left recursively enumerable if it is the limit of a computable sequence
    of rationals approaching from below. -/
def IsLeftRE (h : ℝ) : Prop :=
  ∃ r : ℕ → ℚ, Computable r ∧ (∀ n, (r n : ℝ) ≤ h) ∧
    Filter.Tendsto (fun n => (r n : ℝ)) Filter.atTop (nhds h)

/-! ## F3  IsComputableReal — computable real -/

/-- `h : ℝ` is computable if there is a computable sequence of rationals
    approximating it with effective rate `1/(n+1)`. -/
def IsComputableReal (h : ℝ) : Prop :=
  ∃ q : ℕ → ℚ, Computable q ∧ ∀ n, |((q n : ℝ)) - h| ≤ 1 / (n + 1)
