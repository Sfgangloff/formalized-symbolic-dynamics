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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Partrec
import Mathlib.Data.Rat.Denumerable
import SymbolicDynamics.Dependencies.ComputableRat

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

/-! ## supNorm_neg, supNorm_sub_comm -/

@[simp]
theorem supNorm_neg {d : ℕ} (u : Lat d) : Lat.supNorm (-u) = Lat.supNorm u := by
  unfold Lat.supNorm
  congr 1
  apply Finset.sup_congr rfl
  intros i _
  show ((-u) i).natAbs = (u i).natAbs
  rw [Pi.neg_apply]
  exact Int.natAbs_neg _

theorem supNorm_sub_comm {d : ℕ} (u v : Lat d) : Lat.supNorm (u - v) = Lat.supNorm (v - u) := by
  rw [show u - v = -(v - u) from by ring, supNorm_neg]

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

/-! ## decidable_appearsAt — AppearsAt is decidable for DecidableEq α -/

instance decidable_appearsAt {α : Type*} {d : ℕ} [DecidableEq α] {F : Finset (Lat d)}
    (p : Pattern α F) (x : FullShift α d) (u : Lat d) :
    Decidable (Pattern.AppearsAt p x u) :=
  Fintype.decidableForallFintype

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

/-! ## Pattern ↔ List bridge — uniform List α encoding via `Finset.toList` -/

/-- Encode a pattern as a list of its values along the canonical `F.toList` order.
Marked noncomputable because `Finset.toList` is noncomputable; used only for
equational reasoning, not as a runtime algorithm. -/
noncomputable def toList {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F) : List α :=
  F.toList.attach.map (fun b => p ⟨b.val, Finset.mem_toList.mp b.property⟩)

theorem toList_length {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F) :
    p.toList.length = F.card := by
  simp [Pattern.toList, Finset.length_toList]

/-! ## unionDisjoint — combine two patterns on disjoint supports -/

/-- Combine two patterns on disjoint Finsets into a pattern on their union. -/
def unionDisjoint {α : Type*} {d : ℕ} {A B : Finset (Lat d)}
    (p : Pattern α A) (q : Pattern α B) : Pattern α (A ∪ B) :=
  fun v =>
    if h : v.val ∈ A then p ⟨v.val, h⟩
    else q ⟨v.val, (Finset.mem_union.mp v.property).resolve_left h⟩

@[simp]
theorem unionDisjoint_left {α : Type*} {d : ℕ} {A B : Finset (Lat d)}
    (p : Pattern α A) (q : Pattern α B) (v : Lat d) (hv : v ∈ A) :
    unionDisjoint p q ⟨v, Finset.mem_union_left _ hv⟩ = p ⟨v, hv⟩ := by
  simp [unionDisjoint, hv]

theorem unionDisjoint_right {α : Type*} {d : ℕ} {A B : Finset (Lat d)}
    (hAB : Disjoint A B) (p : Pattern α A) (q : Pattern α B) (v : Lat d) (hv : v ∈ B) :
    unionDisjoint p q ⟨v, Finset.mem_union_right _ hv⟩ = q ⟨v, hv⟩ := by
  have hnA : v ∉ A := fun hA => (Finset.disjoint_left.mp hAB) hA hv
  simp [unionDisjoint, hnA]

theorem restrict_unionDisjoint_left {α : Type*} {d : ℕ} {A B : Finset (Lat d)}
    (p : Pattern α A) (q : Pattern α B) :
    Pattern.restrict A Finset.subset_union_left (Pattern.unionDisjoint p q) = p := by
  funext v
  exact Pattern.unionDisjoint_left p q v.val v.property

theorem restrict_unionDisjoint_right {α : Type*} {d : ℕ} {A B : Finset (Lat d)}
    (hAB : Disjoint A B) (p : Pattern α A) (q : Pattern α B) :
    Pattern.restrict B Finset.subset_union_right (Pattern.unionDisjoint p q) = q := by
  funext v
  exact Pattern.unionDisjoint_right hAB p q v.val v.property

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

/-! ## G4.1  relevantOffsets — finite set of offsets where F + u ⊆ E -/

/-- Finite set of offsets `u : Lat d` such that translating `F` by `u` keeps it within `E`.
For empty `F` this returns `{0}` as a placeholder (the locally-admissible condition is
then independent of `u`). -/
def relevantOffsets {d : ℕ} (F E : Finset (Lat d)) : Finset (Lat d) :=
  if F = ∅ then {(0 : Lat d)}
  else
    ((F ×ˢ E).image (fun p : Lat d × Lat d => p.2 - p.1)).filter
      (fun u => ∀ w ∈ F, w + u ∈ E)

/-! ## G4.2  locallyAdmissible_iff_relevantOffsets — finite reformulation -/

theorem locallyAdmissible_iff_relevantOffsets {α : Type*} {d : ℕ}
    {E : Finset (Lat d)} (F : Finset (Lat d)) (L : Finset (Pattern α F)) (a : Pattern α E) :
    locallyAdmissible F L a ↔
    ∀ u ∈ relevantOffsets F E, ∀ (h : ∀ v : F, v.val + u ∈ E),
      (fun v : F => a ⟨v.val + u, h v⟩) ∈ L := by
  constructor
  · intro hloc u _ h
    exact hloc u h
  · intro hloc u h
    by_cases hF : F = ∅
    · subst hF
      have h0_rel : (0 : Lat d) ∈ relevantOffsets (∅ : Finset (Lat d)) E := by
        unfold relevantOffsets
        rw [if_pos rfl]
        exact Finset.mem_singleton.mpr rfl
      have h0_triv : ∀ v : ((∅ : Finset (Lat d)) : Finset (Lat d)), v.val + 0 ∈ E :=
        fun v => absurd v.property (Finset.notMem_empty v.val)
      have h0_apply := hloc 0 h0_rel h0_triv
      have heq : (fun v : ((∅ : Finset (Lat d)) : Finset (Lat d)) => a ⟨v.val + u, h v⟩) =
          (fun v : ((∅ : Finset (Lat d)) : Finset (Lat d)) => a ⟨v.val + 0, h0_triv v⟩) := by
        funext v
        exact absurd v.property (Finset.notMem_empty v.val)
      rw [heq]; exact h0_apply
    · have hu_in : u ∈ relevantOffsets F E := by
        unfold relevantOffsets
        rw [if_neg hF, Finset.mem_filter]
        refine ⟨?_, fun w hw => h ⟨w, hw⟩⟩
        obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hF
        simp only [Finset.mem_image, Finset.mem_product]
        refine ⟨(v, v + u), ⟨hv, h ⟨v, hv⟩⟩, by simp⟩
      exact hloc u hu_in h

/-! ## G4.3  decidable_locallyAdmissible — decidable instance -/

instance decidable_locallyAdmissible {α : Type*} {d : ℕ} [DecidableEq α]
    {E : Finset (Lat d)} (F : Finset (Lat d)) (L : Finset (Pattern α F)) (a : Pattern α E) :
    Decidable (locallyAdmissible F L a) :=
  decidable_of_iff _ (locallyAdmissible_iff_relevantOffsets F L a).symm

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

/-! ## N_X_pos_iff_nonempty — N_X positive iff carrier is nonempty -/

theorem N_X_pos_iff_nonempty {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) (F : Finset (Lat d)) :
    0 < N_X X F ↔ X.carrier.Nonempty := by
  constructor
  · intro hpos
    rw [N_X, Set.ncard_pos] at hpos
    obtain ⟨_, x, hx, _⟩ := hpos
    exact ⟨x, hx⟩
  · exact N_X_pos_of_nonempty X F

/-! ## globallyAdmissible_restrict — restriction preserves global admissibility -/

theorem Pattern.globallyAdmissible_restrict {α : Type*} {d : ℕ} [TopologicalSpace α]
    {X : Subshift α d} {F : Finset (Lat d)} (G : Finset (Lat d)) (hGF : G ⊆ F)
    {p : Pattern α F} (hp : Pattern.GloballyAdmissible X p) :
    Pattern.GloballyAdmissible X (Pattern.restrict G hGF p) := by
  obtain ⟨x, hxX, u, happ⟩ := hp
  refine ⟨x, hxX, u, ?_⟩
  intro v
  exact happ ⟨v.val, hGF v.property⟩

/-! ## B6  N_X_mono_support — N_X monotone in support -/

/-- If `F ⊆ G`, then there are at most as many globally admissible `F`-patterns as
globally admissible `G`-patterns: every `F`-pattern arises as a restriction. -/
theorem N_X_mono_support {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) {F G : Finset (Lat d)} (hFG : F ⊆ G) :
    N_X X F ≤ N_X X G := by
  unfold N_X
  refine le_trans ?_ (Set.ncard_image_le (Set.toFinite _)
    (f := fun q : Pattern α G => Pattern.restrict F hFG q))
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro p ⟨x, hxX, u, happ⟩
  refine ⟨Pattern.ofColoring G (FullShift.shiftMap u x), ?_, ?_⟩
  · refine ⟨FullShift.shiftMap u x, X.isInvariant u x hxX, 0, ?_⟩
    intro v
    show (FullShift.shiftMap u x) (v.val + 0) = (FullShift.shiftMap u x) v.val
    simp
  · funext v
    show (FullShift.shiftMap u x) v.val = p v
    have : (FullShift.shiftMap u x) v.val = x (v.val + u) := by simp [FullShift.shiftMap]
    rw [this]
    exact happ v

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

/-! ## C4a  boxIndex — computable enumeration of `box d n` via base-n digits -/

/-- The `i`-th element of `box d n` under the canonical base-`n` digit enumeration. -/
def boxIndex (d n i : ℕ) : Lat d :=
  fun j : Fin d => ((i / n ^ j.val) % n : ℤ)

theorem boxIndex_mem {d n i : ℕ} (hi : i < n ^ d) : boxIndex d n i ∈ box d n := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Ico]
  intro j
  -- If n = 0 then n^d = 0 (since d ≥ 1, witnessed by j) so i < 0, contradiction.
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hd_pos : 0 < d := j.pos
      rw [zero_pow hd_pos.ne'] at hi
      exact absurd hi (Nat.not_lt_zero _)
    · exact hn
  show 0 ≤ ((i / n ^ j.val) % n : ℤ) ∧ ((i / n ^ j.val) % n : ℤ) < (n : ℤ)
  refine ⟨Int.ofNat_nonneg _, ?_⟩
  exact_mod_cast Nat.mod_lt _ hn_pos

/-! ## C5  symBox  Q_n = {-n,...,n}^d -/

/-- The symmetric cube `Q_n = {-n,...,n}^d ⊆ ℤ^d`. -/
def symBox (d n : ℕ) : Finset (Lat d) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) (n : ℤ))

/-! ## C6  symBox_card  -/

@[simp]
theorem symBox_card (d n : ℕ) : (symBox d n).card = (2 * n + 1) ^ d := by
  simp only [symBox, Fintype.card_piFinset, Int.card_Icc]
  have h_each : ((n : ℤ) + 1 + (n : ℤ)).toNat = 2 * n + 1 := by
    have heq : ((n : ℤ) + 1 + (n : ℤ)) = ((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [heq, Int.toNat_natCast]
  rw [Finset.prod_const]
  simp [h_each]

/-! ## C7  symBox_mono  -/

theorem symBox_mono {d m n : ℕ} (hmn : m ≤ n) : symBox d m ⊆ symBox d n :=
  Fintype.piFinset_subset _ _ (fun _ => Finset.Icc_subset_Icc
    (by exact_mod_cast neg_le_neg (by exact_mod_cast hmn))
    (by exact_mod_cast hmn))

/-! ## C8  box_subset_symBox  box d (n+1) ⊆ symBox d n -/

theorem box_subset_symBox {d n : ℕ} : box d (n + 1) ⊆ symBox d n := by
  intro u hu
  simp only [box, symBox, Fintype.mem_piFinset, Finset.mem_Ico, Finset.mem_Icc] at hu ⊢
  intro i
  obtain ⟨h1, h2⟩ := hu i
  refine ⟨?_, ?_⟩
  · have : -(n : ℤ) ≤ 0 := by linarith [Int.ofNat_nonneg n]
    linarith
  · push_cast at h2
    linarith

/-! ## C9  Pattern.rCompatible — r-compatibility of two symmetric-cube patterns -/

/-- Patterns `a : Pattern α (Q_k)` and `b : Pattern α (Q_N)` are `r`-compatible (with
respect to subshift `X`) if `k + r + 1 ≤ N` and the joined pattern with `a` on the
inner cube `Q_k` and `b` on the outer ring `Q_N \ Q_{k+r}` is globally admissible
in `X`. The "gap" `Q_{k+r} \ Q_k` is left unconstrained. -/
def Pattern.rCompatible {α : Type*} {d : ℕ} [TopologicalSpace α]
    (X : Subshift α d) (r : ℕ) {k N : ℕ}
    (a : Pattern α (symBox d k)) (b : Pattern α (symBox d N)) : Prop :=
  k + r + 1 ≤ N ∧
  Pattern.GloballyAdmissible X
    (Pattern.unionDisjoint a
      (Pattern.restrict (symBox d N \ symBox d (k + r)) Finset.sdiff_subset b))

/-! ## C10  rCompatible_imp_globallyAdmissible — inner pattern is globally admissible -/

/-- If `a` is `r`-compatible with some `b`, then `a` itself is globally admissible. -/
theorem Pattern.rCompatible.globallyAdmissible {α : Type*} {d : ℕ} [TopologicalSpace α]
    {X : Subshift α d} {r k N : ℕ} {a : Pattern α (symBox d k)} {b : Pattern α (symBox d N)}
    (h : Pattern.rCompatible X r a b) :
    Pattern.GloballyAdmissible X a := by
  obtain ⟨x, hxX, u, happ⟩ := h.2
  refine ⟨x, hxX, u, ?_⟩
  intro v
  have hv : v.val ∈ symBox d k ∪ (symBox d N \ symBox d (k + r)) :=
    Finset.mem_union_left _ v.property
  have hu := happ ⟨v.val, hv⟩
  rwa [Pattern.unionDisjoint_left a _ v.val v.property] at hu

/-! ## C11  symBox_disjoint_sdiff — Q_k disjoint from Q_N \ Q_{k+r} -/

theorem symBox_disjoint_sdiff {d k r N : ℕ} :
    Disjoint (symBox d k) (symBox d N \ symBox d (k + r)) := by
  apply Finset.disjoint_left.mpr
  intro x hxk hxN
  exact (Finset.mem_sdiff.mp hxN).2 (symBox_mono (Nat.le_add_right k r) hxk)

/-! ## globallyAdmissible_iff_appearsAt_zero — normalize to offset 0 via shift -/

theorem Pattern.globallyAdmissible_iff_appearsAt_zero {α : Type*} {d : ℕ}
    [TopologicalSpace α] {X : Subshift α d} {F : Finset (Lat d)} (p : Pattern α F) :
    Pattern.GloballyAdmissible X p ↔ ∃ x ∈ X, Pattern.AppearsAt p x 0 := by
  constructor
  · rintro ⟨x, hx, u, happ⟩
    refine ⟨FullShift.shiftMap u x, X.isInvariant u x hx, ?_⟩
    intro v
    have : (FullShift.shiftMap u x) (v.val + 0) = x (v.val + u) := by
      simp [FullShift.shiftMap]
    rw [this]
    exact happ v
  · rintro ⟨x, hx, happ⟩
    exact ⟨x, hx, 0, happ⟩

/-! ## C12  supNorm separation between Q_k and Q_N \ Q_{k+r} -/

/-- For `u ∈ Q_k` and `v ∈ Q_N \ Q_{k+r}`, the supremum-norm distance is at least `r + 1`. -/
theorem Lat.supNorm_sub_ge_of_inner_outer {d k r N : ℕ}
    (u v : Lat d) (hu : u ∈ symBox d k) (hv : v ∈ symBox d N \ symBox d (k + r)) :
    (r + 1 : ℤ) ≤ Lat.supNorm (v - u) := by
  obtain ⟨_, hvNotKr⟩ := Finset.mem_sdiff.mp hv
  have h_exists : ∃ i, (k + r : ℤ) < |v i| := by
    by_contra h_all
    push_neg at h_all
    apply hvNotKr
    simp only [symBox, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have hi := h_all i
    rw [abs_le] at hi
    push_cast
    exact hi
  obtain ⟨i, hi⟩ := h_exists
  simp only [symBox, Fintype.mem_piFinset, Finset.mem_Icc] at hu
  obtain ⟨hu_l, hu_h⟩ := hu i
  have hu_abs : |u i| ≤ (k : ℤ) := abs_le.mpr ⟨hu_l, hu_h⟩
  have h_diff : (r + 1 : ℤ) ≤ |v i - u i| := by
    have h1 : |v i| - |u i| ≤ |v i - u i| := abs_sub_abs_le_abs_sub _ _
    linarith
  -- Bridge to natAbs and supNorm
  have h_natabs_eq : (v i - u i).natAbs = |v i - u i|.toNat := by
    rw [Int.abs_eq_natAbs, Int.toNat_natCast]
  have h_natabs_ge : (r + 1 : ℕ) ≤ (v i - u i).natAbs := by
    have hnn : 0 ≤ |v i - u i| := abs_nonneg _
    have h_cast : ((v i - u i).natAbs : ℤ) = |v i - u i| := by
      rw [Int.abs_eq_natAbs]
    have : ((r + 1 : ℕ) : ℤ) ≤ ((v i - u i).natAbs : ℤ) := by rw [h_cast]; exact_mod_cast h_diff
    exact_mod_cast this
  -- (v - u) i = v i - u i in Lat d
  unfold Lat.supNorm
  have h_sup_ge : (v i - u i).natAbs ≤ Finset.univ.sup (fun j => ((v - u) j).natAbs) := by
    have h := Finset.le_sup (s := Finset.univ) (f := fun j => ((v - u) j).natAbs)
      (Finset.mem_univ i)
    show ((v - u) i).natAbs ≤ _
    exact h
  exact_mod_cast Nat.le_trans h_natabs_ge h_sup_ge

/-! ## C13  rCompatible_of_irreducible — irreducibility yields r-compatibility -/

/-- If `X` is `r`-irreducible, `a : Pattern α (Q_k)` is globally admissible, and the
restriction of `b : Pattern α (Q_N)` to the outer ring `Q_N \ Q_{k+r}` is globally
admissible, and `k + r + 1 ≤ N`, then `a` and `b` are `r`-compatible. -/
theorem Pattern.rCompatible_of_irreducible {α : Type*} {d : ℕ} [TopologicalSpace α]
    {X : Subshift α d} {r k N : ℕ} (hkN : k + r + 1 ≤ N) (hirr : ShiftIrreducible X r)
    (a : Pattern α (symBox d k)) (b : Pattern α (symBox d N))
    (ha : Pattern.GloballyAdmissible X a)
    (hb_outer : Pattern.GloballyAdmissible X
      (Pattern.restrict (symBox d N \ symBox d (k + r)) Finset.sdiff_subset b)) :
    Pattern.rCompatible X r a b := by
  refine ⟨hkN, ?_⟩
  rw [Pattern.globallyAdmissible_iff_appearsAt_zero] at ha hb_outer
  have h_sep : ∀ u ∈ symBox d k, ∀ v ∈ symBox d N \ symBox d (k + r),
      (r : ℤ) ≤ Lat.supNorm (u - v) := by
    intro u hu v hv
    have h := Lat.supNorm_sub_ge_of_inner_outer u v hu hv
    rw [Lat.supNorm_sub_comm]
    linarith
  obtain ⟨x, hxX, ha_app, hb_app⟩ := hirr (symBox d k) (symBox d N \ symBox d (k + r))
    h_sep a (Pattern.restrict _ Finset.sdiff_subset b) ha hb_outer
  rw [Pattern.globallyAdmissible_iff_appearsAt_zero]
  refine ⟨x, hxX, ?_⟩
  intro v
  by_cases hv : v.val ∈ symBox d k
  · rw [Pattern.unionDisjoint_left a _ v.val hv]
    exact ha_app ⟨v.val, hv⟩
  · have hv_outer : v.val ∈ symBox d N \ symBox d (k + r) :=
      (Finset.mem_union.mp v.property).resolve_left hv
    rw [Pattern.unionDisjoint_right symBox_disjoint_sdiff a _ v.val hv_outer]
    exact hb_app ⟨v.val, hv_outer⟩

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

/-! ## topEntropy_bot — empty subshift has zero entropy -/

theorem topEntropy_bot {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α] :
    topEntropy (Subshift.bot α d) = 0 := by
  unfold topEntropy
  have h_zero : ∀ n : ℕ, 1 ≤ n →
      logN (Subshift.bot α d) n / (n : ℝ) ^ d = 0 := by
    intro n _
    unfold logN N_X
    have hempty : {p : Pattern α (box d n) |
        Pattern.GloballyAdmissible (Subshift.bot α d) p} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨x, hx, _⟩
      exact absurd hx (Set.notMem_empty _)
    rw [hempty, Set.ncard_empty, Nat.cast_zero, Real.log_zero, zero_div]
  have himg : (fun n : ℕ => logN (Subshift.bot α d) n / (n : ℝ) ^ d) '' Set.Ici 1 = {0} := by
    ext y
    simp only [Set.mem_image, Set.mem_Ici, Set.mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨n, hn, rfl⟩; exact h_zero n hn
    · intro hy; exact ⟨1, le_rfl, by rw [h_zero 1 le_rfl]; exact hy.symm⟩
  rw [himg]
  exact csInf_singleton _

/-! ## topEntropy_inter_le — entropy of intersection is at most min -/

theorem topEntropy_inter_le_left {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X Y : Subshift α d) :
    topEntropy (Subshift.inter X Y) ≤ topEntropy X :=
  topEntropy_antitone Set.inter_subset_left

theorem topEntropy_inter_le_right {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X Y : Subshift α d) :
    topEntropy (Subshift.inter X Y) ≤ topEntropy Y :=
  topEntropy_antitone Set.inter_subset_right

/-! ## E5  topEntropy_le_log_card — universal upper bound -/

/-- Every subshift's topological entropy is bounded by `log |α|`. -/
theorem topEntropy_le_log_card {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) :
    topEntropy X ≤ Real.log (Fintype.card α) := by
  rw [← topEntropy_fullShift (α := α) (d := d)]
  exact topEntropy_antitone (Set.subset_univ _)

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

/-! ## G1  locallyAdmissiblePatterns — finset of locally admissible E-patterns -/

/-- The finset of patterns over `E` that are locally admissible for syntax `(F, L)`. -/
def locallyAdmissiblePatterns {α : Type*} [Fintype α] [DecidableEq α] {d : ℕ}
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (E : Finset (Lat d)) :
    Finset (Pattern α E) :=
  (Finset.univ : Finset (Pattern α E)).filter (locallyAdmissible F L)

/-! ## G2  N_bar — number of locally admissible n-box patterns -/

/-- `N_bar F L n` is the number of locally admissible `box d n`-patterns for syntax `(F, L)`. -/
def N_bar {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) : ℕ :=
  (locallyAdmissiblePatterns F L (box d n)).card

/-! ## F4a  computable_imp_leftRE — every computable real is left r.e. -/

theorem computable_imp_leftRE {h : ℝ} (hcomp : IsComputableReal h) : IsLeftRE h := by
  obtain ⟨q, hq_comp, hq_close⟩ := hcomp
  refine ⟨fun n => q n - (1 : ℚ) / ((n : ℚ) + 1),
    ComputableRat.computable_sub_one_div_succ hq_comp, ?_, ?_⟩
  · intro n
    have habs := hq_close n
    have h1 := (abs_le.mp habs).2
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    push_cast
    linarith
  · have h_bias : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have hbase := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
      refine hbase.congr (fun n => ?_)
      simp [Function.comp]
    have h_q : Filter.Tendsto (fun n : ℕ => (q n : ℝ)) Filter.atTop (nhds h) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h_bias) ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hb := hN n hn
      have hclose := hq_close n
      rw [Real.dist_eq] at hb ⊢
      have h_bias_eq : (1 : ℝ) / ((n : ℝ) + 1) - 0 = 1 / ((n : ℝ) + 1) := by ring
      rw [h_bias_eq] at hb
      have h_bias_nn : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      have h_bias_abs : |(1 : ℝ) / ((n : ℝ) + 1)| = 1 / ((n : ℝ) + 1) := abs_of_nonneg h_bias_nn
      rw [h_bias_abs] at hb
      calc |((q n : ℝ)) - h| ≤ 1 / ((n : ℝ) + 1) := hclose
        _ < ε := hb
    have hsum : Filter.Tendsto (fun n : ℕ => (q n : ℝ) - 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds (h - 0)) := h_q.sub h_bias
    rw [sub_zero] at hsum
    convert hsum using 1
    ext n
    push_cast
    ring

/-! ## F4  computable_imp_rightRE — every computable real is right r.e. -/

theorem computable_imp_rightRE {h : ℝ} (hcomp : IsComputableReal h) : IsRightRE h := by
  obtain ⟨q, hq_comp, hq_close⟩ := hcomp
  refine ⟨fun n => q n + (1 : ℚ) / ((n : ℚ) + 1),
    ComputableRat.computable_add_one_div_succ hq_comp, ?_, ?_⟩
  · intro n
    have habs := hq_close n
    have h1 := (abs_le.mp habs).1
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    push_cast
    linarith
  · have h_bias : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have hbase := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
      refine hbase.congr (fun n => ?_)
      simp [Function.comp]
    have h_q : Filter.Tendsto (fun n : ℕ => (q n : ℝ)) Filter.atTop (nhds h) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h_bias) ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hb := hN n hn
      have hclose := hq_close n
      rw [Real.dist_eq] at hb ⊢
      have h_bias_eq : (1 : ℝ) / ((n : ℝ) + 1) - 0 = 1 / ((n : ℝ) + 1) := by ring
      rw [h_bias_eq] at hb
      have h_bias_nn : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      have h_bias_abs : |(1 : ℝ) / ((n : ℝ) + 1)| = 1 / ((n : ℝ) + 1) := abs_of_nonneg h_bias_nn
      rw [h_bias_abs] at hb
      calc |((q n : ℝ)) - h| ≤ 1 / ((n : ℝ) + 1) := hclose
        _ < ε := hb
    have hsum : Filter.Tendsto (fun n : ℕ => (q n : ℝ) + 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds (h + 0)) := h_q.add h_bias
    rw [add_zero] at hsum
    convert hsum using 1
    ext n
    push_cast
    ring

/-! ## F5  computable_iff_leftRE_and_rightRE -/

theorem computable_iff_leftRE_and_rightRE {h : ℝ} :
    IsComputableReal h ↔ IsLeftRE h ∧ IsRightRE h := by
  refine ⟨fun hcomp => ⟨computable_imp_leftRE hcomp, computable_imp_rightRE hcomp⟩, ?_⟩
  rintro ⟨⟨ℓ, hℓ_comp, hℓ_below, hℓ_lim⟩, ⟨r, hr_comp, hr_above, hr_lim⟩⟩
  set P : ℕ → ℕ → Bool :=
    fun n k => decide (r k ≤ ℓ k + (1 : ℚ) / ((n : ℚ) + 1)) with hP_def
  have hP_comp : Computable₂ P := by
    have h_le_pr : Primrec₂ (fun (a b : ℚ) => decide (a ≤ b)) :=
      PrimrecRel.decide ComputableRat.primrec_rat_le
    have h_le : Computable₂ (fun (a b : ℚ) => decide (a ≤ b)) := h_le_pr.to_comp
    have h_add : Computable₂ (fun (q' : ℚ) (n : ℕ) => q' + (1 : ℚ) / ((n : ℚ) + 1)) :=
      ComputableRat.primrec_add_one_div_succ.to_comp
    have h_lk : Computable₂ (fun (_ k : ℕ) => ℓ k) :=
      hℓ_comp.comp Computable.snd
    have h_rk : Computable₂ (fun (_ k : ℕ) => r k) :=
      hr_comp.comp Computable.snd
    have h_n_proj : Computable₂ (fun (n _ : ℕ) => n) := Computable.fst
    have h_lkadd : Computable₂ (fun (n k : ℕ) => ℓ k + (1 : ℚ) / ((n : ℚ) + 1)) :=
      h_add.comp₂ h_lk h_n_proj
    exact h_le.comp₂ h_rk h_lkadd
  have hP_exists : ∀ n : ℕ, ∃ k : ℕ, P n k = true := by
    intro n
    have hr_sub_l : Filter.Tendsto (fun k : ℕ => (r k : ℝ) - (ℓ k : ℝ))
        Filter.atTop (nhds 0) := by
      have hsub := hr_lim.sub hℓ_lim
      simpa using hsub
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [Metric.tendsto_atTop] at hr_sub_l
    obtain ⟨K, hK⟩ := hr_sub_l (1 / ((n : ℝ) + 1)) hpos
    refine ⟨K, ?_⟩
    rw [hP_def]
    apply decide_eq_true
    have hK_val := hK K (le_refl K)
    rw [Real.dist_eq] at hK_val
    have h_diff_nn : (0 : ℝ) ≤ (r K : ℝ) - (ℓ K : ℝ) := by
      linarith [hr_above K, hℓ_below K]
    have hK_val' : (r K : ℝ) - (ℓ K : ℝ) < 1 / ((n : ℝ) + 1) := by
      have heq : (r K : ℝ) - (ℓ K : ℝ) - 0 = (r K : ℝ) - (ℓ K : ℝ) := by ring
      rw [heq] at hK_val
      rw [abs_of_nonneg h_diff_nn] at hK_val
      exact hK_val
    have h_cast : ((ℓ K + (1 : ℚ) / ((n : ℚ) + 1) : ℚ) : ℝ) =
        (ℓ K : ℝ) + 1 / ((n : ℝ) + 1) := by push_cast; ring
    have h_real : (r K : ℝ) ≤ ((ℓ K + (1 : ℚ) / ((n : ℚ) + 1) : ℚ) : ℝ) := by
      rw [h_cast]; linarith
    exact_mod_cast h_real
  let f : ℕ → ℕ := fun n => Nat.find (hP_exists n)
  have hf_comp : Computable f := by
    have h_partrec : Partrec (fun n : ℕ => Nat.rfind (fun k : ℕ => (P n k : Part Bool))) :=
      Partrec.rfind hP_comp.partrec₂
    refine Partrec.of_eq_tot h_partrec ?_
    intro n
    rw [Nat.mem_rfind]
    refine ⟨?_, ?_⟩
    · have hspec : P n (Nat.find (hP_exists n)) = true := Nat.find_spec (hP_exists n)
      exact Part.mem_some_iff.mpr hspec.symm
    · intro m hm
      have hnot : ¬ P n m = true := Nat.find_min (hP_exists n) hm
      have hfalse : P n m = false := by
        cases hcase : P n m
        · rfl
        · exact absurd hcase hnot
      rw [hfalse]
      exact Part.mem_some_iff.mpr rfl
  refine ⟨fun n => ℓ (f n), hℓ_comp.comp hf_comp, fun n => ?_⟩
  have hf_spec : P n (f n) = true := Nat.find_spec (hP_exists n)
  rw [hP_def] at hf_spec
  have hf_rat : r (f n) ≤ ℓ (f n) + (1 : ℚ) / ((n : ℚ) + 1) := of_decide_eq_true hf_spec
  have h_cast : ((ℓ (f n) + (1 : ℚ) / ((n : ℚ) + 1) : ℚ) : ℝ) =
      (ℓ (f n) : ℝ) + 1 / ((n : ℝ) + 1) := by push_cast; ring
  have hf_real : (r (f n) : ℝ) ≤ (ℓ (f n) : ℝ) + 1 / ((n : ℝ) + 1) := by
    have : ((r (f n) : ℚ) : ℝ) ≤ ((ℓ (f n) + (1 : ℚ) / ((n : ℚ) + 1) : ℚ) : ℝ) := by
      exact_mod_cast hf_rat
    rw [h_cast] at this; exact this
  have hℓ_le : (ℓ (f n) : ℝ) ≤ h := hℓ_below (f n)
  have hr_ge : h ≤ (r (f n) : ℝ) := hr_above (f n)
  have hh_le : h ≤ (ℓ (f n) : ℝ) + 1 / ((n : ℝ) + 1) := hr_ge.trans hf_real
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-! ## G3  N_X_le_N_bar — globally admissible count is bounded by local count -/

/-- For the SFT `mkSFT F L`, every globally admissible box-pattern is locally admissible,
    so `N_X (mkSFT F L) (box d n) ≤ N_bar F L n`. -/
theorem N_X_le_N_bar {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) :
    N_X (mkSFT F L) (box d n) ≤ N_bar F L n := by
  unfold N_X N_bar
  rw [← Set.ncard_coe_finset (locallyAdmissiblePatterns F L (box d n))]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro p hp
  simp only [locallyAdmissiblePatterns, Finset.coe_filter, Finset.mem_univ, true_and,
    Set.mem_setOf_eq]
  exact Pattern.globally_imp_locally F L p hp

/-! ## G4.4d  N_bar_eq_fintype_card_subtype — alternative formulation -/

/-- `N_bar F L n` equals the cardinality of the subtype of locally admissible
n-box patterns. Useful for transferring to alternative formulations. -/
theorem N_bar_eq_fintype_card_subtype {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) :
    N_bar F L n =
      Fintype.card { p : Pattern α (box d n) // locallyAdmissible F L p } := by
  unfold N_bar locallyAdmissiblePatterns
  exact (Fintype.subtype_card (Finset.univ.filter (locallyAdmissible F L))
    (by intro p; simp)).symm

/-! ## G4.4a  N_bar_le_card_pow — trivial bound -/

/-- The number of locally admissible n-box patterns is at most `|α|^(n^d)`. -/
theorem N_bar_le_card_pow {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) :
    N_bar F L n ≤ (Fintype.card α) ^ (n ^ d) := by
  unfold N_bar locallyAdmissiblePatterns
  calc (Finset.univ.filter (locallyAdmissible F L)).card
      ≤ (Finset.univ : Finset (Pattern α (box d n))).card := Finset.card_filter_le _ _
    _ = Fintype.card (Pattern α (box d n)) := Finset.card_univ
    _ = Fintype.card α ^ Fintype.card ↥(box d n) := Fintype.card_fun
    _ = Fintype.card α ^ (n ^ d) := by rw [Fintype.card_coe, box_card]

/-! ## G4.4b  N_bar_mono — monotone in the allowed patterns -/

/-- `N_bar` is monotone in the allowed-patterns set `L`: more permitted patterns
gives more locally admissible n-box patterns. -/
theorem N_bar_mono {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    (F : Finset (Lat d)) {L₁ L₂ : Finset (Pattern α F)} (hL : L₁ ⊆ L₂) (n : ℕ) :
    N_bar F L₁ n ≤ N_bar F L₂ n := by
  unfold N_bar locallyAdmissiblePatterns
  refine Finset.card_le_card ?_
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  intro u hu
  exact hL (hp.2 u hu)
