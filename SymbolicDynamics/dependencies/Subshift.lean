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
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Subshift basics

Foundational types and operations for symbolic dynamics on `ℤ^d`:
- the lattice `Lat d = ℤ^d` with `ℓ∞` sup norm,
- the full shift `FullShift α d = α^{ℤ^d}` with shift action and Pi-topology,
- patterns on finite windows `Pattern α F`,
- closed shift-invariant subshifts `Subshift α d`,
- shifts of finite type via `mkSFT F L`,
- the discrete cube `box d n`, the global-pattern count `N_X`,
  `logN`, and topological entropy `topEntropy`.

Originally lived inside `papers/HochmanMeyerovitch/HochmanMeyerovitch.lean`;
moved here for reuse by other papers and open-problem formalizations
(e.g. `openProblems/WeissConjecture/`).
-/

/-! ## The lattice `Lat d` and the ℓ∞ sup-norm -/

/-- The additive group ℤ^d, used as the index lattice. -/
abbrev Lat (d : ℕ) := Fin d → ℤ

namespace Lat


/-- The ℓ∞ (sup) norm on ℤ^d: max of absolute values of coordinates.
    Returns 0 for d = 0. -/
def supNorm {d : ℕ} (u : Lat d) : ℤ :=
  ↑(Finset.univ.sup (fun i => (u i).natAbs))


@[simp]
theorem supNorm_zero {d : ℕ} : supNorm (0 : Lat d) = 0 := by
  simp only [supNorm, Pi.zero_apply, Int.natAbs_zero]
  norm_cast
  exact Finset.sup_bot Finset.univ


theorem supNorm_nonneg {d : ℕ} (u : Lat d) : 0 ≤ supNorm u := by
  simp only [supNorm]
  exact_mod_cast Nat.zero_le _


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

/-! ## The full shift `FullShift α d = α^{ℤ^d}` and the shift action -/

/-- The full shift: the set of all colorings of ℤ^d by alphabet α. -/
abbrev FullShift (α : Type*) (d : ℕ) := Lat d → α

namespace FullShift


@[ext]
lemma ext {α : Type*} {d : ℕ} {x y : FullShift α d} (h : ∀ v, x v = y v) : x = y :=
  funext h


/-- Shift a coloring by lattice vector `u`: `(shiftMap u x) v = x (v + u)`. -/
def shiftMap {α : Type*} {d : ℕ} (u : Lat d) (x : FullShift α d) : FullShift α d :=
  fun v => x (v + u)


@[simp]
theorem shiftMap_zero {α : Type*} {d : ℕ} (x : FullShift α d) : shiftMap 0 x = x := by
  ext v; simp only [shiftMap]; exact congr_arg x (add_zero v)


@[simp]
theorem shiftMap_add {α : Type*} {d : ℕ} (u v : Lat d) (x : FullShift α d) :
    shiftMap (u + v) x = shiftMap u (shiftMap v x) := by
  ext w; simp only [shiftMap]; exact congr_arg x (add_assoc w u v).symm


instance instAddAction {α : Type*} {d : ℕ} : AddAction (Lat d) (FullShift α d) where
  vadd u x := shiftMap u x
  zero_vadd x := shiftMap_zero x
  add_vadd u v x := shiftMap_add u v x


@[simp]
theorem vadd_eq_shiftMap {α : Type*} {d : ℕ} (u : Lat d) (x : FullShift α d) :
    u +ᵥ x = shiftMap u x := rfl


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

/-! ### Topology and measurable-space instances -/

instance instTopologicalSpace {α : Type*} {d : ℕ} [TopologicalSpace α] :
    TopologicalSpace (FullShift α d) := inferInstance

instance instCompactSpace {α : Type*} {d : ℕ} [TopologicalSpace α] [CompactSpace α] :
    CompactSpace (FullShift α d) := inferInstance

instance instT2Space {α : Type*} {d : ℕ} [TopologicalSpace α] [T2Space α] :
    T2Space (FullShift α d) := inferInstance


instance instMeasurableSpace {α : Type*} {d : ℕ} [MeasurableSpace α] :
    MeasurableSpace (FullShift α d) := inferInstance

instance instBorelSpace {α : Type*} {d : ℕ} [TopologicalSpace α] [MeasurableSpace α]
    [SecondCountableTopology α] [BorelSpace α] :
    BorelSpace (FullShift α d) := Pi.borelSpace


theorem shiftMap_continuous {α : Type*} {d : ℕ} [TopologicalSpace α] (u : Lat d) :
    Continuous (shiftMap u (α := α)) :=
  continuous_pi fun v => continuous_apply (v + u)


def shiftMap_homeomorph {α : Type*} {d : ℕ} [TopologicalSpace α] (u : Lat d) :
    FullShift α d ≃ₜ FullShift α d where
  toFun := shiftMap u
  invFun := shiftMap (-u)
  left_inv x := by rw [← shiftMap_add]; simp [neg_add_cancel]
  right_inv x := by rw [← shiftMap_add]; simp [add_neg_cancel]
  continuous_toFun := shiftMap_continuous u
  continuous_invFun := shiftMap_continuous (-u)

end FullShift

/-! ## Patterns on finite windows -/

/-- A pattern over alphabet `α` with support `F ⊆ ℤ^d`. -/
abbrev Pattern (α : Type*) {d : ℕ} (F : Finset (Lat d)) := F → α

namespace Pattern


/-- Restrict a coloring to a finite support. -/
def ofColoring {α : Type*} {d : ℕ} (F : Finset (Lat d)) (x : FullShift α d) : Pattern α F :=
  fun v => x v.val


/-- Restrict a pattern on `F` to a sub-finset `G ⊆ F`. -/
def restrict {α : Type*} {d : ℕ} {F : Finset (Lat d)} (G : Finset (Lat d)) (hGF : G ⊆ F)
    (p : Pattern α F) : Pattern α G :=
  fun v => p ⟨v.val, hGF v.property⟩


/-- Translate the support `F` by lattice vector `u`. -/
def translateFinset {d : ℕ} (u : Lat d) (F : Finset (Lat d)) : Finset (Lat d) :=
  F.image (· + u)


@[simp]
theorem mem_translateFinset {d : ℕ} {u : Lat d} {F : Finset (Lat d)} {v : Lat d} :
    v ∈ translateFinset u F ↔ v - u ∈ F := by
  simp only [translateFinset, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using hw
  · intro hv; exact ⟨v - u, hv, by simp⟩


def AppearsAt {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F)
    (x : FullShift α d) (u : Lat d) : Prop :=
  ∀ v : F, x (v.val + u) = p v


instance decidable_appearsAt {α : Type*} {d : ℕ} [DecidableEq α] {F : Finset (Lat d)}
    (p : Pattern α F) (x : FullShift α d) (u : Lat d) :
    Decidable (Pattern.AppearsAt p x u) :=
  Fintype.decidableForallFintype


def Appears {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F)
    (x : FullShift α d) : Prop :=
  ∃ u : Lat d, AppearsAt p x u

/-! ### Cylinder sets -/

def cylinder {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F) (u : Lat d) :
    Set (FullShift α d) :=
  {x | AppearsAt p x u}


@[simp]
theorem mem_cylinder_iff {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F)
    (u : Lat d) (x : FullShift α d) :
    x ∈ cylinder p u ↔ ∀ v : F, x (v.val + u) = p v :=
  Iff.rfl


theorem cylinder_isOpen {α : Type*} {d : ℕ} {F : Finset (Lat d)} [TopologicalSpace α]
    [DiscreteTopology α] (p : Pattern α F) (u : Lat d) :
    IsOpen (cylinder p u) := by
  simp only [cylinder, AppearsAt, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro v
  change IsOpen ((fun x : FullShift α d => x (v.val + u)) ⁻¹' {p v})
  exact (continuous_apply (v.val + u)).isOpen_preimage _ (isOpen_discrete _)


theorem cylinder_isClosed {α : Type*} {d : ℕ} {F : Finset (Lat d)} [TopologicalSpace α]
    [T1Space α] (p : Pattern α F) (u : Lat d) :
    IsClosed (cylinder p u) := by
  simp only [cylinder, AppearsAt, Set.setOf_forall]
  apply isClosed_iInter
  intro v
  change IsClosed ((fun x : FullShift α d => x (v.val + u)) ⁻¹' {p v})
  exact IsClosed.preimage (continuous_apply (v.val + u)) isClosed_singleton

/-! ### Pattern ↔ list bridge -/

/-- Encode a pattern as a list of its values along the canonical `F.toList` order.
Marked noncomputable because `Finset.toList` is noncomputable; used only for
equational reasoning, not as a runtime algorithm. -/
noncomputable def toList {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F) : List α :=
  F.toList.attach.map (fun b => p ⟨b.val, Finset.mem_toList.mp b.property⟩)

theorem toList_length {α : Type*} {d : ℕ} {F : Finset (Lat d)} (p : Pattern α F) :
    p.toList.length = F.card := by
  simp [Pattern.toList, Finset.length_toList]

/-! ### Disjoint union of patterns -/

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

/-! ## Subshifts -/

-- @ontology: hm:def:subshift
structure Subshift (α : Type*) (d : ℕ) [TopologicalSpace α] where
  carrier : Set (FullShift α d)
  isClosed : IsClosed carrier
  isInvariant : ∀ (u : Lat d) (x : FullShift α d), x ∈ carrier → FullShift.shiftMap u x ∈ carrier

namespace Subshift


instance instMembership {α : Type*} {d : ℕ} [TopologicalSpace α] :
    Membership (FullShift α d) (Subshift α d) where
  mem (X : Subshift α d) (x : FullShift α d) := x ∈ X.carrier


@[simp]
theorem mem_iff {α : Type*} {d : ℕ} [TopologicalSpace α]
    (X : Subshift α d) (x : FullShift α d) :
    x ∈ X ↔ x ∈ X.carrier :=
  Iff.rfl


def univ (α : Type*) (d : ℕ) [TopologicalSpace α] : Subshift α d where
  carrier := Set.univ
  isClosed := isClosed_univ
  isInvariant := fun _ _ _ => Set.mem_univ _


def bot (α : Type*) (d : ℕ) [TopologicalSpace α] : Subshift α d where
  carrier := ∅
  isClosed := isClosed_empty
  isInvariant := fun _ _ hx => absurd hx (Set.notMem_empty _)


def inter {α : Type*} {d : ℕ} [TopologicalSpace α]
    (X Y : Subshift α d) : Subshift α d where
  carrier := X.carrier ∩ Y.carrier
  isClosed := X.isClosed.inter Y.isClosed
  isInvariant := fun u x ⟨hxX, hxY⟩ =>
    ⟨X.isInvariant u x hxX, Y.isInvariant u x hxY⟩


def iInter {α : Type*} {d : ℕ} [TopologicalSpace α] {ι : Type*}
    (Xs : ι → Subshift α d) : Subshift α d where
  carrier := ⋂ i, (Xs i).carrier
  isClosed := isClosed_iInter (fun i => (Xs i).isClosed)
  isInvariant := fun u x hx =>
    Set.mem_iInter.mpr (fun i => (Xs i).isInvariant u x (Set.mem_iInter.mp hx i))

end Subshift

/-! ## Shifts of finite type (SFT) -/

/-- A coloring `x` is admissible for the syntax `(F, L)` if the F-pattern at every offset is in L.
-/
def SFT_admissible {α : Type*} {d : ℕ} (F : Finset (Lat d))
    (L : Finset (Pattern α F)) (x : FullShift α d) : Prop :=
  ∀ u : Lat d, Pattern.ofColoring F (FullShift.shiftMap u x) ∈ L


/-- The carrier set of the SFT with window `F` and syntax `L`. -/
def SFT_carrier {α : Type*} {d : ℕ} (F : Finset (Lat d))
    (L : Finset (Pattern α F)) : Set (FullShift α d) :=
  {x | SFT_admissible F L x}


theorem SFT_carrier_isInvariant {α : Type*} {d : ℕ} (F : Finset (Lat d))
    (L : Finset (Pattern α F)) :
    ∀ (u : Lat d) (x : FullShift α d), x ∈ SFT_carrier F L →
      FullShift.shiftMap u x ∈ SFT_carrier F L := by
  intro u x hx w
  simp only [SFT_carrier, Set.mem_setOf_eq, SFT_admissible] at hx ⊢
  show Pattern.ofColoring F (FullShift.shiftMap w (FullShift.shiftMap u x)) ∈ L
  rw [← FullShift.shiftMap_add]
  exact hx (w + u)


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


/-- The SFT with window `F` and allowed patterns `L`. -/
-- @ontology: hm:def:sft
def mkSFT {α : Type*} {d : ℕ} [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) : Subshift α d where
  carrier   := SFT_carrier F L
  isClosed  := SFT_carrier_isClosed F L
  isInvariant := SFT_carrier_isInvariant F L


@[simp]
theorem mem_mkSFT {α : Type*} {d : ℕ} [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (x : FullShift α d) :
    x ∈ mkSFT F L ↔ SFT_admissible F L x :=
  Iff.rfl


/-- A subshift `X : Subshift α d` is a **shift of finite type (SFT)** if
it equals `mkSFT F L` for some finite window `F` and finite list of
allowed `F`-patterns `L`. -/
def IsSFT {α : Type*} {d : ℕ} [TopologicalSpace α] [T1Space α]
    (X : Subshift α d) : Prop :=
  ∃ (F : Finset (Lat d)) (L : Finset (Pattern α F)),
    X.carrier = (mkSFT F L).carrier

/-- Every `mkSFT F L` is, by definition, an SFT. -/
theorem mkSFT_isSFT {α : Type*} {d : ℕ} [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) :
    IsSFT (mkSFT F L) := ⟨F, L, rfl⟩

/-! ## Globally admissible patterns and the count `N_X` -/

namespace Pattern

/-- Pattern `p` is globally admissible for `X` if it appears somewhere in
some point of `X`. -/
-- @ontology: hm:def:globally-admissible
def GloballyAdmissible {α : Type*} {d : ℕ} [TopologicalSpace α]
    {F : Finset (Lat d)} (X : Subshift α d) (p : Pattern α F) : Prop :=
  ∃ x ∈ X, Appears p x

end Pattern


/-- The number of globally admissible `F`-patterns in subshift `X`. -/
noncomputable def N_X {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) (F : Finset (Lat d)) : ℕ :=
  Set.ncard {p : Pattern α F | Pattern.GloballyAdmissible X p}

/-! ## Discrete cubes -/

/-- The discrete cube `{0,...,n-1}^d ⊆ ℤ^d`. -/
def box (d n : ℕ) : Finset (Lat d) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) (n : ℤ))

/-! ## Logarithmic count and topological entropy -/

/-- `logN X n` is `log (N_X X (box d n))`, the log of the count of globally
admissible patterns on the box `F_n = {0,...,n-1}^d`. -/
noncomputable def logN {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) (n : ℕ) : ℝ :=
  Real.log (N_X X (box d n))


/-- Topological entropy: the infimum of `logN X n / n^d` over `n ≥ 1`.
For 1D subshifts, this equals the Fekete limit of the subadditive sequence
`logN X`. -/
-- @ontology: hm:def:top-entropy
noncomputable def topEntropy {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) : ℝ :=
  sInf ((fun n : ℕ => logN X n / (n : ℝ) ^ d) '' Set.Ici 1)
