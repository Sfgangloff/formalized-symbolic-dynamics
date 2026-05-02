import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Basic

/-!
# Symbolic Dynamics — Foundational Definitions

This file formalizes the basic objects of symbolic dynamics following
Hochman–Meyerovitch (arXiv:math/0703206):

  * `Lattice d`       — the group ℤ^d
  * `FullShift Σ d`   — the full shift Σ^{ℤ^d}
  * `FullShift.shiftMap` — the ℤ^d shift action σ^u
  * `Pattern Σ F`     — a coloring of a finite subset F ⊆ ℤ^d
  * `Subshift`        — closed shift-invariant subset
  * `SFT_admissible`  — global admissibility for a syntax L
  * `mkSFT`           — packages an SFT as a Subshift
  * `Irreducible`     — irreducibility condition with gap r
-/

/-! ## The Lattice ℤ^d -/

/-- The group ℤ^d, used as the index lattice for all symbolic systems. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

namespace Lattice

instance instAddCommGroup (d : ℕ) : AddCommGroup (Lattice d) :=
  Pi.addCommGroup

/-- The ℓ∞ (sup) norm on ℤ^d. -/
def supNorm {d : ℕ} (u : Lattice d) : ℤ :=
  if h : d = 0 then 0
  else Finset.sup' Finset.univ ⟨⟨0, Nat.pos_of_ne_zero h⟩, Finset.mem_univ _⟩ (fun i => |u i|)

@[simp]
theorem supNorm_zero {d : ℕ} : supNorm (0 : Lattice d) = 0 := by
  simp [supNorm]
  split_ifs with h
  · rfl
  · apply le_antisymm
    · apply Finset.sup'_le
      simp
    · apply le_refl

theorem supNorm_nonneg {d : ℕ} (u : Lattice d) : 0 ≤ supNorm u := by
  simp [supNorm]
  split_ifs with h
  · exact le_refl 0
  · apply Finset.le_sup'
    intro i _
    exact abs_nonneg _

end Lattice

/-! ## The Full Shift -/

/-- The full shift Σ^{ℤ^d}: all colorings of the lattice ℤ^d by alphabet Σ. -/
def FullShift (Σ : Type*) (d : ℕ) : Type* := Lattice d → Σ

namespace FullShift

variable {Σ : Type*} {d : ℕ}

/-- The shift map σ^u: (σ^u x)(v) = x(v + u). -/
def shiftMap (u : Lattice d) (x : FullShift Σ d) : FullShift Σ d :=
  fun v => x (v + u)

@[simp]
theorem shiftMap_zero (x : FullShift Σ d) : shiftMap 0 x = x := by
  ext v; simp [shiftMap]

theorem shiftMap_add (u v : Lattice d) (x : FullShift Σ d) :
    shiftMap (u + v) x = shiftMap u (shiftMap v x) := by
  ext w; simp [shiftMap, add_assoc]

/-- The shift maps give an additive action of ℤ^d on the full shift. -/
instance instAddAction : AddAction (Lattice d) (FullShift Σ d) where
  vadd u x     := shiftMap u x
  zero_vadd x  := shiftMap_zero x
  add_vadd u v x := shiftMap_add u v x

theorem vadd_eq_shiftMap (u : Lattice d) (x : FullShift Σ d) :
    u +ᵥ x = shiftMap u x := rfl

/-- Each shift map is bijective. -/
theorem shiftMap_bijective (u : Lattice d) :
    Function.Bijective (shiftMap u (Σ := Σ)) :=
  ⟨fun x y h => by ext v; simpa [shiftMap, sub_add_cancel] using congr_fun h (v - u),
   fun y => ⟨shiftMap (-u) y, by ext v; simp [shiftMap, add_assoc]⟩⟩

/-- When Σ carries the discrete topology, FullShift Σ d gets the product topology. -/
instance [TopologicalSpace Σ] : TopologicalSpace (FullShift Σ d) :=
  Pi.topologicalSpace

/-- When Σ is a finite discrete type, the full shift is compact (Tychonoff). -/
instance [Fintype Σ] [TopologicalSpace Σ] [DiscreteTopology Σ] :
    CompactSpace (FullShift Σ d) :=
  Pi.compactSpace

/-- When Σ is T2, so is FullShift Σ d. -/
instance [TopologicalSpace Σ] [T2Space Σ] : T2Space (FullShift Σ d) :=
  Pi.t2Space

/-- Each shift map is continuous. -/
theorem shiftMap_continuous [TopologicalSpace Σ] (u : Lattice d) :
    Continuous (shiftMap u (Σ := Σ)) :=
  continuous_pi fun v => continuous_apply _

end FullShift

/-! ## Patterns -/

/-- A pattern over F ⊆ ℤ^d is a coloring of F by Σ. -/
def Pattern (Σ : Type*) {d : ℕ} (F : Finset (Lattice d)) : Type* :=
  F → Σ

namespace Pattern

variable {Σ : Type*} {d : ℕ}

/-- Restrict a global coloring x to the finite window F. -/
def ofColoring (x : FullShift Σ d) (F : Finset (Lattice d)) : Pattern Σ F :=
  fun ⟨v, _⟩ => x v

/-- Restrict a pattern on F to a subset E. -/
def restrict {E F : Finset (Lattice d)} (hEF : E ⊆ F) (a : Pattern Σ F) : Pattern Σ E :=
  fun ⟨v, hv⟩ => a ⟨v, hEF hv⟩

/-- The translate F + u of a finite set. -/
def translateFinset (F : Finset (Lattice d)) (u : Lattice d) : Finset (Lattice d) :=
  F.image (· + u)

theorem mem_translateFinset {F : Finset (Lattice d)} {u w : Lattice d} :
    w ∈ translateFinset F u ↔ ∃ v ∈ F, v + u = w := by
  simp [translateFinset, Finset.mem_image]

/-- Pattern a on F appears in x at offset u:
    a(v) = x(v + u) for all v ∈ F. -/
def AppearsAt {F : Finset (Lattice d)} (a : Pattern Σ F) (x : FullShift Σ d)
    (u : Lattice d) : Prop :=
  ∀ v : F, x (v.1 + u) = a v

/-- Pattern a appears in x (at some offset). -/
def Appears {F : Finset (Lattice d)} (a : Pattern Σ F) (x : FullShift Σ d) : Prop :=
  ∃ u, AppearsAt a x u

/-- The cylinder set [a]_F = {x | x agrees with a on F}. -/
def cylinder {F : Finset (Lattice d)} (a : Pattern Σ F) : Set (FullShift Σ d) :=
  {x | ofColoring x F = a}

theorem mem_cylinder_iff {F : Finset (Lattice d)} (a : Pattern Σ F) (x : FullShift Σ d) :
    x ∈ cylinder a ↔ ∀ v : F, x v.1 = a v := by
  simp [cylinder, ofColoring, funext_iff]

/-- Cylinder sets are open in the product topology. -/
theorem cylinder_isOpen [TopologicalSpace Σ] [DiscreteTopology Σ]
    {F : Finset (Lattice d)} (a : Pattern Σ F) :
    IsOpen (cylinder a) := by
  rw [show cylinder a =
      ⋂ v : F, {x : FullShift Σ d | x v.1 = a v} from by
    ext x; simp [mem_cylinder_iff]]
  exact isOpen_iInter_of_finite fun v =>
    isOpen_discrete _  |>.preimage (continuous_apply _)

/-- Cylinder sets are closed in the product topology. -/
theorem cylinder_isClosed [TopologicalSpace Σ] [DiscreteTopology Σ]
    {F : Finset (Lattice d)} (a : Pattern Σ F) :
    IsClosed (cylinder a) := by
  rw [show cylinder a =
      ⋂ v : F, {x : FullShift Σ d | x v.1 = a v} from by
    ext x; simp [mem_cylinder_iff]]
  exact isClosed_iInter fun v =>
    (isClosed_discrete _).preimage (continuous_apply _)

end Pattern

/-! ## Subshifts -/

/-- A ℤ^d-subshift is a closed shift-invariant subset of the full shift. -/
structure Subshift (Σ : Type*) [TopologicalSpace Σ] (d : ℕ) where
  carrier    : Set (FullShift Σ d)
  isClosed   : IsClosed carrier
  isInvariant : ∀ (u : Lattice d) (x : FullShift Σ d),
                  x ∈ carrier → FullShift.shiftMap u x ∈ carrier

namespace Subshift

variable {Σ : Type*} [TopologicalSpace Σ] {d : ℕ}

instance : Membership (FullShift Σ d) (Subshift Σ d) :=
  ⟨fun x X => x ∈ X.carrier⟩

@[simp]
theorem mem_iff {X : Subshift Σ d} {x : FullShift Σ d} :
    x ∈ X ↔ x ∈ X.carrier := Iff.rfl

/-- The full shift itself as a subshift. -/
def univ : Subshift Σ d where
  carrier     := Set.univ
  isClosed    := isClosed_univ
  isInvariant := fun _ _ _ => Set.mem_univ _

end Subshift

/-! ## Shifts of Finite Type -/

/-- A coloring x is globally admissible for syntax L ⊆ Σ^F if, for every
    offset u ∈ ℤ^d, the F-pattern of x at u belongs to L. -/
def SFT_admissible {Σ : Type*} {d : ℕ}
    {F : Finset (Lattice d)}
    (L : Finset (Pattern Σ F))
    (x : FullShift Σ d) : Prop :=
  ∀ u : Lattice d, (fun v : F => x (v.1 + u)) ∈ L

/-- The carrier of the SFT defined by syntax L. -/
def SFT_carrier {Σ : Type*} {d : ℕ}
    {F : Finset (Lattice d)}
    (L : Finset (Pattern Σ F)) : Set (FullShift Σ d) :=
  {x | SFT_admissible L x}

section SFT

variable {Σ : Type*} [TopologicalSpace Σ] [DiscreteTopology Σ]
variable {d : ℕ} {F : Finset (Lattice d)}

theorem SFT_carrier_isInvariant (L : Finset (Pattern Σ F)) :
    ∀ (u : Lattice d) (x : FullShift Σ d),
      x ∈ SFT_carrier L → FullShift.shiftMap u x ∈ SFT_carrier L := by
  intro u x hx v
  have h := hx (v + u)
  simp only [SFT_carrier, Set.mem_setOf_eq, SFT_admissible] at *
  convert h using 1
  ext w
  simp [FullShift.shiftMap, add_assoc]

/-- The SFT carrier is a closed set. -/
theorem SFT_carrier_isClosed (L : Finset (Pattern Σ F)) :
    IsClosed (SFT_carrier L) := by
  have hd : SFT_carrier L =
      ⋂ u : Lattice d, ⋃ p ∈ L,
        ⋂ v : F, {x : FullShift Σ d | x (v.1 + u) = p v} := by
    ext x
    simp only [SFT_carrier, SFT_admissible, Set.mem_setOf_eq, Set.mem_iInter,
               Set.mem_iUnion, Finset.mem_coe, Set.mem_iInter]
    constructor
    · intro h u
      exact ⟨_, h u, fun v => rfl⟩
    · intro h u
      obtain ⟨p, hp, heq⟩ := h u
      convert hp using 1
      ext v; exact (heq v).symm
  rw [hd]
  apply isClosed_iInter; intro u
  apply Finset.isClosed_biUnion
  intro p _
  apply isClosed_iInter; intro v
  exact (isClosed_discrete _).preimage (continuous_apply _)

/-- Package a syntax into a Subshift. -/
def mkSFT (L : Finset (Pattern Σ F)) : Subshift Σ d where
  carrier     := SFT_carrier L
  isClosed    := SFT_carrier_isClosed L
  isInvariant := SFT_carrier_isInvariant L

theorem mem_mkSFT {L : Finset (Pattern Σ F)} {x : FullShift Σ d} :
    x ∈ mkSFT L ↔ SFT_admissible L x := Iff.rfl

end SFT

/-! ## Locally Admissible Patterns -/

/-- A pattern a on a finite set E is locally admissible for syntax L ⊆ Σ^F if,
    for every offset u such that the window F + u is contained in E, the
    restriction of a to F + u belongs (up to translation) to L. -/
def locallyAdmissible {Σ : Type*} {d : ℕ}
    {F : Finset (Lattice d)}
    (L : Finset (Pattern Σ F))
    {E : Finset (Lattice d)}
    (a : Pattern Σ E) : Prop :=
  ∀ u : Lattice d,
    Pattern.translateFinset F u ⊆ E →
    (fun v : F => a ⟨v.1 + u, by
      have := Pattern.mem_translateFinset.mpr ⟨v.1, v.2, rfl⟩
      exact Pattern.translateFinset F u |>.mem_of_mem_filter _ (by simpa using this) |>.mp
        (Finset.mem_of_mem_filter _ (by
          rw [Finset.filter_true_of_mem (by intros; trivial)]
          exact Pattern.mem_translateFinset.mpr ⟨v.1, v.2, rfl⟩))⟩) ∈ L

/-! We give a cleaner standalone version used in the entropy argument. -/

/-- Cleaner formulation: a pattern a on box E is locally admissible for L if
    for every u with F + u ⊆ E, the "patch" fun v => a(v + u) belongs to L. -/
def locallyAdmissible' {Σ : Type*} {d : ℕ}
    {F : Finset (Lattice d)}
    (L : Finset (Pattern Σ F))
    {E : Finset (Lattice d)}
    (a : Pattern Σ E) : Prop :=
  ∀ u : Lattice d, ∀ hFu : Pattern.translateFinset F u ⊆ E,
    ∃ p ∈ L, ∀ v : F, a ⟨v.1 + u, hFu (Pattern.mem_translateFinset.mpr ⟨v.1, v.2, rfl⟩)⟩ = p v

/-! ## Irreducible Subshifts -/

/-- A subshift X is irreducible with gap r > 0 if: whenever A, B ⊆ ℤ^d are
    finite sets at ℓ∞-distance ≥ r apart, any two globally admissible patterns
    on A and B can be simultaneously realized by some x ∈ X. -/
def Irreducible {Σ : Type*} [TopologicalSpace Σ] {d : ℕ}
    (X : Subshift Σ d) (r : ℤ) : Prop :=
  0 < r ∧
  ∀ (A B : Finset (Lattice d)),
    (∀ u ∈ A, ∀ v ∈ B, r ≤ Lattice.supNorm (u - v)) →
    ∀ (a : Pattern Σ A) (b : Pattern Σ B),
      (∃ x ∈ X, Pattern.AppearsAt a x 0) →
      (∃ x ∈ X, Pattern.AppearsAt b x 0) →
      ∃ x ∈ X, Pattern.AppearsAt a x 0 ∧ Pattern.AppearsAt b x 0

/-- A subshift is irreducible if it has some gap r. -/
def IsIrreducible {Σ : Type*} [TopologicalSpace Σ] {d : ℕ}
    (X : Subshift Σ d) : Prop :=
  ∃ r, Irreducible X r
