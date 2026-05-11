import dependencies.Subshift

/-! # Factor maps between subshifts

A *factor map* `π : Y → X` between subshifts is a continuous,
shift-equivariant map whose image lies inside `X.carrier`. When the image
equals `X.carrier`, the factor map is **onto** and we say `X` is a
*factor* of `Y` (or equivalently, `Y` is an *extension* of `X`).

A subshift `X : Subshift α d` is **sofic** iff it is the image of some
SFT under an onto factor map. (Equivalently: the image of a sliding-block
code applied to an SFT; the equivalence with the present definition is
Curtis–Hedlund–Lyndon.)

These definitions support the formalization of open problems concerning
sofic shifts (e.g. `open-problems/WeissConjecture/`). Definitions only;
no theorems beyond bookkeeping. -/

/-- A factor map from `Y : Subshift β d` to `X : Subshift α d` is a
continuous, shift-equivariant map `φ : FullShift β d → FullShift α d`
whose image of `Y.carrier` lies inside `X.carrier`.

Note the direction: a factor map `Y → X` sends points of `Y` into points
of `X`. `Y` is the **extension** (or "cover"), `X` is the **factor**. -/
structure FactorMap {α β : Type*} {d : ℕ}
    [TopologicalSpace α] [TopologicalSpace β]
    (Y : Subshift β d) (X : Subshift α d) where
  /-- The underlying continuous, shift-equivariant map. -/
  toFun : FullShift β d → FullShift α d
  continuous : Continuous toFun
  shift_equivariant : ∀ (u : Lat d) (x : FullShift β d),
    toFun (FullShift.shiftMap u x) = FullShift.shiftMap u (toFun x)
  image_subset : Set.image toFun Y.carrier ⊆ X.carrier

namespace FactorMap

variable {α β γ : Type*} {d : ℕ}
  [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- The factor map is **onto** if its image of `Y.carrier` equals
`X.carrier`. -/
def IsOnto {Y : Subshift β d} {X : Subshift α d} (π : FactorMap Y X) : Prop :=
  Set.image π.toFun Y.carrier = X.carrier

/-- The identity factor map `X → X`. -/
def id (X : Subshift α d) : FactorMap X X where
  toFun := _root_.id
  continuous := continuous_id
  shift_equivariant := by intro u x; rfl
  image_subset := by intro y hy; obtain ⟨x, hx, rfl⟩ := hy; exact hx

/-- The identity factor map is onto. -/
theorem id_isOnto (X : Subshift α d) : (FactorMap.id X).IsOnto := by
  ext x
  refine ⟨fun ⟨y, hy, hyx⟩ => ?_, fun hx => ⟨x, hx, rfl⟩⟩
  -- (id X).toFun y = y by definition
  change y = x at hyx
  exact hyx ▸ hy

end FactorMap

/-- A subshift `X : Subshift α d` is **sofic** if there exists a finite
alphabet `β`, an SFT `Y : Subshift β d`, and an onto factor map `Y → X`.

Concretely: we package the SFT data `(F, L)` together with the onto
factor map. The discrete-topology instance on `β` is required for
`mkSFT` to be well-typed. -/
def IsSofic {α : Type*} {d : ℕ} [TopologicalSpace α]
    (X : Subshift α d) : Prop :=
  ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β)
    (_ : TopologicalSpace β) (_ : T1Space β)
    (F : Finset (Lat d)) (L : Finset (Pattern β F))
    (π : FactorMap (mkSFT F L) X), π.IsOnto
