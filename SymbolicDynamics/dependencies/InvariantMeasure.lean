import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import dependencies.Subshift

/-! # Shift-invariant probability measures on a subshift

The type `InvMeasure X` of shift-invariant Borel probability measures
concentrated on `X.carrier`, with its weak-* topology, and closedness
of the carrier inside `ProbabilityMeasure (FullShift α d)` (used to
discharge `InvMeasure.compactSpace` from a single ambient-compactness
axiom).

The deep ergodic-theory facts (existence by Krylov–Bogolyubov, the
Kolmogorov–Sinai entropy, the variational principle, upper
semi-continuity, ambient compactness on a finite alphabet) live in
`axioms/InvariantMeasure.lean`.
-/

/-- Type of shift-invariant Borel probability measures on `X`, defined as the
subtype of `MeasureTheory.ProbabilityMeasure (FullShift α d)` consisting of
those `μ` invariant under every shift and concentrated on `X.carrier`.

Requires `[MeasurableSpace α]`; for finite `α` with discrete topology one
typically takes the discrete sigma-algebra.

Restricted to `α : Type` (universe 0) for compatibility with Mathlib's
measure-theoretic infrastructure. Downstream theorems that take an
`α : Type*` (universe-polymorphic) need to be specialised to `α : Type` to
talk about `InvMeasure`. -/
def InvMeasure {α : Type} [MeasurableSpace α] {d : ℕ} [TopologicalSpace α]
    (X : Subshift α d) : Type :=
  { μ : MeasureTheory.ProbabilityMeasure (FullShift α d) //
      (∀ u : Lat d, μ.toMeasure.map (FullShift.shiftMap u) = μ.toMeasure)
      ∧ μ.toMeasure X.carrier = 1 }

/-- Topology on `InvMeasure X` (the weak-* topology, inherited from
`MeasureTheory.ProbabilityMeasure` via the subtype topology). -/
instance InvMeasure.instTopologicalSpace {α : Type} [MeasurableSpace α] {d : ℕ}
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α]
    (X : Subshift α d) : TopologicalSpace (InvMeasure X) :=
  inferInstanceAs (TopologicalSpace
    { μ : MeasureTheory.ProbabilityMeasure (FullShift α d) //
        (∀ u : Lat d, μ.toMeasure.map (FullShift.shiftMap u) = μ.toMeasure)
        ∧ μ.toMeasure X.carrier = 1 })

/-! ## Closedness of the InvMeasure carrier in `ProbabilityMeasure` -/

/-- Closedness of the shift-invariance condition (per shift `u`).
For each `u : Lat d`, the set of probability measures fixed by the
pushforward under `FullShift.shiftMap u` is closed in the weak-* topology. -/
theorem InvMeasure.isClosed_setOf_invariant {α : Type} [MeasurableSpace α] {d : ℕ}
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α]
    [HasOuterApproxClosed (FullShift α d)] (u : Lat d) :
    IsClosed { μ : MeasureTheory.ProbabilityMeasure (FullShift α d) |
      μ.toMeasure.map (FullShift.shiftMap u) = μ.toMeasure } := by
  have h_cont : Continuous (FullShift.shiftMap (α := α) (d := d) u) :=
    FullShift.shiftMap_continuous u
  set f : MeasureTheory.ProbabilityMeasure (FullShift α d) →
      MeasureTheory.ProbabilityMeasure (FullShift α d) :=
    fun ν => ν.map h_cont.measurable.aemeasurable with hf_def
  have h_f_cont : Continuous f :=
    MeasureTheory.ProbabilityMeasure.continuous_map h_cont
  have set_eq :
      { μ : MeasureTheory.ProbabilityMeasure (FullShift α d) |
          μ.toMeasure.map (FullShift.shiftMap u) = μ.toMeasure }
        = { μ : MeasureTheory.ProbabilityMeasure (FullShift α d) | f μ = μ } := by
    ext μ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact MeasureTheory.ProbabilityMeasure.toMeasure_injective h
    · exact congr_arg MeasureTheory.ProbabilityMeasure.toMeasure h
  rw [set_eq]
  exact isClosed_eq h_f_cont continuous_id

/-- Closedness of the support condition: the set of probability measures with
full mass on the closed shift `X.carrier` is closed in the weak-* topology
(via portmanteau). -/
theorem InvMeasure.isClosed_setOf_support {α : Type} [MeasurableSpace α] {d : ℕ}
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α]
    [HasOuterApproxClosed (FullShift α d)]
    (X : Subshift α d) :
    IsClosed { μ : MeasureTheory.ProbabilityMeasure (FullShift α d) |
      μ.toMeasure X.carrier = 1 } := by
  set g : MeasureTheory.ProbabilityMeasure (FullShift α d) → ENNReal :=
    fun μ => μ.toMeasure X.carrier with hg_def
  have h_usc : UpperSemicontinuous g := by
    apply upperSemicontinuous_iff_limsup_le.mpr
    intro μ₀
    exact MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
      Filter.tendsto_id X.isClosed
  have h_le_one : ∀ μ : MeasureTheory.ProbabilityMeasure (FullShift α d), g μ ≤ 1 := by
    intro μ
    calc g μ
        = μ.toMeasure X.carrier := rfl
      _ ≤ μ.toMeasure Set.univ := μ.toMeasure.mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
  have set_eq :
      { μ : MeasureTheory.ProbabilityMeasure (FullShift α d) |
          μ.toMeasure X.carrier = 1 }
        = g ⁻¹' Set.Ici 1 := by
    ext μ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
    refine ⟨fun h => h.ge, fun h => le_antisymm (h_le_one μ) h⟩
  rw [set_eq]
  exact h_usc.isClosed_preimage 1

/-- The set of shift-invariant probability measures concentrated on `X.carrier`,
viewed as a subset of `ProbabilityMeasure (FullShift α d)`, is closed in the
weak-* topology. -/
theorem InvMeasure.isClosed_setOf {α : Type} [MeasurableSpace α] {d : ℕ}
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α]
    [HasOuterApproxClosed (FullShift α d)]
    (X : Subshift α d) :
    IsClosed { μ : MeasureTheory.ProbabilityMeasure (FullShift α d) |
      (∀ u : Lat d, μ.toMeasure.map (FullShift.shiftMap u) = μ.toMeasure)
      ∧ μ.toMeasure X.carrier = 1 } := by
  have h_eq :
      { μ : MeasureTheory.ProbabilityMeasure (FullShift α d) |
          (∀ u : Lat d, μ.toMeasure.map (FullShift.shiftMap u) = μ.toMeasure)
          ∧ μ.toMeasure X.carrier = 1 }
        = (⋂ u : Lat d, { μ : MeasureTheory.ProbabilityMeasure (FullShift α d) |
              μ.toMeasure.map (FullShift.shiftMap u) = μ.toMeasure })
          ∩ { μ : MeasureTheory.ProbabilityMeasure (FullShift α d) |
              μ.toMeasure X.carrier = 1 } := by
    ext μ
    simp [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, and_comm]
  rw [h_eq]
  exact (isClosed_iInter (fun u => InvMeasure.isClosed_setOf_invariant u)).inter
    (InvMeasure.isClosed_setOf_support X)
