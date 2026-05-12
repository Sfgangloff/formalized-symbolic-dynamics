import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import dependencies.Subshift
import dependencies.InvariantMeasure
import axioms.InvariantMeasure

/-! # Consequences of the invariant-measure axioms

Theorems derived from the axioms in `axioms/InvariantMeasure.lean`:

- `measureEntropy_nonneg` — automatic from the `NNReal` codomain of
  `measureEntropy`.
- `InvMeasure.compactSpace` — compactness of `M(X)` in the weak-*
  topology, derived from the ambient-compactness axiom plus
  closedness of the carrier (`InvMeasure.isClosed_setOf`).
-/

/-- Measure entropy is non-negative: free from the `NNReal` codomain. -/
theorem measureEntropy_nonneg {α : Type} [MeasurableSpace α] {d : ℕ}
    [TopologicalSpace α] {X : Subshift α d} (μ : InvMeasure X) :
    (0 : ℝ) ≤ ((measureEntropy μ : NNReal) : ℝ) :=
  NNReal.coe_nonneg _

/-- **Compactness of M(X).** When `α` is a finite, T2, compact alphabet
(so the full shift is compact metrizable), `InvMeasure X` is compact in
the weak-* topology. Derived from `InvMeasure.isClosed_setOf` and the
ambient-compactness axiom. -/
theorem InvMeasure.compactSpace {α : Type} [MeasurableSpace α] {d : ℕ} [Fintype α]
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α]
    [T2Space α] [CompactSpace α] [HasOuterApproxClosed (FullShift α d)]
    (X : Subshift α d) (_hX : X.carrier.Nonempty) :
    CompactSpace (InvMeasure X) :=
  haveI : CompactSpace (MeasureTheory.ProbabilityMeasure (FullShift α d)) :=
    ProbabilityMeasure.compactSpace_aux
  isCompact_iff_compactSpace.mp ((InvMeasure.isClosed_setOf X).isCompact)
