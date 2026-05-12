import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import dependencies.Subshift
import dependencies.InvariantMeasure

/-! # Axioms on shift-invariant probability measures

Standard measure-theoretic facts about the space of shift-invariant
Borel probability measures on a subshift, used in the proof of
Hochman–Meyerovitch Theorem 3.1.

Each axiom corresponds to a well-known theorem in ergodic theory:
- existence of an invariant measure (Krylov–Bogolyubov);
- the Kolmogorov–Sinai entropy as an `NNReal`-valued functional;
- the variational principle (Misiurewicz);
- upper semi-continuity of measure-theoretic entropy in the weak-* topology;
- ambient compactness of the space of probability measures on a finite
  alphabet (`instCompactSpaceProbabilityMeasure` in current Mathlib master,
  not yet available in v4.26.0-rc1 used here).

This file contains *only axioms*. Theorems derived from them
(`measureEntropy_nonneg`, `InvMeasure.compactSpace`) live in
`dependencies/InvMeasureCompactness.lean`.
-/

/-- A nonempty subshift carries at least one shift-invariant probability measure
(by Krylov–Bogolyubov). -/
axiom InvMeasure.instInhabited {α : Type} [MeasurableSpace α] {d : ℕ}
    [TopologicalSpace α] (X : Subshift α d) :
    (X.carrier.Nonempty) → Inhabited (InvMeasure X)

/-- Measure-theoretic (Kolmogorov–Sinai) entropy of a shift-invariant probability
measure, valued in `ℝ≥0` (`NNReal`). Opaque; in the full development this is
the Kolmogorov–Sinai entropy of the `Lat d`-action. Returning `NNReal` makes
non-negativity automatic. -/
axiom measureEntropy {α : Type} [MeasurableSpace α] {d : ℕ} [TopologicalSpace α]
    {X : Subshift α d} (μ : InvMeasure X) : NNReal

/-- **Variational principle.** For a nonempty subshift `X`, the topological
entropy equals the supremum of measure-theoretic entropies (coerced to `ℝ`)
over all shift-invariant probability measures on `X`. -/
axiom variationalPrinciple {α : Type} [MeasurableSpace α] {d : ℕ} [Fintype α]
    [TopologicalSpace α] {X : Subshift α d} (hX : X.carrier.Nonempty) :
    topEntropy X = ⨆ μ : InvMeasure X, ((measureEntropy μ : NNReal) : ℝ)

/-- **Upper semi-continuity of entropy.** The real-valued map
`μ ↦ ((measureEntropy μ : NNReal) : ℝ)` is upper semi-continuous in the
weak-* topology on `InvMeasure X`. -/
axiom measureEntropy_uppersemicontinuous {α : Type} [MeasurableSpace α] {d : ℕ}
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α]
    (X : Subshift α d) :
    UpperSemicontinuous (fun μ : InvMeasure X => ((measureEntropy μ : NNReal) : ℝ))

/-- **Ambient-compactness axiom.** For a finite, T2, compact alphabet `α`,
the space of probability measures on `FullShift α d` is itself compact in the
weak-* topology. This is `instCompactSpaceProbabilityMeasure` in
`Mathlib.MeasureTheory.Measure.Prokhorov` (current Mathlib master); this
project pins Mathlib `v4.26.0-rc1`, which predates that module, hence we
axiomatize the instance here. -/
axiom ProbabilityMeasure.compactSpace_aux {α : Type} [MeasurableSpace α] {d : ℕ}
    [Fintype α] [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α]
    [T2Space α] [CompactSpace α] :
    CompactSpace (MeasureTheory.ProbabilityMeasure (FullShift α d))
