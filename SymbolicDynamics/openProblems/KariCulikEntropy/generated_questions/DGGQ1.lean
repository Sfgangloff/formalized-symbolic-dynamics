import dependencies.Subshift
import dependencies.Box
import dependencies.GloballyAdmissible
import dependencies.KariCulik
import axioms.KariCulik
import openProblems.KariCulikEntropy.KariCulikEntropy

/-! # DGG-Q1 — Is one substitutive pair alone dense in any given tiling?

**Source.** B. Durand, G. Gamard, A. Grandjean, *Aperiodic tilings and
entropy*, [arXiv:1312.4126v2](https://arxiv.org/abs/1312.4126),
Section 4 ("Positive entropy"), subsection "Open problems",
**first paragraph**. Verbatim:

> *We proved that the two pairs are together dense in any tiling. Is
> one of those pairs dense alone in a given tiling?*

The two pairs are the 2×2 patterns `(A₁, A'₁)` and `(A₂, A'₂)`
displayed in Section 4 (subsection "Coming back to the function") of
the same paper. We use the axiomatised representatives
`dgg_A1, dgg_A1', dgg_A2, dgg_A2'` from `axioms/KariCulik.lean`.

**Status:** `open`.

## Relevance to the main problem

DGG's positive-entropy proof uses that the **union** of the two pairs
is dense in every Kari–Culik tiling. A positive answer to DGG-Q1 would
say that *each* individual tiling already gets positive entropy from a
*single* pair — a much finer structural statement. Either answer
constrains the combinatorial model of Kari–Culik configurations and
therefore the asymptotic count governing `kariCulikEntropy`.
-/

/-- **DGG-Q1 (statement).** In every Kari–Culik configuration `x`, at
least one of the two DGG substitutive pairs is *fully* dense in `x`
— both of its members occur with positive density. -/
def DGGQ1_OnePairAloneIsDense : Prop :=
  ∀ x ∈ kariCulikShift.carrier,
    (Pattern.hasPositiveDensity dgg_A1 x ∧ Pattern.hasPositiveDensity dgg_A1' x) ∨
    (Pattern.hasPositiveDensity dgg_A2 x ∧ Pattern.hasPositiveDensity dgg_A2' x)
