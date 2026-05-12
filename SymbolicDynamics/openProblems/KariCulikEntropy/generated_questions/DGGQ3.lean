import dependencies.Subshift
import dependencies.FactorMap
import dependencies.KariCulik
import axioms.KariCulik
import openProblems.KariCulikEntropy.KariCulikEntropy

/-! # DGG-Q3 — Characterise the Kari-words

**Source.** B. Durand, G. Gamard, A. Grandjean, *Aperiodic tilings and
entropy*, [arXiv:1312.4126v2](https://arxiv.org/abs/1312.4126),
Section 4 ("Positive entropy"), subsection "Open problems",
**third paragraph**. Verbatim:

> *Using substitutive pairs we proved that there are tilings which
> horizontal lines do not represent mechanical words. Is it possible
> to better characterize the Kari-words: the language of the lines
> that can appear in a tiling?*

The 1D subshift `kariCulikHorizontalShift` (axiomatised in
`axioms/KariCulik.lean`) is the natural carrier for the language of
horizontal lines. "Characterising the language" is open-ended; we
render it as one of the most-studied concrete characterisations:
whether the 1D shift is **sofic**.

**Status:** `open`.

## Relevance to the main problem

Topological entropy is determined by the rate of growth of the
admissible-pattern language. A characterisation of the horizontal
language — sofic, regular, decidable, … — would yield bounds (and
possibly a closed form) for the entropy of the horizontal-line
subshift, which lower-bounds `kariCulikEntropy`.
-/

/-- **DGG-Q3 (statement).** The 1D shift of horizontal lines appearing
in Kari–Culik tilings is sofic.

This is a concrete formal rendering of "characterise the Kari-words";
other natural renderings (regular, decidable, with computable factor
complexity, …) could be added to this folder. -/
def DGGQ3_HorizontalShiftIsSofic : Prop :=
  IsSofic kariCulikHorizontalShift
