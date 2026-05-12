import Mathlib.Analysis.SpecialFunctions.Log.Basic
import dependencies.Subshift
import dependencies.Box
import dependencies.GloballyAdmissible
import dependencies.KariCulik
import axioms.KariCulik
import openProblems.KariCulikEntropy.KariCulikEntropy

/-! # DGG-Q2 — Entropy of restricted Kari–Culik tilesets

**Source.** B. Durand, G. Gamard, A. Grandjean, *Aperiodic tilings and
entropy*, [arXiv:1312.4126v2](https://arxiv.org/abs/1312.4126),
Section 4 ("Positive entropy"), subsection "Open problems",
**second paragraph**. Verbatim:

> *Consider the extended tileset where we forbid one pattern in each
> of the presented pairs. The obtained tileset is still a palette.
> Has this tileset a positive entropy? If the answer is positive, is
> it possible to exclude a finite number of patterns so that all the
> resulting tilings have zero entropy?*

We split the paragraph into two distinct `Prop`s, DGG-Q2a (does
positive entropy survive forbidding one pattern in each pair?) and
DGG-Q2b (can finite-exclusion drive the entropy to zero?). The
restricted-tileset subshift is `kariCulikShift_forbid` from
`axioms/KariCulik.lean`.

**Status:** `open`.

## Relevance to the main problem

DGG-Q2a tests whether the positive-entropy mechanism is robust to
local-rule perturbations or specifically tied to the substitutive
pairs they identified.

DGG-Q2b is a quantitative refinement: how much of the local rule is
"necessary" for positive entropy?  A `yes` to DGG-Q2b combined with
the right witness would also give an upper bound on `kariCulikEntropy`
via a quotient-entropy argument.
-/

/-- **DGG-Q2a (statement).** Forbidding one 2×2 pattern from each of
the DGG substitutive pairs preserves positive entropy. -/
def DGGQ2a_RestrictedTilesetHasPositiveEntropy : Prop :=
  ∀ f1 ∈ ({dgg_A1, dgg_A1'} : Set (Pattern KCTile (box 2 2))),
  ∀ f2 ∈ ({dgg_A2, dgg_A2'} : Set (Pattern KCTile (box 2 2))),
    0 < topEntropy (kariCulikShift_forbid {f1, f2})

/-- **DGG-Q2b (statement).** There exists a finite set of 2×2 patterns
whose exclusion drives the topological entropy to zero. -/
def DGGQ2b_FiniteExclusionDrivesEntropyToZero : Prop :=
  ∃ F : Finset (Pattern KCTile (box 2 2)),
    topEntropy (kariCulikShift_forbid F) = 0
