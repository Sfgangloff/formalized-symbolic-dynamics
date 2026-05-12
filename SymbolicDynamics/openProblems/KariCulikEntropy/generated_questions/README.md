# Generated questions — Kari–Culik entropy

This folder collects **auxiliary questions** related to the main open
problem ([`../README.md`](../README.md): *what is the value of
`kariCulikEntropy`*?). The aim is to record questions whose
resolution — whether by proof, computation, or counterexample search —
would shed light on the main problem.

Questions can come from three places:

1. **Open questions stated in the literature** (e.g. the
   Durand–Gamard–Grandjean paper),
2. **Formal sub-renderings** of the main question as concrete Lean
   `Prop`s (e.g. "is the value computable / algebraic / rational?"),
3. **Computational experiments** (counting locally admissible patterns
   on small boxes, sampling configurations) whose outcomes could
   suggest or rule out conjectures about the value.

Each question is recorded as a Lean `Prop` in its own `.lean` file,
with a docstring giving the precise paper location for literature
questions.

## Formal sub-renderings of "what is the value?"

- [`Computability.lean`](Computability.lean) —
  `KariCulikEntropyComputableStatement`: is `kariCulikEntropy`
  computable as a real?
- [`Algebraicity.lean`](Algebraicity.lean) —
  `KariCulikEntropyAlgebraicStatement`: is `kariCulikEntropy`
  algebraic over `ℚ`?

## Open questions from the Durand–Gamard–Grandjean paper

All three are from Section 4 ("Positive entropy"), subsection "Open
problems" of arXiv:1312.4126v2.

- [`DGGQ1.lean`](DGGQ1.lean) — `DGGQ1_OnePairAloneIsDense`: is one of
  the two substitutive pairs alone dense in any given tiling?
- [`DGGQ2.lean`](DGGQ2.lean) —
  `DGGQ2a_RestrictedTilesetHasPositiveEntropy` and
  `DGGQ2b_FiniteExclusionDrivesEntropyToZero`: does forbidding one
  pattern in each pair preserve positive entropy? Can finite-exclusion
  drive the entropy to zero?
- [`DGGQ3.lean`](DGGQ3.lean) — `DGGQ3_HorizontalShiftIsSofic`: is the
  1D shift of horizontal Kari–Culik lines sofic?
