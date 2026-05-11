# Weiss conjecture — entropy-preserving SFT covers of sofic shifts

**Conjecture (B. Weiss, ca. 1973).** *Every sofic `ℤ^d`-shift admits an SFT
cover of the same topological entropy.*

In one dimension this is a classical theorem (every 1D sofic shift admits a
finite-state SFT cover whose entropy equals that of the sofic shift — the
"minimal right-resolving presentation" construction). For `d ≥ 2` it remains
**open**.

## Statement

Let `α` be a finite alphabet and `X ⊆ α^{ℤ^d}` a sofic subshift — i.e.,
`X = π(Y)` for some SFT `Y ⊆ β^{ℤ^d}` (some finite alphabet `β`) and some
factor map (continuous, shift-equivariant) `π : Y → X`. The Weiss conjecture
asserts there exist:

- a finite alphabet `β'`,
- an SFT `Y' ⊆ (β')^{ℤ^d}`,
- a factor map `π' : Y' → X`,

with the additional condition

  `topEntropy Y' = topEntropy X`.

The witness SFT `Y'` is the conjectured **entropy-preserving cover**.

For `d = 1`, the cover is constructed by the right-resolving presentation of
the labelled graph of `X`. For `d ≥ 2`, no analogous combinatorial
construction is known.

## Files in this folder

- [`README.md`](README.md) — problem statement and pointers (this file).
- [`WeissConjecture.lean`](WeissConjecture.lean) — Lean formalization of the
  statement. All supporting definitions (`IsSFT`, `FactorMap`, `IsSofic`,
  `HasEntropyPreservingSFTCover`) live in `../../dependencies/`.

## References

- B. Weiss, *Subshifts of finite type and sofic systems*, Monatsh. Math.,
  77 (1973), 462–474. (The 1D theorem; conjecture for `d ≥ 2` widely
  attributed to Weiss thereafter.)
- M. Boyle, R. Pavlov, M. Schraudner, *Multidimensional sofic shifts without
  separation and their factors*, Trans. AMS 362 (2010), 4617–4653. (Surveys
  the d ≥ 2 obstructions.)
- M. Hochman, *On the dynamics and recursive properties of multidimensional
  symbolic systems*, Invent. math. 176 (2009), 131–167. (Related entropy
  results.)
