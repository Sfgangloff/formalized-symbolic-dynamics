# Kari–Culik shift — value of the topological entropy

**Status:** `open`.

**Problem.** *What is the value of the topological entropy of the
Kari–Culik shift?*

## Statement

The Kari–Culik tile set, introduced independently by Kari (1996) and
Culik (1996), is a set of 13 Wang tiles that admits tilings of the plane
but only aperiodic ones. It is the smallest known aperiodic tile set.
The set of valid Kari–Culik tilings forms a 2D shift of finite type,
the **Kari–Culik shift** `kariCulikShift : Subshift KCTile 2`. Its
topological entropy is named:

```lean
noncomputable def kariCulikEntropy : ℝ := topEntropy kariCulikShift
```

What is known:

- The shift is nonempty and aperiodic.
- **Positive entropy** (Durand–Gamard–Grandjean 2013):
  `0 < kariCulikEntropy`. This was a surprise: all other small
  aperiodic tile sets known at the time were self-similar and had zero
  entropy.
- **Right r.e.** (Hochman–Meyerovitch Theorem 3.1, formalised in
  `papers/HochmanMeyerovitch/`): `kariCulikEntropy` is approximable
  from above by a computable sequence of rationals.

What is **open**:

- The exact value of `kariCulikEntropy`. No closed form, computable
  lower bound, or other effective characterisation is known.

## Lean rendering

The main problem is recorded by *naming* the value:

```lean
noncomputable def kariCulikEntropy : ℝ := topEntropy kariCulikShift
```

This is fundamentally a *value-finding* question, not a single
`Prop`-statement. Formal sub-renderings ("the value is computable",
"the value is algebraic", …) are auxiliary questions that, if
resolved, would shed light on the main problem; they live in
[`generated_questions/`](generated_questions/) alongside informal
open questions taken from the Durand–Gamard–Grandjean paper.

## Files in this folder

- [`README.md`](README.md) — this file.
- [`KariCulikEntropy.lean`](KariCulikEntropy.lean) — the name
  `kariCulikEntropy` for the value under investigation.
- [`generated_questions/`](generated_questions/) — auxiliary
  questions related to the main problem.

## Supporting files elsewhere

- [`../../dependencies/KariCulik.lean`](../../dependencies/KariCulik.lean)
  — alphabet `KCTile = Fin 13` and instances.
- [`../../axioms/KariCulik.lean`](../../axioms/KariCulik.lean)
  — existence, SFT-ness, nonemptiness, and positive entropy of the
  Kari–Culik shift (the construction itself is not formalised).
- [`../../papers/DurandGamardGrandjean/`](../../papers/DurandGamardGrandjean/)
  — preprint of the positive-entropy proof.

## References

- J. Kari, *A small aperiodic set of Wang tiles*, Discrete Math. 160
  (1996) 259–264.
- K. Culik II, *An aperiodic set of 13 Wang tiles*, Discrete Math. 160
  (1996) 245–251.
- B. Durand, G. Gamard, A. Grandjean, *Aperiodic tilings and entropy*,
  DLT 2014, also [arXiv:1312.4126](https://arxiv.org/abs/1312.4126).
- J. Siefken, *A minimal subsystem of the Kari–Culik tilings*, Ergodic
  Theory Dynam. Systems 37 (2017),
  [arXiv:1410.1572](https://arxiv.org/abs/1410.1572).
