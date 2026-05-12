# Durand, Gamard, Grandjean — Aperiodic Tilings and Entropy

**Reference.** B. Durand, G. Gamard, A. Grandjean,
*Aperiodic tilings and entropy*,
DLT 2014 / LNCS 8633, also arXiv:[1312.4126](https://arxiv.org/abs/1312.4126).

## Main result

The Kari–Culik aperiodic tile set (13 Wang tiles, the smallest known
aperiodic set) gives rise to a 2D SFT — the **Kari–Culik shift** — and
this SFT has **strictly positive topological entropy**.

This is striking because previous small aperiodic tile sets are
self-similar / hierarchical and have zero entropy; the Kari–Culik
construction breaks that pattern.

## Use in this project

We do not formalise the construction of the Kari–Culik tile set or the
positive-entropy proof; both are recorded as **axioms** in
[`../../axioms/KariCulik.lean`](../../axioms/KariCulik.lean), supporting
the open-problem entry
[`../../openProblems/KariCulikEntropy/`](../../openProblems/KariCulikEntropy/)
("what is the value of `topEntropy kariCulikShift`?").

## Files in this folder

- [`README.md`](README.md) — this file.
- [`1312.4126v2.pdf`](1312.4126v2.pdf) — preprint.
