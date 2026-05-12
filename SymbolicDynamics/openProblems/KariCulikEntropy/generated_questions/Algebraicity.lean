import Mathlib.RingTheory.Algebraic.Defs
import openProblems.KariCulikEntropy.KariCulikEntropy

/-! # Generated question: is `kariCulikEntropy` algebraic over `ℚ`?

A natural sub-question of the main open problem (determine the value
of `kariCulikEntropy`). Algebraicity would yield a *finite description*
of the value: the entropy as a root of an explicit polynomial over `ℚ`,
plus a choice among finitely many real roots.

Status: `open`.

Many small-tile-set and SFT entropies that have been computed turn out
to be algebraic (e.g. the golden-mean shift's entropy is `log φ`,
algebraic via `φ² = φ + 1`); so algebraicity is a natural conjecture to
entertain for `kariCulikEntropy`.

Logically independent in principle from `KariCulikEntropyComputableStatement`:
an algebraic real need not be computable in the `ℕ → ℚ` sense without
an explicit polynomial, and a computable real need not be algebraic.

Not raised explicitly in the Durand–Gamard–Grandjean paper.
-/

/-- **Generated question.** The topological entropy of the Kari–Culik
shift is algebraic over `ℚ`. -/
def KariCulikEntropyAlgebraicStatement : Prop :=
  IsAlgebraic ℚ kariCulikEntropy
