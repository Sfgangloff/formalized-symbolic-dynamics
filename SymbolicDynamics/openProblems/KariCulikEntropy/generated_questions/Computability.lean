import dependencies.Computable
import openProblems.KariCulikEntropy.KariCulikEntropy

/-! # Generated question: is `kariCulikEntropy` computable?

A natural sub-question of the main open problem (determine the value
of `kariCulikEntropy`). Computability would let us approximate the
value algorithmically to any desired precision, even without a
closed-form expression.

Status: `open`.

Why this is a meaningful sub-question:

- By `topEntropy_rightRE` (Hochman–Meyerovitch Theorem 3.1, formalised
  in this project), `kariCulikEntropy` is right r.e. — already
  approximable from above.
- Computability of a real is equivalent to right r.e. ∧ left r.e.
  (`computable_iff_leftRE_and_rightRE` in
  `dependencies/Computable.lean`).
- So the open content is whether `kariCulikEntropy` is left r.e.
- `topEntropy_irreducible_computable` (Hochman–Meyerovitch
  Theorem 1.3) handles the irreducible case. The Kari–Culik shift is
  **not** known to be irreducible; it has interesting minimal
  subsystems (Siefken 2014). So the irreducible-SFT theorem does not
  directly apply.

Not raised explicitly in the Durand–Gamard–Grandjean paper.
-/

/-- **Generated question.** The topological entropy of the Kari–Culik
shift is computable. -/
def KariCulikEntropyComputableStatement : Prop :=
  IsComputableReal kariCulikEntropy
