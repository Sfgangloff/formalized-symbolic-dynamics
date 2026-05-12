import dependencies.Subshift
import dependencies.KariCulik
import axioms.KariCulik

/-! # Kari–Culik shift — value of the topological entropy

**Open problem.** *What is the value of the topological entropy of the
Kari–Culik shift?*

What is known:

- `kariCulikShift_carrier_nonempty` — the shift is nonempty.
- `kariCulikShift_entropy_pos` — the entropy is strictly positive
  (Durand–Gamard–Grandjean 2013).
- `topEntropy_rightRE` (Hochman–Meyerovitch Theorem 3.1, formalised in
  `papers/HochmanMeyerovitch/`) — the entropy of any SFT is right
  recursively enumerable, so `kariCulikEntropy` is in particular
  approximable from above.

What is open: the exact value of `kariCulikEntropy`.

This is fundamentally a *value-finding* question, not a single Prop.
Formal renderings — "the value is computable", "the value is
algebraic", etc. — are auxiliary sub-questions that, if resolved, would
shed light on the main problem. They live in
[`generated_questions/`](generated_questions/) alongside open questions
from the Durand–Gamard–Grandjean paper itself.

See [`README.md`](README.md) for context and references. -/

/-- The topological entropy of the Kari–Culik shift. Its exact value
is the subject of the open problem. -/
noncomputable def kariCulikEntropy : ℝ := topEntropy kariCulikShift
