# Hochman–Meyerovitch (arXiv:math/0703206)

*Mike Hochman & Tom Meyerovitch (2007), "A characterization of the entropies of multidimensional shifts of finite type."*

## Files in this folder

- [`0703206v1.pdf`](0703206v1.pdf) — the paper.
- [`plan.txt`](plan.txt) — long-form mathematical formalization plan
  (milestones, proof sketches, axiom strategy, Mathlib gaps).
- [`implementation_list.md`](implementation_list.md) — per-item Lean checklist
  with current status. The `[MAIN]` markers identify the paper's main theorems.
- [`HochmanMeyerovitch.lean`](HochmanMeyerovitch.lean) — the Lean
  formalization. Search for `MAIN THEOREM` to locate the main theorems.

The shared helper module
[`../../dependencies/ComputableRat.lean`](../../dependencies/ComputableRat.lean)
provides the `Primrec`/`Computable` arithmetic on ℚ used in the F-section.

## Status (high level)

- **Theorem 1.1 necessity** — axiomatized (I1).
- **Theorem 1.1 sufficiency** — not started (I2/I3).
- **Theorem 1.2** — not started.
- **Theorem 1.3** — proven from I1 + a left-r.e. axiom (J9).

See `implementation_list.md` for the granular checklist.
