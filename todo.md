# Formalization Methodology — TODO & Notes

## Approach

This project formalizes Hochman–Meyerovitch (arXiv:math/0703206) in Lean 4 / Mathlib 4.
The method follows a strict incremental loop:

1. **Formalization plan** — write `hochman_meyerovitch_implementation_list.md` with every `def`, `instance`, and
   `theorem` needed, in dependency order, before touching any Lean code.
2. **Object-by-object coding** — implement exactly one item at a time (one `def` or one theorem),
   keeping the file compiling at every step.
3. **Repair loop** — after each addition, run the LSP diagnostics and fix any errors before
   moving to the next item. Never accumulate errors across multiple items.
4. **Commit on green** — commit and push to `main` every time the file compiles without errors,
   so the history is a sequence of clean snapshots.

## Why this matters

- Errors compound quickly in Lean; fixing one item at a time keeps the search space small.
- A clean git history makes it easy to bisect regressions and see what each item cost.
- The plan (`hochman_meyerovitch_implementation_list.md`) serves as a checklist and a contract: no item is added
  that was not planned, and every planned item is eventually checked off.

## Current status

See `hochman_meyerovitch_implementation_list.md` for the full checklist.
Items 0.1–0.12 are complete and pushed.

## Pending items (next up)

- [ ] 0.13  `FullShift.shiftMap_continuous`
- [ ] A1–A4  Missing subshift infrastructure
- [ ] 0.14–0.24  Pattern definitions and cylinder sets
- [ ] 0.25–0.28  Subshift structure
- (see full list in `hochman_meyerovitch_implementation_list.md`)

## Known import pitfalls (Mathlib v4.26)

| What you need | Correct import |
|---|---|
| `Finset.sup'`, `Finset.sup_bot` | `Mathlib.Data.Finset.Lattice.Fold` |
| `Fintype (Fin d)` | `Mathlib.Data.Fintype.Basic` |
| `AddZeroClass ℤ`, `Ring ℤ` | `Mathlib.Algebra.Ring.Int.Defs` |
| Pi group instances (`add_zero`, `add_assoc` for `Fin d → ℤ`) | `Mathlib.Algebra.Group.Pi.Basic` |
| `AddAction` | `Mathlib.Algebra.Group.Action.Defs` |
| Pi `CompactSpace` | `Mathlib.Topology.Compactness.Compact` |
| Pi `T2Space` | `Mathlib.Topology.Separation.Hausdorff` |

## Style rules

- No comments unless the *why* is non-obvious.
- One `/-! ## N.n  ItemName -/` section header per item.
- Proofs stay ≤ 5 lines; longer proofs indicate the wrong lemma was chosen.
