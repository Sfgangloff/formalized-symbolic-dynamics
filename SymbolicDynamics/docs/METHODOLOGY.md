# Formalization Methodology

This document records the methodology used to formalize the Hochman–Meyerovitch
paper (`arXiv:math/0703206`) in Lean 4 / Mathlib 4. The same approach should
work for any sustained formalization effort driven by an LLM coding assistant.

## Core principle: bound the search space at every step

A Lean file with even one error often produces *cascading* errors below it.
For an LLM agent, this is doubly costly:

- The model's context fills with diagnostic noise that's not actionable.
- Each fix attempt may introduce two new errors elsewhere, leaving the agent
  unable to converge.

Our defence is to **never accumulate more than one error at a time**. After
every single addition (one `def`, one `theorem`, one `instance`), the LSP
diagnostics must be clean before moving to the next item.

The rest of the methodology is the scaffolding that makes this discipline
practical.

---

## Artifact 1: the formalization plan (`<paper>_formalization_plan.txt`)

Written **before any Lean code is touched**. A long-form document that:

- **Identifies the main theorems of the paper up front.** Use a dedicated
  section at the top of the plan (e.g. `## Main theorems`) listing each one
  with its paper number, statement, and the implementation-list identifier
  it will receive (e.g. `Theorem 1.3 → J9 → topEntropy_irreducible_computable`).
  Main theorems should be recognisable at a glance to a future agent picking
  up the project.
- Names the milestones (e.g. *Module 3.1: necessity direction of Theorem 1.1*).
- Sketches the proof structure for each milestone (in math, not Lean).
- Identifies external dependencies (Mathlib gaps, axioms that will be needed
  for theorems whose full proof is out of scope, e.g. the variational
  principle).
- Maps mathematical concepts to Lean encodings (e.g. `Pattern α F` as
  `F → α`, `Subshift` as a `structure` carrying closed shift-invariance).

This is the **strategic** layer: it tells you *what to prove and why*. It
rarely changes during a session.

### Marking main theorems

For each paper formalized in this project, the main theorems should be:

1. **Listed in a `## [MAIN] Main theorems` section at the top of the plan**,
   with their paper number and the matching implementation-list identifier:

   ```
   ## [MAIN] Main theorems (Hochman–Meyerovitch)
   - [MAIN] Theorem 1.1 (SFT entropies = right r.e. ≥ 0)
       - Necessity: I1 → `topEntropy_rightRE`
       - Sufficiency: I2 → `rightRE_imp_SFT_entropy`  (NOT YET DONE)
       - Combined: I3 → `SFT_entropy_iff_rightRE`
   - [MAIN] Theorem 1.2 (Sofic shift entropies = SFT entropies)  (NOT YET STARTED)
   - [MAIN] Theorem 1.3 (irreducible SFT entropy is computable): J9 →
     `topEntropy_irreducible_computable`
   ```

2. **Mirrored at the top of the implementation list** in a `## [MAIN] Main
   theorems` summary block, with each entry prefixed `**[MAIN]**` so it can be
   located by a literal search for `[MAIN]`.

3. **Marked in the Lean source** with a top-level comment-block header
   (`/-! # MAIN THEOREM 1.3 — entropy of an irreducible SFT is computable -/`,
   note the `#` rather than `##`, making it stand out as a file-level
   landmark) immediately above the declaration.

These three locations (plan / list / source) keep the main results
discoverable from any entry point. Searching for the literal string
`MAIN THEOREM` in any project file should always return only the main
results.

## Artifact 2: the implementation list (`hochman_meyerovitch_implementation_list.md`)

The **tactical** layer. A flat checklist where each item is a single
self-contained Lean unit:

```
- [ ] G4.4d `theorem N_bar_eq_fintype_card_subtype` — alternative formulation
- [ ] G4.4e `def boxIndex` + `boxIndex_mem` (computable enumeration via base-n digits)
```

Rules:

1. **One item = one `def`, `instance`, `theorem`, or `axiom`.** If a planned
   item turns out to need a proof more than ~5 lines or splits naturally, it
   is broken into sub-items (`G4.4`, `G4.4a`, `G4.4b`, ...). Re-organising
   the list is encouraged when the structure of the proof becomes clearer.
2. **Items are added in dependency order.** Section A is committed before
   anything that uses A. Phase letters within a milestone (Phase A, Phase B,
   ...) make this explicit when a milestone gets large.
3. **Tick the checkbox when the file compiles cleanly.** The checkbox is
   the contract; an item is "done" only when the whole file builds with no
   `sorry` and no errors.
4. **Commit one item per commit.** The commit message names the item. This
   gives you a `git log` that is itself a usable progress report.

## Artifact 3: the live build status (`mcp__lean-lsp-mcp__lean_diagnostic_messages`)

The **closed-loop control signal**. After every edit, the agent calls

```text
mcp__lean-lsp-mcp__lean_diagnostic_messages(
    file_path = ".../HochmanMeyerovitch.lean",
    severity  = "error")
```

and only proceeds when the result is `[]`. Warnings are addressed
opportunistically (deprecations, style hints), but errors are always blocking.

This is what enforces the "never accumulate errors" rule.

---

## Workflow per item

```
       ┌─ pick next unchecked item from implementation list ──┐
       │                                                       │
       ▼                                                       │
write the def / theorem statement                              │
       │                                                       │
       ▼                                                       │
draft the proof (≤ 5 lines if possible)                        │
       │                                                       │
       ▼                                                       │
lean_diagnostic_messages ────► clean? ──no──► repair loop      │
       │                                       │               │
       │                              (search Mathlib,         │
       │                               try tactics,            │
       │                               adjust the statement)   │
       │                                       │               │
       │                                       ▼               │
       │                              (back to diagnostics)    │
       ▼ (yes)                                                 │
git commit (item + checklist update) ──────────────────────────┘
```

The repair loop is where the lean-lsp-mcp tools earn their keep.

---

## Lean LSP tools — what to reach for, when

The full set is documented in the
[`lean-lsp-mcp` README](https://github.com/oOo0oOo/lean-lsp-mcp); the subset we
use most often:

| Situation                                         | Tool                                                        |
| ------------------------------------------------- | ----------------------------------------------------------- |
| "Did this edit break anything?"                   | `lean_diagnostic_messages` (severity: error)                |
| "What is the goal at line N?"                     | `lean_goal` (omit column to see before/after)               |
| "What does identifier X mean / what is its type?" | `lean_hover_info` (column at the **start** of the name)     |
| "I want to test 3 candidate tactics."             | `lean_multi_attempt` with a list of snippets                |
| "Does this lemma name exist in Mathlib?"          | `lean_local_search` (fast, file index)                      |
| "Does Mathlib have a lemma that says ...?"        | `lean_leansearch` (natural language → Mathlib)              |
| "Find a lemma with type pattern `_ * (_ ^ _)`."   | `lean_loogle`                                               |
| "What lemmas could close this goal?"              | `lean_state_search`                                         |
| "What feeds a `simp` to make progress?"           | `lean_hammer_premise`                                       |
| "I added an `import`; rebuild."                   | `lean_build` (slow; only when imports change)               |

A few rules of thumb:

- **Always search for the lemma first.** Mathlib is enormous and most
  arithmetic / set-theoretic facts already exist. Five minutes with
  `lean_leansearch` saves hours of redoing the proof by hand.
- **Use `lean_multi_attempt` to A/B test tactics** when you're unsure whether
  to use `simp`, `omega`, `linarith`, `decide`, etc. It does not modify the
  file.
- **Don't trust your mental model of the goal** — ask `lean_goal` instead of
  guessing what the elaborator has produced.

---

## Commit hygiene

- One Lean item per commit. Keep `hochman_meyerovitch_implementation_list.md`
  updates either in the same commit or in a follow-up commit named
  `Track <item> progress`.
- Commit messages start with the item identifier (e.g. `G4.4f-pre:` or
  `J6c:`). This makes the log searchable.
- Never commit a file containing `sorry`, even temporarily. If a step is too
  large, break it into sub-items and commit only the pieces that compile
  cleanly.
- `git push` after each milestone, not after each commit, so that history
  is published in coherent chunks.

---

## Why this works (and when it doesn't)

This methodology trades raw throughput for predictability:

- **Throughput cost:** 50+ commits to finish what looks like a single
  theorem. Phases within a milestone proliferate (e.g. G4.4 ended up with
  Phases A–G).
- **Predictability gain:** the file *always* compiles. The agent is never
  stuck in a multi-error swamp. If a proof attempt fails, the failure is
  isolated to a single statement; we either succeed or revert that one
  statement.

Where it strains:

- **Heavy infrastructure jumps.** Some Lean 4 / Mathlib gaps require building
  a whole sub-library (e.g. `Primrec` rational arithmetic) before a single
  downstream theorem can be stated. In that case the implementation list
  should grow a *Dependencies* section (we did this for `Computable ℚ`)
  rather than blocking the main milestone.
- **Statements that need axiomatisation.** When a planned theorem requires a
  tool that genuinely doesn't exist in Mathlib (the variational principle,
  Mozes' theorem), we declare it as an `axiom` with a docstring naming the
  external reference. This is preferable to `sorry`: the file still compiles,
  the dependency is explicit, and the axiom can be discharged in a future
  pass.

---

## TL;DR

1. Plan in math first (`*_formalization_plan.txt`).
2. Translate the plan into a checklist of single-unit items
   (`*_implementation_list.md`).
3. Implement one item at a time; after every edit run
   `lean_diagnostic_messages`; do not move on until errors = 0.
4. Use `lean_leansearch` / `lean_loogle` / `lean_local_search` aggressively
   before writing any proof — Mathlib probably has it.
5. Commit on green; one item per commit; tick the checklist.
6. When an item is too big, split it. Re-organise the list to reflect what
   you've learned. The list is a living document, not a contract.
