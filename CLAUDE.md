# Claude Code project guide

This file is loaded automatically at the start of every session. It states
the invariants Claude must respect when working on this repository.

---

## Project & direction

A Lean 4 formalization of symbolic dynamics, paired with a Python "ontology"
package (`onto` CLI) that maintains a literature-wide knowledge graph of
definitions, lemmas, theorems, conjectures, and open problems with their
dependencies. The graph drives formalization order (root → leaf); the two
sides co-evolve in a batched cycle.

Strategic documents:

- `ROADMAP.md` — single-paper formalization workflow, dictionary, equivalences.
- `ONTOLOGY_PLAN.md` — knowledge-graph pipeline (Phases A–E, gates G1–G3).
  §6.5 describes the steady-state cycle this repo runs.

Per-session memory (kept under `~/.claude/projects/.../memory/`) contains
the live status, including `ontology-graph-direction.md` (current strategic
direction) — read it when reasoning about high-level next steps.

---

## Repository layout

```
SymbolicDynamics/        Lean 4 library  (build: `lake build`)
  axioms/                opaque constants                ← AXIOMS ONLY
  dependencies/          shared infrastructure           ← NO AXIOMS
  papers/<Paper>/        per-paper stubs, defs, proofs   ← NO AXIOMS
  openProblems/          Prop-valued open problems
  trajectories/          proof-attempt scratchpads
  docs/methodology.md    per-node formalization loop
ontology/                Python package + `onto` CLI
  snapshots/*.jsonl      canonical graph                 ← git-tracked
  build/, corpus/        derived / raw harvested data    ← gitignored
  gold/                  hand-curated gold subgraphs
mcp-tools/               local MCP servers (symdyn-*, proof-explorer, …)
scripts/check_symbolic_dynamics_policy.sh
                         module-partition lint (pre-push hook gate)
```

---

## Module partition (HARD invariants)

Enforced by `scripts/check_symbolic_dynamics_policy.sh`, the
`PostToolUse(Write|Edit)` Claude hook, and the `.git/hooks/pre-push` hook:

- `SymbolicDynamics/axioms/` may contain **only** `axiom` declarations.
- `SymbolicDynamics/dependencies/` may contain **no** `axiom` declarations.
- `SymbolicDynamics/papers/` may contain **no** `axiom` declarations.

To add an opaque constant for paper `P`: put it in `axioms/P.lean` and
import it from `papers/P/P.lean`. See `axioms/KariCulik.lean` and
`axioms/DGG.lean` for the pattern.

---

## `@ontology` markers

Every paper-level declaration (in `papers/`, `openProblems/`, and the
mirror `axioms/` files) carries an `-- @ontology: <node-id>` line directly
above it. After adding, moving, or renaming markers, reconcile the graph:

```bash
(cd ontology && uv run onto sync-lean)
```

This refreshes `lean_decl` / `lean_status` on each node and rewrites
`ontology/snapshots/{manifest,nodes}.jsonl`. Commit the snapshot updates in
the same logical batch as the Lean change.

---

## `sorry` budget

- `sorry` is **allowed** inside coherent stub batches under `papers/` and
  `openProblems/` (a stub batch = a set of statements-only `theorem … := by
  sorry` decls, each with an `@ontology` marker, intended to seed the
  ontology graph).
- `sorry` is **never** allowed in `dependencies/` or `axioms/`. Opaque
  content lives in `axioms/` as `axiom`, by design.
- A commit may introduce many sorries together when they share a bootstrap
  reason; subsequent commits should reduce the count, not grow it.

---

## Commit cadence

- One Lean item per commit (per `SymbolicDynamics/docs/methodology.md`).
- No errors carried across commits — `lake build` must succeed before each
  commit.
- Commit message: imperative summary under ~70 chars on the first line, body
  explaining *why*. End with:
  ```
  Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
  ```

---

## Build & verify commands

| What                       | Command                                                   |
| -------------------------- | --------------------------------------------------------- |
| Lean build                 | `(cd SymbolicDynamics && lake build)`                     |
| Lean LSP (preferred)       | `mcp__lean-lsp-mcp__*` tools                              |
| Policy lint                | `bash scripts/check_symbolic_dynamics_policy.sh`          |
| Ontology status            | `(cd ontology && uv run onto status)`                     |
| Ontology lint              | `(cd ontology && uv run onto lint)`                       |
| Sync Lean ↔ ontology       | `(cd ontology && uv run onto sync-lean)`                  |
| Next ready node            | `(cd ontology && uv run onto next)`                       |
| Python tests               | `(cd ontology && uv run pytest)`                          |

---

## Never do

- Force-push, `--no-verify`, `--no-gpg-sign` (any combination of these is
  blocked by `.claude/settings.json` `deny` + `.claude/hooks/bash-guard.sh`).
- `git push` — reserved for manual operation by the user.
- `git config user.*` or any `git config --global *`.
- `git commit --amend` or `git reset --hard` on a published commit.
- Hand-edit `lake-manifest.json` or `uv.lock` — they are auto-generated by
  `lake update` / `uv lock`.
- Hand-edit `.git/` directly.
- Hand-edit `ontology/snapshots/*.jsonl` — always go through `onto` CLI
  commands so the manifest hash stays consistent.

---

## When to pause and ask

- Introducing a new `axiom`, even into `axioms/`.
- Adding a new module (e.g. `dependencies/X.lean`, `papers/<NewPaper>/X.lean`)
  — also remember to wire it into `SymbolicDynamics/lakefile.toml`.
- Any git merge, rebase, or cherry-pick.
- Any deletion (file or directory) outside the gitignored derived dirs.

---

## Starting Claude Code on this project

```bash
cd /Users/silveregangloff/Desktop/formalized-symbolic-dynamics
claude
```

The project-shared `.claude/settings.json` and `.claude/hooks/` are picked
up automatically. The default permission mode is `acceptEdits` — Write/Edit
inside the repo auto-approve; arbitrary Bash still prompts unless covered
by the `allow` list.

For unattended runs (e.g. inside `/loop`), prefer the stricter mode:

```bash
claude --permission-mode dontAsk
```

which auto-denies anything not pre-approved. Never use
`--dangerously-skip-permissions`.

---

## Guardrails summary

Permissions and per-tool hooks are in `.claude/settings.json` and
`.claude/hooks/`. The pre-push git hook (`.git/hooks/pre-push`) runs the
policy lint at the push boundary as the final safety net.

- `PreToolUse(Bash)` → `.claude/hooks/bash-guard.sh`
- `PreToolUse(Write|Edit)` → `.claude/hooks/edit-guard.sh`
- `PostToolUse(Write|Edit)` → `.claude/hooks/post-lean-edit.sh`
- `Stop` → `.claude/hooks/stop-verify.sh` + `.claude/hooks/notify.sh`
- `Notification` → `.claude/hooks/notify.sh`
