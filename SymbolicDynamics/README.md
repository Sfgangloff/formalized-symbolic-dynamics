# SymbolicDynamics

A Lean 4 / Mathlib 4 formalization of papers in symbolic dynamics, currently
focused on:

- **Hochman & Meyerovitch (2007),** *A characterization of the entropies of
  multidimensional shifts of finite type* ([arXiv:math/0703206](https://arxiv.org/abs/math/0703206)).

The active formalization target is `SymbolicDynamics/HochmanMeyerovitch.lean`.

## Project structure

```
SymbolicDynamics/
├── docs/
│   └── methodology.md            # how this project is being formalized
├── SymbolicDynamics/
│   ├── HochmanMeyerovitch.lean   # main formalization file
│   └── Dependencies/
│       └── ComputableRat.lean    # Primrec/Computable for ℚ (helper)
├── lakefile.toml
└── lean-toolchain
```

The plan and progress checklist live at the project root:

- `hochman_meyerovitch_formalization_plan.txt` — the long-form mathematical plan.
- `hochman_meyerovitch_implementation_list.md` — the per-item checklist (what
  is built / what is next).

## Methodology

This project is being formalized incrementally with the help of an LLM coding
agent. The methodology — designed to keep the LLM productive over very long
sessions by never letting errors accumulate — is documented in
[`docs/methodoology.md`](docs/methodology.md).

In short: a plan + a checklist + the
[lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) diagnostics loop, with
**one Lean item per commit, no `sorry` ever, and no errors carried across
commits**.

### Marking main theorems

Every paper formalized in this project lists its **main theorems up front**:

- A `## Main theorems` section at the top of `<paper>_formalization_plan.txt`,
  with each main theorem named, numbered (matching the paper), and tied to its
  implementation-list identifier.
- A "🎯 Main theorems" summary block at the top of `<paper>_implementation_list.md`.
- A `/-! ## 🎯 MAIN THEOREM N — ... -/` comment-block header above each main
  theorem in the Lean source.

The 🎯 emoji is used as a fast `grep`/search marker so any agent picking up the
project can immediately locate the main results across plan, list, and source.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".
