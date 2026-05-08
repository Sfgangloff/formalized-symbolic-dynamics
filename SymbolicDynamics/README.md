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
│   └── METHODOLOGY.md            # how this project is being formalized
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
[`docs/METHODOLOGY.md`](docs/METHODOLOGY.md).

In short: a plan + a checklist + the
[lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) diagnostics loop, with
**one Lean item per commit, no `sorry` ever, and no errors carried across
commits**.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".
