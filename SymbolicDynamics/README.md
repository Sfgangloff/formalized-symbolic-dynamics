# SymbolicDynamics

A Lean 4 / Mathlib 4 formalization of papers in symbolic dynamics, currently
focused on:

- **Hochman & Meyerovitch (2007),** *A characterization of the entropies of
  multidimensional shifts of finite type* ([arXiv:math/0703206](https://arxiv.org/abs/math/0703206)).

The active formalization target is `SymbolicDynamics/HochmanMeyerovitch.lean`.

## Project structure

```
SymbolicDynamics/
├── SymbolicDynamics.lean         # library entry-point
├── lakefile.toml
├── lean-toolchain
├── README.md
├── docs/
│   └── methodology.md            # how this project is being formalized
├── papers/                       # one folder per paper, all materials co-located
│   └── HochmanMeyerovitch/
│       ├── README.md             # paper-level overview + status
│       ├── 0703206v1.pdf         # the paper
│       ├── plan.txt              # long-form mathematical plan
│       ├── implementation_list.md
│       └── HochmanMeyerovitch.lean   # the Lean formalization
├── dependencies/                 # cross-paper Lean helpers
│   ├── ComputableRat.lean
│   └── FactorMap.lean
└── openProblems/                 # open-problem formalizations
    └── WeissConjecture/
```

**Per-paper folders are self-contained**: PDF, plan, checklist, and Lean source
all live together under `papers/<PaperShortName>/`. Cross-paper helpers go in
`dependencies/`.

Lake is configured (in `lakefile.toml`) to recognise this layout via explicit
`roots` for the `SymbolicDynamics` library.

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

- A `## [MAIN] Main theorems` section at the top of
  `<paper>_formalization_plan.txt`, with each main theorem named, numbered
  (matching the paper), and tied to its implementation-list identifier.
- A `## [MAIN] Main theorems` summary block at the top of
  `<paper>_implementation_list.md`, with each entry prefixed `**[MAIN]**`.
- A `/-! # MAIN THEOREM N — ... -/` comment-block header (note the `#`, top-
  level) above each main theorem in the Lean source.

Searching for the literal string `MAIN THEOREM` (or `[MAIN]`) in any project
file returns the main results across plan, list, and source.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".
