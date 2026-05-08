# Papers

Each subfolder corresponds to a single paper being formalized and is
**self-contained**: it holds the paper's PDF, formalization plan, per-item
implementation checklist, and Lean source(s) all together.

| Paper folder                                                            | Title                                                                                       | Status  |
| ----------------------------------------------------------------------- | ------------------------------------------------------------------------------------------- | ------- |
| [`HochmanMeyerovitch/`](HochmanMeyerovitch/)                            | Hochman & Meyerovitch (2007), characterization of multidimensional SFT entropies            | active  |

Cross-paper Lean helpers live in [`../dependencies/`](../dependencies/).

## Adding a new paper

1. Create `papers/<PaperShortName>/` (CamelCase).
2. Drop the PDF in.
3. Write `plan.txt` (long-form mathematical plan; identify the **main
   theorems** at the top).
4. Write `implementation_list.md` (per-item Lean checklist).
5. Add a `<PaperShortName>.lean` file with the formalization.
6. Add the new module to `lakefile.toml`'s `roots` list (e.g.
   `papers.PaperShortName.PaperShortName`).
7. Create a `README.md` in the paper folder summarising files and status.

See [`../docs/methodology.md`](../docs/methodology.md) for the methodology.
