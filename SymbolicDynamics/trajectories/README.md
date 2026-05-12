# Trajectories

Attempts to prove (or disprove) questions stated in `../openProblems/`.

## Convention

- One **subfolder per question**, named after the Lean `Prop` it
  targets (e.g. `KariCulikEntropyComputableStatement/`).
- Each `.lean` file inside a subfolder is **one attempt**.
- Subfolders are created on demand — no need for placeholders for
  questions nobody has attempted yet.
- Attempts may be partial: a successful trajectory can prove a strictly
  weaker statement that documents progress toward the full one. The
  weaker statement is named explicitly (e.g.
  `kariCulikEntropy_isRightRE` for a partial attempt at
  `KariCulikEntropyComputableStatement`).
- Per project policy, **committed files must not contain `sorry`**.
  Failed attempts that rely on unproved intermediate steps should not
  be committed; record the obstruction in the file's docstring and
  delete or rewrite the file before staging.

## Eligible targets

Targets in `openProblems/`:

- `WeissConjectureStatement`
- `OddShiftSoficityStatement`

Targets in `openProblems/KariCulikEntropy/generated_questions/`:

- `KariCulikEntropyComputableStatement`
- `KariCulikEntropyAlgebraicStatement`
- `DGGQ1_OnePairAloneIsDense`
- `DGGQ2a_RestrictedTilesetHasPositiveEntropy`
- `DGGQ2b_FiniteExclusionDrivesEntropyToZero`
- `DGGQ3_HorizontalShiftIsSofic`

The main file in `openProblems/KariCulikEntropy/` records the value
`kariCulikEntropy : ℝ`, not a `Prop`, so it has no trajectory folder.

## Current subfolders

- [`KariCulikEntropyComputableStatement/`](KariCulikEntropyComputableStatement/)
  — one partial attempt proving the right-r.e. half.
