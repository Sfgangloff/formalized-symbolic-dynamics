# Open problems

Folder reserved for formalizations of *open* problems in symbolic dynamics —
problems whose mathematical statement is settled but whose resolution (proof
or counter-example) is currently unknown.

Each open problem gets a folder with

- a `README.md` writing up the problem statement and references,
- a `<ProblemName>.lean` recording the **statement** in Lean
  (supporting definitions live in `../dependencies/`),
- optionally a `formalization_plan.md` / `implementation_list.md`
  while the formalization is still in flux (delete once the
  statement is fully recorded).

## Status tags

Every open problem's `README.md` carries a `**Status:** …` line at
the top using one or more of the following tags:

- `open` — no known proof or counter-example.
- `partially-solved` — proved in some special case (e.g. low
  dimension, restricted alphabet) but not in full generality.
- `solved` — proved or disproved; if disproved, the entry records
  the counter-example. The proof may or may not yet be formalized
  in Lean.
- `unpublished` — a solution exists but is not in a published paper
  (private communication, preprint, lost note, …). Usually combined
  with `partially-solved` or `solved`.

Multiple tags can apply at once (e.g. `partially-solved` +
`unpublished` for a result proved in `d = 2` only in private notes).
When a problem's status differs across cases (typically across
dimensions), the README's body should make that explicit.

## Current entries

- [`WeissConjecture/`](WeissConjecture/) — entropy-preserving SFT
  covers of sofic shifts. Status: `solved` (`d = 1`, classical) /
  `open` (`d ≥ 2`).
- [`OddShiftSoficity/`](OddShiftSoficity/) — is the multidimensional
  odd shift sofic? Status: `solved` (`d = 1`, trivial) /
  `partially-solved` + `unpublished` (`d = 2`) / `open` (`d ≥ 3`).
