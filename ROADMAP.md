# Research roadmap

This document is the long-term plan for the `formalized-symbolic-dynamics`
repository. It is a sibling of `SymbolicDynamics/README.md` (project
overview) and `SymbolicDynamics/docs/methodology.md` (per-commit
discipline). The roadmap describes *where the project is going* over
many papers and many months, not *how a single commit is made*.

## 1. Vision

Build a Lean 4 / Mathlib 4 library that formalizes a coherent slice of
modern symbolic dynamics — multidimensional SFTs, sofic shifts,
computability/entropy results, and the structural theorems that connect
them. Each formalized paper lives in its own self-contained folder
(`SymbolicDynamics/papers/<PaperShortName>/`) with the PDF, plan,
checklist, and Lean source side-by-side.

The library is **not just a translation of papers**. The long-term aim
is a *navigable* corpus where, given a concept, a researcher can:

- find every paper that uses it,
- find every definition that purports to capture it,
- see which of those definitions are proven equivalent (and how), and
- pick the formulation that fits their proof context.

## 2. Active and planned papers

| Status | Paper | Folder |
| --- | --- | --- |
| active  | Hochman & Meyerovitch (2007) — characterization of multidimensional SFT entropies | `papers/HochmanMeyerovitch/` |
| queued  | Hochman (2009) — universal minimal systems / dynamical embedding | TBD |
| queued  | Pavlov & Schraudner — sofic shifts on ℤ^d | TBD |
| queued  | Boyle–Pavlov–Schraudner — multidimensional sofic entropies | TBD |
| open    | A paper of the user's choice on tilings / Wang shifts | TBD |

The queue is a *suggestion*, not a commitment. Papers are added to the
queue when they share enough infrastructure with already-formalized
papers that the marginal cost is low.

## 3. Methodology recap

The single-commit discipline is fixed in
`SymbolicDynamics/docs/methodology.md`:

- one Lean item per commit,
- never commit/push when the file does not compile,
- never commit/push while a `sorry` remains,
- main theorems flagged with `[MAIN]` in markdown and `# MAIN THEOREM`
  in Lean source.

This roadmap does not relax any of those rules; it only describes the
shape of work *across* commits.

## 4. Definition uniformization

This is the central long-term concern of the project.

### 4.1 The problem

Different papers define the same object differently. *Topological
entropy* alone admits at least four flavours (limit of `(log N(F)) /
|F|` over Følner sequences, supremum over open covers, Bowen
metric-balls, variational supremum). Each flavour is most natural in a
different proof. Formalizing several papers naïvely produces several
incompatible `topEntropy` definitions and a wall of unrelated lemmas.

The naïve fix — pick one canonical definition and rewrite the others —
is wrong. It throws away the very feature that makes the alternative
formulations useful: each one *was* easier to use for some proof in
some paper.

### 4.2 The proposed approach

**Accept that the same mathematical object can have many definitions.**
Instead of forcing a single canonical form, build infrastructure that
lets the library carry several formulations *and prove they coincide*.

The plan has three pieces:

1. **Definition catalogue.** A central index of every definition in
   the library, grouped by the informal concept it tries to capture.
2. **Equivalence map.** A graph whose nodes are catalogue entries and
   whose edges are *proved* identity lemmas. Edges are *named theorems*
   and live in their own files (not buried inside paper folders).
3. **Refactor criterion.** An explicit, conservative criterion for
   when an equivalence justifies deleting one of the two definitions
   in favour of the other.

### 4.3 The catalogue

Concrete realisation: a directory `SymbolicDynamics/dictionary/` (peer
of `dependencies/`, `papers/`, `open-problems/`). It contains one
markdown file per *informal concept*, e.g. `topological_entropy.md`,
`sft.md`, `sofic_shift.md`, `block_gluing.md`. Each concept file
lists every Lean definition in the repo that captures the concept,
with:

- a fully-qualified Lean name,
- the file and line where it is defined,
- the typeclass signature (so we can spot which formulations are more
  general),
- a one-sentence informal description,
- the paper(s) where this formulation is used,
- pointers into the equivalence map (§4.4).

The catalogue is hand-curated. Resist the temptation to make it a
generated file: the value is in the *human classification* by informal
concept. (A separate `make catalogue-check` script can verify that
every catalogued name still resolves and warn about uncatalogued
candidates.)

### 4.4 The equivalence map

Realisation: a directory `SymbolicDynamics/equivalences/` containing
Lean files of the form `topEntropy_HM_eq_topEntropy_classical.lean`.
Each file contains exactly one (or a small bundle of) identity
theorem(s) connecting two catalogued definitions, plus the imports
needed to state them.

Properties of the equivalence map we should preserve:

- **Edges are theorems, not axioms.** An edge that is conjectured but
  unproved is recorded in the catalogue as a *missing edge*, not as an
  `axiom`.
- **The map is sparse.** With *n* definitions of a concept we do *not*
  prove all *n(n−1)/2* identities; we prove a spanning tree and let
  transitivity handle the rest. Auxiliary edges are added only when
  composing two equivalences is so painful that a direct lemma pays
  for itself.
- **The map carries metadata.** Each edge records hypotheses (e.g.
  "needs finite alphabet", "needs amenable group", "needs T2"). The
  same two definitions may have *different* equivalences under
  different hypothesis strengths.

Concretely, each concept's catalogue page should embed an ASCII or
mermaid graph of its equivalence map at the top.

### 4.5 Detecting candidate equivalences

When a new paper is added, *before* writing any new definition, the
agent should:

1. Open every catalogue page that names a concept the paper appears to
   use (search by paper keywords against catalogue concept names).
2. For each concept, check whether one of the existing definitions can
   be *reused as-is* in the new paper. If yes, reuse it.
3. If no existing definition fits, write a new one **and** add a
   catalogue entry **and** open an issue / TODO for a candidate
   equivalence to the closest existing definition.

Heuristics for "close enough to attempt an equivalence proof":

- Same informal concept name.
- Same return type (e.g. both produce `ℝ`, or both produce
  `Set (Lat d → α)`).
- Hypothesis signatures that are comparable (one is a strengthening of
  the other, or both reduce to the same thing under an extra
  assumption).
- Identical or near-identical first-order property the definition is
  meant to encode (e.g. "it is the smallest closed shift-invariant set
  containing X" is a strong hint).

When two definitions have completely different return types (e.g.
"entropy as a real" vs. "entropy as an element of `ℝ≥0∞`"), the edge is
not an equality but a *coercion-respecting equality*; record the
coercion explicitly in the equivalence file.

### 4.6 Refactor criterion

An equivalence does **not** automatically justify deleting a
definition. Multiple formulations have value. Removal of a definition
is justified only when **all** of the following hold:

1. There is a proved equivalence to a chosen "canonical" formulation.
2. The deprecated formulation is **not used** in any paper folder
   *outside* the one that introduced it (i.e. it has not been adopted
   as a working formulation by anyone else).
3. Either:
   a. the deprecated formulation is *strictly less general* (its
      typeclass signature is a strict strengthening of the canonical
      one), and no proof in the repo exploits the extra strength, **or**
   b. the deprecated formulation is *strictly less ergonomic* by an
      objectively measurable axis: longer proofs of the same downstream
      lemma, more imports needed, more universe constraints.

If the case for removal is anything weaker than the above, **keep both
definitions** and the equivalence theorem. The cost of carrying a
duplicated definition is small; the cost of removing one researcher's
preferred formulation is the loss of their proof's clarity.

### 4.7 What this is *not*

- It is not a replacement for `Mathlib`. When `Mathlib` already has a
  definition the dictionary points to it; the catalogue entry just
  records the name.
- It is not an excuse to avoid writing equivalences. The library's
  value compounds when the equivalence map fills in.
- It is not a separate verification project. Every entry/edge lives in
  Lean source files, type-checked the same way as the rest.

## 5. Cross-paper dependencies

`SymbolicDynamics/dependencies/` collects helpers used by more than
one paper (currently only `ComputableRat.lean`). The rule for moving a
helper from a paper folder into `dependencies/` is:

- it is *needed* by a second paper, **or**
- it is generically useful (computable rational arithmetic,
  finset/lattice combinatorics, Pi-space measure-theoretic plumbing)
  and a second use is *anticipated* within the next planned paper.

We resist speculative generality. A helper graduates only when there
is a concrete second consumer.

## 6. Open problems track

`SymbolicDynamics/open-problems/` is reserved for formalizations that
are not tied to a single paper — e.g. "is X computable?", "is the
entropy of d-dimensional sofic shifts the same set as that of
d-dimensional SFTs above d=2?". Each open-problem folder mirrors the
paper-folder structure (a plan, a checklist, a Lean file) but has no
PDF.

Promotion path: an open problem becomes a paper folder if a paper is
written about it; until then it stays in `open-problems/`.

## 7. Tooling and ergonomics

The methodology document describes the diagnostics-loop tooling
(`lean-lsp-mcp`). The roadmap-level tooling needs are:

- A **catalogue lint** that verifies every name in `dictionary/*.md`
  still resolves to a Lean declaration.
- An **equivalence lint** that verifies no equivalence file carries an
  `axiom` or `sorry` (the dictionary is a *proved* graph).
- A **paper-status lint** that compares each paper's
  `implementation_list.md` against its `MAIN THEOREM` markers in the
  Lean file and flags drift.

These are scripts, not part of the proof obligation.

## 8. Milestones (rough, calendar-free)

The following ordering captures dependency, not deadlines.

1. **Hochman–Meyerovitch necessity (Theorem 1.1 ⇒, Theorem 1.3).**
   Currently in progress; necessity (I1) and Theorem 1.3 (J9) are
   axiomatized-but-derived; H section is being discharged.
2. **Hochman–Meyerovitch sufficiency (I2/I3).** The construction.
   Multi-month.
3. **Theorem 1.2** (sofic shift entropies = SFT entropies for d ≥ 2).
4. **First multi-paper concept** under the dictionary regime (most
   likely *topological entropy*, since every queued paper uses it). At
   this point we commit to the §4 infrastructure: write the first
   catalogue page, the first equivalence file, and the first lint.
5. **Second paper formalization** *under* the dictionary regime —
   confirms the workflow scales.

## 9. Non-goals

- A general computability library inside `SymbolicDynamics/`. The
  `dependencies/ComputableRat.lean` file exists out of necessity; if it
  grows much further it should become its own Mathlib contribution.
- Performance optimisation. Build time and tactic speed are out of
  scope until a future user complains.
- Constructive / `Decidable` reformulations of every classical theorem.
  We use `noncomputable` freely.

## 10. Living document

This roadmap is rewritten when reality diverges from it, not on a
schedule. Treat any conflict between this file and a current paper's
`plan.txt` as a signal to reconcile (and the paper plan wins by
default — the roadmap is downstream of the work).
