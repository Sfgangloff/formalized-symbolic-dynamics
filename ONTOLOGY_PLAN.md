# Ontology plan

This document is a long-term strategic plan, a **sibling of `ROADMAP.md`**.
Where `ROADMAP.md` describes how single papers get formalized and how the
hand-curated Lean dictionary/equivalence map should be kept, this document
describes the **upstream knowledge graph**: a literature-wide directed graph
of symbolic-dynamics objects (definitions, lemmas, theorems, conjectures,
open problems) and their dependencies, harvested from arXiv, deduplicated,
and used to *drive* formalization root-to-leaf.

It is deliberately exhaustive. It is also a *living document* in the sense of
`ROADMAP.md` §10: when reality diverges, the document is rewritten, and any
in-progress paper `plan.txt` wins by default.

---

## 0. Scope and decisions already taken

Three decisions frame everything below (chosen 2026-05-19):

- **Corpus scope: core symbolic dynamics.** Subshifts; shifts of finite
  type; sofic shifts; multidimensional shifts; Wang tiles and tilings; the
  domino problem; cellular automata (as they bear on subshifts); topological
  entropy and factor complexity of shifts; structural theorems connecting
  these. *Out of core (cited but not extracted):* general ergodic theory,
  combinatorics on words for its own sake, aperiodic order / quasicrystals
  as a physics topic, general topological dynamics. Adjacent papers are
  still recorded as `Paper` nodes when cited, but only core papers are
  extracted into the object graph.
- **Storage: hybrid, file-based.** Canonical source of truth is
  **git-tracked JSONL snapshots** (diff-friendly, reviewable in PRs,
  reproducibly rebuildable). A **SQLite** database and a **FAISS** vector
  index are *derived build artifacts*, rebuilt from the snapshots by a
  single command and git-ignored. No server, no managed service.
- **Automation level: checkpoint gates.** The pipeline runs fully
  automatically *between* gates, but stops for human review at three
  points: (G1) the master paper list, (G2) a per-batch extraction sample,
  (G3) every dedup MERGE decision whose ambiguity exceeds a threshold.

### 0.1 Relationship to `ROADMAP.md` §4

`ROADMAP.md` §4 ("Definition uniformization") describes a *hand-curated*,
*Lean-embedded* catalogue (`SymbolicDynamics/dictionary/`) and equivalence
map (`SymbolicDynamics/equivalences/`), scoped to content that is *already
formalized*. This plan does not replace that — it **feeds** it:

- The ontology's `Concept` nodes correspond to dictionary concept pages.
- The ontology's *proved* `equivalent_to` edges correspond to equivalence
  files.
- Every formalized node carries a `lean_decl` backlink, so the Lean
  dictionary becomes a **materialized projection** of the subgraph that has
  been formalized, kept in sync by a lint (§8.4).

The ontology is broad, machine-extracted, and *claimed* (statements may be
wrong or duplicated until verified). The Lean dictionary is narrow,
hand-curated, and *proved*. The ontology is upstream; the Lean library is
the part of it that has been discharged. Recommended (not done here without
your say-so): add a one-line cross-reference from `ROADMAP.md` §4 to this
file.

---

## 1. The data model

The whole project hinges on the schema. Get this right before writing a
harvester.

### 1.1 Node kinds

| kind | meaning |
|------|---------|
| `Paper` | an arXiv (or, rarely, non-arXiv) document |
| `Definition` | a definiendum + definiens; **may be inline in prose**, not in an environment |
| `Theorem` / `Lemma` / `Proposition` / `Corollary` | a proved assertion |
| `Claim` | an asserted-but-unlabeled result stated in running text |
| `Conjecture` | an unproved assertion the authors believe |
| `OpenProblem` | a question, possibly multi-part, possibly parameterized by a regime (e.g. "for `d ≥ 3`") |
| `Example` / `Counterexample` | a witnessing object |
| `Construction` | a *named reusable object* (e.g. "the Kari–Culik shift", "the Robinson tiling", "the hat") |
| `Concept` | an *informal umbrella* clustering many `Definition`s (bridge to `ROADMAP.md` §4 dictionary; e.g. `concept:topological_entropy`) |

`Concept` nodes are not extracted from a single paper; they are introduced
during dedup/curation when several `Definition`s are recognized as flavours
of one informal idea (the §4.5 "same informal concept" heuristic).

### 1.2 Node properties

Stored on every non-`Paper`, non-`Concept` node:

- `id` — stable, content-derived (see §1.5).
- `kind`, `name` / `title`.
- `statement_latex` — normalized canonical LaTeX (see normalization, §4.4).
- `statement_text` — plain-language gloss (LLM-produced; this is what gets
  embedded and what a human reads in review).
- `hypotheses[]` — structured list of conditions (for results).
- `conclusion` — structured.
- `parameters[]` — regime tags: dimension `d`, alphabet finiteness, group
  (ℤ^d / amenable / free), mixing/gluing assumptions. Critical: many
  symbolic-dynamics statements are *true in one regime and open in another*
  (e.g. sofic ⇒ SFT-entropy for `d ≥ 2`; the odd shift for `d = 1` vs
  `d ≥ 3`). The regime is part of the node identity.
- `tags[]` — concept tags (SFT, sofic, entropy, computability, tiling, CA,
  minimal, mixing, block-gluing, …).
- `status` — for `Conjecture`/`OpenProblem`: `open` | `partially-resolved`
  | `resolved` | `refuted` | `folklore`; for results: `with-proof` |
  `proof-sketch` | `stated-only`.
- `aliases[]` — every name/label this object has been seen under.
- `provenance[]` — list of
  `{paper, label, env_name, section, char_span, run_id, confidence,
  human_verified}`. A node can be stated by several papers; each gets a
  provenance record.
- `content_hash`, `structural_sig` — for dedup (§5).
- `embedding` — vector (stored in the embeddings table, not inline).
- `lean_decl` — nullable: fully-qualified Lean name + `file:line`.
- `lean_status` — nullable: `stated` | `proved` | `axiomatized` | `sorry`.
- `merged_from[]`, `canonical_id` — non-destructive dedup bookkeeping.
- `created_run`, `updated_run`.

### 1.3 Edge kinds

All edges are directed and typed. `depends_on` is the spine that drives
formalization order.

| edge | from → to | meaning |
|------|-----------|---------|
| `defines` | Paper → Definition/Construction | source of a definition |
| `states` | Paper → Theorem/…/Conjecture/OpenProblem | source of a statement |
| `depends_on` | result → result/Definition | the **statement or proof** of the source uses the target; property `where ∈ {in_statement, in_proof}` |
| `uses_definition` | result → Definition | a `depends_on` kept distinct because it is the binding constraint for formalization order |
| `specializes` | A → B | A is a special case / instance of B (B more general) |
| `equivalent_to` | A ↔ B | mathematically equivalent, **not the same statement**; carries `regime` + coercion metadata; `proved ∈ {claimed, lean-proved}` |
| `same_as` | A ≡ B | *identity* (dedup result); after merge this is bookkeeping, not a live graph edge |
| `resolves` | Theorem → Conjecture/OpenProblem | property `effect ∈ {affirms, refutes, partial:<regime>}` |
| `refutes` | Theorem/Counterexample → Conjecture/Claim | a disproof |
| `improves` | A → B | strengthens a bound/result |
| `corollary_of` | Corollary → Theorem | |
| `instance_of` | Definition/Construction → Concept | bridge to the dictionary |
| `cites` | Paper → Paper | bibliographic |
| `attributed_to` | Node → Paper | "Theorem (Berger 1966)" cross-paper attribution |

Edge properties: `id`, `type`, `src`, `dst`, `regime`, `provenance[]`,
`confidence`, `human_verified`, `in_lean` (realized as a Lean
dependency/equivalence file), `notes`.

### 1.4 The identity vs equivalence distinction (critical)

You asked for "identical, not equivalent". We make this a hard rule:

- **`same_as` (merge):** the two are the *same statement* up to renaming
  bound variables, notation synonyms, and trivial reordering of
  hypotheses. After merge there is one node.
- **`equivalent_to` (no merge):** the two are provably inter-derivable but
  are *different statements* (different shape, different primitive
  notions, a non-trivial proof connects them). Both nodes survive; this is
  exactly the `ROADMAP.md` §4.4 equivalence-map edge.
- **`specializes` / `improves` (no merge):** asymmetric relations. A
  generalization is never merged with its special case.

Merging on equivalence (instead of identity) is the single worst failure
mode — it silently collapses distinct mathematics. Hence dedup defaults to
*not* merging, and the LLM judge (§5, L3) must return `same` with high
confidence to trigger a merge; anything else is an *edge*, not a merge.

### 1.5 Identifiers and idempotency

- Node `id = hash(kind ‖ normalized_statement)` for results/definitions;
  `Construction`/`Concept` get a curated slug (`construction:kari-culik`,
  `concept:topological-entropy`).
- Paper `id = arxiv:<id>` (or `doi:<…>` / `slug:<…>` for non-arXiv).
- Provenance natural key `(paper, env_name, label)` makes re-extracting a
  paper **idempotent**: the same statement re-extracted updates the
  existing node's provenance instead of forking a duplicate.
- Every merge is recorded in a `merges` log with the losing id, the
  canonical id, the justification, and the run — so **every merge is
  reversible** and the absorbed id is kept as a redirect tombstone.

---

## 2. Storage and on-disk layout

A new top-level directory, peer of `SymbolicDynamics/` and `mcp-tools/`:

```
ontology/
  README.md
  pyproject.toml              # uv, mirrors mcp-tools conventions
  ontology/                   # python package
    schema.py                 # dataclasses + SQLite DDL + migrations
    harvest.py  acquire.py  extract.py  dedup.py  merge.py
    embed.py    export.py    formalize.py
    cli.py                    # `onto <subcommand>`
  snapshots/                  # CANONICAL, git-tracked, diff-friendly
    papers.jsonl  nodes.jsonl  edges.jsonl  merges.jsonl
    manifest.json             # snapshot hashes + run ids (reproducible rebuild)
  corpus/<arxiv_id>/          # raw LaTeX/text source (git-ignored; large)
  build/                      # DERIVED, git-ignored, rebuildable
    ontology.db  embeddings.faiss
  reviews/                    # checkpoint-gate artifacts (G1/G2/G3)
  gold/                       # hand-curated gold standard for evaluation
```

- **Canonical = `snapshots/*.jsonl`.** One JSON object per line, stable key
  order, sorted by id. These are committed; PRs show real diffs of the
  graph.
- **Derived = `build/ontology.db` + `build/embeddings.faiss`.** Built by
  `onto build` from the snapshots; never committed; safe to delete.
- `manifest.json` records the content hash of each snapshot and the run
  that produced it, so any state is reproducible and a stale build is
  detectable.

A SQLite DDL sketch is in Appendix A.

Optionally (later, §8.5) a fifth MCP server `symdyn-ontology` exposes
read-only graph queries so the Lean-formalizing agent can ask "what should
I formalize next / what does node X depend on" from inside its loop.

---

## 3. Phase A — paper harvesting

Goal: a deduplicated master list of core symbolic-dynamics papers from the
start of the math arXiv (~1992) to today, as `Paper` nodes with metadata.
Output reviewed at gate **G1** before anything downstream runs.

### 3.1 Tools

`math-search` MCP: `arxiv_search`, `arxiv_get`, `arxiv_outline`,
`arxiv_fetch_source`, `arxiv_fetch_text`, `arxiv_extract_definitions`,
`arxiv_extract_math`, `arxiv_extract_citations`.

### 3.2 Query matrix

Iterate the cartesian product **{year} × {category} × {keyword}** because
the arXiv API caps a single result window; sharding by year+category+keyword
keeps every bucket under the cap and makes the run resumable.

- **Years:** 2026 → 1992, descending.
- **Categories:** `math.DS`, `cs.DM`, `cs.FL`, `cs.CC`, `math.LO`,
  `math.CO`; legacy archives for early years: `chao-dyn` (1993–),
  `nlin.CG`, `nlin.CD`, `comp-gas`. (The modern `math.DS` class only
  appears ~1998; pre-1998 dynamics preprints hide in `math.*` and
  `chao-dyn`.)
- **Keywords:** "symbolic dynamics", "subshift", "shift of finite type",
  "sofic shift", "Wang tiles", "Wang tiling", "domino problem",
  "aperiodic tiling", "multidimensional shift", "subshift of finite type",
  "cellular automata" (filtered hard — see relevance gate),
  "topological entropy" + "shift", "factor complexity", "block gluing",
  "minimal subshift", "substitution subshift", "S-adic", "tilings" +
  "computability".

### 3.3 Relevance gate

Keyword search over `cs.DM`/`nlin.CG`/`math.CO` returns many false
positives ("symbolic" computation, "cellular automata" in physics). Each
candidate gets an **LLM relevance score** (0–3) from title+abstract against
a written core-scope rubric. Score ≥ 2 enters the master list; 1 goes to a
"borderline" file for human inclusion at G1; 0 is dropped but logged (so a
later scope change can revisit without re-querying).

### 3.4 Deduplication of papers

Same arXiv id across versions → one node (track `latest_version`). Match
withdrawn/duplicate/journal-vs-preprint pairs by normalized title +
author-set + abstract embedding similarity; ambiguous pairs → G1.

### 3.5 Resumability

Per `(year, category, keyword)` shard: status `pending | done`, last
offset, result count, timestamp, stored in the DB. Re-running `onto
harvest` skips `done` shards and resumes partial ones. arXiv rate limits
are respected with backoff; a shard that 429s is left `pending`.

### 3.6 Output and gate G1

`reviews/G1_master_list.md` (and `.csv`): id, title, authors, year,
categories, relevance score, abstract. Human reviews: spot-check
borderline inclusions/exclusions, confirm scope, can hand-add known
papers. **Nothing in Phase B/C runs until G1 is signed off** (a
`reviews/G1.signed` marker with the reviewer + snapshot hash).

---

## 4. Phases B & C — acquisition and per-paper extraction

### 4.1 Phase B — source acquisition

For each core paper (relevance ≥ 2, G1-approved): fetch arXiv **LaTeX
source** via `arxiv_fetch_source` into `corpus/<id>/`. LaTeX is far better
than PDF for extraction: theorem environments, `\label`/`\ref`/`\cite`
give dependency edges almost for free. Fallbacks in order: `arxiv_fetch_text`,
then PDF text, then `arxiv_outline` + `arxiv_extract_*` only. Record which
fidelity tier each paper got (extraction confidence depends on it).
Resumable per paper.

### 4.2 Phase C — per-paper subgraph extraction

For each paper, produce `corpus/<id>/subgraph.json` validated against the
schema, then a per-batch sample goes to gate **G2**.

1. **Environment detection.** Parse `\newtheorem` declarations first —
   environment names are *per-paper* (`thm`, `theorem`, `lem`, `prop`,
   `defn`, `dfn`, `conj`, `prob`, `ques`, …). Then extract every such
   environment: kind, `\label`, statement body, optional name in
   `[...]`, and (for results) the following `proof` body.

2. **Inline / prose objects.** A dedicated LLM pass over the sectioned
   text extracts what environments miss, which you flagged explicitly:
   - definitions introduced in running prose ("We say a subshift is *block
     gluing* if …") with no `definition` environment;
   - **named constructions** ("the Kari–Culik shift", "the hat tile")
     that are objects, not statements;
   - conjectures/open problems stated only in discussion text.

3. **Dependency edges.**
   - *Explicit, in-paper:* resolve `\ref`/`\eqref` and "by Theorem 3.2",
     "using Lemma 4" → `depends_on(where=in_statement|in_proof)`.
   - *Proof mining:* an LLM pass per `proof` body lists which prior results
     it invokes (including ones named only in prose) → `depends_on`.
   - *Cross-paper:* resolve `\cite` keys to bibliography entries; resolve
     bib entries to arXiv ids via `arxiv_extract_citations` + title/author
     search → `cites` (Paper→Paper) and, when a specific external result is
     invoked, `attributed_to` / cross-paper `depends_on`.

4. **Subtle text-encoded relations.** A typed relation-extraction LLM pass
   over each statement plus its surrounding prose, emitting only schema
   edge types (`specializes`, `generalizes`, `equivalent_to` (claimed),
   `resolves`, `refutes`, `improves`, `instance_of`). This is where
   "Theorem 2 strengthens the main result of [7]" or "this answers a
   question of Weiss" becomes an edge. Every such edge carries the text
   span as provenance and a confidence.

5. **Normalization & enrichment.** For each node: canonicalize
   `statement_latex` (expand paper-local macros, alpha-rename bound
   variables, map notation synonyms via a maintained lexicon — `Σ^{ℤ^d}`,
   `A^{ℤ^d}`, `X ⊆ A^{ℤ^d}` …); produce `statement_text`; split
   hypotheses/conclusion; infer `parameters[]`/`tags[]`; compute
   `content_hash`, `structural_sig`; embed `statement_text`.

6. **Gate G2.** Per batch of ~20 papers, sample ~3 papers' subgraphs for
   human review against the source PDF: node recall, edge correctness,
   regime tagging. A batch failing G2 (precision/recall below the §9
   thresholds) is re-extracted with prompt fixes before Phase D sees it.

The per-paper subgraph is **not** written to the global snapshots yet —
Phase D does the merge.

---

## 5. Phase D — dedup and merge into the global graph

This is the operation you described: not "append", but "is this object
already in the graph?". A new paper's subgraph is merged node-by-node.

### 5.1 The dedup ladder

For each incoming node, in order, cheapest first:

- **L0 — exact.** Equal `content_hash` (post-normalization) → strong
  same-candidate.
- **L1 — structural bucketing.** Restrict candidates to same `kind` +
  same `structural_sig` (kind, sorted hypothesis-type tags,
  conclusion-type tag, parameter arity) + overlapping concept tags.
- **L2 — semantic retrieval.** Embed `statement_text`; FAISS cosine
  top-`k`; take the **first 4–5** (your spec).
- **L3 — LLM identity adjudication.** For each candidate pair, an LLM
  judge with the §1.4 rubric returns
  `{verdict ∈ same|specializes|generalizes|equivalent|related|unrelated,
  confidence, regime_diffs, justification}`.
  - `same` & confidence ≥ τ_high → **merge** (§5.2).
  - `specializes`/`generalizes`/`equivalent`/`improves`/`related` → **add
    that typed edge, do not merge.**
  - `same` & confidence ∈ [τ_low, τ_high), or any verdict the judge marks
    low-confidence → **review queue → gate G3.**
  - all `unrelated` → it is a genuinely new node; add it.
- **L4 — Lean identity (late, optional).** *Only when both candidates
  already carry `lean_decl`.* Probe `@A = @B` / `A ↔ B` with
  `rfl`/`Iff.rfl`/`decide`/trivial `exact?` via `lean-lsp-mcp`. A trivial
  (defeq/`rfl`) proof confirms `same`. A *non-trivial* proof means they
  are merely `equivalent_to` — **do not merge**, downgrade to an
  equivalence edge. L4 runs as a repair pass after formalization and feeds
  corrections back into the graph.

#### Design note — why Lean can't be the primary dedup gate

You proposed checking identity "with Lean if possible". The catch:
**at dedup time almost nothing is formalized yet** (formalization is Phase
E, *after* the graph exists). So Lean identity is a *chicken-and-egg*: it
can only adjudicate pairs where *both* sides already have a `lean_decl`,
which is a tiny minority during graph construction. Therefore the primary
gate is semantic + structural + LLM adjudication (L0–L3), and L4 is a
*later confirmation/repair* pass that progressively hardens the graph as
formalization fills in. This is a deliberate correction to the original
sketch, not an omission.

### 5.2 The merge operation (non-destructive, idempotent)

When L3/L4 confirm `same`:

1. **Pick canonical** deterministically: prefer the node already in the
   global graph; tie-break by earliest publication year, then most-cited,
   then lexicographic id. (Never silently prefer the *more general* of two
   non-identical statements — if generality differs they were not `same`.)
2. **Fold** the absorbed node's `aliases`, `provenance`, `tags`,
   `parameters`, `lean_decl` into the canonical node (union, dedup).
3. **Rewire edges** — exactly your rules:
   - both endpoints already in the graph and an equivalent edge (same
     type + regime) already exists → **do not add**; union its
     provenance.
   - both endpoints in the graph, edge absent → **add** the edge.
   - an endpoint not yet in the graph → add that node first, then the
     edge, **using the canonical id** so the edge's representation matches
     what the graph already stores.
4. **Log** the merge to `merges.jsonl` (`losing_id`, `canonical_id`,
   verdict, confidence, run, justification). Keep the losing id as a
   **redirect tombstone** so external references resolve and
   re-extraction stays idempotent. Every merge is reversible from this
   log.

### 5.3 Connected-component canonicalization

`same_as` is transitive: periodically union-find the `same_as` closure and
re-point all edges to component representatives, so transitivity does not
leave dangling near-duplicates.

### 5.4 Gate G3

Any pair in `[τ_low, τ_high)` (the ambiguous band) is *not* auto-merged;
it lands in `reviews/G3_merge_queue.jsonl` with both statements, the
candidates, the judge's justification, and a one-keystroke
merge/edge/separate decision. The pipeline proceeds with these nodes
**unmerged** until a human rules; a bad auto-merge is far costlier than a
transient duplicate. G3 decisions are themselves logged as provenance
(human-labeled training data for tuning τ).

---

## 6. Phase E — formalization driver

Once the global graph exists (even partially), it *orders* formalization.

### 6.1 Selecting and ordering

- Restrict the graph to nodes reachable from a chosen **target subgraph**
  (initially the Hochman–Meyerovitch / Kari–Culik / DGG neighborhood
  already in flight — this is where `ROADMAP.md` milestones 1–3 live).
- **Topologically sort** by `uses_definition` ∪ `depends_on(in_statement)`.
  Roots = definitions and lemmas whose statement-dependencies are all
  already formalized. Formalize roots first, then peel inward toward the
  target theorem (the leaf).
- A node is "ready" when every `in_statement` dependency has
  `lean_status ∈ {proved, axiomatized}`. `in_proof`-only dependencies do
  not block *stating* a node (matching the existing axiomatize-then-derive
  practice for HM I1/J9).

### 6.2 Per-node loop (reuses existing methodology unchanged)

For each ready node, follow `SymbolicDynamics/docs/methodology.md`
verbatim: plan → implementation checklist → `lean-lsp-mcp` diagnostics
loop, **one Lean item per commit, no `sorry`, no errors carried across
commits**. Before writing a new definition, run the `ROADMAP.md` §4.5
candidate-equivalence check **against the ontology** (now automatable: the
`Concept`/`equivalent_to` neighborhood is already in the graph).

### 6.3 Refine-after-each-node (the feedback loop)

You asked to "refine after formalizing each node". Formalizing routinely
reveals graph errors: a missing hypothesis, a `depends_on` that was
actually `in_proof` not `in_statement`, two "different" lemmas that are
defeq, a regime that was mis-tagged. After each formalized node:

- write back `lean_decl` + `lean_status`;
- run the **L4** Lean-identity pass over that node's L2 semantic
  neighbors (now that it has a `lean_decl`) — possibly triggering a late
  merge or an equivalence edge;
- emit any discovered corrections (missing edge, wrong regime, split
  node) as a **graph patch** committed to the snapshots with provenance
  `human_verified` (formalization *is* verification);
- materialize the §0.1 projection: a proved `equivalent_to` edge becomes
  an `equivalences/` file; a `Concept` with ≥ 2 formalized `Definition`s
  gets/updates its `dictionary/` page.

So Phase E is not downstream-only; it is a loop that *hardens* the graph
the formalization touches.

---

### 6.4 Integrating already-formalized Lean assets

The repo already contains substantial Lean formalization of HM and the
Kari–Culik neighborhood (`SymbolicDynamics/papers/HochmanMeyerovitch/`,
`dependencies/`, `axioms/`, `openProblems/`, `trajectories/`). Phase E
must **not** redo that — it must back-link existing declarations into
the graph so `onto next` skips them and the L4 Lean-identity probe can
fire on their neighbors.

The mechanism is the `lean_decl` + `lean_status` fields already on
`Node` (§1.2). They are populated from three sources, in order of
authority:

1. **Manual, during gold curation.** Every gold subgraph that covers a
   paper with pre-existing Lean (HM is the template, §10.2) sets
   `lean_decl` to the fully-qualified Lean name and `lean_status` to
   `proved` / `axiomatized` / `stated` / `sorry`. This is how
   integration starts.
2. **Doc-comment annotation in Lean source.** A convention
   `-- @ontology: <node-id-or-slug>` above (or in the docstring of) a
   declaration is read by `onto sync-lean` and pushed into the graph.
   Cheap, in-repo, reviewable in PRs, doesn't bloat the snapshots with
   data Lean already records.
3. **Heuristic auto-suggestion (later).** Cosine-match the Lean
   declaration's docstring against `statement_text`; suggestions land in
   `reviews/G3_merge_queue.jsonl` for human confirmation — same gate
   that handles ambiguous dedup. Never an auto-merge.

A new `onto sync-lean` reconciles these three sources, flags every
`lean_decl` that no longer resolves (Lean decl renamed/deleted), and
warns about Lean `MAIN THEOREM` markers (`SymbolicDynamics/README.md`
convention) with no graph node — an orphan main theorem is a graph gap,
not a Lean problem. The §8.4 lean-sync lint becomes the CI gate.

When `onto next` proposes a target *X* whose neighbors carry
`lean_decl`, the Phase-E loop first runs **L4** (the Lean identity probe)
against those neighbors; if defeq/`rfl` identity holds, no new Lean def
is created — an `equivalent_to` edge is added and `X.lean_decl` points
at the existing Lean name. This is the runtime side of integration: the
graph drives toward "one Lean object per ontology node", with the
existing repo as the bootstrap.

The materialized projection (§0.1) then regenerates from the graph:
each `Concept` with ≥2 formalized `Definition` instances yields a
`SymbolicDynamics/dictionary/` page; each `proved` `equivalent_to` edge
whose endpoints both carry `lean_decl` becomes a
`SymbolicDynamics/equivalences/` file. The hand-curated `ROADMAP.md` §4
catalogue and the graph become two views of the same data, kept in sync
by the lint.

### 6.5 The steady-state cycle (the systematic mechanism)

The integration of §6.4 is not a one-shot setup but a **repeatable
batched algorithm**. One iteration of the cycle = one batch of papers;
each iteration grows both the graph *and* the Lean library, with
bounded scope per cycle.

| step | command | what it does |
|------|---------|--------------|
| 1. select batch | (curation) | choose the next ~5–10 papers — typically the closest unprocessed neighborhood of the current formalization target |
| 2. acquire     | `onto acquire --only …`     | fetch LaTeX sources |
| 3. extract     | `onto extract --only …`     | structural baseline subgraphs (LLM extractor when wired, M3) |
| 4. gold-curate | (hand or LLM + G2 review)   | promote each subgraph to a hand/LLM-vetted gold; bootstrap back-links for any pre-existing Lean |
| 5. merge       | `onto merge`                | dedup against the existing graph; ambiguous pairs → G3 |
| 6. sync-lean   | `onto sync-lean`            | pull in `-- @ontology:` back-links from any Lean written since the last cycle |
| 7. plan        | `onto next --target T`      | proposes ready unformalized nodes in root→leaf order |
| 8. formalize   | (per existing methodology)  | one Lean item per commit, no sorry, no errors; add `-- @ontology:` to each new decl |
| 9. loop        |                             | back to step 1 (new batch) or step 6 (continue formalizing within the current batch) |

Two cycles are running at once: a **graph cycle** (steps 1–5) and a
**formalization cycle** (steps 6–8). Step 6 is the meeting point.

Two non-obvious properties make the cycle stable:

- **Bootstrap is the same operation as steady state.** Step 4 of the
  *first* iteration on a paper that already has Lean code is identical
  to step 4 on a fresh paper, except `lean_decl`/`lean_status` are
  filled in from the existing repo instead of left empty. There is no
  separate "migration" mode — the existing HM/Kari–Culik formalization
  is integrated by treating it as the first batch.
- **The cycle is reversible.** Every merge is logged and tombstones
  redirect; every `lean_decl` set by `sync-lean` is reproducible from
  the doc-comment. If a later batch reveals an earlier decision was
  wrong, the merge log + tombstones unwind it.

The cycle is intentionally **not coupled to a calendar**. Batch size
and cadence are set by the formalizer; an open batch (steps 1–6 done
but 7–8 still in flight) is fine and is in fact the normal state of
the project.

## 7. Pipeline orchestration

`onto` CLI subcommands, each resumable, each stage's state in the DB:

```
onto harvest      # Phase A  → papers + shards; stop at G1
onto acquire      # Phase B  → corpus/<id>/ sources
onto extract      # Phase C  → corpus/<id>/subgraph.json; stop at G2
onto dedup        # Phase D  → review queue; stop at G3 on ambiguity
onto merge        # Phase D  → apply confirmed merges into snapshots
onto build        # rebuild build/ontology.db + embeddings.faiss
onto export       # GraphML / Cypher / per-concept mermaid / JSONL
onto status       # per-paper, per-stage progress dashboard
onto next         # Phase E  → next ready-to-formalize node + its deps
```

- Every run writes a manifest (`run_id`, inputs, snapshot hashes,
  tool/model versions) for reproducibility.
- Stages are pure functions of (snapshots, corpus, run params); re-running
  is idempotent thanks to §1.5 natural keys.
- `onto build` is the only thing that touches `build/`; it is never
  required for correctness, only for speed.

---

## 8. Tooling, lints, and the optional MCP server

- **8.1 Schema validation lint** — every snapshot line validates against
  `schema.py`; every edge endpoint resolves (or is a redirect tombstone).
- **8.2 Dangling-reference lint** — no `\ref`/`\cite`-derived edge points
  at a non-existent node.
- **8.3 Acyclicity lint** — `uses_definition` ∪
  `depends_on(in_statement)` is a DAG (cycles are extraction errors;
  report the cycle).
- **8.4 Lean-sync lint** — every node with a `lean_decl` resolves to a
  real Lean declaration (extends the `ROADMAP.md` §7 catalogue lint to the
  whole graph); every `equivalences/` file corresponds to a `proved`
  `equivalent_to` edge and carries no `axiom`/`sorry`.
- **8.5 Optional `symdyn-ontology` MCP server** — read-only tools
  (`onto_query`, `onto_neighbors`, `onto_next_target`,
  `onto_concept_page`) so the Lean-formalizing agent consults the graph
  inside its loop. Built only after the graph proves useful, mirroring
  `mcp-tools/` conventions (FastMCP, uv workspace).

---

## 9. Quality, evaluation, and risks

### 9.1 Gold standard and metrics

Hand-curate a `gold/` set of ~10 papers' subgraphs (the §10.1 pilot).
Measure, per release of the extraction prompts:

- node **recall** (extracted / true) and **precision**, by kind;
- edge precision/recall, by edge type (dependency edges weighted highest —
  they drive formalization order);
- dedup **merge precision** (merges that are truly identical) and **merge
  recall** (true duplicates actually merged).

**Acceptance thresholds** (tunable, initial): node recall ≥ 0.90 for
`Theorem`/`Definition`; `depends_on(in_statement)` edge precision ≥ 0.95
(false dependency edges corrupt formalization order); **merge precision ≥
0.99** (false merges corrupt the graph; recall can lag — duplicates are
cheap, false merges are not). A batch below threshold blocks at G2.

### 9.2 Risk register

| risk | mitigation |
|------|------------|
| LLM hallucinates statements/edges | every node/edge carries a verbatim source span; G2 sampling; gold-standard metrics |
| **False merge collapses distinct math** | identity-not-equivalence rule (§1.4); τ_high gate; G3 for the ambiguous band; every merge reversible (§5.2) |
| bib→arXiv resolution noise | confidence on `cites`; unresolved cites kept as opaque bib nodes, not dropped |
| LaTeX variability / no source | fidelity tiers (§4.1); confidence scaled by tier |
| Lean-identity chicken-and-egg | L4 is a *late repair* pass, not the primary gate (§5.1 design note) |
| scale / arXiv rate limits | year×cat×keyword shards, backoff, resumable; pilot before full harvest |
| extraction prompt drift | versioned prompts; gold metrics gate every prompt change |
| graph rot vs Lean | §8.4 sync lint in CI |

---

## 10. Milestones (dependency-ordered, calendar-free)

Mirrors `ROADMAP.md` §8 style. Ordering is dependency, not deadline.

1. **Schema + storage skeleton.** `ontology/` package, `schema.py`,
   snapshots/build split, `onto build/status`, validation lints (§8.1–8.3).
   No data yet.
2. **Pilot (≈10 papers).** Hand-pick the HM/DGG/Kari–Culik neighborhood
   (Hochman–Meyerovitch `math/0703206`, Durand–Gamard–Grandjean, Kari's
   aperiodic set, Berger, Robinson, Mozes, a Weiss sofic paper,
   Aubrun–Sablik, Pavlov–Schraudner, Hochman). Run B→C→D *manually
   curated* into `gold/`. This both seeds the graph and creates the
   evaluation set.
3. **Extraction validated.** Iterate Phase C prompts until pilot metrics
   clear §9.1 thresholds against `gold/`.
4. **Full harvest (Phase A) + G1.** Only after extraction is trusted on
   the pilot — otherwise we harvest into a pipeline we can't trust.
5. **Bulk B→C→D** over the core corpus, batched, G2/G3 gates live.
6. **First formalization driven by `onto next`** on the HM/Kari–Culik
   target subgraph — confirms Phase E and the §6.3 feedback loop, and
   reconciles with `ROADMAP.md` milestones 1–3.
7. **Materialized projection.** First `dictionary/` page + `equivalences/`
   file generated/maintained from the graph (`ROADMAP.md` milestone 4
   discharged *from* the ontology rather than by hand).
8. **Steady state.** New paper → `onto harvest`(incremental) → extract →
   dedup → formalize the now-reachable nodes; graph and Lean library grow
   together.

The pilot deliberately precedes the full harvest: validating extraction on
known papers before scaling is cheaper than rebuilding a corrupted graph.

---

## 11. Open decisions (resolve before the phase that needs them)

- **Embedding model** (needed before Phase C/D): a local sentence-encoder
  vs an API embedding. Affects reproducibility (local = deterministic,
  git-friendly) vs quality. *Leaning local* for reproducibility; revisit
  if dedup recall is poor.
- **τ_low / τ_high** merge thresholds: set empirically from the pilot's
  G3-labeled pairs; start conservative (high τ_high) to favour precision.
- **Non-arXiv core references** (Lind–Marcus, Berger 1966, books): include
  as metadata-only `Paper` nodes with no extraction (citation targets
  only) — confirm this is acceptable.
- **CI cost** of the §8.4 Lean-sync lint over a large graph: may need to
  scope it to nodes with `lean_decl` only (cheap) — likely fine.

---

## Appendix A — SQLite DDL sketch (derived store)

```sql
CREATE TABLE papers (
  id TEXT PRIMARY KEY,            -- arxiv:xxxx.xxxxx
  title TEXT, authors TEXT, year INT, categories TEXT,
  abstract TEXT, relevance INT, fidelity_tier TEXT, latest_version TEXT
);
CREATE TABLE nodes (
  id TEXT PRIMARY KEY, kind TEXT, name TEXT,
  statement_latex TEXT, statement_text TEXT,
  hypotheses TEXT, conclusion TEXT, parameters TEXT, tags TEXT,
  status TEXT, content_hash TEXT, structural_sig TEXT,
  lean_decl TEXT, lean_status TEXT, canonical_id TEXT,
  created_run TEXT, updated_run TEXT
);
CREATE TABLE aliases  (node_id TEXT, alias TEXT);
CREATE TABLE provenance (
  node_id TEXT, paper TEXT, label TEXT, env_name TEXT,
  section TEXT, char_span TEXT, run_id TEXT,
  confidence REAL, human_verified INT
);
CREATE TABLE edges (
  id TEXT PRIMARY KEY, type TEXT, src TEXT, dst TEXT,
  regime TEXT, where_ TEXT, proved TEXT, confidence REAL,
  human_verified INT, in_lean INT, notes TEXT
);
CREATE TABLE edge_provenance (edge_id TEXT, paper TEXT, char_span TEXT, run_id TEXT);
CREATE TABLE embeddings (node_id TEXT PRIMARY KEY, vec BLOB);
CREATE TABLE merges (
  losing_id TEXT, canonical_id TEXT, verdict TEXT,
  confidence REAL, run_id TEXT, justification TEXT
);
CREATE TABLE shards (
  year INT, category TEXT, keyword TEXT,
  status TEXT, last_offset INT, count INT, ts TEXT,
  PRIMARY KEY (year, category, keyword)
);
CREATE INDEX nodes_kind ON nodes(kind);
CREATE INDEX nodes_hash ON nodes(content_hash);
CREATE INDEX edges_src  ON edges(src);
CREATE INDEX edges_dst  ON edges(dst);
```

`embeddings.faiss` is built from `embeddings.vec`; both live in `build/`
and are rebuilt by `onto build` from the git-tracked JSONL snapshots.
```
