# ontology

Implementation of `../ONTOLOGY_PLAN.md`: a literature-wide directed
knowledge graph of symbolic dynamics that drives root→leaf formalization.

This is **Milestone 1** of the plan (§10): the schema + storage skeleton,
the full `onto` CLI, the validation lints, and the phase A–E pipeline
modules. The deterministic phases run end-to-end now; the LLM-driven and
human-gated phases (relevance scoring, prose/relation extraction, the L3
identity judge) sit behind explicit interfaces with reproducible no-LLM
baselines, to be wired to a model during the pilot (Milestone 2).

## Design refinement vs the plan

The plan's §3.1 names the `math-search` MCP tools. Those are only available
to the in-session agent, not to standalone Python, so the **production
pipeline talks to the public arXiv API directly** (stdlib `urllib` + Atom
parsing for search; `https://arxiv.org/e-print/<id>` tarballs for source).
This makes the pipeline self-contained and reproducible. The MCP tools
remain useful for ad-hoc exploration by the agent.

## Layout

```
ontology/                 python package (schema, store, phases A–E, cli)
snapshots/   CANONICAL, git-tracked: papers/nodes/edges/merges .jsonl + manifest.json
build/       DERIVED, git-ignored: ontology.db + embeddings.faiss (rebuild with `onto build`)
corpus/      git-ignored: raw arXiv source per paper
reviews/     checkpoint-gate artifacts: G1 master list, G2 samples, G3 merge queue
gold/        hand-curated gold-standard subgraphs for evaluation
```

Canonical state is the JSONL in `snapshots/`. `build/` is a cache;
deleting it loses nothing.

## Quickstart

```bash
cd ontology
uv sync                       # installs dev deps; no runtime deps required
uv run onto status            # pipeline dashboard
uv run onto build             # snapshots/ -> build/ontology.db (+ embeddings)
uv run onto lint              # schema / dangling-ref / acyclicity lints
uv run pytest                 # unit tests
```

Per-phase (each resumable, state in the DB):

```bash
uv run onto harvest           # Phase A: arXiv -> papers + shards; stops at gate G1
uv run onto acquire           # Phase B: fetch source into corpus/
uv run onto extract <id...>   # Phase C: corpus/<id>/subgraph.json; sample -> gate G2
uv run onto dedup             # Phase D: build merge plan; ambiguous -> gate G3
uv run onto merge             # Phase D: apply confirmed merges into snapshots/
uv run onto export <fmt>      # graphml | cypher | mermaid | jsonl
uv run onto next [--target T] # Phase E: next ready-to-formalize node + its deps
```

## Checkpoint gates

The pipeline refuses to cross a gate until a signed marker exists:

- **G1** `reviews/G1_master_list.{md,csv}` → sign with `onto gate sign G1`
- **G2** `reviews/G2_sample_<batch>.md` → `onto gate sign G2:<batch>`
- **G3** `reviews/G3_merge_queue.jsonl` → resolve entries, then
  `onto gate sign G3`

A signature records the reviewer (`$USER`) and the snapshot hash, so a
later snapshot change re-opens the gate.

## Status of stubs

`RelevanceScorer`, `LLMExtractor`, `IdentityJudge`, `LeanIdentityProbe`
are protocols in their respective modules. Default implementations are
deterministic and conservative (structural-only extraction, no
auto-merges) so the whole pipeline is runnable and testable without a
model. Wiring a model is Milestone 2/3 work and is intentionally isolated
to those classes.
