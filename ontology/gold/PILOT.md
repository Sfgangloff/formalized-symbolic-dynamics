# Pilot corpus (Milestone 2)

The pilot is the **dependency neighborhood of the HM / Kari–Culik
formalization target** — not a random sample. It validates extraction
and *is* the gold standard the automated extractor is measured against
(ONTOLOGY_PLAN §9.1, §10.2). Per the strategy correction: we do **not**
harvest the whole field first; we extract this target closure, formalize
from it, and let formalization harden the graph (§6.3).

All arXiv IDs below were verified via `arxiv_search` (no guessed IDs).

## Extractable (arXiv source → Phase C)

| # | arXiv | authors / short title | role in the target closure |
|---|-------|-----------------------|----------------------------|
| 1 | `math/0703206` | Hochman & Meyerovitch, *Characterization of entropies of multidim. SFT* | **the target paper** (repo's active formalization); gold template |
| 2 | `1312.4126` | Durand, Gamard, Grandjean, *Aperiodic tilings and entropy* | Kari–Culik 14-tile set has positive entropy (repo's KariCulik work) |
| 3 | `1410.1572` | Siefken, *A minimal subsystem of the Kari–Culik tilings* | Kari–Culik structure |
| 4 | `0910.2415` | Durand, Romashchenko, Shen, *Fixed-point tile sets* | fixed-point construction; aperiodicity machinery |
| 5 | `1003.3103` | Durand, Romashchenko, Shen, *Effective closed subshifts 1D→2D* | answers Hochman's question; SFT-simulation backbone |
| 6 | `1602.06095` | Aubrun & Sablik, *Simulation of effective subshifts by 2D SFT* | effective ⇒ sofic realization (HM Thm 1.2 neighborhood) |
| 7 | `1308.1702` | Crumière, Sablik, Schraudner, *Speed of convergence …* | glues Hochman-2009 / DRS-2010 / Aubrun-Sablik-2010 |
| 8 | `1412.2582` | Aubrun, Barbieri, Sablik, *Effectiveness for subshifts on f.g. groups* | generalizes effectiveness; dedup stress-test |
| 9 | `1712.03182` | Gangloff & Sablik, *Entropy dimensions of minimal 3D SFT* | HM-style characterization; **author can validate at G2** |
| 10 | `2201.01991` | Bland, McGoff, Pavlov, *Subsystem entropies of SFT/sofic (amenable)* | entropy of SFT/sofic, amenable-group regime |
| + | `0901.3600` | Hochman, *Universality in multidimensional symbolic dynamics* | resolvable proxy for the Hochman-2009 hub |

## Metadata-only (pre-arXiv classics — §11: cited, not extracted)

These become `Paper` nodes with no source; they are citation targets
that anchor cross-paper `cites` / `attributed_to` edges.

| key | reference |
|-----|-----------|
| `berger1966` | R. Berger, *The undecidability of the domino problem*, Mem. AMS 66 (1966) |
| `robinson1971` | R. M. Robinson, *Undecidability and nonperiodicity for tilings of the plane*, Invent. Math. 12 (1971) |
| `weiss1973` | B. Weiss, *Subshifts of finite type and sofic systems*, Monatsh. Math. 77 (1973) |
| `mozes1989` | S. Mozes, *Tilings, substitution systems …*, J. Anal. Math. 53 (1989) |
| `kari1996` | J. Kari, *A small aperiodic set of Wang tiles*, Discrete Math. 160 (1996) |
| `culik1996` | K. Culik II, *An aperiodic set of 13 Wang tiles*, Discrete Math. 160 (1996) |
| `hochman2009` | M. Hochman, *On the dynamics and recursive properties of multidim. symbolic systems*, Invent. Math. 176 (2009) — arXiv id to resolve |
| `pavlovSchraudner` | Pavlov & Schraudner, *Entropies of multidim. shifts* — arXiv id to resolve |

## Why these ten

Papers 1–2 are exactly the repo's active targets (HM + Kari–Culik
entropy). 4–8 are the effective-subshift ⇒ SFT/sofic simulation chain
that HM Theorem 1.2 lives in. 3 and 9–10 stress dedup with
closely-related-but-distinct entropy/Kari–Culik statements (the §1.4
identity-not-equivalence test). The classics are the citation anchors
every one of them shares.
