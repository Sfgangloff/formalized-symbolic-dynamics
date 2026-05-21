"""Seed the Milestone-2 pilot Paper nodes (see ../gold/PILOT.md).

Idempotent: re-running updates existing rows, never duplicates. Run with
``uv run python scripts/seed_pilot.py``.
"""

from __future__ import annotations

from pathlib import Path

from ontology.schema import Paper, paper_id
from ontology.store import Store

# (arxiv_id, year, short title, [authors])
EXTRACTABLE = [
    ("math/0703206", 2007, "A characterization of the entropies of multidimensional SFT",
     ["M. Hochman", "T. Meyerovitch"]),
    ("1312.4126", 2013, "Aperiodic tilings and entropy",
     ["B. Durand", "G. Gamard", "A. Grandjean"]),
    ("1410.1572", 2014, "A minimal subsystem of the Kari-Culik tilings",
     ["J. Siefken"]),
    ("0910.2415", 2009, "Fixed-point tile sets and their applications",
     ["B. Durand", "A. Romashchenko", "A. Shen"]),
    ("1003.3103", 2010, "Effective closed subshifts in 1D can be implemented in 2D",
     ["B. Durand", "A. Romashchenko", "A. Shen"]),
    ("1602.06095", 2016, "Simulation of effective subshifts by two-dimensional SFT",
     ["N. Aubrun", "M. Sablik"]),
    ("1308.1702", 2013, "Speed of convergence for the realization of an effective "
     "subshift by a multidimensional SFT or sofic",
     ["A. Crumiere", "M. Sablik", "M. Schraudner"]),
    ("1412.2582", 2014, "A notion of effectiveness for subshifts on finitely "
     "generated groups", ["N. Aubrun", "S. Barbieri", "M. Sablik"]),
    ("1712.03182", 2017, "A characterization of entropy dimensions of minimal "
     "tridimensional SFT", ["S. Gangloff", "M. Sablik"]),
    ("2201.01991", 2022, "Subsystem entropies of shifts of finite type and sofic "
     "shifts on countable amenable groups",
     ["R. Bland", "K. McGoff", "R. Pavlov"]),
    ("0901.3600", 2009, "Universality in multidimensional symbolic dynamics",
     ["M. Hochman"]),
]

# Pre-arXiv classics: metadata-only citation anchors (§11).
METADATA_ONLY = [
    ("berger1966", 1966, "The undecidability of the domino problem", ["R. Berger"]),
    ("robinson1971", 1971, "Undecidability and nonperiodicity for tilings of the "
     "plane", ["R. M. Robinson"]),
    ("weiss1973", 1973, "Subshifts of finite type and sofic systems", ["B. Weiss"]),
    ("mozes1989", 1989, "Tilings, substitution systems and dynamical systems",
     ["S. Mozes"]),
    ("kari1996", 1996, "A small aperiodic set of Wang tiles", ["J. Kari"]),
    ("culik1996", 1996, "An aperiodic set of 13 Wang tiles", ["K. Culik II"]),
    ("hochman2009", 2009, "On the dynamics and recursive properties of "
     "multidimensional symbolic systems", ["M. Hochman"]),
    ("pavlovSchraudner", 2015, "Entropies of multidimensional shifts",
     ["R. Pavlov", "M. Schraudner"]),
    ("friedland1997", 1997, "On the entropy of Z^d subshifts of finite type",
     ["S. Friedland"]),
]


def _upsert(store: Store, pid: str, title: str, year: int,
            authors: list[str], relevance: int, tier: str) -> None:
    p = store.papers.get(pid)
    if p is None:
        store.papers[pid] = Paper(
            id=pid, title=title, authors=authors, year=year,
            categories=["math.DS"], relevance=relevance, fidelity_tier=tier,
        )
    else:
        p.title = p.title or title
        p.year = p.year or year
        p.relevance = max(p.relevance or 0, relevance)


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    store = Store.load(root)
    for aid, yr, title, auth in EXTRACTABLE:
        _upsert(store, paper_id(aid), title, yr, auth, 3, "")
    for key, yr, title, auth in METADATA_ONLY:
        _upsert(store, f"arxiv:{key}", title, yr, auth, 2, "metadata")
    store.save("seed-pilot")
    print(f"seeded {len(EXTRACTABLE)} extractable + "
          f"{len(METADATA_ONLY)} metadata-only; total {len(store.papers)}")


if __name__ == "__main__":
    main()
