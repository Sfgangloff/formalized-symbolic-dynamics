"""Wang tile representation and named-tileset catalog.

A Wang tile is a unit square with colored edges (N, S, E, W). Two tiles
match vertically iff lower.N == upper.S, horizontally iff left.E ==
right.W. Edge colors are arbitrary strings — only equality matters.

The named catalog includes the Kari–Culik aperiodic tile set under the
DGG (arXiv:1312.4126v2) encoding, plus small test tilesets.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable


@dataclass(frozen=True)
class WangTile:
    """Wang tile with four colored edges."""

    N: str
    S: str
    E: str
    W: str


# Kari–Culik tiles, DGG (arXiv:1312.4126v2) encoding: 14 tiles t1..t14
# with `\newwangstyle{top}{bottom}{right}{left}`. We expose:
#   - `kari_culik_14_dgg`: all 14 tiles as in the DGG paper
#   - `dgg_14_first_13`:   DGG t1..t13 (drop t14). NOT the original
#                          Culik 1996 13-tile set — it is a truncation
#                          of the DGG construction. Empirically its
#                          transfer-matrix has spectral radius 0 at
#                          width n ≥ 4 (zero-entropy SFT), which is
#                          inconsistent with the original 13-tile
#                          Kari–Culik set's positive-entropy result
#                          (Durand–Gamard–Grandjean 2013). Retained
#                          for testing/pedagogy only.
# Colors are opaque labels matching DGG's TikZ definitions; correctness
# of graph-theoretic / transfer-matrix work depends only on edge-color
# equality, which is preserved.
_KC_TILES_14 = [
    WangTile(N="letter2", S="letter1", E="state01", W="state01"),  # t1
    WangTile(N="letter0", S="letter2", E="state03", W="state23"),  # t2
    WangTile(N="letter1", S="letter1", E="state23", W="state03"),  # t3
    WangTile(N="letter1", S="letter1", E="state11", W="state01"),  # t4
    WangTile(N="letter0", S="letter1", E="state13", W="state23"),  # t5
    WangTile(N="letter1", S="letter2", E="state23", W="state13"),  # t6
    WangTile(N="letter2", S="letter1", E="state11", W="state11"),  # t7
    WangTile(N="letter2", S="letter2", E="state13", W="statep3"),  # t8
    WangTile(N="letter1", S="letter1", E="state23", W="state13"),  # t9
    WangTile(N="letter1", S="letter1", E="state13", W="state03"),  # t10
    WangTile(N="letter1", S="letter1", E="state03", W="statep3"),  # t11
    WangTile(N="letter2", S="letter1", E="statep3", W="state03"),  # t12
    WangTile(N="letter2", S="letter1", E="state03", W="state13"),  # t13
    WangTile(N="letter2", S="letter1", E="state13", W="state23"),  # t14
]


# Full 2-color 2D shift: all 16 (N,S,E,W) tiles over {0,1}. The valid
# tilings are the full shift {0,1}^{Z^2}; entropy = log 2.
_TWO_COLOR_FULL = [
    WangTile(N=a, S=b, E=c, W=d)
    for a in ("0", "1")
    for b in ("0", "1")
    for c in ("0", "1")
    for d in ("0", "1")
]


CATALOG: dict[str, list[WangTile]] = {
    "kari_culik_14_dgg": _KC_TILES_14,
    "dgg_14_first_13": _KC_TILES_14[:13],
    "two_color_full_2d": _TWO_COLOR_FULL,
}


def list_catalog() -> list[str]:
    """Return sorted names of available tilesets."""
    return sorted(CATALOG.keys())


def get_tileset(name: str) -> list[WangTile]:
    """Return the tileset named `name`. Raises KeyError if unknown."""
    if name not in CATALOG:
        available = ", ".join(sorted(CATALOG.keys()))
        raise KeyError(f"Unknown tileset '{name}'. Available: {available}")
    return CATALOG[name]


def tiles_to_dicts(tiles: Iterable[WangTile]) -> list[dict[str, str]]:
    """Serialise tiles as JSON-friendly dicts."""
    return [{"N": t.N, "S": t.S, "E": t.E, "W": t.W} for t in tiles]


def tiles_from_dicts(data: Iterable[dict[str, str]]) -> list[WangTile]:
    """Parse tiles from JSON-friendly dicts."""
    return [WangTile(N=d["N"], S=d["S"], E=d["E"], W=d["W"]) for d in data]
