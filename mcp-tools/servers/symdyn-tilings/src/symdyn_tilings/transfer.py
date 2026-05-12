"""Row-transfer-matrix entropy bounds for 2D Wang SFTs.

For a Wang tileset T, fix a row width `n`. A `valid row` of width `n` is
a horizontally-compatible sequence (t_1, ..., t_n) of tiles. Let
R_n(T) denote the set of valid rows. The transfer matrix is

    M_n[r, r'] = 1   iff r above r' is vertically compatible
                       (i.e. r[k].S == r'[k].N for all k = 1..n).

A standard argument (e.g. Friedland, "On the entropy of Z^d subshifts of
finite type") gives, for every n ≥ 1,

    h_top(T)  ≤  log ρ(M_n) / n,

where ρ(M_n) is the spectral radius of M_n. The bound is non-increasing
in n and converges to h_top(T) as n → ∞.
"""

from __future__ import annotations

import math
from typing import Sequence

import numpy as np

from .tilesets import WangTile


def enumerate_rows(tiles: Sequence[WangTile], n: int) -> list[tuple[int, ...]]:
    """Return all horizontally-compatible n-rows as tuples of tile indices.

    For n = 0 returns `[()]` by convention (single empty row).
    """
    if n < 0:
        raise ValueError(f"n must be ≥ 0, got {n}")
    if n == 0:
        return [()]
    rows: list[tuple[int, ...]] = [(i,) for i in range(len(tiles))]
    for _ in range(n - 1):
        extended: list[tuple[int, ...]] = []
        for r in rows:
            right_edge = tiles[r[-1]].E
            for i, t in enumerate(tiles):
                if right_edge == t.W:
                    extended.append(r + (i,))
        rows = extended
    return rows


def transfer_matrix(
    tiles: Sequence[WangTile], n: int
) -> tuple[list[tuple[int, ...]], np.ndarray]:
    """Build the n-row transfer matrix `M_n`.

    Returns `(rows, M)` where `rows = enumerate_rows(tiles, n)` and
    `M[i, j] = 1` iff `rows[i]` placed above `rows[j]` is vertically
    compatible (lower row's N edges equal upper row's S edges,
    pointwise).
    """
    rows = enumerate_rows(tiles, n)
    k = len(rows)
    M = np.zeros((k, k), dtype=np.int64)
    # Pre-compute S-tuple and N-tuple for each row to speed up.
    south = [tuple(tiles[i].S for i in r) for r in rows]
    north = [tuple(tiles[i].N for i in r) for r in rows]
    for i in range(k):
        s_i = south[i]
        for j in range(k):
            if s_i == north[j]:
                M[i, j] = 1
    return rows, M


def spectral_radius(M: np.ndarray) -> float:
    """Return the spectral radius (largest |eigenvalue|) of `M`."""
    if M.size == 0:
        return 0.0
    eigvals = np.linalg.eigvals(M.astype(float))
    return float(max(abs(e) for e in eigvals))


def entropy_upper_bound(tiles: Sequence[WangTile], n: int) -> dict:
    """Return the transfer-matrix entropy upper bound `log ρ(M_n) / n`.

    Returns a dict with `n`, `n_rows`, `spectral_radius`, and `bound`.
    If the SFT has no valid row of width `n` (empty), `bound = 0.0` and
    `spectral_radius = 0.0`.
    """
    if n < 1:
        raise ValueError(f"n must be ≥ 1, got {n}")
    rows, M = transfer_matrix(tiles, n)
    rho = spectral_radius(M)
    if rho == 0.0:
        bound = 0.0  # entropy of empty subshift is 0
    else:
        bound = math.log(rho) / n
    return {
        "n": n,
        "n_rows": len(rows),
        "spectral_radius": rho,
        "bound": bound,
    }
