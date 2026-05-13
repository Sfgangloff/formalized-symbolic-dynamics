"""Finite-rectangle Wang tileability via backtracking DFS.

Decides whether an `m` (rows) by `n` (columns) rectangle can be tiled by
a given Wang tileset, respecting NSEW edge-matching rules within the
rectangle. Edges along the rectangle's outer boundary are unconstrained
unless the caller pins them.

For small `m·n` (say ≤ 64) this is faster than building a SAT instance.
For larger rectangles a Z3 encoding would scale better but is omitted
here to avoid the heavy `z3-solver` build dependency.
"""

from __future__ import annotations

from typing import Optional, Sequence

from .tilesets import WangTile


def is_tileable_rectangle(
    tiles: Sequence[WangTile], m: int, n: int, max_solutions: int = 1
) -> dict:
    """Search for tilings of an `m × n` rectangle by `tiles`.

    Returns `{tileable: bool, n_solutions: int, witness: Optional[list[list[int]]]}`.

    - `tileable = True` iff at least one tiling exists.
    - `n_solutions = min(max_solutions, # tilings found before stopping)`.
    - `witness`: a single tiling, given as an `m×n` array of tile
      indices (rows top-to-bottom; columns left-to-right). `None` if no
      tiling exists.
    """
    if m < 1 or n < 1:
        raise ValueError(f"m, n must be ≥ 1; got m={m}, n={n}")
    grid: list[list[int]] = [[-1] * n for _ in range(m)]
    solutions: list[list[list[int]]] = []

    def fill(pos: int) -> None:
        if len(solutions) >= max_solutions:
            return
        if pos == m * n:
            solutions.append([row[:] for row in grid])
            return
        r, c = divmod(pos, n)
        for idx, t in enumerate(tiles):
            # Horizontal: left neighbor's E == this.W
            if c > 0:
                left = tiles[grid[r][c - 1]]
                if left.E != t.W:
                    continue
            # Vertical: above neighbor's S == this.N
            if r > 0:
                above = tiles[grid[r - 1][c]]
                if above.S != t.N:
                    continue
            grid[r][c] = idx
            fill(pos + 1)
            grid[r][c] = -1
            if len(solutions) >= max_solutions:
                return

    fill(0)
    witness: Optional[list[list[int]]] = solutions[0] if solutions else None
    return {
        "tileable": bool(solutions),
        "n_solutions": len(solutions),
        "witness": witness,
    }


def search_periodic_tiling(
    tiles: Sequence[WangTile], period_h: int, period_v: int
) -> dict:
    """Search for a `(period_h, period_v)`-periodic tiling of Z² by `tiles`.

    A periodic tiling exists iff a `period_v × period_h` rectangle has a
    tiling whose right-edge column matches its left-edge column and
    bottom-edge row matches its top-edge row (wrap-around).

    Returns `{periodic: bool, witness: Optional[list[list[int]]]}`.
    """
    if period_h < 1 or period_v < 1:
        raise ValueError(f"periods must be ≥ 1; got h={period_h}, v={period_v}")

    grid: list[list[int]] = [[-1] * period_h for _ in range(period_v)]
    found: list[list[list[int]]] = []

    def fill(pos: int) -> None:
        if found:
            return
        if pos == period_v * period_h:
            # Check wrap-around
            for r in range(period_v):
                left = tiles[grid[r][0]]
                right = tiles[grid[r][period_h - 1]]
                if right.E != left.W:
                    return
            for c in range(period_h):
                top = tiles[grid[0][c]]
                bot = tiles[grid[period_v - 1][c]]
                if bot.S != top.N:
                    return
            found.append([row[:] for row in grid])
            return
        r, c = divmod(pos, period_h)
        for idx, t in enumerate(tiles):
            if c > 0:
                left = tiles[grid[r][c - 1]]
                if left.E != t.W:
                    continue
            if r > 0:
                above = tiles[grid[r - 1][c]]
                if above.S != t.N:
                    continue
            grid[r][c] = idx
            fill(pos + 1)
            grid[r][c] = -1
            if found:
                return

    fill(0)
    return {
        "periodic": bool(found),
        "witness": (found[0] if found else None),
    }
