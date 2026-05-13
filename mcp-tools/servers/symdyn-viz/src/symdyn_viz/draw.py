"""PNG rendering for Wang tilesets, tilings, and complexity curves.

Returns base64-encoded PNG payloads. Each tool produces a dict
`{"image": "<base64>", "description": "..."}` matching the MCP image
convention.
"""

from __future__ import annotations

import base64
import io
from typing import Sequence


def _png_to_base64(fig) -> str:
    buf = io.BytesIO()
    fig.savefig(buf, format="png", bbox_inches="tight", dpi=120)
    buf.seek(0)
    return base64.b64encode(buf.read()).decode("ascii")


def _color_for_label(label: str) -> tuple[float, float, float]:
    """Stable hash → RGB color in [0, 1]^3 for an arbitrary string label."""
    import hashlib

    h = hashlib.md5(label.encode("utf-8")).digest()
    return (h[0] / 255.0, h[1] / 255.0, h[2] / 255.0)


def draw_wang_tileset(tiles: Sequence[dict]) -> dict:
    """Render a Wang tileset as a grid of colored unit squares.

    Each tile is drawn as a square divided into N/S/E/W triangles whose
    fill colors come from the (hashed) edge labels. The tile's index is
    written in the center.
    """
    import matplotlib.pyplot as plt

    n = len(tiles)
    cols = min(7, max(1, n))
    rows = (n + cols - 1) // cols
    fig, ax = plt.subplots(figsize=(cols * 1.2, rows * 1.2))
    ax.set_aspect("equal")
    ax.set_xlim(-0.1, cols + 0.1)
    ax.set_ylim(-0.1, rows + 0.1)
    ax.invert_yaxis()
    ax.axis("off")

    for idx, t in enumerate(tiles):
        r, c = divmod(idx, cols)
        x0, y0 = c, r
        cx, cy = c + 0.5, r + 0.5
        # 4 triangles N, E, S, W
        corners = {
            "N": [(x0, y0), (x0 + 1, y0), (cx, cy)],
            "E": [(x0 + 1, y0), (x0 + 1, y0 + 1), (cx, cy)],
            "S": [(x0, y0 + 1), (x0 + 1, y0 + 1), (cx, cy)],
            "W": [(x0, y0), (x0, y0 + 1), (cx, cy)],
        }
        for side in ("N", "E", "S", "W"):
            tri = corners[side]
            colour = _color_for_label(str(t.get(side, "")))
            ax.fill([p[0] for p in tri], [p[1] for p in tri], color=colour, edgecolor="black", linewidth=0.5)
        ax.text(cx, cy, str(idx + 1), ha="center", va="center", fontsize=8, color="white", weight="bold")

    fig.suptitle(f"Wang tileset ({n} tiles)", fontsize=10)
    img = _png_to_base64(fig)
    plt.close(fig)
    return {
        "image": img,
        "description": (
            f"Wang tileset with {n} tiles. Each tile shown as a square with 4 "
            f"triangular regions (N=top, E=right, S=bottom, W=left), filled "
            f"with hash-derived colors for each edge label."
        ),
    }


def draw_wang_tiling(tiles: Sequence[dict], witness: Sequence[Sequence[int]]) -> dict:
    """Render a Wang tiling given by a 2D array of tile indices.

    `witness[r][c]` is the index of the tile placed at row `r`, column `c`.
    """
    import matplotlib.pyplot as plt

    if not witness:
        raise ValueError("empty witness")
    m = len(witness)
    n = len(witness[0])
    fig, ax = plt.subplots(figsize=(n * 0.7, m * 0.7))
    ax.set_aspect("equal")
    ax.set_xlim(-0.05, n + 0.05)
    ax.set_ylim(-0.05, m + 0.05)
    ax.invert_yaxis()
    ax.axis("off")

    for r in range(m):
        for c in range(n):
            idx = witness[r][c]
            t = tiles[idx]
            x0, y0 = c, r
            cx, cy = c + 0.5, r + 0.5
            corners = {
                "N": [(x0, y0), (x0 + 1, y0), (cx, cy)],
                "E": [(x0 + 1, y0), (x0 + 1, y0 + 1), (cx, cy)],
                "S": [(x0, y0 + 1), (x0 + 1, y0 + 1), (cx, cy)],
                "W": [(x0, y0), (x0, y0 + 1), (cx, cy)],
            }
            for side in ("N", "E", "S", "W"):
                tri = corners[side]
                colour = _color_for_label(str(t.get(side, "")))
                ax.fill([p[0] for p in tri], [p[1] for p in tri], color=colour, edgecolor="black", linewidth=0.3)

    fig.suptitle(f"Wang tiling ({m} × {n})", fontsize=10)
    img = _png_to_base64(fig)
    plt.close(fig)
    return {
        "image": img,
        "description": (
            f"{m} × {n} Wang tiling rendered with hash-derived edge colors."
        ),
    }


def plot_complexity_curve(values: Sequence[int], label: str = "p(n)") -> dict:
    """Plot a complexity curve `n ↦ value[n-1]` on a log-y axis.

    Adds reference lines `n` (Morse–Hedlund threshold) and `n + 1`
    (Sturmian) for orientation.
    """
    import matplotlib.pyplot as plt

    n_max = len(values)
    xs = list(range(1, n_max + 1))
    fig, ax = plt.subplots(figsize=(5, 3.5))
    ax.plot(xs, values, "o-", label=label)
    ax.plot(xs, xs, "--", color="gray", label="n (M–H threshold)")
    ax.plot(xs, [n + 1 for n in xs], ":", color="gray", label="n + 1 (Sturmian)")
    ax.set_xlabel("n")
    ax.set_ylabel("complexity")
    ax.set_yscale("log")
    ax.grid(True, alpha=0.3)
    ax.legend(loc="best", fontsize=8)
    ax.set_title(f"Factor complexity ({label})", fontsize=10)
    img = _png_to_base64(fig)
    plt.close(fig)
    return {
        "image": img,
        "description": (
            f"Log-y plot of complexity {label}(n) for n = 1..{n_max}. "
            f"Dashed line = n (Morse–Hedlund: p(n) ≤ n forces eventual "
            f"periodicity). Dotted line = n + 1 (attained by Sturmian words)."
        ),
    }
