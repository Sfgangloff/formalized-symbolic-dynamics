import json

from fastmcp import FastMCP

from . import draw

mcp = FastMCP("symdyn-viz")


@mcp.tool()
def symdyn_viz_info() -> str:
    """Describe this server and its tool surface (Phase B)."""
    return (
        "symdyn-viz — visualization for symbolic dynamics.\n\n"
        "Status: Phase B (Wang tileset / tiling rendering + complexity curves).\n\n"
        "Tools:\n"
        "  - symdyn_draw_wang_tileset(tiles_json):\n"
        "      render a Wang tileset as a grid; each tile shows N/E/S/W\n"
        "      colored triangles\n"
        "  - symdyn_draw_wang_tiling(tiles_json, witness_json):\n"
        "      render an m×n Wang tiling from a tile-index witness\n"
        "  - symdyn_plot_complexity_curve(values_json, label):\n"
        "      log-y plot of a factor-complexity sequence with M–H and\n"
        "      Sturmian reference lines\n"
        "\nAll draw_*/plot_* tools return a base64 PNG payload:\n"
        "  {image: <base64-png>, description: ...}\n"
    )


@mcp.tool()
def symdyn_draw_wang_tileset(tiles_json: str) -> dict:
    """Render a Wang tileset as a PNG grid.

    `tiles_json` is a JSON array of `{N, S, E, W}` dicts (matching the
    output of `symdyn_tileset_catalog_get`). Returns
    `{image, description}` with base64 PNG.
    """
    tiles = json.loads(tiles_json)
    return draw.draw_wang_tileset(tiles)


@mcp.tool()
def symdyn_draw_wang_tiling(tiles_json: str, witness_json: str) -> dict:
    """Render a Wang tiling as a PNG.

    `tiles_json`: JSON array of `{N, S, E, W}` dicts.
    `witness_json`: JSON 2D array of tile indices (rows top-to-bottom,
    columns left-to-right) — e.g. the `witness` field of
    `symdyn_wang_finite_tileability` output.
    """
    tiles = json.loads(tiles_json)
    witness = json.loads(witness_json)
    return draw.draw_wang_tiling(tiles, witness)


@mcp.tool()
def symdyn_plot_complexity_curve(values_json: str, label: str = "p(n)") -> dict:
    """Plot a factor-complexity sequence on a log-y axis.

    `values_json`: JSON array `[p(1), p(2), ...]`. Annotates the plot
    with `n` (Morse–Hedlund threshold) and `n + 1` (Sturmian).
    """
    values = json.loads(values_json)
    return draw.plot_complexity_curve(values, label=label)


def main() -> None:
    mcp.run()


if __name__ == "__main__":
    main()
