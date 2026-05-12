from fastmcp import FastMCP

mcp = FastMCP("symdyn-viz")


@mcp.tool()
def symdyn_viz_info() -> str:
    """Describe this server and its planned tool surface.

    Useful as a sanity check that the server is registered and as a quick
    reminder of what symdyn-viz will expose. Returns a Markdown blurb.
    """
    return (
        "symdyn-viz — visualization for symbolic dynamics.\n\n"
        "Status: Phase A (skeleton). Real tools land in Phase B.\n\n"
        "Planned tools:\n"
        "  - symdyn_draw_pattern_2d(pattern, palette):\n"
        "      render a Z^2 pattern as a colored grid PNG\n"
        "  - symdyn_draw_wang_tileset(tileset):\n"
        "      render the tile palette with edge colors\n"
        "  - symdyn_draw_wang_tiling(tiling):\n"
        "      render an explicit Wang tiling\n"
        "  - symdyn_draw_presentation_graph(graph, with_labels=True):\n"
        "      labeled-graph drawing for a sofic presentation / Fischer cover\n"
        "  - symdyn_plot_complexity_curve(p, n):\n"
        "      plot p(n) (or p(m,n) as a heatmap)\n"
        "\n"
        "All draw_*/plot_* tools return a base64 PNG payload:\n"
        "  {\"image\": \"<base64-png>\", \"description\": \"...\"}\n"
    )


def main() -> None:
    mcp.run()


if __name__ == "__main__":
    main()
