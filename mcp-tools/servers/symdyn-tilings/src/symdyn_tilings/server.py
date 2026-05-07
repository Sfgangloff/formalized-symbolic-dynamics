from fastmcp import FastMCP

mcp = FastMCP("symdyn-tilings")


@mcp.tool()
def symdyn_tilings_info() -> str:
    """Describe this server and its planned tool surface.

    Useful as a sanity check that the server is registered and as a quick
    reminder of what symdyn-tilings will expose. Returns a Markdown blurb.
    """
    return (
        "symdyn-tilings — Wang tilesets and 2D SFT primitives.\n\n"
        "Status: Phase A (skeleton). Real tools land in Phase B.\n\n"
        "Planned tools:\n"
        "  - symdyn_wang_finite_tileability(tileset, m, n):\n"
        "      SAT (Z3) check for an m×n tileable rectangle\n"
        "  - symdyn_wang_periodic_search(tileset, period_max):\n"
        "      search for a periodic tiling up to period_max\n"
        "  - symdyn_wang_transfer_matrix(tileset, n):\n"
        "      build the n-row transfer matrix\n"
        "  - symdyn_wang_entropy_bounds(tileset, n):\n"
        "      log of row-spectral-radius / n; relevant to Kari–Culik\n"
        "  - symdyn_tileset_catalog_get(name):\n"
        "      named tilesets: 'berger', 'robinson', 'kari', 'culik',\n"
        "      'kari_culik', 'jeandel_rao'\n"
        "  - symdyn_lean_emit_tileset(tileset, name):\n"
        "      Lean 4 stub describing the tileset\n"
    )


def main() -> None:
    mcp.run()


if __name__ == "__main__":
    main()
