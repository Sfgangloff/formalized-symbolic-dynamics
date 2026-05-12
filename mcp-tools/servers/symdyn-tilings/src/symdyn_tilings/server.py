import json

from fastmcp import FastMCP

from . import tilesets, transfer

mcp = FastMCP("symdyn-tilings")


@mcp.tool()
def symdyn_tilings_info() -> str:
    """Describe this server and its tool surface (Phase B)."""
    return (
        "symdyn-tilings — Wang tilesets and 2D SFT primitives.\n\n"
        "Status: Phase B (transfer-matrix entropy bounds + named-tileset catalog).\n\n"
        "Tools:\n"
        "  - symdyn_tileset_catalog_list():\n"
        "      list available named tilesets (e.g. 'kari_culik_13')\n"
        "  - symdyn_tileset_catalog_get(name):\n"
        "      retrieve a named tileset as JSON list of (N,S,E,W) tiles\n"
        "  - symdyn_wang_entropy_upper_bound(tileset_json_or_name, n):\n"
        "      log(spectral_radius(M_n)) / n — upper bound on h_top\n"
        "  - symdyn_wang_transfer_matrix_size(tileset_json_or_name, n):\n"
        "      report number of horizontally-compatible rows of width n\n"
        "\nNamed tilesets exposed: 'kari_culik_13', 'kari_culik_14_dgg',\n"
        "'two_color_full_2d'. (Berger / Robinson / Jeandel–Rao TBD.)\n"
    )


def _resolve_tiles(spec: str) -> list[tilesets.WangTile]:
    """Accept either a catalog name or a JSON-encoded list of tile dicts."""
    spec = spec.strip()
    if spec.startswith("["):
        return tilesets.tiles_from_dicts(json.loads(spec))
    return tilesets.get_tileset(spec)


@mcp.tool()
def symdyn_tileset_catalog_list() -> str:
    """List the named tilesets available in this server.

    Returns a JSON array of names.
    """
    return json.dumps(tilesets.list_catalog())


@mcp.tool()
def symdyn_tileset_catalog_get(name: str) -> str:
    """Look up a named Wang tileset.

    Returns a JSON array of `{N,S,E,W}` tile dicts. Use
    `symdyn_tileset_catalog_list` to see available names. Throws if the
    name is unknown.

    Example: `name='kari_culik_13'` returns 13 tiles in the
    Durand–Gamard–Grandjean (arXiv:1312.4126v2) encoding.
    """
    tiles = tilesets.get_tileset(name)
    return json.dumps(tilesets.tiles_to_dicts(tiles))


@mcp.tool()
def symdyn_wang_transfer_matrix_size(tileset: str, n: int) -> str:
    """Count horizontally-compatible rows of width `n` for a tileset.

    `tileset` is either a catalog name (e.g. 'kari_culik_13') or a JSON
    array of `{N,S,E,W}` tile dicts. Returns a JSON `{n_rows: int}`.

    Sanity check before calling `symdyn_wang_entropy_upper_bound`:
    transfer-matrix size is `n_rows × n_rows`, so this scales with the
    tileset and `n`. Practical limit ≈ 2000 rows.
    """
    tiles = _resolve_tiles(tileset)
    rows = transfer.enumerate_rows(tiles, n)
    return json.dumps({"n_rows": len(rows)})


@mcp.tool()
def symdyn_wang_entropy_upper_bound(tileset: str, n: int) -> str:
    """Compute the transfer-matrix entropy upper bound `log ρ(M_n) / n`.

    `tileset` is either a catalog name or a JSON array of tile dicts.
    `n` is the row width (must be ≥ 1).

    For any `n ≥ 1`, `log ρ(M_n) / n ≥ h_top(tileset)`. The bound is
    non-increasing in `n` and converges to `h_top` as `n → ∞`.

    Returns a JSON object `{n, n_rows, spectral_radius, bound}`.

    Caveats:
      - Naive eigenvalue computation; row count > 2000 may be slow.
      - Returns `bound = 0.0` for empty SFTs.

    Example: `symdyn_wang_entropy_upper_bound('kari_culik_13', 3)`
    yields a bound on the Kari–Culik 2D SFT entropy.
    """
    tiles = _resolve_tiles(tileset)
    result = transfer.entropy_upper_bound(tiles, n)
    return json.dumps(result)


def main() -> None:
    mcp.run()


if __name__ == "__main__":
    main()
