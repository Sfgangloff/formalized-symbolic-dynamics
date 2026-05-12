from fastmcp import FastMCP

mcp = FastMCP("symdyn-shifts")


@mcp.tool()
def symdyn_shifts_info() -> str:
    """Describe this server and its planned tool surface.

    Useful as a sanity check that the server is registered and as a quick
    reminder of what symdyn-shifts will expose. Returns a Markdown blurb.
    """
    return (
        "symdyn-shifts — primitives for 1D and Z^d SFT and sofic shifts.\n\n"
        "Status: Phase A (skeleton). Real tools land in Phase B.\n\n"
        "Planned tools:\n"
        "  - symdyn_sft_admissible_count(forbidden, alphabet, shape, d=1):\n"
        "      count globally admissible patterns of given shape\n"
        "  - symdyn_sft_language_size(forbidden, alphabet, n, d=1):\n"
        "      |L_n(X)| (1D), or |L_{n×n}(X)| (2D)\n"
        "  - symdyn_sft_entropy_1d(forbidden, alphabet):\n"
        "      exact entropy via spectral radius of the transition matrix\n"
        "  - symdyn_sft_entropy_2d_bounds(forbidden, alphabet, n):\n"
        "      transfer-matrix upper/lower bounds for Z^2 SFT entropy\n"
        "  - symdyn_sofic_fischer_cover(forbidden_factors):\n"
        "      Fischer cover (minimal right-resolving labeled graph) from\n"
        "      forbidden factors\n"
        "  - symdyn_sofic_minimize_presentation(graph):\n"
        "      minimize a labeled graph by follower equivalence\n"
        "  - symdyn_sofic_is_sofic_via_dfa(samples_or_pattern, n_max):\n"
        "      DFA-minimization heuristic; supports the odd-shift sofic test\n"
        "  - symdyn_sft_cover_of_sofic(presentation):\n"
        "      explicit SFT cover of a sofic shift (Weiss-conjecture work)\n"
        "  - symdyn_lean_emit_subshift(forbidden, alphabet, name):\n"
        "      Lean 4 stub for the subshift\n"
    )


def main() -> None:
    mcp.run()


if __name__ == "__main__":
    main()
