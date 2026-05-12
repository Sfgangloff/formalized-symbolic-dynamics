from fastmcp import FastMCP

mcp = FastMCP("symdyn-complexity")


@mcp.tool()
def symdyn_complexity_info() -> str:
    """Describe this server and its planned tool surface.

    Useful as a sanity check that the server is registered and as a quick
    reminder of what symdyn-complexity will expose. Returns a Markdown blurb.
    """
    return (
        "symdyn-complexity — pattern-complexity tooling.\n\n"
        "Status: Phase A (skeleton). Real tools land in Phase B.\n\n"
        "Planned tools:\n"
        "  - symdyn_complexity_1d(words, n_max):\n"
        "      p_X(n) computed from a sample of words\n"
        "  - symdyn_complexity_2d(pattern, m_max, n_max):\n"
        "      p_x(m,n) for a finite or computable pattern\n"
        "  - symdyn_periods_2d(pattern):\n"
        "      compute the period lattice {v ∈ Z^2 : σ^v x = x}\n"
        "  - symdyn_nivat_check_finite(pattern, m, n):\n"
        "      check whether p(m,n) ≤ mn forces a period in this example\n"
        "  - symdyn_morse_hedlund_test(seq):\n"
        "      bounded p_X(n) ⇒ ultimately periodic test for a 1D sequence\n"
        "  - symdyn_lean_emit_complexity_lemma(pattern, name):\n"
        "      Lean 4 stub for a complexity-bound lemma\n"
    )


def main() -> None:
    mcp.run()


if __name__ == "__main__":
    main()
