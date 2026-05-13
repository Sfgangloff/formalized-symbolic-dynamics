import json

from fastmcp import FastMCP

from . import complexity

mcp = FastMCP("symdyn-complexity")


@mcp.tool()
def symdyn_complexity_info() -> str:
    """Describe this server and its tool surface (Phase B)."""
    return (
        "symdyn-complexity — 1D pattern complexity and Morse–Hedlund.\n\n"
        "Status: Phase B (1D factor complexity for SFTs + words; M–H test).\n\n"
        "Tools:\n"
        "  - symdyn_complexity_1d_sft(alphabet, forbidden, n_max):\n"
        "      p_X(1)..p_X(n_max) for a 1D SFT\n"
        "  - symdyn_complexity_1d_word(word, n_max):\n"
        "      factor complexity of a finite word\n"
        "  - symdyn_complexity_1d_periodic(period, n_max):\n"
        "      factor complexity of the bi-infinite period word\n"
        "  - symdyn_morse_hedlund_check(complexity_values):\n"
        "      Morse–Hedlund eventual-periodicity test\n"
        "\nPlanned (not yet exposed):\n"
        "  - symdyn_complexity_2d(tileset, m, n)\n"
        "  - symdyn_periods_2d, symdyn_nivat_check_finite\n"
    )


def _parse_alphabet(spec: str) -> list[str]:
    s = spec.strip()
    if s.startswith("["):
        return [str(x) for x in json.loads(s)]
    return [c for c in s if not c.isspace()]


def _parse_forbidden(spec: str) -> list[list[str]]:
    s = spec.strip()
    if s.startswith("["):
        return [[str(c) for c in w] for w in json.loads(s)]
    return [[c for c in w.strip()] for w in s.split(",") if w.strip()]


@mcp.tool()
def symdyn_complexity_1d_sft(alphabet: str, forbidden: str, n_max: int) -> str:
    """Compute `p_X(n)` for `n = 1..n_max` where `X` is a 1D SFT.

    Returns JSON `{n_max, p_X: [int, ...]}`.

    Example: golden-mean shift (no `11`) returns Fibonacci numbers.
    """
    sigma = _parse_alphabet(alphabet)
    forb = _parse_forbidden(forbidden)
    p = complexity.sft_factor_complexity(sigma, forb, n_max)
    return json.dumps({"n_max": n_max, "p_X": p})


@mcp.tool()
def symdyn_complexity_1d_word(word: str, n_max: int) -> str:
    """Compute the factor complexity `p_w(1), ..., p_w(n_max)` of a word.

    `p_w(n)` is the number of distinct length-`n` factors of `w`.
    """
    p = complexity.word_factor_complexity(word, n_max)
    return json.dumps({"n_max": n_max, "p_w": p})


@mcp.tool()
def symdyn_complexity_1d_periodic(period: str, n_max: int) -> str:
    """Factor complexity of the bi-infinite word `(period)^∞`.

    Plateaus at `len(period)` for `n ≥ len(period)`.
    """
    p = complexity.periodic_word_factor_complexity(period, n_max)
    return json.dumps({"n_max": n_max, "p_x": p, "period_length": len(period)})


@mcp.tool()
def symdyn_morse_hedlund_check(complexity_values: str) -> str:
    """Morse–Hedlund test: does some `p(n) ≤ n` certify eventual periodicity?

    `complexity_values`: JSON list `[p(1), p(2), ...]`.

    Returns `{eventually_periodic, witness_n, checked_up_to}`.

    By Morse–Hedlund (1938): a bi-infinite word is eventually periodic
    iff such an `n` exists; aperiodic words satisfy `p(n) ≥ n + 1` for
    all `n ≥ 1`. (Sturmian words attain equality `p(n) = n + 1`.)
    """
    values = json.loads(complexity_values)
    return json.dumps(complexity.morse_hedlund_eventually_periodic(values))


def main() -> None:
    mcp.run()


if __name__ == "__main__":
    main()
