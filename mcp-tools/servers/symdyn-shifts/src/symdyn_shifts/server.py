import json

from fastmcp import FastMCP

from . import lean_emit, sft1d

mcp = FastMCP("symdyn-shifts")


@mcp.tool()
def symdyn_shifts_info() -> str:
    """Describe this server and its tool surface (Phase B)."""
    return (
        "symdyn-shifts — primitives for 1D SFT and sofic shifts.\n\n"
        "Status: Phase B (1D SFT entropy + admissible counts + Lean stubs).\n\n"
        "Tools:\n"
        "  - symdyn_sft_admissible_count(alphabet, forbidden, length):\n"
        "      |L_n(X)| via enumeration (1D)\n"
        "  - symdyn_sft_entropy_1d(alphabet, forbidden):\n"
        "      exact entropy log ρ(M) via step-k transition matrix\n"
        "  - symdyn_lean_emit_subshift(alphabet, forbidden, name):\n"
        "      Lean 4 stub for the 1D SFT\n"
        "\nPlanned (not yet exposed):\n"
        "  - symdyn_sft_entropy_2d_bounds(forbidden, alphabet, n)\n"
        "  - symdyn_sofic_fischer_cover, symdyn_sofic_is_sofic_via_dfa\n"
        "  - symdyn_sft_cover_of_sofic\n"
    )


def _parse_alphabet(spec: str) -> list[str]:
    s = spec.strip()
    if s.startswith("["):
        return [str(x) for x in json.loads(s)]
    return [c for c in s if not c.isspace()]


def _parse_forbidden(spec: str) -> list[list[str]]:
    """Forbidden factors as a JSON array of arrays of single-char strings,
    or a comma-separated string like `'11,000'` with each word a
    sequence of single-char letters."""
    s = spec.strip()
    if s.startswith("["):
        return [[str(c) for c in w] for w in json.loads(s)]
    return [[c for c in w.strip()] for w in s.split(",") if w.strip()]


@mcp.tool()
def symdyn_sft_admissible_count(alphabet: str, forbidden: str, length: int) -> str:
    """Count length-`length` admissible words of a 1D SFT.

    `alphabet`: JSON array `'["0","1"]'` or compact string `'01'`.
    `forbidden`: JSON `'[["1","1"]]'` or compact `'11'` (a comma-list
    `'11,000'` for multiple factors).
    `length`: length of words to count (≥ 0).

    Returns JSON `{n: int, count: int}`.

    Example: golden-mean (no `11`) with `length=5`:
      `symdyn_sft_admissible_count('01', '11', 5)` → `{"n": 5, "count": 13}`
      (Fibonacci-like growth).
    """
    sigma = _parse_alphabet(alphabet)
    forb = _parse_forbidden(forbidden)
    count = sft1d.admissible_count(sigma, forb, length)
    return json.dumps({"n": length, "count": count})


@mcp.tool()
def symdyn_sft_entropy_1d(alphabet: str, forbidden: str, k: int = 0) -> str:
    """Exact 1D SFT entropy via spectral radius of the step-k transition matrix.

    `alphabet`, `forbidden`: same shapes as `symdyn_sft_admissible_count`.
    `k`: optional memory parameter (defaults to `max_forbidden_length - 1`).

    Returns JSON `{k, n_states, spectral_radius, entropy}`.

    Example: golden-mean shift (no `11`) returns `entropy ≈ log φ ≈ 0.481`.
    """
    sigma = _parse_alphabet(alphabet)
    forb = _parse_forbidden(forbidden)
    k_arg = None if k == 0 else k
    return json.dumps(sft1d.entropy_1d_step_k(sigma, forb, k_arg))


@mcp.tool()
def symdyn_lean_emit_subshift(alphabet: str, forbidden: str, name: str) -> str:
    """Emit a Lean 4 stub for a 1D SFT.

    Output is a Lean `def` referencing the project's `Subshift` type.
    The user adapts the stub to match their concrete alphabet encoding.
    """
    sigma = _parse_alphabet(alphabet)
    forb = _parse_forbidden(forbidden)
    return lean_emit.emit_subshift_stub(sigma, forb, name)


def main() -> None:
    mcp.run()


if __name__ == "__main__":
    main()
