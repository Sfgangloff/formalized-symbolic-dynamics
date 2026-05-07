# Claude Code instructions for mcp-tools

This subdirectory develops MCP servers specialized for symbolic dynamics, paired with the
Lean 4 formalization in `../SymbolicDynamics`. Follow these conventions when working here.

## Working in this repo

- Servers live in `servers/<name>/`. Each is an independent Python package using FastMCP.
- `scripts/` contains setup/check/reload automation — keep aligned with the server discovery
  convention (each server is a directory under `servers/` with a `pyproject.toml` exporting
  `[project.scripts]`).
- All servers use [FastMCP](https://github.com/jlowin/fastmcp): `from fastmcp import FastMCP`.

## Code conventions

- Tools return either a plain string (text / LaTeX / Lean source) or a dict
  `{"image": "<base64-png>", "description": "..."}` for visual output.
- No tool writes to disk or makes mutating network calls.
- Tool names use `snake_case` and the `symdyn_` prefix to namespace cleanly against
  math-reasoning-tools (which may run alongside).
- Domain sub-prefixes within `symdyn_`:
  - `symdyn_sft_*`, `symdyn_sofic_*`           (in `symdyn-shifts`)
  - `symdyn_wang_*`, `symdyn_tileset_*`        (in `symdyn-tilings`)
  - `symdyn_complexity_*`, `symdyn_periods_*`,
    `symdyn_nivat_*`, `symdyn_morse_hedlund_*` (in `symdyn-complexity`)
  - `symdyn_draw_*`, `symdyn_plot_*`           (in `symdyn-viz`)
  - `symdyn_lean_emit_*`                       (any server, when emitting Lean stubs)
- Tool docstrings are what the model sees — make them precise and include example inputs.

## Dimension API

The core types accept a generic `d: int`. Internally:

- `d == 1`: spectral / matrix algorithms (NumPy / SciPy).
- `d == 2`: transfer-matrix and SAT (Z3) fast paths.
- `d >= 3`: generic enumeration only — flag with a `# slow for d>=3` comment in tool
  docstrings so the model knows.

## When to use which tool

| Task | Preferred tool |
|------|----------------|
| Count globally admissible patterns of a 1D/2D SFT | `symdyn_sft_admissible_count` |
| Compute exact 1D SFT entropy | `symdyn_sft_entropy_1d` |
| Bound Zᵈ SFT entropy via transfer matrix | `symdyn_sft_entropy_2d_bounds` |
| Construct a Fischer cover from forbidden words | `symdyn_sofic_fischer_cover` |
| Test whether a 1D shift is sofic | `symdyn_sofic_is_sofic_via_dfa` |
| Build the SFT cover of a sofic shift | `symdyn_sft_cover_of_sofic` |
| SAT-check Wang m×n tileability | `symdyn_wang_finite_tileability` |
| Search for a periodic Wang tiling | `symdyn_wang_periodic_search` |
| Compute Wang transfer-matrix entropy bound | `symdyn_wang_entropy_bounds` |
| Look up a named Wang tileset | `symdyn_tileset_catalog_get` |
| Compute pattern complexity `p_X(n)` | `symdyn_complexity_1d` |
| Compute 2D complexity `p_x(m,n)` | `symdyn_complexity_2d` |
| Find the period lattice of a 2D pattern | `symdyn_periods_2d` |
| Test whether `p(m,n) <= mn` forces a period | `symdyn_nivat_check_finite` |
| Render a 2D pattern as PNG | `symdyn_draw_pattern_2d` |
| Render a Wang tileset / tiling | `symdyn_draw_wang_tileset`, `symdyn_draw_wang_tiling` |
| Plot a complexity curve | `symdyn_plot_complexity_curve` |
| Emit a Lean stub for a subshift / tileset | `symdyn_lean_emit_subshift`, `symdyn_lean_emit_tileset` |

## Lean workflow

1. Compute objects in Python via the symdyn tools (admissible counts, entropy estimates,
   covers).
2. Use `symdyn_lean_emit_*` to get a Lean 4 stub.
3. Paste into `../SymbolicDynamics/SymbolicDynamics/<topic>.lean` and adapt to the canonical
   types in `HochmanMeyerovitch.lean`.
4. Use the `lean-lsp-mcp` server (separately registered) for proof state and Mathlib search.

## Development

```bash
# from this directory
uv sync                                              # install workspace
python3 scripts/setup-mcp.py                         # register in ~/.claude.json
python3 scripts/check-mcp.py                         # boot each + tools/list
python3 scripts/reload-mcp.py                        # after editing a server

cd servers/<name> && uv run fastmcp dev src/<pkg>/server.py    # dev inspector
cd servers/<name> && uv run pytest                              # tests
```
