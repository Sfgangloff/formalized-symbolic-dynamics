# mcp-tools

MCP servers specialized for symbolic dynamics, paired with the Lean 4 formalization in
`../SymbolicDynamics`.

Layout follows [Sfgangloff/math-reasoning-tools](https://github.com/Sfgangloff/math-reasoning-tools):
each server is an independent Python package under `servers/`, with FastMCP as the framework
and `uv` as the workspace manager.

## Servers

| Server | Status | Tools | Scope |
|---|---|---|---|
| `symdyn-shifts` | Phase B | 4 | 1D SFT admissible counts, exact entropy via spectral radius, Lean stub emit. Planned: sofic / Fischer / 2D bounds. |
| `symdyn-tilings` | Phase B | 8 | Named Wang-tileset catalog (`kari_culik_14_dgg`, `dgg_14_first_13`, `two_color_full_2d`); transfer-matrix entropy upper bound `log ρ(M_n)/n`; DFS-based finite tileability and periodic search; Lean stub emit. The original Culik 1996 13-tile set is not in the catalog; `dgg_14_first_13` is a DGG-truncation and has zero entropy. |
| `symdyn-complexity` | Phase B | 5 | 1D factor complexity (`p_X(n)` for SFTs, words, periodic words); Morse–Hedlund eventual-periodicity test. Planned: 2D / Nivat. |
| `symdyn-viz` | Phase B | 4 | PNG rendering of Wang tilesets and tilings (hash-colored N/E/S/W triangles); log-y complexity-curve plot with M–H and Sturmian reference lines. |

Each server boots stand-alone and exposes `<name>_info` describing its surface.

## Targeted research problems

The tool surface is shaped around concrete targets:

- **Nivat conjecture** — `symdyn-complexity`
- **x2×3 conjecture** — multidimensional ergodic tools (shared infra)
- **Kari–Culik subshift entropy** — `symdyn-tilings` (transfer matrix)
- **Weiss conjecture on covers of subshifts** — `symdyn-shifts` (sofic / SFT cover)
- **Odd shift sofic** — `symdyn-shifts` (DFA minimization)

## Quick start

```bash
# from this directory
uv sync
python3 scripts/setup-mcp.py    # register all servers in ~/.claude.json
python3 scripts/check-mcp.py    # boot each, list tools
```

After editing a server, reload it without restarting Claude Code:

```bash
python3 scripts/reload-mcp.py
```

## Lean integration

Tools that produce mathematical objects (subshifts, tilesets, complexity functions)
optionally emit a Lean 4 stub that can be pasted into `../SymbolicDynamics/`. The
`*_lean_emit_*` tools own this surface — see each server's `lean_emit.py`.

## Development

Each server has a FastMCP dev inspector:

```bash
cd servers/<name>
uv run fastmcp dev src/<package>/server.py
```

Run tests:

```bash
uv run pytest servers/<name>/tests/ -v
```
