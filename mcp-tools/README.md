# mcp-tools

MCP servers specialized for symbolic dynamics, paired with the Lean 4 formalization in
`../SymbolicDynamics`.

Layout follows [Sfgangloff/math-reasoning-tools](https://github.com/Sfgangloff/math-reasoning-tools):
each server is an independent Python package under `servers/`, with FastMCP as the framework
and `uv` as the workspace manager.

## Servers

| Server | Status | Scope |
|---|---|---|
| `symdyn-shifts` | skeleton | 1D / Zᵈ SFT and sofic primitives — language enumeration, transition-matrix entropy, Fischer/Krieger covers, DFA-based sofic tests |
| `symdyn-tilings` | skeleton | Wang tilesets and 2D SFT specifics — SAT-based tileability, transfer-matrix entropy bounds, named-tileset catalog (Berger, Robinson, Kari, Culik, Kari–Culik, Jeandel–Rao) |
| `symdyn-complexity` | skeleton | Pattern-complexity tooling — `p_X(n)`, `p_x(m,n)`, period search, Nivat-condition tests, Morse–Hedlund |
| `symdyn-viz` | skeleton | Rendering for 2D patterns, Wang tilings, Fischer covers, complexity curves |

All four servers are currently in **Phase A**: they boot, register, and expose a single
`*_info` tool that describes the planned tool surface. Real tool implementations land
in Phase B.

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
