#!/usr/bin/env python3
"""Health-check the MCP servers from this repo against ~/.claude.json.

For each server discovered under servers/, performs the MCP initialize handshake
and tools/list to confirm it boots and responds. Reports pass/fail and the list
of exposed tools.
"""

import json
import os
import subprocess
import sys
import threading
import tomllib
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SERVERS_DIR = REPO_ROOT / "servers"
CLAUDE_JSON = Path.home() / ".claude.json"
TIMEOUT = 15  # seconds per server


def _send(proc, msg: dict) -> None:
    proc.stdin.write((json.dumps(msg) + "\n").encode())
    proc.stdin.flush()


def _recv(proc) -> dict:
    return json.loads(proc.stdout.readline())


def discover_servers() -> dict[str, list[str]]:
    servers: dict[str, list[str]] = {}
    if not SERVERS_DIR.exists():
        return servers
    for child in sorted(SERVERS_DIR.iterdir()):
        pyproject = child / "pyproject.toml"
        if not pyproject.exists():
            continue
        with open(pyproject, "rb") as f:
            data = tomllib.load(f)
        scripts = data.get("project", {}).get("scripts", {})
        if not scripts:
            continue
        script_name = next(iter(scripts))
        servers[child.name] = [
            "uv", "run", "--directory", str(child.resolve()), script_name,
        ]
    return servers


def check_server(name: str, command: list[str]) -> tuple[bool, str, list[str]]:
    result = {"ok": False, "info": "no response", "tools": []}

    def run():
        proc = subprocess.Popen(
            command,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=os.environ.copy(),
        )
        try:
            _send(proc, {
                "jsonrpc": "2.0", "id": 1, "method": "initialize",
                "params": {
                    "protocolVersion": "2024-11-05",
                    "capabilities": {},
                    "clientInfo": {"name": "check-mcp", "version": "1.0"},
                },
            })
            resp = _recv(proc)
            if "error" in resp:
                result["info"] = str(resp["error"])
                return
            _send(proc, {"jsonrpc": "2.0", "method": "notifications/initialized", "params": {}})
            _send(proc, {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
            tools_resp = _recv(proc)
            result["ok"] = True
            result["info"] = "ok"
            result["tools"] = [t["name"] for t in tools_resp.get("result", {}).get("tools", [])]
        except Exception as e:
            result["info"] = f"{type(e).__name__}: {e}"
        finally:
            proc.kill()
            proc.wait()

    t = threading.Thread(target=run, daemon=True)
    t.start()
    t.join(TIMEOUT)

    if t.is_alive():
        return False, "timeout", []
    return result["ok"], result["info"], result["tools"]


def main():
    servers = discover_servers()
    if not servers:
        print(f"No servers found under {SERVERS_DIR}.", file=sys.stderr)
        sys.exit(1)

    print(f"Checking {len(servers)} MCP servers...\n")
    all_ok = True

    for name, command in servers.items():
        sys.stdout.write(f"  {name:<32}")
        sys.stdout.flush()
        ok, info, tools = check_server(name, command)
        if ok:
            tool_list = ", ".join(tools) if tools else "(none)"
            print(f"OK   {len(tools)} tools: {tool_list}")
        else:
            print(f"FAIL  {info}")
            all_ok = False

    print()
    if all_ok:
        print("All servers OK.")
    else:
        print("Some servers failed — check the entries above.")
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
