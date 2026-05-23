#!/usr/bin/env bash
# PreToolUse hook for Write/Edit. Reads tool-input JSON on stdin; exits 2 to
# block the call. Refuses writes outside the project root and writes to
# auto-generated files (lake-manifest.json, uv.lock), .git/, and derived
# directories (ontology/build/, ontology/corpus/, caches).

set -uo pipefail

INPUT="$(cat)" python3 - <<'PY'
import json, os, sys

def block(msg: str) -> None:
    print(msg, file=sys.stderr)
    sys.exit(2)

raw = os.environ.get("INPUT", "")
try:
    data = json.loads(raw)
except Exception:
    sys.exit(0)

file_path = data.get("tool_input", {}).get("file_path", "")
if not file_path:
    sys.exit(0)

root = os.path.realpath(os.environ.get("CLAUDE_PROJECT_DIR") or os.getcwd())
abs_path = file_path if os.path.isabs(file_path) else os.path.join(root, file_path)
abs_path = os.path.realpath(abs_path)

# Block writes outside the project root.
if abs_path != root and not abs_path.startswith(root + os.sep):
    block(f"Refusing: write to {abs_path} is outside the project root ({root}).")

rel = os.path.relpath(abs_path, root)
parts = rel.split(os.sep)

# Block writes into .git/ anywhere in the tree.
if ".git" in parts:
    block("Refusing: never write directly into .git/.")

# Block derived ontology dirs.
if rel.startswith("ontology/build/") or rel.startswith("ontology/build" + os.sep):
    block("Refusing: ontology/build/ is a derived artifact (run `uv run onto build`).")
if rel.startswith("ontology/corpus/") or rel.startswith("ontology/corpus" + os.sep):
    block("Refusing: ontology/corpus/ holds harvested raw input (rebuilt by `uv run onto acquire`).")

# Block writes into common cache/venv dirs.
for forbidden in ("__pycache__", ".venv", ".ruff_cache", ".pytest_cache"):
    if forbidden in parts:
        block(f"Refusing: write to a {forbidden} directory (generated cache).")

# Block hand-edits of auto-generated lock/manifest files.
basename = os.path.basename(abs_path)
if basename == "lake-manifest.json":
    block("Refusing: lake-manifest.json is auto-generated; run `lake update` instead.")
if basename == "uv.lock":
    block("Refusing: uv.lock is auto-generated; run `uv lock` / `uv sync` instead.")

sys.exit(0)
PY
