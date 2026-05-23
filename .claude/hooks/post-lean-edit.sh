#!/usr/bin/env bash
# PostToolUse hook for Write/Edit. If the touched file is a `.lean` source
# under SymbolicDynamics/, run scripts/check_symbolic_dynamics_policy.sh
# and surface any failure to Claude (exit 2 + stderr) so the next turn can
# fix the violation.

set -uo pipefail

FILE="$(python3 -c '
import json, sys
try:
    print(json.loads(sys.stdin.read()).get("tool_input", {}).get("file_path", ""))
except Exception:
    print("")
')"

[ -z "$FILE" ] && exit 0

case "$FILE" in
  *SymbolicDynamics/*.lean) : ;;
  *) exit 0 ;;
esac

ROOT="${CLAUDE_PROJECT_DIR:-$PWD}"

if ! OUT=$(bash "$ROOT/scripts/check_symbolic_dynamics_policy.sh" 2>&1); then
  {
    echo "post-lean-edit hook: policy check failed after editing $FILE"
    echo "----"
    echo "$OUT"
  } >&2
  exit 2
fi

exit 0
