#!/usr/bin/env bash
# Stop hook. Runs final-state checks before Claude yields back to the user.
# Blocks the stop (exit 2) on a Lean-policy failure — that violates the
# project's HARD invariant and must be addressed in the same turn. Treats
# the ontology lint and bookkeeping drift as warnings (exit 0 with stderr).

set -uo pipefail

ROOT="${CLAUDE_PROJECT_DIR:-$PWD}"
FAIL=0

# 1. Lean module-partition policy (hard).
if ! POLICY_OUT=$(bash "$ROOT/scripts/check_symbolic_dynamics_policy.sh" 2>&1); then
  {
    echo "stop-verify hook: scripts/check_symbolic_dynamics_policy.sh FAILED"
    echo "----"
    echo "$POLICY_OUT"
  } >&2
  FAIL=1
fi

# 2. Ontology snapshot lint (warn only).
if [ -d "$ROOT/ontology" ]; then
  if ! LINT_OUT=$(cd "$ROOT/ontology" && uv run onto lint 2>&1); then
    {
      echo "stop-verify hook: \`onto lint\` reported issues (warning)"
      echo "----"
      echo "$LINT_OUT"
    } >&2
  fi
fi

# 3. Bookkeeping drift (warn only): auto-generated or canonical files
#    modified outside of their generating commands.
if command -v git >/dev/null 2>&1; then
  DIRTY="$(cd "$ROOT" && git status --porcelain -- \
    ontology/snapshots \
    SymbolicDynamics/lake-manifest.json \
    ontology/uv.lock 2>/dev/null || true)"
  if [ -n "$DIRTY" ]; then
    {
      echo "stop-verify hook: bookkeeping files modified — review before committing"
      echo "$DIRTY"
    } >&2
  fi
fi

exit "$FAIL"
