#!/usr/bin/env bash
# Notification hook. Fires a macOS native notification whenever Claude
# reports findings (Stop event) or asks for attention (Notification event).
# Idempotent and best-effort — exits 0 even if `osascript` is unavailable.

set -uo pipefail

INPUT="$(cat 2>/dev/null || true)" python3 - <<'PY' || true
import json, os, sys, subprocess, shutil

if not shutil.which("osascript"):
    sys.exit(0)

try:
    data = json.loads(os.environ.get("INPUT", ""))
except Exception:
    data = {}

event = data.get("hook_event_name", "")
message = (
    data.get("message")
    or data.get("hookSpecificOutput", {}).get("message")
    or {"Stop": "Claude reported findings — ready for review",
        "Notification": "Claude needs attention"}.get(event, event or "Claude Code update")
)

project = os.path.basename(os.environ.get("CLAUDE_PROJECT_DIR", os.getcwd()))
title = f"Claude Code — {project}"

# Trim long messages so the notification renders cleanly.
message = (message or "").strip()
if len(message) > 240:
    message = message[:237] + "..."

# Build the AppleScript safely via json.dumps quoting.
script = (
    f"display notification {json.dumps(message)} "
    f"with title {json.dumps(title)} "
    f'sound name "Glass"'
)

try:
    subprocess.run(["osascript", "-e", script], check=False, timeout=5)
except Exception:
    pass
PY

exit 0
