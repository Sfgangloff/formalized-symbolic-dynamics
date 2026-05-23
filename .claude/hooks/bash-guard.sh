#!/usr/bin/env bash
# PreToolUse hook for Bash. Reads tool-input JSON on stdin; exits 2 with a
# reason on stderr to block the call. Uses `shlex` to tokenize the command
# so banned flags / subcommands are only matched as actual CLI tokens, not
# as substrings of quoted arguments (e.g. a heredoc commit message that
# happens to mention `--no-verify` does not trigger the block).

set -uo pipefail

INPUT="$(cat)" python3 - <<'PY'
import json, os, shlex, sys

def block(msg: str) -> None:
    print(msg, file=sys.stderr)
    sys.exit(2)

raw = os.environ.get("INPUT", "")
try:
    data = json.loads(raw)
except Exception:
    sys.exit(0)

cmd = data.get("tool_input", {}).get("command", "")
if not cmd:
    sys.exit(0)

# Tokenize. If the command has unbalanced quotes (e.g. unusual heredoc
# patterns shlex doesn't model), fall back to whitespace splitting.
try:
    tokens = shlex.split(cmd, comments=False, posix=True)
except ValueError:
    tokens = cmd.split()

# 1. Banned bare flags (must appear as standalone tokens).
BANNED_FLAGS = {"--no-verify", "--no-gpg-sign"}
for t in tokens:
    if t in BANNED_FLAGS:
        block(f"Refusing: {t} bypasses hooks/signing.")

# 2. `sudo` as the leading command.
if tokens and tokens[0] == "sudo":
    block("Refusing: sudo escalation is out of scope.")

# 3. Git-subcommand-specific guards.
if len(tokens) >= 2 and tokens[0] == "git":
    sub = tokens[1]
    rest = tokens[2:]
    if sub == "push":
        if any(t in ("--force", "-f", "--force-with-lease") for t in rest):
            block("Refusing: force-push loses upstream work.")
        block("Refusing: git push is reserved for manual operation by the user.")
    if sub == "commit" and "--amend" in rest:
        block("Refusing: --amend rewrites a published commit; create a new commit instead.")
    if sub == "reset" and "--hard" in rest:
        block("Refusing: git reset --hard discards uncommitted work.")
    if sub == "restore" and "." in rest:
        block("Refusing: git restore . discards working-tree changes.")
    if sub == "checkout" and ("." in rest or "--orphan" in rest):
        block("Refusing: git checkout . / --orphan loses work.")
    if sub == "branch" and any(t == "-D" for t in rest):
        block("Refusing: git branch -D force-deletes a branch.")
    if sub == "clean" and any(t.startswith("-") and ("f" in t or "F" in t) for t in rest):
        block("Refusing: git clean -f deletes untracked files.")
    if sub == "tag" and any(t in ("-d", "--delete") for t in rest):
        block("Refusing: git tag -d / --delete removes a tag.")
    if sub == "config":
        if "--global" in rest:
            block("Refusing: modifying global git config is out of scope.")
        for t in rest:
            if t.startswith("user.") or t in ("user", "user.name", "user.email"):
                block("Refusing: modifying git user config is out of scope.")

# 4. Pipe-to-shell detection — `curl|wget` ... `|` ... `sh|bash|zsh|fish`,
# all as standalone tokens (so a quoted commit message containing `curl|sh`
# does not trip the check).
SHELLS = {"sh", "bash", "zsh", "fish"}
DOWNLOADERS = {"curl", "wget"}
for i, t in enumerate(tokens):
    if t == "|" and i + 1 < len(tokens) and tokens[i + 1] in SHELLS:
        if any(prev in DOWNLOADERS for prev in tokens[:i]):
            block("Refusing: piping a download into a shell is unsafe.")

# 5. `rm -rf` whose target escapes the project root or is `.`/`..`.
for i, t in enumerate(tokens):
    if t != "rm":
        continue
    flags, targets = [], []
    saw_double_dash = False
    for u in tokens[i + 1:]:
        if u == "--":
            saw_double_dash = True
        elif not saw_double_dash and u.startswith("-") and len(u) > 1:
            flags.append(u)
        else:
            targets.append(u)
    recursive = any(("r" in f or "R" in f) for f in flags)
    forced = any("f" in f or "F" in f for f in flags)
    if not (recursive and forced):
        continue
    for tgt in targets:
        if (tgt.startswith("/")
            or tgt.startswith("~")
            or tgt.startswith("$HOME")
            or tgt.startswith("${HOME}")
            or tgt.startswith("..")
            or tgt in (".", "./", "./*", "*")):
            block(f"Refusing: rm -rf {tgt} targets a path outside the project root.")
    break

sys.exit(0)
PY
