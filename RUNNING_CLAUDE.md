# Running Claude Code on this project

Quick reference. Detailed policy lives in [`CLAUDE.md`](CLAUDE.md) and
[`.claude/settings.json`](.claude/settings.json).

## Default invocation

```bash
cd /Users/silveregangloff/Desktop/formalized-symbolic-dynamics
claude
```

Picks up `.claude/settings.json` and `.claude/hooks/` automatically.
Default mode is **`acceptEdits`** — writes inside the repo auto-approve;
arbitrary Bash still prompts unless it matches the `allow` list.

## For long unattended sessions

```bash
claude --permission-mode dontAsk
```

Auto-denies anything not pre-approved. Use this for `/loop` runs or any
session you start and walk away from. Stricter than `acceptEdits` —
combine with a well-maintained allow list.

## Never use

```bash
claude --dangerously-skip-permissions   # ← do not use; bypasses everything
```

## Pushing

`git push` is in the `deny` list — Claude cannot push. Push from your
shell:

```bash
git push origin main
```

## Notifications

macOS notifications fire on:
- `Stop` — Claude finished its turn and has findings to report.
- `Notification` — Claude needs attention.

If they stop appearing, check System Settings → Notifications →
Script Editor / `osascript` is allowed to send notifications.

## Adjusting policy

- [`.claude/settings.json`](.claude/settings.json) — `allow` / `ask` /
  `deny` rules and `defaultMode`.
- [`.claude/hooks/*.sh`](.claude/hooks/) — programmatic guards
  (token-aware bash guard, edit guard, post-edit policy check,
  stop verification, notification).
- [`CLAUDE.md`](CLAUDE.md) — auto-loaded project context.

All three are git-tracked; changes go through normal review.

## First-run trust prompt

The very first `claude` invocation in this folder asks "trust this
folder" — answer yes once; it remembers.
