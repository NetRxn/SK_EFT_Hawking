#!/usr/bin/env bash
# Create/refresh the persistent lean-worker slots wt1..wtN for parallel Lean development.
#
# WHY persistent: each slot has its OWN fast lean-lsp MCP server (lean-lsp-wt1/2/3 in the
# workspace .mcp.json), which Claude Code attaches at SESSION START — so the slot worktrees
# must already exist when you launch. Inline per-subagent MCP servers do NOT surface via the
# Agent tool in this environment (verified), so static per-slot servers + persistent slots are
# the only way to give every parallel worker its own build-isolated LSP with no coordination.
#
# Run this ONCE (the slots persist, gitignored under .claude/worktrees/). The goal-mode lead
# resets a slot to main + re-clones its build per task; you don't re-run this each time.
#
# Disk: each slot is ~1 GB of source checkout; the .lake build is cloned with `cp -c` (APFS
# copy-on-write) so it costs ~MB of real disk, not GB. 3 slots ≈ ~3 GB total.
#
# Usage:  scripts/setup_lean_worktree_slots.sh [N]   (default N=3)
set -euo pipefail

REPO="$(git rev-parse --show-toplevel)"
cd "$REPO"
N="${1:-3}"

# Refuse to run if the main build isn't present (nothing to clone).
[ -d lean/.lake/build ] || { echo "ERROR: lean/.lake/build missing — run 'cd lean && lake build' first." >&2; exit 1; }

for i in $(seq 1 "$N"); do
  SLOT=".claude/worktrees/wt$i"; BR="worktree-wt$i"
  if git worktree list --porcelain | grep -qx "worktree $REPO/$SLOT"; then
    echo "wt$i: exists — refreshing its build clone only"
    # NOTE: we deliberately do NOT 'git reset --hard' / 'git clean' here (the dev-harness
    # guardrail blocks those, by design). Re-seeding the .lake build clone is what matters
    # for a stale slot; syncing a slot's SOURCE to main is the lead's per-task job
    # (e.g. `git -C <slot> merge --ff-only main`), done deliberately, not by this script.
  else
    echo "wt$i: creating worktree on branch $BR"
    git branch -D "$BR" >/dev/null 2>&1 || true
    git worktree add "$SLOT" -b "$BR" >/dev/null
  fi
  # COW-clone the build so the slot's LSP is instant + isolated (writes never touch main).
  # rm -rf of the gitignored .lake is allowed (not a git reset/clean).
  rm -rf "$SLOT/lean/.lake"
  cp -c -R lean/.lake "$SLOT/lean/.lake"
  echo "wt$i: ready -> $REPO/$SLOT/lean   (served by mcp__lean-lsp-wt${i}__*)"
done
echo "Done. Restart Claude Code so lean-lsp-wt1..wt${N} attach to these slots."
