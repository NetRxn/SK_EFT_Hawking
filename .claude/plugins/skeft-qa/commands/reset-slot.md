---
description: Reset a parallel Lean worktree slot (wt1/wt2/wt3) to current main — the guardrail-safe way (checkout -B, refuses if the slot has commits not yet on main). Use before dispatching a lean-worker to a slot.
argument-hint: <N>
allowed-tools: Bash(uv run *)
---
<!-- A COMMAND (v4.1), MODEL-invocable (no disable-model-invocation) so the autonomous lead can call it from
     any context without loading the goal-dev skill. Atomic, globally-accessible, PD-immune action — the FM-1
     action-point fix: it puts the guardrail-safe `checkout -B` recipe where the work happens, so `git reset
     --hard` (denied by the auto-mode classifier on a worktree the agent didn't create) is never reached for. -->

Reset worktree slot `wt$ARGUMENTS` to current `main`:

Run: `` !`uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/reset_slot.py" $ARGUMENTS 2>&1` ``

Report the result. The script does `git -C .claude/worktrees/wtN checkout -B worktree-wtN main` (guardrail-safe;
**never** `git reset --hard`/`git clean`, which the auto-mode permission classifier denies on a slot) and
**refuses if the slot holds commits not on `main`** (merge/cherry-pick them first, then re-run). If it asks you
to re-clone the slot's `.lake` (because `main`'s build advanced), run the printed `cp -c` line. Full fan-out
flow: the `goal-dev` skill's `references/parallel-worktrees.md`.
