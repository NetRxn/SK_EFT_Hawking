---
name: sync
description: Run the full mechanical Stage-12 sync (counts, tables, deps, citation cache) in one command. Use before a wave gate, or whenever counts/tables/figures may have drifted from the Lean/Python sources.
allowed-tools: Bash(git rev-parse *), Bash(uv run python *), Bash(grep *)
---

<!-- INVOCABILITY (spec 11 — per-skill invocability fix): NO `disable-model-invocation`
     here → the DEFAULT state, so BOTH the user and the agent may invoke `/sync`. In
     autonomous goal mode the user is intentionally out of the loop, so the loop must
     self-serve mechanical sync on demand. Self-invocation is safe: `/sync` is idempotent
     / re-runnable, and every shared-artifact regen is serialized by the Task-7 regen
     concurrency lock, so a concurrent agent's loop can't race the same regen. User-only
     (`disable-model-invocation: true`) is reserved for the skills where agent
     self-invocation is self-defeating/unsafe — goal-prompt / goal-guard / debrief (other
     plans); it is deliberately NOT set here. -->

Run the one foolproof mechanical-sync command and report the result.

1. **Resolve the repo root** (do NOT use `${CLAUDE_PROJECT_DIR}` — it is NOT a skill substitution, only a
   hooks/MCP/LSP var): `` !`git rev-parse --show-toplevel 2>/dev/null || echo UNRESOLVED` ``. If that is
   `UNRESOLVED` (launched from the non-git workspace root), tell the user to `cd` into `SK_EFT_Hawking/` and
   re-run. (NB: `git rev-parse` here correctly resolves the *user's cwd* repo — distinct from, not contradicting,
   the Plan-1 harness-*state* resolver, which avoids a git-root walk because ITS cwd may be the `~/.claude` plugin
   cache.)
2. **Verify the L2 pre-commit gate is installed for THIS checkout, and warn loudly if not (review A4 / spec
   12 L2 "Coverage residual").** The L2 commit gate is a *local* git hook (`<repo-root>/.git/hooks/pre-commit`),
   not a plugin mechanism — a **fresh clone / new worktree where the installer never ran** has NO mechanical gate
   at all (the v3.0 CC `PostToolUse(git commit)` advisory backstop is dropped in v4.0). Run a cheap deterministic
   check via Bash and surface the result:
   ```bash
   H="<repo-root>/.git/hooks/pre-commit"
   if [ -x "$H" ] && grep -q 'pre-commit-sync.sh' "$H"; then
     echo "✅ pre-commit gate installed (leak-guard + sync gate present)"
   else
     echo "⚠️  WARNING: the local pre-commit gate is NOT installed for this checkout"
     echo "    ($H missing, not executable, or lacks the pre-commit-sync.sh chain)."
     echo "    Commits from here have NO mechanical sync/soundness gate AND NO leak-guard."
     echo "    Re-run the canonical pre-commit installer for this clone before committing."
   fi
   ```
   ⚠ **Public-safety (when authoring this committed public `skeft-qa` skill):** the installer that regenerates
   the hook is the private leak-guard installer, whose path contains the private directory name the public
   leak-guard greps for — so the skill's prose **must NOT name that path literally** (it would trip the leak-guard
   at commit time). Keep the install hint generic ("re-run the canonical pre-commit installer for this clone"), as
   above; the user knows where it lives.
   (`grep` for the `pre-commit-sync.sh` marker confirms it is the *current* hook — a stale pre-L2 hook with only
   the leak-guard fails the check and is flagged. This is a non-mutating, deterministic check; it never installs
   anything — installing is the user's deliberate one-time step. `goal-prompt` runs the identical check at
   arm-time — spec 12 L2.) If the warning fires, surface it prominently; do not bury it in the sync output.
3. From that repo root, run via Bash: `uv run python <repo-root>/scripts/sync.py --full` (the script
   self-locates its own `ROOT` from `__file__`, so an absolute path is safe from any cwd).

Then state which artifacts were regenerated and remind the user that Aristotle (S4) is excluded by design and
judgment docs (the prose Inventory, README) are flag-only — never silently regenerated. If any regen failed,
surface the failing command verbatim; do not paper over it. (Each shared-artifact regen is serialized by the
Task-7 regen concurrency lock inside `sync.py`, so running `/sync` concurrently with another agent's loop is
safe — a contended artifact is skipped, never raced; spec 12.)
