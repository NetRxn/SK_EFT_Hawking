---
description: Re-orient on the current managed dev loop — a ≤200-word compass from the goal marker + source-of-truth docs (where am I, what's the next brick).
---

Produce a tight **≤200-word** compass for the current dev loop. No preamble.

1. Read the marker for this session (project-scoped under the repo, not `~/.claude`):
   ```bash
   SID="${CLAUDE_SESSION_ID}"
   # cwd-robust repo resolve (works from the workspace root too); falls back to git rev-parse.
   REPO="$(uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" repo-root 2>/dev/null)"
   test -n "$REPO" || REPO="$(git rev-parse --show-toplevel 2>/dev/null || echo UNRESOLVED)"
   cat "$REPO/.claude/dev-harness/managed/$SID.json" 2>/dev/null || echo "NO MARKER (not a managed loop)"
   ```
   If there is no marker, say so and stop — there is nothing to orient against.

2. Read the **tail** of the marker's `notebook_path` (recent bricks/lessons) and the
   relevant section of `roadmap_path` (the settled scope + next planned brick).

3. Output exactly these four lines, each ≤ 1 sentence:
   - **Goal:** the marker's goal (the settled acceptance criteria).
   - **Done:** the last shipped brick (from the notebook tail).
   - **Next:** the single next brick to build now.
   - **Guardrails:** kernel-pure / invariants respected / scope is settled (no re-litigating).

Keep it to a glance. This is a re-orientation aid, not a status report — do not
re-plan, re-scope, or propose alternatives; name the next brick and stop.
