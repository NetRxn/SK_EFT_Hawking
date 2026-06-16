---
description: Arm a managed autonomous /goal dev loop — write the harness marker (so the goal + source-of-truth survive every compaction) and compose the self-describing goal prompt.
argument-hint: <goal description> [role=solo|lead] [roadmap=<path>] [notebook=<path>]
---

You are arming a **managed `/goal` dev loop** for the skeft-qa dev-harness. The
marker you write lets the `SessionStart` hook re-inject the goal + source-of-truth
after every compaction (the Phase-5q.F durability fix) and arms the de-pollution
guard on the roadmap/notebook. Do this now, concretely:

1. **Resolve the session id.** Run `echo "$CLAUDE_CODE_SESSION_ID"`. If empty,
   derive it from the most-recent transcript:
   `ls -t ~/.claude/projects/*/*.jsonl | head -1 | xargs -I{} basename {} .jsonl`.

2. **Resolve role + paths** from `$ARGUMENTS`:
   - `role`: `lead` when coordinating a team; otherwise `solo` (default;
     orchestrator-of-one). Anything other than `lead` gets the build directive.
   - `roadmap`: the **tracked** roadmap path (the settled scope's source of truth).
     If not given, locate the active one under `docs/dev-loops/` or `docs/roadmaps/`.
   - `notebook`: the **tracked** lab-notebook path. Default to the roadmap's
     sibling `LAB_NOTEBOOK.md` (ideally under `docs/dev-loops/<roadmap>/`).
   - Prefer tracked paths — a goal prompt's self-describing paths rot if the files
     they name are untracked and move.

3. **Write the marker** (the harness reads `~/.claude/skeft-harness/managed/<session_id>.json`):
   ```bash
   SID="<resolved session id>"
   mkdir -p ~/.claude/skeft-harness/managed
   cat > ~/.claude/skeft-harness/managed/"$SID".json <<'JSON'
   {"role": "<solo|lead>", "goal": "<one-line goal>", "roadmap_path": "<abs roadmap>", "notebook_path": "<abs notebook>"}
   JSON
   ```

4. **Compose the goal prompt** (≤ 4000 chars, self-describing): the concrete
   acceptance criteria, the roadmap + notebook paths, and the posture — *scope is
   settled; build the next brick; a stop-hook firing is a GO signal; legitimate
   stops = a kernel-checked no-go or a genuine user decision.* Make completion
   **demonstrable in surfaced output** (e.g. "validate.py prints N/N in the
   transcript"), since the native `/goal` evaluator sees only the transcript and
   cannot run tools.

5. **Hand off to native `/goal`.** Print the composed prompt and tell the user to
   run `/goal <prompt>` to arm the loop — the assistant cannot set `/goal` itself.
   The marker is already in place, so re-injection works the moment `/goal` is active.

End by confirming the marker path written, the role, and the roadmap/notebook paths.
