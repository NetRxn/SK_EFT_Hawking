---
name: wave-close
description: Close a wave deterministically — run the gate prerequisites, dispatch the fresh-context adversarial review, and record the close. Use once per wave when the wave's bricks are shipped and validate is green.
argument-hint: <wave-or-bundle-id>
allowed-tools: Bash(git rev-parse *), Bash(uv run python *), Agent
---

<!-- INVOCABILITY (spec 11 — per-skill invocability fix): NO `disable-model-invocation`
     here → the DEFAULT state, so BOTH the user and the agent may invoke `/wave-close`.
     This skill MUST be agent-invocable: in autonomous goal mode the user is intentionally
     out of the loop, and `/wave-close` is the explicit GAP-B path the loop runs ITSELF —
     if an agent could not invoke it, the loop could never satisfy its own GAP-B acceptance
     criteria (the fresh-context review has to actually run and surface in the transcript).
     Self-invocation is safe: the close is idempotent / re-runnable. User-only
     (`disable-model-invocation: true`) is reserved for goal-prompt / goal-guard / debrief
     (other plans), where agent self-invocation would be self-defeating; it is deliberately
     NOT set here. (`disallowed-tools` is a separate axis — only the model-invocation gate
     changes.) -->

Close wave **$ARGUMENTS** in one deliberate pass. Do NOT do this per-task — once per wave.

0. **Resolve the repo root** (NOT `${CLAUDE_PROJECT_DIR}` — not a skill substitution; `git rev-parse` here
   resolves the *user's cwd* repo, distinct from the Plan-1 harness-*state* resolver):
   `` !`git rev-parse --show-toplevel 2>/dev/null || echo UNRESOLVED` ``. If `UNRESOLVED`, tell the user to
   `cd` into `SK_EFT_Hawking/` and re-run. Use `<repo-root>` for the absolute script paths below.

1. **Full sync + gate prereqs (deterministic).** Run via Bash (the scripts self-locate their own ROOT;
   `sync.py`'s shared-artifact regen is serialized by the Task-7 regen concurrency lock, so a concurrent
   worktree/worker can't race the same regen — spec 12):
   - `uv run python <repo-root>/scripts/sync.py --full`
   - `uv run python <repo-root>/scripts/gate_precheck.py s13`
   If `gate_precheck s13` is FAIL, STOP — fix the red checks first; do not spend an
   Opus review on a failing tree.

2. **Dispatch the fresh-context review** (a real model call, the GAP-B safeguard the
   self-audit blind spot requires): invoke the `skeft-qa:adversarial-reviewer`
   (and `skeft-qa:claims-reviewer` for paper-shaped output) on $ARGUMENTS in a
   fresh context. It must run with **zero BLOCKER findings surfaced in the
   transcript** before the wave can be called closed.

3. **Record the close.** Write `docs/dev-loops/<roadmap>/<wave>_close.md` with: the
   validate result, the reviewer report path, the BLOCKER count (must be 0), and the
   commit range. Never edit CLAUDE.md / hooks / roadmaps here.

State plainly whether the wave is closeable (zero BLOCKERs, green tree) or what
remains. This is the explicit complement to the `/goal` acceptance-criteria path
(the `goal-prompt` skill bakes the same zero-BLOCKER requirement into the loop).
