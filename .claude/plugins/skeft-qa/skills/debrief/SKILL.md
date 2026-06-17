---
name: debrief
description: Interactively review the System-2 dev-process harvest — promote agent-reviewed findings to human-reviewed (or close them), and triage GAP-A gate proposals. Use when you want to sign off on what the autonomous loop learned about HOW it ran.
disable-model-invocation: true
allowed-tools: Bash(uv run python *), Read
---

<!-- INVOCABILITY (spec 11): `disable-model-invocation: true` is the deliberate USER-ONLY
     posture for /debrief, because the promotion it performs (agent-reviewed -> human-reviewed)
     is BY DEFINITION a human judgment — an agent must not self-promote its own harvest
     findings to the human-verified tier. (Contrast: /wave-close and /sync are agent-invocable
     by default — those are Plan 2's skills; only /debrief lives here.) -->

Interactively promote System-2 findings to `human-reviewed` and triage GAP-A proposals. This
is the **periodic human governor** step — never auto-run; never auto-edit CLAUDE.md / hooks /
roadmaps (those need their own explicit sign-off — spec 1 principle 6, "self-improving, never
self-mutating").

1. **Resolve the repo root:** `` !`git rev-parse --show-toplevel 2>/dev/null || echo UNRESOLVED` ``.
   If `UNRESOLVED`, ask the user to `cd` into `SK_EFT_Hawking/` and re-run.

2. **Read the register + proposals.** Read `<repo>/docs/dev-loops/SYSTEM2_REGISTER.md` (the
   `## Open` section) and any drafts under `<repo>/docs/dev-loops/proposals/`. Cluster the
   `agent-reviewed` findings (use the per-occurrence `goal_id` goal-pointer to group by origin —
   goal-authoring vs other-harness-component vs tactical friction).

3. **Present one cluster at a time** to the user with: the title, why, how-to-apply, tally
   (distinct compact-events), and goal-origin. For each, ask the user to choose:
   - **promote** → `human-reviewed` (the lesson is confirmed),
   - **close** → resolved (`status: closed`, with a one-line `evidence` of why it's resolved —
     fixed, superseded, or promoted to a System-1 gate),
   - **leave** → keep `agent-reviewed` (not yet confirmed).

4. **Apply the user's choice via the register CLI** (NOT by hand-editing the markdown — let the
   register own dedup / tier-monotonicity / round-trip). For a finding `F` (its full JSON record
   from the register) with the user's decision applied (`"tier": "human-reviewed"` to promote, or
   `"status": "closed"` + `"evidence": "..."` to close):
   `echo '<F-json>' | uv run python <repo>/scripts/system2_register.py --upsert`
   (upsert raises tier monotonically — agent-reviewed → human-reviewed is allowed; it never
   downgrades.) A **closed** finding drops out of the register-wide active-issues view on the
   next harvest refresh.

5. **GAP-A proposals.** For each `proposals/<id>.md`, present the proposed structural prevention.
   On the user's sign-off it becomes a **tracked build task** (a new `validate.py` check /
   `goal-prompt` reference tweak / automation) — **never auto-applied here**. Note the disposition;
   do not implement the gate in this skill.

6. After the pass, refresh the active-issues view so closures take effect immediately:
   `uv run python <repo>/scripts/system2_register.py --write-active-issues`. Summarize what was
   promoted / closed / left and which proposals were signed off.
