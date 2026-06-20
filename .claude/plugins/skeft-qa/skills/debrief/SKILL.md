---
name: debrief
description: Interactively review the System-2 dev-process harvest — promote agent-reviewed findings to human-reviewed (or close them), and triage GAP-A gate proposals. Runs over the register-aware harvest's already-synthesized register (it files/combines/re-opens continuously); debrief is the human governor — only it promotes to human-reviewed. Use when you want to sign off on what the autonomous loop learned about HOW it ran.
disable-model-invocation: true
allowed-tools: Bash(cd *), Bash(uv run python *), Read
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

1. **Resolve the repo root (cwd-robust — works from the workspace root OR inside the repo):**
   `` !`R=$(uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" repo-root 2>/dev/null); test -n "$R" || R=$(git rev-parse --show-toplevel 2>/dev/null); echo "${R:-UNRESOLVED}"` `` (harness `repo_root()`, the
   same resolver the hooks use, with a `git rev-parse` fallback). `UNRESOLVED` only if launched entirely outside
   the workspace — then ask the user to `cd` into `SK_EFT_Hawking/` and re-run. Use `<repo>` below.

2. **Read the register + proposals.** Read `<repo>/docs/dev-loops/SYSTEM2_REGISTER.md` (the
   `## Open` section) and any drafts under `<repo>/docs/dev-loops/proposals/`. Cluster the
   `agent-reviewed` findings (use the per-occurrence `goal_id` goal-pointer to group by origin —
   goal-authoring vs other-harness-component vs tactical friction).

3. **Present one cluster at a time** to the user with: the title, why, how-to-apply, tally
   (distinct compact-events), and goal-origin. For each, ask the user to choose:
   - **promote** → `human-reviewed` (the lesson is confirmed). For an OPEN ISSUE this records the
     confirmation. For a **process win**, promotion triggers the win **LIFECYCLE**: promote →
     **integrate the best practice into the harness** (a CLAUDE.md line / the relevant skill /
     context bootstrap — wins are NOT injected via the active-issues view, so the integration IS the
     win's in-loop visibility) → then **close** it (it now lives in the harness). Propose the exact
     edit + target and apply it on the user's OK (the per-win sign-off principle 6 requires); record
     the integration target in `evidence`.
   - **close** → resolved (`status: closed`, one-line `evidence` of why — fixed, superseded,
     integrated into the harness, or promoted to a System-1 gate),
   - **misfile** → `status: misfiled` (it was never a real finding — harvest noise that slipped
     through). The harvest no longer writes `misfiled`, so this human sweep is the ONLY path into
     `## Misfiled`.
   - **leave** → keep `agent-reviewed` (not yet confirmed).

4. **Apply the user's choice via the register CLI** (NOT by hand-editing the markdown — let the
   register own dedup / tier-monotonicity / round-trip). For a finding `F` with the decision applied:
   - **promote** (set `"tier":"human-reviewed"`): `cd "<repo>" && echo '<F-json>' | uv run python scripts/system2_register.py --upsert --promote`
     — the **`--promote` flag is REQUIRED**. Without it, `--upsert` **deterministically clamps** the
     tier to `agent-reviewed` (the structural block on harvest self-promotion to human-reviewed —
     the tier-as-visibility gaming vector). **Only `/debrief` passes `--promote`.**
   - **close / misfile / leave**: the same `--upsert` **without** `--promote` (`"status":"closed"` or
     `"misfiled"` + `"evidence"`; *leave* = no write). A closed/misfiled finding drops out of the
     register-wide active-issues view on the next refresh.

5. **GAP-A proposals.** For each `proposals/<id>.md`, present the proposed structural prevention.
   On the user's sign-off it becomes a **tracked build task** (a new `validate.py` check /
   `goal-prompt` reference tweak / automation) — **never auto-applied here**. Note the disposition;
   do not implement the gate in this skill.

6. After the pass, refresh the active-issues view so closures take effect immediately:
   `cd "<repo>" && uv run python scripts/system2_register.py --write-active-issues`. Summarize what was
   promoted / closed / left and which proposals were signed off.
