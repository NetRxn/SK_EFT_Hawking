---
name: goal-prompt
description: Goal-mode LAUNCH + always-on posture for an autonomous /goal dev loop. On invocation it composes the /goal condition AND registers the session with the harness; its core posture re-attaches after compaction. Use when STARTING a managed /goal dev loop, or writing/refining a goal prompt + acceptance criteria. (For IN-LOOP development guidance — the MCP proof loop, worktree fan-out, friction catalog — use the goal-dev skill instead.)
argument-hint: <what the loop should achieve> [role=solo|lead]
disable-model-invocation: true
allowed-tools: Bash(git rev-parse *), Bash(ls *), Bash(test *), Bash(date *), Bash(uv run *), Write, mcp__scheduled-tasks__list_scheduled_tasks, mcp__scheduled-tasks__create_scheduled_task
---
<!-- disable-model-invocation: true is a deliberate USER-ONLY safety posture, not a technical
     requirement (spec 11 refined): an agent must NOT be able to auto-kick-off a goal. It is
     a per-skill policy choice (revisitable as the feature matures), not a blanket rule.
     allowed-tools lists the tools Claude ITSELF may call (the Write of the marker + the
     per-goal prompt file). The `!cmd` shell injections below (git rev-parse / ls / test / date)
     run BEFORE the skill is sent and are gated by `disableSkillShellExecution`, NOT by
     allowed-tools (skills.md:432/477) — see the A2 note before section 1. -->


## Always-on goal-mode posture (this core re-attaches after every compaction)
You are running a **managed native `/goal` dev loop**. Native `/goal` IS the loop; this
skill carries the posture and (at launch) arms it. Hold this posture every turn:
- **Scope is SETTLED. Do the next increment of real work THIS turn.** A stop-hook firing
  is a **GO signal**, never a cue to stop, hold, hand back, or re-scope.
- **You are managed; the source-of-truth = the tracked roadmap + lab notebook** (paths in
  the marker / the `/goal` condition). Do not re-pollute them with escape-bait
  ("person-year / precluded / no foothold / wall / multi-day, next session").
- **Legitimate stops only:** a kernel-checked no-go, or a genuine user-only decision.
  If you feel blocked, run full diligence first; if one option is clearly best, TAKE IT
  and log the rationale in the notebook.
- **For the in-loop development work, invoke the `goal-dev` skill** (`/skeft-qa:goal-dev`) — the
  model-invocable companion that carries the MCP-first proof loop, kernel-purity rules, the worktree
  fan-out flow (`/reset-slot` + `lean-worker`), a symptom-indexed Lean friction catalog, the full
  decision heuristics, and the lab-notebook lifecycle. **This skill (`goal-prompt`) only AUTHORS the goal at
  launch + holds this re-attaching posture core; `goal-dev` is where the dev references live.**

## At launch (invoked by the user) — arm the loop
Native `/goal` is the loop; this skill (1) registers the session and (2) composes the
condition. Do BOTH, concretely. Read `references/goal-prompt-authoring.md` first for the
composition discipline + acceptance criteria.

> **The one rule that matters most when composing the condition:** it is re-stated to the model
> **every turn** by native `/goal` — so it must hold **DURABLE content only** (success criteria,
> settled locks/non-negotiables, source-of-truth paths). **NEVER** bake in mutable tactical state
> (current sorry line, "close-path engines: X/Y/Z", the "live"/"breakthrough" lemma, commit SHAs,
> "next brick") — it goes stale and re-seeds whatever route it names, every turn. Mutable state is
> the **live probe**'s job (`scripts/repo_state_probe.py`, run as FIRST_ACTION) + `SETTLED_FORKS.md`
> + the notebook FRONTIER. Per-line test: *"true in 30 turns?"*

> **⚠ Inline-shell gating (review A2 — fail loud, never silently inert).** The `!cmd` shell injections below
> run **before** this skill is sent to the model and are gated by **`disableSkillShellExecution`** (the
> managed-settings kill-switch — skills.md:432/477), **NOT** by `allowed-tools` (which governs only the tools
> *Claude itself* later calls, e.g. the `Write` below). If that kill-switch is set, each `!cmd` injection is replaced
> by the literal sentinel `[shell command execution disabled by policy]`. **Before using any injected value, check
> for that sentinel; if present, STOP** with a clear message ("shell-command execution is disabled by policy, so
> the repo / transcript paths could not be resolved — re-enable it or arm the loop manually") rather than writing
> a marker with `UNRESOLVED` / sentinel paths (a mis-resolved marker makes the whole durability fix a silent
> no-op).

### 1. Register the session (write the marker)
- **Repo root (cwd-robust — resolves from the workspace root OR inside the repo):**
  `` !`R=$(uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" repo-root 2>/dev/null); test -n "$R" || R=$(git rev-parse --show-toplevel 2>/dev/null); echo "${R:-UNRESOLVED}"` `` —
  this resolves the plugin's OWN repo via the harness `repo_root()` (`find_workspace()` / `REPO_DIR_NAME`), the
  SAME resolver the hooks use, so it works whether CC was launched from the **workspace root** (where `.mcp.json` /
  lean-lsp lives — the usual launch point) or from inside the repo, and the marker lands exactly where the hooks
  read it. It falls back to `git rev-parse` for an in-repo launch outside the workspace. The line above is
  `UNRESOLVED` only if launched entirely outside the workspace (or is the `[shell command execution disabled by
  policy]` sentinel — see the A2 note above); in that case STOP and tell the user to launch from the workspace
  root or inside the repo. (`<repo>` below = this resolved path.)
- **Transcript path (deterministic, first-turn-safe — resolve now, while this session is live):**
  `` !`uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" jsonl-path ${CLAUDE_SESSION_ID}` `` —
  the harness resolves this session's `<sid>.jsonl` **deterministically**: an existing file if present, else it
  reconstructs `~/.claude/projects/<cwd-slug>/<sid>.jsonl` (CC's slug = the cwd with every non-alphanumeric → `-`,
  verified to match incl. worktree dirs). This is **first-turn-safe** — `goal-prompt` runs before CC has flushed
  the transcript to disk, so a bare `ls` glob would be momentarily empty; the CLI never returns empty for a valid
  `${CLAUDE_SESSION_ID}`. Use this exact path as `jsonl_path`. (If it is the A2 `[shell command execution disabled
  by policy]` sentinel, STOP — see the A2 note above.)
- **Pre-commit gate install-check (review A4):** `` !`R=$(uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" repo-root 2>/dev/null); test -n "$R" || R=$(git rev-parse --show-toplevel 2>/dev/null); test -n "$R" && test -x "$R/.git/hooks/pre-commit" && echo INSTALLED || echo MISSING` `` — the
  local git pre-commit hook is the **sole enforcing mechanical gate** (the v3.0 CC commit advisory was dropped,
  spec 12 L2), and it fires only where installed; a fresh clone / new worktree may have **no gate at all**. If this
  prints `MISSING` (or the A2 sentinel), **warn the user loudly** ("⚠ no pre-commit gate installed for this
  checkout — run the canonical pre-commit installer before committing") but still arm the loop.
- **Mint `goal_id` (spec 2/8/A.5):** `goal_id = `` !`date +%Y%m%dT%H%M%S` `` — a datetime stamp that is the
  **stable logical-goal identity**. If this is the A2 sentinel, **STOP** (the sentinel-detect-and-STOP above
  covers it — never write a marker / per-goal file with a sentinel `goal_id`). **Re-arm of the SAME goal reuses
  its existing `goal_id`** (recovered from the prior `goal_prompt_<goal_id>.md` — see crash recovery in step 3);
  a **NEW goal mints a fresh one**. (A roadmap hosts many goals over time, so `goal_id` — not `roadmap_path` —
  is the unique identity.)
- **Role:** parse `role=solo|lead` from `$ARGUMENTS` (**default `solo`** — orchestrator-of-one). `lead` only for
  an agent-team orchestrator. **`role` is DESCRIPTIVE METADATA ONLY** (logging / harvest attribution — spec
  5/A.5): it is recorded in the marker but the harness **never branches on it** (the SessionStart re-injection
  is role-agnostic — spec 4). Do **not** treat `lead` vs `solo` as a behavioral switch.
- Resolve the **tracked** `roadmap_path`, the lab-notebook **home**, and the `goal` text from `$ARGUMENTS`.
  The notebook home **defaults to `docs/dev-loops/<roadmap>/`** (in-repo → stable paths + the pre-commit
  `notebook check` applies; the notebook files are **git-ignored**, so nothing auto-commits → leak-safe in
  full-auto mode). **Override** by passing `notebook=<dir>` in `$ARGUMENTS` for a loop whose notebook lives
  elsewhere (e.g. an existing `Lit-Search/<phase>/` notebook — used as-is, never moved). All consumers read
  the home from the marker's `notebook_path`, so an override propagates automatically.
- **Scaffold the lab notebook (bootstrap-if-missing — idempotent, never clobbers):**
  `uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/notebook_lib.py" new <home> --roadmap <roadmap_path>`.
  This creates a correct active `LAB_NOTEBOOK.md` **and** `LAB_NOTEBOOK_INDEX.md` (the four live blocks:
  FRONTIER / DELIVERABLES CHECKLIST / DECISIONS & DEAD-ENDS / SHARD INDEX — progressive disclosure from turn 1,
  CHECKLIST seeded from the roadmap). The marker's `notebook_path` is the **INDEX**
  (`<home>/LAB_NOTEBOOK_INDEX.md`) — the entry point the SessionStart re-injection + `/orient` read first.
  (Re-arm of an existing loop is a no-op here; it never overwrites an in-progress notebook.) Full model:
  `goal-dev/references/lab-notebook.md`.
- **Write the per-goal prompt file (the durable source) with the Write tool** to
  `<repo>/docs/dev-loops/<roadmap>/goal_prompt_<goal_id>.md` (NOT a bare `goal_prompt.md` — a roadmap hosts many
  goals over time, so name it uniquely by `goal_id`; goals on the same roadmap never collide / overwrite — spec
  8). This **tracked** file is the **durable, crash-recoverable source** of the `/goal` condition; the marker's
  `goal` field below is only the fast-read copy (spec A.5 — see step 3 crash recovery).
- **Write the marker with the Write tool** (clean JSON — NOT a `cat >` heredoc) to
  `<repo>/.claude/dev-harness/managed/${CLAUDE_SESSION_ID}.json` (the **11-field form**):
  `{"role": "<solo|lead>", "goal": "...", "goal_id": "<from above>", "mode": "<lean|general>", "arm_sha": "<from below>", "armed_ts": <from below>, "roadmap_path": "...", "notebook_path": "...", "jsonl_path": "<from above>", "repo": "<basename of repo root>", "question_guard": true}`.
  (`role` is descriptive-only; `goal_id` is the minted goal identity; `notebook_path` is the **INDEX**
  `<home>/LAB_NOTEBOOK_INDEX.md` scaffolded above; `question_guard` defaults `true` — the
  `PreToolUse(AskUserQuestion)` guard reads it; `/goal-guard` flips it. The Write tool creates the `managed/`
  dir as needed.)
  - **`mode`** (the live-anchor scope switch — LIVE_ANCHOR_REDESIGN_SPEC §B / principle 8): **if this is
    a Lean goal, set `"mode": "lean"`, else `"general"`.** (No criteria to evaluate — you are composing
    the goal, so you already know; this single switch gates whether `repo_state_probe.py` and the
    re-injection surface Lean-specific state. **Default `general`** if ever unsure.)
  - **`arm_sha`** = `` !`R=$(uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" repo-root 2>/dev/null); test -n "$R" || R=$(git rev-parse --show-toplevel 2>/dev/null); echo "$(git -C "${R:-.}" rev-parse HEAD 2>/dev/null)"` `` — the exact "since-arm" origin for the live
    repo-state probe (rebase-safe). Uses the harness `repo_root()` resolver (the SAME one the hooks/other
    probes use) so it works from the workspace root too, then `git -C "$R"`; the outer `echo` keeps exit 0 so
    it degrades to `""` (shell disabled / git error / launched outside the repo) — NOT a hard abort. If empty,
    write `""` — the probe degrades down its timestamp/last-N cascade.
  - **`armed_ts`** = `` !`date +%s` `` — arm wall-clock (epoch int), the probe's timestamp fallback.

### 2. Compose the /goal condition (≤ 4,000 chars; transcript-evaluable only — goal.md)
Per `references/goal-prompt-authoring.md`, produce a condition that: (a) is **self-describing** (names the
roadmap + notebook paths); (b) states the **posture** — "scope settled; build the next brick; a stop-hook firing
is a GO signal, never a cue to stop/hold/re-scope; legitimate stops = a kernel-checked no-go or a genuine user
decision"; (c) has **one measurable end state with a transcript-visible check** ("validate.py prints N/N in the
transcript"); (d) **requires the fresh-context review (GAP-B)** — "not complete until the
`skeft-qa:adversarial-reviewer` (and `claims-reviewer` for paper work) ran in a fresh context with **zero BLOCKER
findings, surfaced in the transcript**"

### 3. Facilitate the harvest host (one-time, idempotent) + output
Facilitate the one-time System-2 harvest host (spec 6.3). After writing the marker:
- **(a) Desktop scheduled task (preferred).** If the scheduled-tasks MCP tools are available, call
  `mcp__scheduled-tasks__list_scheduled_tasks` and look for `taskId = skeft-harvest-<repo>`; if absent, call
  `mcp__scheduled-tasks__create_scheduled_task` with the **fixed `taskId = skeft-harvest-<repo>`** (→ idempotent
  singleton; a second arm with the same id is a no-op), **recurring**, prompt = the literal `/skeft-qa:harvest`.
  This triggers a **one-time user-approval** on first arm; then it runs recurring in the background.
- **(b) Second-session `/loop` (CLI fallback).** If the Desktop scheduled-tasks tools are not available, **print**
  the one-line command for the user to run in a **separate** terminal (NEVER this `/goal` session — `/loop` is
  session-scoped and would compete with `/goal`): `/loop <interval> /skeft-qa:harvest`. Re-arm before the 7-day
  `/loop` expiry.
- **Cadence guidance (spec 6.3 — guidance, NOT a hard floor).** Titrate `<interval>` toward the average duration
  of a ~1M-token session (≈ the auto-compact cadence) — **e.g. hourly** — so the **active System-2 issues** view
  stays fresh enough to feed the next SessionStart re-injection / AskUserQuestion redirect near-real-time. Pick a
  sane default (hourly) and tune later; this is the same `cadence_hours` the harvest records in `harvest_state`
  (which drives the SessionStart drift warning).
- **State plainly** that this host setup is **one-time** and is **NOT silently auto-spawned** (review C1 / spec 6.3
  residual): the marker write + this facilitation are automatic, but the host *start* is one deliberate step (a
  Desktop approval, or starting the second-terminal `/loop`).
- **Host-permission note:** the unattended host must run with the harvest skill's `allowed-tools` Bash patterns
  permitted, or `system2_register.py --upsert` auto-denies and the harvest writes nothing.

**Emit the atlas critical-path map (so the user can re-scope BEFORE arming).** Print the derived-atlas
critical-path map — the **KEYSTONE** (the single most-gating open node), the per-area track rollup, and
the most-gating open assumptions — so the goal's structure (e.g. "one keystone open while N other areas
sit available") is visible before `/goal` is run:
`cd "<repo>" && uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" atlas-frontier 12`.
**Node-count reference-class ONLY** — never a calendar / person-year estimate (honors the
ignore-PM-estimates rule). Empty if the atlas is unbuilt → skip silently. This same CLI is the
**on-demand `/orient`** view: re-run it any time mid-loop to re-anchor on the critical path.

Then print the composed condition in a fenced block + one line: "run `/goal <condition>`" (the assistant cannot set
`/goal` itself). Confirm both the per-goal prompt file path and the marker path written.

> **Deterministic persistence / crash recovery (spec A.5).** The gitignored marker is the *fast-read* copy; the
> tracked `goal_prompt_<goal_id>.md` is the **durable, crash-recoverable source**. If the marker is **lost**
> (crash / power-loss / GC) you can re-arm by re-invoking this skill: recover the `/goal` condition + the existing
> `goal_id` from the tracked `goal_prompt_<goal_id>.md`, **reuse that same `goal_id`** (do NOT mint a new one for
> the same goal), and re-write the marker keyed to the (possibly new) `${CLAUDE_SESSION_ID}`. A genuinely **new**
> goal mints a fresh `goal_id` and writes a new per-goal file. (`build_reorientation_payload` reads
> `marker["goal"]` at runtime, with this tracked file as the durable fallback if the marker is gone.)

### 4. Verify the marker armed (review A1 — fail loud, FINAL step)
The marker is keyed by `${CLAUDE_SESSION_ID}`; if it landed at the wrong key (or an empty session id), **every
harness hook is inert and the durability fix is a silent no-op**. So as the FINAL step, verify the file exists at
the resolved key and print **PASS/FAIL** to the user:
`` !`R=$(uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" repo-root 2>/dev/null); test -n "$R" || R=$(git rev-parse --show-toplevel 2>/dev/null); test -n "$R" && test -f "$R/.claude/dev-harness/managed/${CLAUDE_SESSION_ID}.json" && echo "PASS: marker armed for ${CLAUDE_SESSION_ID}" || echo "FAIL: marker NOT found for ${CLAUDE_SESSION_ID} — the loop is UNMANAGED"` ``
If this prints **FAIL** (or the A2 sentinel), tell the user the loop is **not** managed (do not start `/goal` until
the marker is armed at the right key) and re-attempt the Write in step 1.
