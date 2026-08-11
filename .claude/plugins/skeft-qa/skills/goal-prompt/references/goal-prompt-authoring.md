# Goal-prompt authoring discipline

How to compose the native `/goal` **condition** (the string passed to `/goal`). Loaded on
demand by the `goal-prompt` skill at launch.

## Hard constraints

- **≤ 4,000 characters.** The condition is the native `/goal` Stop-hook condition; it has a
  hard length cap (goal.md).
- **Transcript-evaluable ONLY.** After every turn the condition + conversation go to a small
  fast evaluator (Haiku default) that **cannot run tools** — it judges only what is *surfaced
  in the transcript*. So every completion criterion must be demonstrable as text in the
  transcript. "validate.py prints 43/43 in the transcript" is checkable; "the code is correct"
  is not.
- **Self-describing.** Name the **tracked** source-of-truth paths so a fresh post-compaction
  turn can re-read them: `roadmap_path` (`docs/dev-loops/<roadmap>/...`) and the lab-notebook
  **INDEX** (`<home>/LAB_NOTEBOOK_INDEX.md` — the entry point; its FRONTIER + DECISIONS blocks are
  the re-grounding read, shards are opened on demand).
- **DURABLE CONTENT ONLY — never mutable tactical state (the #1 authoring failure).** Native `/goal`
  does **not** re-state the full condition to the *main model* every turn (a common misconception, and
  the mechanism matters here): each turn it sends the condition to a fast **evaluator** (Haiku default),
  which returns yes/no + a short *reason* — and only that reason is fed back to the main model. The full
  condition enters the main model's context **at set-time** (as the directive). What re-states the FULL
  condition to the main model is **our SessionStart re-injection after every compaction** (the ≤4k
  condition is always injected there in full, overriding budget). So anything in it is (a) re-asserted to
  a **fresh post-compaction context on every re-anchor** — and a long goal crosses many compactions — AND
  (b) read by the **evaluator every turn** for its DONE judgment. That is fine for DURABLE facts (success
  criteria; settled locks / non-negotiables; source-of-truth paths) — they don't change. It is **toxic**
  for MUTABLE tactical state, which goes stale and then re-seeds whatever it names:
  - **FORBIDDEN in the condition:** the current sorry line/number, "close-path engines: X/Y/Z",
    which lemma/route is "live" or "the breakthrough", current commit SHAs, "NEXT BRICK", progress
    framing ("one brick from closing"). These are **mutable** — the moment the proof moves, the
    condition is lying, and it is **re-injected in full on every post-compaction re-anchor** (and read
    by the evaluator every turn), **out-ranking** the lower-priority SETTLED_FORKS / PRE_DECISIONS reads.
    **Worked failure mode:** a condition baked `Close-path engines: <lemmaA> + <lemmaB>` (the routes that
    looked live when it was authored); a later turn proved those routes dead and recorded them in
    `SETTLED_FORKS.md`, but each post-compaction re-anchor kept re-injecting them in full as the live
    close-path — out-ranking the recorded ban — so an entire multi-commit session was built on the dead
    route before it was caught and reverted.
  - **Where mutable state lives instead:** the **live probe** `scripts/repo_state_probe.py`
    (recomputes the *real* current sorry + committed engines fresh each turn — run as FIRST_ACTION),
    `docs/dev-loops/SETTLED_FORKS.md` (dead/banned/superseded routes), and the lab-notebook FRONTIER
    (the loop's own next-brick, which the loop updates). The condition POINTS at these; it never
    snapshots them.
  - **Naming a route is allowed ONLY to BAN it** (a durable lock: "never re-open Route C"), never
    to PROMOTE it as the live close-path (mutable). Prefer "see SETTLED_FORKS.md" over inlining.

## What the condition must contain

1. **Posture (anti-escape + throughput + anti-reseed).** State plainly: *scope is settled; **land
   the maximum coherent GREEN increment each turn** (as much as you can finish cleanly — do NOT
   atomize into one tiny brick; fragmenting into many tiny turns multiplies stop→evaluate→restart cycles
   and reaches the next auto-compaction sooner, and breaks the reasoning train); a stop-hook firing is a
   GO signal, never a cue to stop/hold/re-scope; **never re-derive a settled-dead fork** (consult the
   negative frontier / `SETTLED_FORKS.md`); legitimate
   stops = a kernel-checked no-go or a genuine user-only decision.* This is the in-condition defense
   the evaluator re-reads every turn. NB: "maximum increment" is a **durable posture verb** (always
   true), NOT the forbidden mutable "NEXT BRICK: <specific lemma>" (which snapshots tactical state).
2. **One measurable end state with a transcript-visible check.** e.g. "the wave's bricks are
   shipped (kernel-pure, zero new sorry/axiom), `validate.py` prints N/N in the transcript,
   and the theorem/brick count reached <target>."
3. **GAP-B acceptance criterion (mandatory).** "NOT complete until the
   `skeft-qa:adversarial-reviewer` (and `skeft-qa:claims-reviewer` for paper-shaped output)
   ran in a **fresh context** with **zero BLOCKER findings, surfaced in the transcript**."
   Because the evaluator judges only the transcript, the loop cannot mark itself complete
   until that review evidence is literally present. (`/skeft-qa:wave-close` is the explicit
   companion path; this bakes the same bar into `/goal` itself.)

## Template

```
GOAL: <one-sentence outcome>. Source-of-truth: <roadmap_path> + <notebook_index_path> (re-read
the roadmap + the notebook INDEX after any compaction; open shards on demand). SCOPE IS SETTLED —
land the MAXIMUM coherent GREEN increment THIS turn (as much as you can finish cleanly; do NOT
atomize — per-turn throughput matters); a stop-hook firing is a GO signal, never a cue to
stop/hold/re-scope/hand back; never re-derive a settled-dead fork (negative frontier /
SETTLED_FORKS.md). Legitimate stops ONLY: a kernel-checked no-go, or a genuine user-only decision
(ask once, keep shipping meanwhile).
DONE when: (1) <measurable end state>; (2) validate.py prints N/N in the transcript;
(3) the fresh-context skeft-qa:adversarial-reviewer [+ claims-reviewer for papers] ran with
ZERO BLOCKER findings surfaced in the transcript.
```

## Anti-patterns (do not write)

- **Mutable tactical state in the condition** — current sorry line, "close-path engines: …",
  the "live"/"breakthrough" lemma, commit SHAs, "NEXT BRICK", "one brick from closing". It is
  re-injected in full on **every post-compaction re-anchor** (and read by the evaluator every turn),
  goes stale the moment the proof moves, and re-seeds whatever route it names — out-ranking
  SETTLED_FORKS/PRE_DECISIONS (this has cost an entire session built on a route already recorded as dead).
  Tactical state belongs in the live probe (`repo_state_probe.py`) / `SETTLED_FORKS.md` / the
  notebook FRONTIER. The condition points at them; it never snapshots them. **Test before writing
  each line: "will this still be true in 30 turns?" If no, it does not go in the condition.**
- Vibes-based completion ("the physics is right") — not transcript-checkable.
- Open scope ("do the rest of the phase") — that is the *whole wave*, not a `/goal`; pick a
  measurable wave-sized end state.
- **Atomize framing** — "build the next brick" as the per-turn target *under*-scopes the turn (the
  opposite error from open scope). A turn should land the **maximum coherent GREEN increment** it can
  (often many bricks): fragmenting into many tiny turns multiplies stop→evaluate→restart overhead and
  reaches the next auto-compaction sooner (the expensive context re-read is at compaction, not per turn),
  and the per-turn quality ceiling only rises as models improve. Write "land the maximum coherent GREEN
  increment each turn", not
  "the next brick". The ~5–10-brick COMMIT cadence is an orthogonal safety checkpoint, **not a per-turn
  cap**. (See the `feedback-maximize-per-turn-throughput` operating principle.)
- Omitting the fresh-context-review criterion (self-audit is insufficient — the
  `qi-gate-5-self-audit-blind-spot` lesson).

---

## Launch mechanics (moved from `SKILL.md`, TODO-D28)

These are the step-by-step mechanics for **arming** a loop. They are needed once, at
launch, and are not part of the always-on posture, so they live here rather than in the
skill body.

### Registering the session (marker write)
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
  `<repo>/.claude/dev-harness/managed/${CLAUDE_SESSION_ID}.json` (the **11-field form**, plus optional `slots`):
  `{"role": "<solo|lead>", "goal": "...", "goal_id": "<from above>", "mode": "<lean|general>", "arm_sha": "<from below>", "armed_ts": <from below>, "roadmap_path": "...", "notebook_path": "...", "jsonl_path": "<from above>", "repo": "<basename of repo root>", "question_guard": true}`.
  (`role` is descriptive-only; `goal_id` is the minted goal identity; `notebook_path` is the **INDEX**
  `<home>/LAB_NOTEBOOK_INDEX.md` scaffolded above; `question_guard` defaults `true` — the
  `PreToolUse(AskUserQuestion)` guard reads it; `/goal-guard` flips it. The Write tool creates the `managed/`
  dir as needed.)
  - **`mode`** (the live-anchor scope switch — LIVE_ANCHOR_REDESIGN_SPEC §B / principle 8): **if this is
    a Lean goal, set `"mode": "lean"`, else `"general"`.** (No criteria to evaluate — you are composing
    the goal, so you already know; this single switch gates whether `repo_state_probe.py` and the
    re-injection surface Lean-specific state. **Default `general`** if ever unsure.)
  - **`slots`** *(optional, worktree-venue goals only)*: the worktree slots this goal will own, e.g.
    `"slots": [2]` (solo on wt2) or `"slots": [1, 2]` (fan-out). Drives the **slot-aware re-anchor** —
    the probe + injected anchor surface the LIVE slot's tree (branch/HEAD/ahead/dirty) instead of main,
    and keep it isolated to this goal. **Omit it** if the goal declares no slot up front — `/reset-slot N`
    auto-stamps ownership the first time you reset a slot to prep it (exclusive per goal; `--force` to
    reclaim a slot another goal's marker still owns). Absent/empty ⇒ main-only anchor (unchanged behavior).
  - **`arm_sha`** = `` !`R=$(uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" repo-root 2>/dev/null); test -n "$R" || R=$(git rev-parse --show-toplevel 2>/dev/null); echo "$(git -C "${R:-.}" rev-parse HEAD 2>/dev/null)"` `` — the exact "since-arm" origin for the live
    repo-state probe (rebase-safe). Uses the harness `repo_root()` resolver (the SAME one the hooks/other
    probes use) so it works from the workspace root too, then `git -C "$R"`; the outer `echo` keeps exit 0 so
    it degrades to `""` (shell disabled / git error / launched outside the repo) — NOT a hard abort. If empty,
    write `""` — the probe degrades down its timestamp/last-N cascade.
  - **`armed_ts`** = `` !`date +%s` `` — arm wall-clock (epoch int), the probe's timestamp fallback.


### Facilitating the harvest host
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

**Emit the atlas critical-path map — BOTH fronts (so the user can re-scope BEFORE arming).** Print the
derived-atlas critical-path map — the **KEYSTONE** (the single most-gating open node), the per-area track
rollup, and the most-gating open assumptions — AND the **negative frontier** (the ranked kernel-checked
settled-dead forks the goal must NOT re-derive), so the goal's structure (e.g. "one keystone open while N
other areas sit available, and these dead-forks are fenced off") is visible before `/goal` is run:
`cd "<repo>" && uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" atlas-frontier 12`
`&& uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" atlas-antifrontier 8`.
**Plan-currency check (past-run lesson).** Before arming, confirm the `roadmap_path` + notebook INDEX the
condition points at are **current** — not a stale framing the plan has since outgrown. A goal armed on an
unvalidated/stale plan **thrashes turn-1** (the loop's first turn discovers the plan is wrong — a real
failure mode); the atlas KEYSTONE above is the fast cross-check that the plan's stated apex matches the
graph's most-gating node. If they disagree, fix the plan before arming, not in the loop.
**Node-count reference-class ONLY** — never a calendar / person-year estimate (honors the
ignore-PM-estimates rule). Empty if the atlas is unbuilt → skip silently. This same pair is the
**on-demand `/skeft-qa:frontier`** view: re-run it any time mid-loop to re-anchor on both fronts.

Then print the composed condition in a fenced block + one line: "run `/goal <condition>`" (the assistant cannot set
`/goal` itself). Confirm both the per-goal prompt file path and the marker path written.

> **Deterministic persistence / crash recovery (spec A.5).** The gitignored marker is the *fast-read* copy; the
> tracked `goal_prompt_<goal_id>.md` is the **durable, crash-recoverable source**. If the marker is **lost**
> (crash / power-loss / GC) you can re-arm by re-invoking this skill: recover the `/goal` condition + the existing
> `goal_id` from the tracked `goal_prompt_<goal_id>.md`, **reuse that same `goal_id`** (do NOT mint a new one for
> the same goal), and re-write the marker keyed to the (possibly new) `${CLAUDE_SESSION_ID}`. A genuinely **new**
> goal mints a fresh `goal_id` and writes a new per-goal file. (`build_reorientation_payload` reads
> `marker["goal"]` at runtime, with this tracked file as the durable fallback if the marker is gone.)

