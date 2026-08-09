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


## Always-on goal-mode posture

> ⚠️ **Corrected 2026-08-09 (TODO-D28).** This heading read *"this core re-attaches after every
> compaction"*. It does not. `harness_reinject.py` composes a **minimal frame** (one GO-signal
> line) plus a payload built by `harness_common.build_reorientation_payload` — RE-ANCHOR, the live
> HEAD anchor, the coaching block. **It never reads this file.** The reinjector's own docstring
> says so: *"the full discipline is the mandated read"*, meaning `PRE_DECISIONS.md`.
>
> The practical consequence, and why it is worth stating: moving content out of this file does
> **not** drop it from the compaction path, because this file was never on it. What must survive a
> compaction belongs in `PRE_DECISIONS.md` or the payload, not here.
You are running a **managed native `/goal` dev loop**. Native `/goal` IS the loop; this
skill carries the posture and (at launch) arms it. Hold this posture every turn:
- **Scope is SETTLED. Land the MAXIMUM coherent increment of real work THIS turn** — as much as you
  can finish cleanly; do NOT atomize into one tiny brick (fragmenting into many tiny turns multiplies
  stop→evaluate→restart cycles and reaches the next auto-compaction sooner, and breaks the reasoning
  train). A stop-hook firing is a **GO signal**, never a cue to stop, hold, hand back, or re-scope.
- **You are managed; the source-of-truth = the tracked roadmap + lab notebook** (paths in
  the marker / the `/goal` condition). Do not re-pollute them with escape-bait
  ("person-year / precluded / no foothold / wall / multi-day, next session").
- **Legitimate stops only:** a kernel-checked no-go, or a genuine user-only decision.
  If you feel blocked, run full diligence first; if one option is clearly best, TAKE IT
  and log the rationale in the notebook.
- **You own the builds.** If you fan out to worktree slots, **only you run `lake build` /
  `lake build SKEFTHawking.ExtractDeps` / `validate.py`** — on `main`, after merging. Workers gate on
  their slot's `lean_diagnostic_messages` / `lean_goal` / `lean_verify`. Slot `.lake` isolation prevents
  corruption, not CPU contention: Lake takes one job per core, so concurrent slot builds oversubscribe
  the machine and the cost lands on *your* serialized gate (measured: a ~15 s pre-commit hook stretched
  past 10 min under three slot builds — indistinguishable from a broken toolchain). Rule + the one
  narrow exception: `goal-dev/references/parallel-worktrees.md`.
- **For the in-loop development work, invoke the `goal-dev` skill** (`/skeft-qa:goal-dev`) — the
  model-invocable companion that carries the MCP-first proof loop, kernel-purity rules, the worktree
  fan-out flow (`/reset-slot` + `lean-worker`), a symptom-indexed Lean friction catalog, the full
  decision heuristics, and the lab-notebook lifecycle. **This skill (`goal-prompt`) only AUTHORS the goal at
  launch + holds this re-attaching posture core; `goal-dev` is where the dev references live.**

## At launch (invoked by the user) — arm the loop
Native `/goal` is the loop; this skill (1) registers the session and (2) composes the
condition. Do BOTH, concretely. Read `references/goal-prompt-authoring.md` first for the
composition discipline + acceptance criteria.

> **The one rule that matters most when composing the condition:** it is re-injected in full to the model
> on **every post-compaction re-anchor** (our SessionStart mechanism — native `/goal` itself only feeds the
> *evaluator's* reason back each turn, not the full condition) AND read by the `/goal` **evaluator** every
> turn for its DONE judgment — so it must hold **DURABLE content only** (success criteria, settled
> locks/non-negotiables, source-of-truth paths). **NEVER** bake in mutable tactical state (current sorry
> line, "close-path engines: X/Y/Z", the "live"/"breakthrough" lemma, commit SHAs, "next brick") — it goes
> stale and re-seeds whatever route it names on the next re-anchor. Mutable state is
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
Resolve, then write the marker. Each step's exact command and its failure mode are in
`references/goal-prompt-authoring.md` → *Launch mechanics*; do not improvise them.

1. **Repo root** — cwd-robust, via `harness_common_cli.py repo-root` with a `git rev-parse`
   fallback. `UNRESOLVED` (or the A2 sentinel) → **STOP** and tell the user where to launch from.
2. **Transcript path** — `harness_common_cli.py jsonl-path ${CLAUDE_SESSION_ID}`, which is
   first-turn-safe (a bare `ls` glob is momentarily empty before CC flushes).
3. **Pre-commit gate check** — the local hook is the sole enforcing mechanical gate. `MISSING`
   → warn loudly, still arm.
4. **Mint `goal_id`** — a datetime stamp, the stable logical-goal identity. Re-arming the SAME
   goal reuses its id; a new goal mints a fresh one. Never write a sentinel id.
5. **Role** — `solo` (default) or `lead`. **Descriptive metadata only**; the harness never
   branches on it.
6. **Roadmap, notebook home, goal text** from `$ARGUMENTS`. Notebook defaults to
   `docs/dev-loops/<roadmap>/`; override with `notebook=<dir>`.
7. **Scaffold the notebook** (idempotent, never clobbers) and **write the per-goal prompt file**
   to `goal_prompt_<goal_id>.md`, then the marker itself.

### 2. Compose the /goal condition (≤ 4,000 chars; transcript-evaluable only — goal.md)
Per `references/goal-prompt-authoring.md`, produce a condition that: (a) is **self-describing** (names the
roadmap + notebook paths); (b) states the **posture** — "scope settled; land the maximum coherent GREEN increment
each turn (don't atomize); a stop-hook firing is a GO signal, never a cue to stop/hold/re-scope; never re-derive a
settled-dead fork (negative frontier / SETTLED_FORKS); legitimate stops = a kernel-checked no-go or a genuine user
decision"; (c) has **one measurable end state with a transcript-visible check** ("validate.py prints N/N in the
transcript"); (d) **requires the fresh-context review (GAP-B)** — "not complete until the
`skeft-qa:adversarial-reviewer` (and `claims-reviewer` for paper work) ran in a fresh context with **zero BLOCKER
findings, surfaced in the transcript**"

### 3. Facilitate the harvest host (one-time, idempotent) + output
One-time and idempotent: facilitate the System-2 harvest host so the loop's process signal is
captured. Exact commands, crash-recovery and the output contract are in `references/goal-prompt-authoring.md` → *Launch mechanics*.

### 4. Verify the marker armed (review A1 — fail loud, FINAL step)
The marker is keyed by `${CLAUDE_SESSION_ID}`; if it landed at the wrong key (or an empty session id), **every
harness hook is inert and the durability fix is a silent no-op**. So as the FINAL step, verify the file exists at
the resolved key and print **PASS/FAIL** to the user:
`` !`R=$(uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" repo-root 2>/dev/null); test -n "$R" || R=$(git rev-parse --show-toplevel 2>/dev/null); test -n "$R" && test -f "$R/.claude/dev-harness/managed/${CLAUDE_SESSION_ID}.json" && echo "PASS: marker armed for ${CLAUDE_SESSION_ID}" || echo "FAIL: marker NOT found for ${CLAUDE_SESSION_ID} — the loop is UNMANAGED"` ``
If this prints **FAIL** (or the A2 sentinel), tell the user the loop is **not** managed (do not start `/goal` until
the marker is armed at the right key) and re-attempt the Write in step 1.
