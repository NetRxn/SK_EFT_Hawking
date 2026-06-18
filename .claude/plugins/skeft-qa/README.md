# skeft-qa

QA review agents **and** the autonomous-development harness for the
**SK_EFT_Hawking** physics project.

> **▶ Using the harness (launch, arm a `/goal` loop, slash-command reference, harvest
> host, troubleshooting, cache refresh): see the operator's guide
> [`docs/dev-loops/HARNESS_GUIDE.md`](../../../docs/dev-loops/HARNESS_GUIDE.md).**
> Quickstart: launch CC from inside `SK_EFT_Hawking/` (or, in a multi-repo setup, from the
> workspace root one level up — both work), then
> `/skeft-qa:goal-prompt <what the loop should achieve>` → paste the printed `/goal …`.

## Review agents (Stage 13)

Run in a **fresh context window** — no author-side assumptions, no confirmation
bias — to catch what the internal pipeline (Stages 1–12) misses before a paper or
notebook is finalized.

| Agent | Purpose |
|---|---|
| `adversarial-reviewer` | Fresh-context paper audit against the readiness-gate taxonomy: wrong-target citations, parameter drift, placeholder theorems cited as verified, cross-paper contradictions, narrative overclaims, stale counts, production-run health. Emits `ReviewFinding` records; BLOCKER findings reopen the relevant gate. |
| `claims-reviewer` | Sentence-level prose audit with chain-of-backing + verdict across five finding classes (arithmetic / toolchain-pin / pipeline-vs-prose / theorem-name drift, hypothesis-disclosure gap). Reconciles prior findings instead of silently superseding. |
| `figure-reviewer` | Visual review of generated figures (after `review_figures.py`) for rendering quality, physics accuracy, and style. |

`adversarial-reviewer` and `claims-reviewer` accept a `bundle_target` argument for
bundle-aware Stage-13 review (anchors in `docs/agents/claims-reviewer-bundle-prompts.md`).

## Dev-harness (autonomous `/goal` loops)

Keeps a long-running, multi-agent `/goal` loop on-track across compactions — the
mechanism that fixes the "lost the big picture / re-scoped the settled goal"
failure mode. **Default-inert + fail-open:** every hook does nothing unless this
session is a *managed* loop (a `/skeft-qa:goal-prompt` marker exists for its
`session_id`) *and* is not a subagent (`agent_id` present). It never touches
Explore/Plan/review subagents or non-dev interactive sessions.

### Skills (`skills/<name>/SKILL.md`) — progressive-disclosure workflows

| Skill | Invocation | Purpose |
|---|---|---|
| `/skeft-qa:goal-prompt` | you (user-only) | **Goal-mode LAUNCH + the always-on posture core** (re-attaches after compaction). On invocation it composes the `/goal` condition + registers the session (8-field marker, incl. `question_guard:true`). You then run native `/goal`. *Authoring only — in-loop dev guidance is `goal-dev`.* |
| `/skeft-qa:goal-dev` | you **or** the loop | **The in-loop development skill** — MCP-first proof loop, kernel-purity rules, the worktree fan-out flow, a symptom-indexed Lean friction catalog. Invoke while developing; its `references/` load on demand. |
| `/skeft-qa:sync` | you **or** the loop | Mechanical Stage-12 sync (counts/tables/deps/citation cache) in one command. Idempotent, regen-lock-serialized. |
| `/skeft-qa:wave-close` | you **or** the loop | Deterministic per-wave close: prereq checks → dispatch the fresh-context review → record `*_close.md`. |
| `/skeft-qa:harvest` | scheduled task / 2nd-session `/loop` | Off-hot-loop System-2 harvest: Haiku extract → **register-aware Opus consolidate** (files/combines into the four-section `SYSTEM2_REGISTER.md`: re-open recurring closed, group semi-related, route real wins → Process Wins, misfile noise). Never inside a `/goal` session. |
| `/skeft-qa:debrief` | you (user-only) | Interactive promotion `agent-reviewed → human-reviewed` over the already-organized register; never auto-edits CLAUDE.md/hooks/roadmaps. |

### Commands (`commands/<name>.md`) — atomic, globally-accessible actions

| Command | Invocation | Purpose |
|---|---|---|
| `/skeft-qa:orient` | you | A ≤200-word compass from the marker + source-of-truth docs (where am I, what's the next brick). |
| `/skeft-qa:goal-guard <on\|off>` | you (user-only) | Toggle the AskUserQuestion guard (`off` = let the loop ask you a question; `on` = resume autonomous redirect; default on). |
| `/skeft-qa:goal-end` | you (user-only) | Disarm the loop — remove this session's marker. The explicit teardown for a mid-session `/goal clear` (which fires no hook). |
| `/skeft-qa:reset-slot <N>` | you **or** the loop | Reset worktree slot `wtN` to `main` the guardrail-safe way (`checkout -B`; **refuses if the slot has commits not yet on `main`**). |

### Hooks (`hooks/hooks.json` → `scripts/`) — three (all default-inert + fail-open)

| Hook | Job |
|---|---|
| `SessionStart` (compact\|resume) | Re-inject the **shared re-orientation payload** (the `/goal` condition + "re-read CLAUDE.md" + the **`/skeft-qa:goal-dev` pointer** + active System-2 issues **& `[WIN]` process wins** + heuristics) + a best-effort first-turn self-check — **the durability fix**. |
| `PreToolUse(AskUserQuestion)` | Deny + redirect a blocking question with the re-orientation payload; log the question to `blocked_questions.jsonl`. Marker-gated, top-level-only, honors `question_guard`, fail-open. |
| `SessionEnd` | **Marker teardown** — removes this session's marker on `reason=clear` only (a `/clear` that also clears the goal), so a dead loop's marker stops re-injecting. Never on `logout`/`resume` (a still-active goal restores on `--resume`). |

No Stop/SubagentStop (`/goal` owns continuation), no PreCompact (the harvest is
off-hot-loop), no PostToolUse (the local git pre-commit hook is the sole enforcing
mechanical gate). Hook commands invoke the repo's uv Python ≥3.14
(`uv run --no-sync python … 2>/dev/null || true`).

Harness state (markers, watermarks, the active-issues cache, the blocked-question log)
lives under **`<repo>/.claude/dev-harness/`** — project-scoped + gitignored, where
`<repo>` is resolved cwd-based via `find_workspace()`/`REPO_DIR_NAME` (NOT `~/.claude`,
NOT `$CLAUDE_PLUGIN_DATA`), keyed by the globally-unique `session_id`.

## Packaging & enablement

Auto-discovered agents (`agents/*.md`) + commands (`commands/*.md`) + hooks
(`hooks/hooks.json`); no component paths declared in the manifest. Distributed as
the `skeft-qa` plugin in the in-repo `skeft-local` marketplace
(`.claude-plugin/marketplace.json` at the repo root).

Enablement is **per-machine** — the repo does not force-enable the plugin on
everyone who trusts it. To turn it on:

```bash
claude plugin marketplace add . --scope local   # from the repo root
claude plugin install skeft-qa@skeft-local --scope local
```
