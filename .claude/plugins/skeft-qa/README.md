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

### Skills / commands

| Skill | Purpose |
|---|---|
| `/skeft-qa:goal-prompt` | **The unified goal-mode skill** — its core is the always-on operating posture (re-attaches after compaction); on invocation it composes the `/goal` condition + registers the session (writes the 8-field marker, incl. `question_guard:true`). You then run native `/goal`. |
| `/skeft-qa:goal-guard` | Toggle the AskUserQuestion guard for this managed loop (`on`\|`off`; default on — turn off when you want to be asked). |
| `/skeft-qa:orient` | A ≤200-word compass from the marker + source-of-truth docs (where am I, what's the next brick). |

(`/skeft-qa:sync` + `/skeft-qa:wave-close` ship in Plan 2; `/skeft-qa:harvest` + `/skeft-qa:debrief` in Plan 3.)

### Hooks (`hooks/hooks.json` → `scripts/`) — exactly two

| Hook | Job |
|---|---|
| `SessionStart` (compact\|resume) | Re-inject the **shared re-orientation payload** (the `/goal` condition + "re-read CLAUDE.md" + active System-2 issues + heuristics) + a best-effort first-turn self-check — **the durability fix**. |
| `PreToolUse(AskUserQuestion)` | Deny + redirect a blocking question with the re-orientation payload; log the question to `blocked_questions.jsonl`. Marker-gated, top-level-only, honors `question_guard`, fail-open. |

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
