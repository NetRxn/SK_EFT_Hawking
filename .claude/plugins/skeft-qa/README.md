# skeft-qa

QA review agents **and** the autonomous-development harness for the
**SK_EFT_Hawking** physics project.

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
session is a *managed* loop (a `/dev-goal` marker exists for its `session_id`)
*and* is not a subagent (`agent_id` present). It never touches Explore/Plan/review
subagents or non-dev interactive sessions.

### Commands

| Command | Purpose |
|---|---|
| `/dev-goal` | Arm a managed loop: write the per-session marker + compose the self-describing goal prompt, then hand off to native `/goal`. |
| `/orient` | A ≤200-word compass from the marker + source-of-truth docs (where am I, what's the next brick). |
| `/debrief` | Synthesize harvested learnings into **proposed** (`agent-reviewed`) QI findings. Never auto-edits CLAUDE.md / hooks / roadmaps. |

### Hooks (`hooks/hooks.json` → `scripts/`)

| Hook | Job |
|---|---|
| `SessionStart` (compact\|resume) | Re-inject the role-appropriate goal/roadmap directive — **the durability fix**. |
| `PreCompact` | Harvest the lab-notebook tail into the QI intake before compaction squashes it. |
| `PostToolUse(Edit\|Write)` | De-pollution guard: flag escape-language written into the marker's source-of-truth docs (the exact 5q.F re-pollution, at write time). |
| `PostToolUse(Bash: git commit)` | Refresh counts / inventory / QI register; flag regenerated tracked artifacts for re-commit. |

Harness state (markers, QI intake) lives under `~/.claude/skeft-harness/` — a
fixed, load-mechanism-independent dir (commands can't compute `$CLAUDE_PLUGIN_DATA`),
keyed by the globally-unique `session_id`.

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
