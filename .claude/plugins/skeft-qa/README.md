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
| `claims-reviewer` | Sentence-level prose audit with chain-of-backing + verdict across six finding classes (arithmetic / toolchain-pin / pipeline-vs-prose / theorem-name drift, hypothesis-disclosure gap, placeholder-cited-as-verified). Reconciles prior findings instead of silently superseding. |
| `figure-reviewer` | Visual review of generated figures (after `review_figures.py`) for rendering quality, physics accuracy, and style. |
| `prose-reviewer` | **The fourth reviewer.** Reads a bundle draft start to finish as a referee at its named venue: does the abstract lead with the result, does each section advance a single argument, where would a reader stop. The other three ask *does it render*, *is it backed*, *is it wrong*; none asks whether it lands. Output is a RESTRUCTURING INSTRUCTION, not a finding list. Runs at lift §7.5, before Stage 9. |
| `paper-drafter` | **The drafting counterpart to the four reviewers, and the only agent that produces manuscript prose.** It RETURNS a section and the lead places it — a bundle is one monolithic draft, so parallel drafters must not write it; it holds no `Write`/`Edit`. Drafts ONE assigned bundle section at Stage 10 against a lead-authored brief, with `paper-authoring` loaded. Dispatch several in parallel over DISJOINT sections; the lead owns the outline, the argument's spine, and integration. Its governing rule: a section that cites must be written against the cited work read IN FULL for that portion — misrepresented prior art is the one class no layer beneath it can catch, since every layer checks a source resolves, never that the prose is faithful to it. |

`adversarial-reviewer` and `claims-reviewer` accept a `bundle_target` argument for
bundle-aware Stage-13 review (anchors in `docs/agents/claims-reviewer-bundle-prompts.md`).

## Harness agents (dispatched by the loop, not by you)

These are not review agents; they are the workers and proxies an autonomous `/goal` loop
dispatches for itself. Listed here because they ship in `agents/` and are therefore live and
invocable — an undocumented agent is one no operator knows exists.

| Agent | Dispatched by | Purpose |
|---|---|---|
| `lean-worker` | the lead, during worktree fan-out | Proves ONE independent Lean sub-chain in a pre-built slot (`wt1`/`wt2`/`wt3`), each with its own build-isolated `mcp__lean-lsp-wtN__*` and its own `.lake`, so several run in parallel with zero coordination. Commits on the slot branch for the lead to merge. |
| `coach` | the `PreToolUse(AskUserQuestion)` guard | In-time human proxy for a loop that tried to ask a blocking question while the user is out of the loop. Reads the pre-decisions store plus loop state and returns ONE decision and ONE next action. Fresh context is the point. |
| `research-scout` | the lead, after Tier-0 local research is exhausted | Read-only web reconnaissance for a single focused question. Holds web tools and nothing that can mutate the repo, so a poisoned page cannot turn it into an editor. Reports; never decides, edits, or commits. |
| `harvest-extractor` | the `harvest` skill | Extracts dev-process signal from one `/goal` transcript span, including the pre-vs-post-compact delta. Haiku. |
| `harvest-consolidator` | the `harvest` skill | Register-AWARE consolidation of extractor candidates into the four-section System-2 register (files, combines, re-opens). Opus. |

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
| `/skeft-qa:paper-authoring` | you **or** the loop | **The drafting counterpart to `prose-reviewer`.** House voice, venue conventions, and the prohibited-pattern floor for `papers/<bundle>/paper_draft.tex`. Its `references/prohibited-patterns.md` is a MANDATORY read before drafting and is SHARED with the reviewer, so a rule cannot drift between writing and review. |
| `/skeft-qa:architecture-change` | you **or** the loop | **The repeatable infra-lane process** (ADR-012 D18): orient → measure at HEAD → ADR/spec **before** the code → adversarially review the SPECIFICATION with three different instruments → pilot → plan → subagent-driven build → ship with non-vacuity, every registration site, and the docs in the same commit. Its `references/` carry ADR-012 as the worked example — all three correction rounds — and the derive-don't-quote registration checklist. |
| `/skeft-qa:sync` | you **or** the loop | Mechanical Stage-12 sync (counts/tables/deps/citation cache) in one command. Idempotent, regen-lock-serialized. |
| `/skeft-qa:wave-close` | you **or** the loop | Deterministic per-wave close: prereq checks → dispatch the fresh-context review → record `*_close.md`. |
| `/skeft-qa:harvest` | scheduled task / 2nd-session `/loop` | Off-hot-loop System-2 harvest: Haiku extract → **register-aware Opus consolidate** (files/combines into the four-section `SYSTEM2_REGISTER.md`: re-open recurring closed, group semi-related, route real wins → Process Wins, misfile noise). Never inside a `/goal` session. |
| `/skeft-qa:debrief` | you (user-only) | Interactive promotion `agent-reviewed → human-reviewed` over the already-organized register; never auto-edits CLAUDE.md/hooks/roadmaps. |

### Commands (`commands/<name>.md`) — atomic, globally-accessible actions

| Command | Invocation | Purpose |
|---|---|---|
| `/skeft-qa:orient` | you | A ≤200-word compass from the marker + source-of-truth docs (where am I, what's the next brick). |
| `/skeft-qa:frontier` | you **or** the loop | Read-only compass over **both** atlas fronts: the positive frontier (ADR-005 D-I) ranked by gating impact for high-leverage fan-out, and the **negative** frontier (ADR-007 N-D) of kernel-checked settled-dead forks a context-free worker must not re-enter. Never mutates the atlas. |
| `/skeft-qa:notebook` | you **or** the loop | Maintain the `/goal` lab notebook (`sync`/`shard`/`check`) so the active shard self-levels under the ~25k-token Read guard. A command rather than a skill so the lead can log a brick from any context without loading `goal-dev`. |
| `/skeft-qa:goal-guard <on\|off>` | you (user-only) | Toggle the AskUserQuestion guard (`off` = let the loop ask you a question; `on` = resume autonomous redirect; default on). |
| `/skeft-qa:goal-end` | you (user-only) | Disarm the loop — remove this session's marker. The explicit teardown for a mid-session `/goal clear` (which fires no hook). |
| `/skeft-qa:reset-slot <N>` | you **or** the loop | Reset worktree slot `wtN` to `main` the guardrail-safe way (`checkout -B`; **refuses if the slot has commits not yet on `main`**). |

### Hooks (`hooks/hooks.json` → `scripts/`) — six

**Four are default-inert + fail-open** (the loop-durability hooks: they do nothing unless this
session is a managed loop, and a crash never blocks the tool call). **Two are neither** — the
web-egress guard is *unconditional* and *fail-closed*, because a guard that fails open is not a
guard; the worker shell guard is *subagent-scoped* and denies inside that scope while leaving the
lead untouched. Read the posture per row; there is no blanket rule.

| Hook (`scripts/…`) | Posture | Job |
|---|---|---|
| `SessionStart` (compact\|resume) — `harness_reinject.py` | inert + open | Re-inject the **shared re-orientation payload** (the `/goal` condition + the always-on RE-ANCHOR + a **live git HEAD anchor** + the **FIRST_ACTION** mandating `repo_state_probe.py` (the LIVE REPO-STATE anchor — supersedes any narrated frontier) + `PRE_DECISIONS.md` + `SETTLED_FORKS.md` reads + the `/skeft-qa:goal-dev` pointer + the optional coaching block) — **the durability fix**. The prose lab-notebook FRONTIER is NO LONGER injected (the proven drift vector). |
| `PreToolUse(AskUserQuestion)` — `harness_question_guard.py` | inert + open | Deny + redirect a blocking question with the re-orientation payload; log the question to `blocked_questions.jsonl`. Marker-gated, top-level-only, honors `question_guard`, fail-open. |
| `PreCompact` — `harness_precompact.py` | inert + open | **Durable-channel staging only** (Live-Anchor Move 3): synchronously write the gitignored pre-loss **snapshot** artifact (last substantive message + HEAD) and — for a `mode=lean` goal — a `regen_requested.flag` staging the boundary atlas regen (the agent executes the regen post-compact via backgrounded Bash). Marker+mode-gated; **NO context injection / NO summary steer** (aligns to autocompact, never owns it); **writes ONLY under the gitignored `.claude/dev-harness/`** — never a git-tracked path (QI invariant). |
| `SessionEnd` — `harness_session_end.py` | inert + open | **Marker teardown** — removes this session's marker on `reason=clear` only (a `/clear` that also clears the goal), so a dead loop's marker stops re-injecting. Never on `logout`/`resume` (a still-active goal restores on `--resume`). |
| `PreToolUse(WebSearch\|WebFetch)` — `harness_web_egress_guard.py` | **unconditional + fail-CLOSED** | Screens outbound web calls against the research egress denylist. **Not marker-gated** — it applies to every session, managed or not, including subagents, because an un-managed session is exactly where an unreviewed fetch is most likely. If the guard cannot launch, the hook command emits a literal `deny` payload rather than falling through, so a broken guard blocks egress instead of silently permitting it. Denylist: `scripts/research_egress_denylist.txt` (seeded from `.sample.txt` by `scripts/install_egress_denylist.sh`). |
| `PreToolUse(Bash)` — `harness_worker_shell_guard.py` | subagent-scoped + denies in scope | **ADR-008 parity with the Codex-side policy.** Denies build / cache / integration commands (`lake build\|clean\|exe cache get`, `rm -rf …/.lake`, `git merge\|rebase\|cherry-pick`, `slotctl build\|absorb\|supervisor`) to SUBAGENTS ONLY, keyed on `agent_id`. The lead is never affected — it is the party that builds. An unparseable event reads as the lead and allows, since bricking the lead's Bash is the worse failure. |

No Stop/SubagentStop (`/goal` owns continuation), no PostToolUse (the local git pre-commit hook is
the sole enforcing mechanical gate). PreCompact is **synchronous staging only** — the harvest
remains off-hot-loop. Hook commands invoke the repo's uv Python ≥3.14. The four durability hooks
trail `2>/dev/null || true` so a crash can never block the tool call; the egress guard deliberately
does **not** — it trails a literal `deny` payload instead, which is what makes it fail-closed.

**Standing invariant (QI, 2026-06-24):** a hook MUST NOT write a git-tracked path — all
harness-written artifacts live under the gitignored `.claude/dev-harness/`. They resolve there
launch-independently (hooks via `repo_root()`/`REPO_DIR_NAME`; repo scripts via `__file__`), so the
launch point (workspace parent vs. inside the repo) never changes the destination, and the public
harness never writes the private repo.

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
