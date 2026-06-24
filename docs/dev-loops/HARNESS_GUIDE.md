# Dev-Harness Operator's Guide (skeft-qa)

**Audience:** you (the human driving the loop) and any future session that needs to *use* the harness rather than build it. This is the forward-facing "how do I actually run this" manual. The design rationale lives in the harness design spec (kept on the private design side); this guide is operations only. (A private sibling plugin mirrors this same model for the private repo and has its own guide there; everything below is the public `skeft-qa` side.)

> **TL;DR**
> 1. **Launch Claude Code from inside `SK_EFT_Hawking/`** (the normal case — a standalone clone of this repo). The plugin resolves its repo from your cwd, so it Just Works. *(If you run the optional multi-repo setup where lean-lsp's `.mcp.json` sits at a workspace root one level up, launch from that root instead so lean-lsp loads — the harness resolves `SK_EFT_Hawking` from there too. Either launch point is fine.)*
> 2. Arm a loop: **`/skeft-qa:goal-prompt <what the loop should achieve>`**. It prints a `/goal <condition>` — paste that to start the native loop.
> 3. The harness re-grounds the loop after every compaction and intercepts blocking questions automatically. You're hands-off until the goal is met.

---

## 1. What the harness is

`skeft-qa` is a Claude Code plugin that keeps a long-running autonomous **native `/goal`** loop on-track across compactions, without competing with `/goal` itself. (A private sibling plugin mirrors the same model for the private repo — lighter wrappers, documented on the private side.)

It ships **three CC hooks** (all default-inert + fail-open, gated on a per-session marker):
- `SessionStart` — after every compaction/resume, re-injects the settled `/goal` condition + an always-on **RE-ANCHOR** + the live lab-notebook **FRONTIER** + a **mandatory read** of `PRE_DECISIONS.md` + the `/skeft-qa:goal-dev` pointer + (when the harvest authored one) the per-goal **coaching block**. (This replaced the old blind active-issues/wins/heuristics injection; the pre-decisions are now READ, not inlined — so they grow unbounded, and the emitted payload sits well under the 10,000-char `additionalContext` limit.)
- `PreToolUse(AskUserQuestion)` — when the loop tries to block on a question (and you're not there), it denies + redirects with the same re-orientation payload, so the loop keeps moving instead of stalling.
- `SessionEnd` — marker teardown on `reason=clear` (a `/clear` that also clears the goal), so a dead loop's marker stops re-injecting. (A mid-session `/goal clear` fires no event → use `/skeft-qa:goal-end`.)

Plus skills you invoke, a mechanical-sync layer, and an off-hot-loop System-2 "what went **poorly or extremely well** from a process standpoint" harvest — a **register-aware** consolidator that files & combines each finding into the **sharded** register (active `SYSTEM2_REGISTER.md`: `## Index` + **Open** + **Process Wins**; archive `SYSTEM2_ARCHIVE.md`: **Closed** + **Misfiled**) so it stays synthesized, and **authors the per-goal coaching block** (the synthesized re-orientation the SessionStart re-inject surfaces).

---

## 2. Where to launch — anywhere; the harness resolves its repo cwd-robustly

You can launch Claude Code from **wherever suits your setup** — the skills and hooks all resolve `SK_EFT_Hawking` via the harness `repo_root()` (`find_workspace()/REPO_DIR_NAME`, with a `git rev-parse` fallback), so you never have to think about cwd:

- **Standalone / public use — launch from inside the repo** (`cd /path/to/SK_EFT_Hawking && claude`). This is the **normal case**: a clone of just this repo, no parent workspace. Resolution uses the cwd git-root. **You do not need anything "one level up."**
- **Multi-repo dev setup — launch from the workspace root.** If this repo lives under a workspace dir that also holds `.mcp.json` (which auto-loads **lean-lsp**, the primary Lean dev loop) one level up, launch from that root so lean-lsp loads — there is no `SK_EFT_Hawking/.mcp.json`, so an in-repo launch wouldn't auto-load it. The harness resolves `SK_EFT_Hawking` from the workspace root via `find_workspace()`, so `/skeft-qa:*` still works without `cd`-ing in. (This is a core requirement of *this project's* local setup; a public user won't have it.)
- **Worktrees** also work (git-root fallback).

The only `UNRESOLVED` case is launching from somewhere with no path to the repo at all. (Historically the skills used a bare `git rev-parse`, which broke at the workspace root — a build defect, now fixed: every skill + review agent uses `repo_root()`.)

---

## 3. The core workflow — arm and run a `/goal` loop

1. **Arm it** (you invoke; an agent cannot auto-start a goal):
   ```
   /skeft-qa:goal-prompt finish the Phase 6X wave per docs/roadmaps/<roadmap>.md
   ```
   The skill: composes a ≤4,000-char `/goal` condition (self-describing, with transcript-visible acceptance criteria incl. a zero-BLOCKER fresh-context review, and **durable content ONLY** — success criteria + settled locks + source-of-truth paths; **never mutable tactical state** like the current sorry line or "close-path engines: X/Y/Z", which native `/goal` would re-inject every turn and re-seed once stale — that state is the live probe's / SETTLED_FORKS' / notebook FRONTIER's job), **writes the session marker** (incl. `mode`/`arm_sha`/`armed_ts`) to `<repo>/.claude/dev-harness/managed/<session_id>.json`, **facilitates the one-time harvest host**, prints **PASS/FAIL** that the marker armed, and prints the composed condition.
2. **Start the native loop** — paste the printed condition:
   ```
   /goal <the condition it printed>
   ```
   (The assistant can't set `/goal` for you — that's a native command.)
3. **Walk away.** The loop ships increments; after each compaction the SessionStart hook re-grounds it on the settled scope; blocking questions are intercepted and redirected. It ends only when the goal's acceptance criteria are met (or you `/clear`).

`role=lead` vs `role=solo`: pass `role=lead` only if you're orchestrating an agent team; default `solo`. (Descriptive metadata — the harness behaves identically either way.)

---

## 4. Slash-command reference (`/skeft-qa:<name>`)

| Name | Kind | Who invokes | What it does |
|---|---|---|---|
| **goal-prompt** | skill | you (user-only) | **Goal-mode LAUNCH + posture core.** Composes the `/goal` condition + arms the marker + facilitates the harvest host. Its ≤5k core **re-attaches after every compaction** (the durable anti-drift posture). *Authoring only — in-loop dev guidance is `goal-dev`.* |
| **goal-dev** | skill | you **or** the loop | **The in-loop development skill** (model-invocable). MCP-first proof loop, kernel-purity rules, worktree fan-out, a symptom-indexed Lean friction catalog; `references/` load on demand. The SessionStart re-inject points here. |
| **orient** | command | you | A ≤200-word compass from the marker + roadmap/notebook: Goal / Done / Next / Guardrails. |
| **goal-guard `<on\|off>`** | command | you (user-only) | Toggle the AskUserQuestion guard. **off** = let the loop ask you a question; **on** = resume autonomous redirect. Default on in goal mode. |
| **goal-end** | command | you (user-only) | Disarm the loop — remove this session's marker. The explicit teardown for a mid-session `/goal clear` (the platform fires no event there). |
| **reset-slot `<N>`** | command | you **or** the loop | Reset worktree slot `wtN` to `main` the guardrail-safe way (`checkout -B`; **refuses if the slot has commits not on `main`**). Replaces hand-typed `git reset --hard` (which the auto-mode classifier denies). |
| **sync** | skill | you **or** the loop | Run the mechanical Stage-12 sync (counts/tables/deps/citation cache) in one command. Idempotent, regen-lock-serialized. |
| **wave-close `<wave-id>`** | skill | you **or** the loop | Deterministic per-wave close: gate prereqs → dispatch the fresh-context adversarial review (zero BLOCKERs) → write `<wave>_close.md`. The loop runs this itself to satisfy its acceptance criteria. |
| **harvest** | skill | scheduled task / second-terminal `/loop` — **never the goal session** | Off-hot-loop System-2 harvest: Haiku extract → **register-aware Opus consolidate** (reads the standing register; stacks a recurrence onto an open finding, **re-opens** a recurring closed one, **groups** semi-related via `--group`, files real wins → **Process Wins** (capped at agent-reviewed; never injected — they reach the loop via `/debrief` → human-reviewed → harness integration), and **drops** noise (the harvest never writes `## Misfiled` — that is `/debrief`'s human sweep bucket). Self-aborts if run inside a managed loop. |
| **debrief** | skill | you (user-only) | Interactively promote System-2 `agent-reviewed` findings → `human-reviewed`, triage GAP-A gate proposals — over an **already-organized** register (the consolidator keeps it synthesized; promotion to `human-reviewed` is debrief's exclusive call). |

---

## 5. The System-2 harvest host (one-time setup)

The harvest reads finished/running loop transcripts off the hot loop and records process lessons into the **sharded** System-2 register (active `docs/dev-loops/SYSTEM2_REGISTER.md`: `## Index` + **Open** + **Process Wins**; archive `SYSTEM2_ARCHIVE.md`: **Closed** + **Misfiled**), and authors the per-goal **coaching block** (`.claude/dev-harness/coaching/<goal_id>.json`) the SessionStart re-inject surfaces (computed off the derived atlas + `stall_detector.py`). The Opus consolidator is **register-aware** — it reads the whole register and files/combines each candidate, so recurrences re-open and semi-related items merge instead of accreting as one-offs; only `/debrief` promotes a finding to `human-reviewed`. `goal-prompt` facilitates the host, but a skill **cannot** silently spawn a standing background process — you complete it **once**:

- **Preferred — Desktop scheduled task:** `goal-prompt` offers to create a recurring task (idempotent) running `/skeft-qa:harvest`. Approve it once; it then runs in the background (~hourly).
- **CLI fallback — second terminal:** run `/loop <interval> /skeft-qa:harvest` in a **separate** terminal (never the `/goal` session). Re-arm before the 7-day `/loop` expiry.

If the SessionStart re-injection ever prints "⚠ System-2 harvest hasn't run in N days", the host died — restart it.

---

## 6. Troubleshooting

| Symptom | Cause | Fix |
|---|---|---|
| `command not found: cmd` on a `/skeft-qa:*` invocation | A stale plugin **cache** still has the old `` !`cmd` `` skill prose (fixed in source 2026-06-17). | `claude plugin update skeft-qa@skeft-local --scope local` (see §7), then **restart CC**. |
| Skill prints **`UNRESOLVED`** repo root / marker **FAIL** | Launched from **outside the workspace** (or the cache is pre-fix). | Launch from the workspace root or inside the repo; refresh the cache (§7) + restart. |
| `/goal-prompt` (bare, no namespace) errors but `/skeft-qa:goal-prompt` works | The running session predates a cache update; the bare alias resolved a stale copy. | Restart CC (both forms then use the current cache); or just use the namespaced form. |
| Claude **Desktop**: "could not load skill files" | Desktop is viewing a stale/orphaned cache SHA after a `claude plugin update`. | Fully **quit + reopen** Claude Desktop (a Customize-tab refresh isn't enough). |
| `!cmd` injection asks for approval with no "allow" button | The pre-send shell injection hit the permission classifier. | The harness Bash verbs are whitelisted in each `.claude/settings.local.json` (`permissions.allow`): `git rev-parse, echo, date, ls, head, test, grep, jq, python3, uv run, lake build, cd`. If a new verb is added to a skill, whitelist it there. |
| A loop "holds" / asks "should I continue?" | Anti-pattern (the loop should self-serve). | `/goal-guard` is on by default to prevent the question-stall; SessionStart re-grounds it. If it persists, the goal condition's acceptance criteria may be unmeasurable — re-arm with a transcript-visible end state. |

---

## 7. How the plugin is installed + how to update after editing it

**Install model (per-machine, untracked).** The repo is registered as a *local marketplace* and the plugin enabled in `.claude/settings.local.json` (`enabledPlugins` — gitignored, never committed, so opening the repo never auto-enables a hook-bearing plugin for a collaborator/CI). The workspace root also enables it so a workspace-root launch picks it up.

**The running plugin is a CACHE COPY**, not the in-repo source:
- cache: `~/.claude/plugins/cache/skeft-local/skeft-qa/<git-sha>/` (keyed by the repo **commit SHA**).

**So after editing plugin source you MUST refresh the cache, or the running app keeps the old copy:**
```bash
# 1. Commit the source change (the cache is keyed by the committed HEAD).
# 2. Refresh:
claude plugin marketplace update
claude plugin update skeft-qa@skeft-local --scope local   # run from BOTH the workspace root AND inside SK_EFT_Hawking/
# 3. Restart Claude Code (and fully quit+reopen Desktop) — "restart required to apply".
```
> ⚠ **skeft-qa has two local install records** (one per launch point: the workspace root and `SK_EFT_Hawking/`). `claude plugin update` only refreshes the record for your *current* cwd, so run it from **both** to update both. Verify with:
> `python3 -c "import json;d=json.load(open('$HOME/.claude/plugins/installed_plugins.json'));[print(r['projectPath'].split('/')[-1],'->',r['installPath'].split('/')[-1]) for r in d['plugins']['skeft-qa@skeft-local']]"`

(The private sibling plugin has its own semver-keyed update step — see its guide on the private side.)

---

## 8. Invariants you can rely on

- **Default-inert:** every hook does nothing unless a marker exists for *this* `session_id` in *this* plugin's repo and the session is not a subagent. A non-dev session sees no `[dev-harness]` injection and no question interception.
- **Fail-open:** any hook/lock error → allow/proceed; a harness bug never strands the loop.
- **Leak-safe by construction:** the public `skeft-qa` resolves only `SK_EFT_Hawking` (its `REPO_DIR_NAME`); it can never read the private sibling's marker. The public System-2 register additionally drop-scrubs any finding naming the private repo.
- **Nothing competes with `/goal`:** `/goal` *is* the Stop hook; the harness ships none.
- **Positive state is recomputed live, never remembered (Live-Anchor redesign, 2026-06-24).** After a compaction the loop's FIRST_ACTION runs `scripts/repo_state_probe.py` — the LIVE REPO-STATE anchor (commits since arm, working-tree, and for a Lean goal the atlas engine inventory + the `lean_diagnostic_messages` live-sorry mandate) — which **supersedes any narrated frontier/summary**. The prose lab-notebook FRONTIER is no longer injected (it was the proven drift vector behind System-2 `compaction-summary-quality`). Negative/procedural state (dead/banned/superseded routes) lives in `docs/dev-loops/SETTLED_FORKS.md` — a mandated read; grep it before any "impossible/needs-banned" reasoning. Lean-specific behavior is gated by the marker's `mode` field (default `general`; Lean is opt-in, never assumed for a non-Lean goal). Full spec: `LIVE_ANCHOR_REDESIGN_SPEC.md`.
- **A hook MUST NOT write a git-tracked path (QI invariant, 2026-06-24).** Every harness-written artifact (marker, watermark, snapshot, `regen_requested.flag`, the boundary atlas `atlas_view.boundary.json`) lives under the **gitignored** `.claude/dev-harness/` — so a hook never dirties the working tree with un-authored diffs. The PreCompact hook only *stages* (synchronous snapshot + flag, <1s, no context injection); the heavy atlas regen runs as the agent's backgrounded Bash post-compact (ENFILE-single-flighted), writing the gitignored boundary atlas — never the tracked `lean/atlas_view.json`. Destinations resolve **launch-independently** (hooks via `repo_root()`/`REPO_DIR_NAME`; repo scripts via `__file__`), so workspace-parent vs. in-repo launch is irrelevant.
- **Self-improving, never self-mutating:** findings are tagged by review tier and *proposed*; the agent never edits CLAUDE.md / roadmaps / hooks / gates on the fly.
- **Runs under the project's Python 3.14, from any cwd.** Harness scripts are invoked with **`uv run --no-sync python`** (which yields the uv-managed 3.14 even at the workspace root, via an ephemeral interpreter), **never bare `python3`** (that's the system 3.9.x). Repo *resolution* and *stdlib* helpers run from any cwd; *project-dependency* scripts (`validate.py`, `system2_register`→`src.core`, `update_counts`, `lake`) `cd` into the repo first so `uv` gives them the repo's deps/pythonpath. **Maintainers: keep `uv run --no-sync python`; do not switch to bare `python3`, and do not add a workspace-root uv project — the project scripts need *each repo's own* env, which a root project can't supply.**
- **The transcript path is captured deterministically, never guessed.** At arm time `goal-prompt` records the loop's transcript (`jsonl_path` in the marker) via `harness_common_cli.py jsonl-path ${CLAUDE_SESSION_ID}`. The **session id is not invented or predicted** — it's the real current id Claude Code supplies as `${CLAUDE_SESSION_ID}`, which is exactly the basename CC names the transcript by. Only the *path around that id* is assembled, and it's fully determined by the id + the cwd: `~/.claude/projects/<cwd-slug>/<sid>.jsonl` (slug = the cwd with every non-alphanumeric → `-`, CC's own encoding). The resolver returns an existing file if one is on disk (e.g. a resumed session), else the reconstructed path — so it works on a **first-turn arm**, when CC hasn't flushed the `.jsonl` yet (the harvest reads it later, by which point CC has written it to exactly that path). If `${CLAUDE_SESSION_ID}` is empty it returns `""` and `goal-prompt` STOPs rather than arm a marker pointing at the wrong/no transcript — it can never resolve a *different* session's file.

---

## 9. Parallel Lean apparatus (persistent worktree slots)

For a `lead` orchestrating **independent** Lean sub-chains, fan out to the **`lean-worker`** project
agent (`skeft-qa:lean-worker`, in `.claude/plugins/skeft-qa/agents/`), one per **persistent worktree slot** (`wt1/2/3`). Each slot has
its **own** build-isolated lean-lsp server (`mcp__lean-lsp-wt1/2/3__*`, defined in the workspace
`.mcp.json`), so up to 3 workers run **fully in parallel with no coordination and no shared LSP**.

**Why persistent static slots** (not inline per-subagent MCP): inline `mcpServers` in subagent
frontmatter **do not surface** via the Agent tool here (verified) — only **inherited** `.mcp.json`
servers do, and those attach at **session start**, so the slots must pre-exist. One-time setup:
`scripts/setup_lean_worktree_slots.sh` creates `wt1/2/3` + COW-clones the build into each (~500 MB real
disk for all 3 — the `.lake` clones are APFS copy-on-write; `du`'s ~43 GB is logical/COW-blind). The
servers are enabled in `.claude/settings.local.json`; **restart once after first setup** so they attach.

Lead flow, per task: **reset the slot** with **`/skeft-qa:reset-slot N`** (it runs the guardrail-safe
`git -C .claude/worktrees/wtN checkout -B worktree-wtN main` and **refuses if the slot holds commits not
yet on `main`** — merge them first; re-clone `.lake` if main's build advanced — **never** hand-type
`git reset --hard`/`git clean`, which the auto-mode permission classifier denies on a slot) → **dispatch**
`Agent(subagent_type="skeft-qa:lean-worker", prompt="SLOT N=2, path=<abs …/wt2>, use
mcp__lean-lsp-wt2__*. <brick>")` → worker proves MCP-first via its own `mcp__lean-lsp-wtN__*`, kernel-pure,
commits on `worktree-wtN` → **merge** `worktree-wtN` into `main`, re-run the full gate. The slot **stays**
for the next task (`/reset-slot`, don't delete). **Fan out only when the proof DAG has genuinely branched.**
Works from either launch point (root or in-repo) — the lead uses plain `git -C <slot>` (no `isolation:
worktree`), and the slot servers use absolute paths. Full convention: **`parallel-worktrees.md`** in the
`goal-dev` skill (`.claude/plugins/skeft-qa/skills/goal-dev/references/parallel-worktrees.md`).

---

*State lives at `<repo>/.claude/dev-harness/` (gitignored): `managed/<sid>.json` markers, `watermarks/`, `active_issues.json`, `coaching/<goal_id>.json` (the per-goal coaching block), `stall_history/<goal_id>.json` (the per-goal stall-detector observations), `blocked_questions.jsonl`, `locks/`. The standing **pre-decisions** the loop reads are tracked at `<repo>/docs/dev-loops/PRE_DECISIONS.md`; the crash-recoverable source of each goal condition is `<repo>/docs/dev-loops/<roadmap>/goal_prompt_<goal_id>.md`.*
