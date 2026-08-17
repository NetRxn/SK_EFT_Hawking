# Dev-Harness Operator's Guide (skeft-qa)

**Audience:** you (the human driving the loop) and any future session that needs to *use* the harness rather than build it. This is the forward-facing "how do I actually run this" manual. The design rationale lives in the harness design spec (kept on the private design side); this guide is operations only. (A private sibling plugin mirrors this same model for the private repo and has its own guide there; everything below is the public `skeft-qa` side.)

> **TL;DR**
> 1. **Launch Claude Code from inside `SK_EFT_Hawking/`** (the normal case — a standalone clone of this repo). The plugin resolves its repo from your cwd, so it Just Works. *(If you run the optional multi-repo setup where lean-lsp's `.mcp.json` sits at a workspace root one level up, launch from that root instead so lean-lsp loads — the harness resolves `SK_EFT_Hawking` from there too. Either launch point is fine.)*
> 2. Arm a loop: **`/skeft-qa:goal-prompt <what the loop should achieve>`**. It prints a `/goal <condition>` — paste that to start the native loop.
> 3. The harness re-grounds the loop after every compaction and intercepts blocking questions automatically. You're hands-off until the goal is met.

---

## 1. What the harness is

`skeft-qa` is a Claude Code plugin that keeps a long-running autonomous **native `/goal`** loop on-track across compactions, without competing with `/goal` itself. (A private sibling plugin mirrors the same model for the private repo — lighter wrappers, documented on the private side.)

It ships two **distinct** hook families, and conflating them is a real hazard — the loop-durability hooks below are default-inert and fail-OPEN, while the enforcement guards are unconditional and fail-CLOSED. A reader who generalises "default-inert, fail-open" across the plugin will mistake an enforced boundary for an advisory one.

The **loop-durability** hooks (default-inert + fail-open, gated on a per-session marker) are operations, and are what this guide covers:
- `SessionStart` — after every compaction/resume, re-injects the settled `/goal` condition + an always-on **RE-ANCHOR** + a **FIRST_ACTION** that recomputes live state via `scripts/repo_state_probe.py` + a **mandatory read** of `PRE_DECISIONS.md` + the `/skeft-qa:goal-dev` pointer + the derived **ATLAS FRONTIER / NEGATIVE FRONTIER** + (when the harvest authored one) the per-goal **coaching block**.
  - ⚠ **The prose lab-notebook FRONTIER is NOT injected, on purpose** (Live-Anchor redesign, Move 1). A hand-written "next brick" is a *proven drift vector* — it survives the compaction that invalidated it and re-seeds a stale tactic, which is precisely what the RE-ANCHOR text warns about. Positive state is **recomputed** by the probe rather than narrated; the notebook INDEX remains the on-demand pointer. `harness_common._frontier_for` still exists and still works — it is a **retired helper**, intentionally uncalled, kept fail-soft like `_read_predecisions_core`. Wiring it back in is a regression; `tests/test_harness_core.py::test_payload_never_injects_prose_frontier` will fail if you do. (This replaced the old blind active-issues/wins/heuristics injection; the pre-decisions are now READ, not inlined — so they grow unbounded, and the emitted payload sits well under the 10,000-char `additionalContext` limit.)
- `PreToolUse(AskUserQuestion)` — when the loop tries to block on a question (and you're not there), it denies + redirects with the same re-orientation payload, so the loop keeps moving instead of stalling.
- `SessionEnd` — marker teardown on `reason=clear` (a `/clear` that also clears the goal), so a dead loop's marker stops re-injecting. (A mid-session `/goal clear` fires no event → use `/skeft-qa:goal-end`.)

The **enforcement** guards — web egress, and the worker shell guard that stops a dispatched subagent running builds or cache mutations — are a different animal: unconditional, fail-closed, and not yours to toggle. They are described where the mechanism lives, in [`../architecture/QA_QI_INFRASTRUCTURE_MAP.md`](../architecture/QA_QI_INFRASTRUCTURE_MAP.md) §1.5, not here; this guide is operations. The one operator action they need is the first-run denylist install (below).

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

(The private sibling plugin now follows this exact model — same git-SHA keying, same command shape, documented on the private side. It used to declare a `version` in its `plugin.json`, which pins the cache to that string: `claude plugin update` then compares versions rather than content and prints `already at the latest version` while serving a **stale** cache. Two committed, docs-mandated components sat missing from every session that way before it was caught on 2026-07-28. Per the plugin reference: omit `version` and Claude Code falls back to the git commit SHA, so every commit is a new version. **Neither plugin should ever declare one.**)

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

## 8b. Lab notebooks — where a loop's durable memory lives, and who can see it

A loop's lab notebook is the project's **cross-session process memory**: what landed, what was
tried and failed, and which routes are settled dead. It is the home of the 5q.B operating rule
**"log tried-and-FAILED so we never repeat post-compact"** — the goldfish-reseed guard.

**Layout** (owned by `.claude/plugins/skeft-qa/scripts/notebook_lib.py`; create with
`/skeft-qa:notebook new`, never by hand):

| file | role |
|---|---|
| `docs/dev-loops/<loop>/LAB_NOTEBOOK_INDEX.md` | the durable, always-loaded entry point — bounded and topical |
| `docs/dev-loops/<loop>/LAB_NOTEBOOK.md` | the active chronological shard, oldest first |
| `docs/dev-loops/<loop>/LAB_NOTEBOOK_W<n>.md` | frozen historical shards; the audit layer, read on demand |

One legacy exception predates the layout: `docs/roadmaps/Phase5qB_LabNotebook.md`.

### ⚠️ Notebooks are GITIGNORED, so no worktree has one

`.gitignore` carries `**/LAB_NOTEBOOK*.md`. Notebooks are therefore **untracked**, and
`git worktree add` materialises only tracked files. **No lab notebook exists in any worktree.**

This matters because subagents are dispatched into worktrees by default, so the tracker the loop
calls authoritative is invisible to the workers doing the work. And the failure is **asymmetric**:
the notebook tooling resolves against the **repo root**, not the caller's cwd (the same
fail-open resolution recorded for `harness_common_cli.py`), so a worker's `notebook new` **writes
to the main checkout** while its reads come back empty. Writes land, reads fail — an agent
consults the tracker, finds nothing, proceeds uninformed, and still contributes to it.

**Rules that follow:**

- **Dispatching a worker that should read a notebook? Cite the ABSOLUTE path into the main
  checkout.** The lead knows it; the worker cannot derive it. A repo-relative path silently
  resolves to nothing inside a worktree.
- **Never conclude from a worktree-relative miss that a notebook does not exist.** Check the main
  checkout before reporting absence — this exact collision produced a live contradiction between a
  lead who had seen both files and an agent that correctly found neither.
- **Never have a worker write a notebook into its own worktree.** Gitignored files there are
  invisible to the merge and are destroyed with the worktree.

### Why a loop without a notebook is a real risk, not a tidiness issue

Notebooks are created per **goal loop**, so a phase that never ran as one never gets a tracker —
and `END_TO_END_MAP.md` records that **nothing validates a roadmap**. Phase 5q.T is the worked
example: a roadmap authored inside another phase's housekeeping commit, no loop, no notebook, and
months later three route errors sitting in it that nothing caught — a change-of-rings adjunction
with the wrong variance for its purpose, an entry-state table silent about work that had already
landed, and a sidedness error making one prescribed construction untypeable. A roadmap is a plan
and is unchecked; the notebook is the tracker and is the only durable place a refuted route gets
recorded.

⚠️ **Open, deliberately not decided here:** whether these should be gitignored at all. The stated
purpose is durable cross-session memory, and untracked files survive neither a fresh clone, nor a
new worktree, nor a machine change. Raised in
`papers/AutomatedReviews/2026-08-17-worktree-agents-cannot-read-notebooks/infra.md`.

## 9. Parallel Lean apparatus (persistent worktree slots)

For a `lead` orchestrating **independent** Lean sub-chains, fan out to the **`lean-worker`** project
agent (`skeft-qa:lean-worker`, in `.claude/plugins/skeft-qa/agents/`), one per **persistent worktree slot** (`wt1/2/3`). Each slot has
its **own** build-isolated Lean LSP behind a shared loopback endpoint (`mcp__skeft_wt1/2/3__*`, generated
into the workspace `.mcp.json`), so up to 3 workers run **fully in parallel with no coordination**.

**Why persistent static slots** (not inline per-subagent MCP): inline `mcpServers` in subagent
frontmatter **do not surface** via the Agent tool here (verified) — only **inherited** `.mcp.json`
servers do, and those attach at **session start**, so the slots must pre-exist. One-time setup:
`scripts/setup_lean_worktree_slots.sh` creates `wt1/2/3` + COW-clones the build into each (~500 MB real
disk for all 3 — the `.lake` clones are APFS copy-on-write; `du`'s ~43 GB is logical/COW-blind).
Endpoints are generated by `slotctl config render --client claude` and served by
`slotctl supervisor start` — **one process per slot for the whole workstation**, shared with Codex rather
than spawned per client or per subagent (ADR-008). **Restart once after rendering** so they attach.

⛔ **The endpoints are lease-gated:** every tool call is rejected unless the slot holds an ACTIVE lease
whose client matches. A connected server with no lease fails every call — acquiring is what makes a slot
usable, not a formality.

Lead flow, per task: **`slotctl acquire --slot N --client claude --base-ref main`** → **`slotctl prepare
--slot N`** (resets the slot to the base and installs a `.lake` matching the published successful-build
epoch; refuses on a dirty or unabsorbed slot, quarantining rather than discarding — **never** hand-type
`git reset --hard`/`git clean`, which the auto-mode permission classifier denies on a slot) → **dispatch**
`Agent(subagent_type="skeft-qa:lean-worker", prompt="SLOT N=2, path=<abs …/wt2>, use
mcp__skeft_wt2__*. <brick>")` → worker proves MCP-first via its own `mcp__skeft_wtN__*`, kernel-pure,
commits on `worktree-wtN` → **`slotctl ready --slot N`** then **`slotctl absorb --slot N`**, which rebases,
fast-forwards (never cherry-picks), runs the authoritative gate under an integration lock, publishes the
epoch, rewarms and releases. The slot **stays** for the next task — don't delete. **Fan out only when the
proof DAG has genuinely branched**, and only to slots `slotctl status` reports FREE.
**`/skeft-qa:reset-slot N`** remains the path for a slot driven **outside** a lease.
⚠️ Run `slotctl` from the primary checkout: it resolves its inventory and lease directory from the cwd,
so invoking it inside a slot addresses a different control plane and reports every slot FREE.

**Cost, measured.** A slot's Lean server (`lake serve` + `lean --server` + `lean --worker`) is spawned
lazily on the first tool call and costs ~4.4 GB; `release`/`absorb` reclaim it automatically, so an idle
slot costs nothing and you never need `supervisor stop` to get memory back. Peak for a full fan-out is
that per active slot — budget accordingly, and prefer two well-chosen slots over three contended ones.

⚠️ **Run `slotctl doctor` before a full fan-out.** A swarm is bounded by kernel **vnodes**, not file
descriptors — a Lean server memory-maps ~10k `.olean` files, which never appear in `ulimit -n` — and
`doctor` asserts the declared floor with a runnable remedy. The setting is runtime-only and lost on
reboot; the persistence recipe is in
[LEAN_SLOT_OPERATOR_GUIDE.md](LEAN_SLOT_OPERATOR_GUIDE.md).

⚠️ **Editing `scripts/lean_slots/*` invalidates the running endpoints.** The supervisor fingerprints the
loaded implementation, so `doctor` reports `proxy=False` while the port is still serving, and the next
`prepare` quarantines the slot. Run `supervisor stop && supervisor start` after any such edit.
Full convention: **`parallel-worktrees.md`** in the
`goal-dev` skill (`.claude/plugins/skeft-qa/skills/goal-dev/references/parallel-worktrees.md`).

---

*State lives at `<repo>/.claude/dev-harness/` (gitignored): `managed/<sid>.json` markers, `watermarks/`, `active_issues.json`, `coaching/<goal_id>.json` (the per-goal coaching block), `stall_history/<goal_id>.json` (the per-goal stall-detector observations), `blocked_questions.jsonl`, `locks/`. The standing **pre-decisions** the loop reads are tracked at `<repo>/docs/dev-loops/PRE_DECISIONS.md`; the crash-recoverable source of each goal condition is `<repo>/docs/dev-loops/<roadmap>/goal_prompt_<goal_id>.md`.*
