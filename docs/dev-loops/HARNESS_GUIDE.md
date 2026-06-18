# Dev-Harness Operator's Guide (skeft-qa)

**Audience:** you (the human driving the loop) and any future session that needs to *use* the harness rather than build it. This is the forward-facing "how do I actually run this" manual. The design rationale lives in the harness design spec (kept on the private design side); this guide is operations only. (A private sibling plugin mirrors this same model for the private repo and has its own guide there; everything below is the public `skeft-qa` side.)

> **TL;DR**
> 1. **Launch Claude Code from inside `SK_EFT_Hawking/`** (the normal case — a standalone clone of this repo). The plugin resolves its repo from your cwd, so it Just Works. *(If you run the optional multi-repo setup where lean-lsp's `.mcp.json` sits at a workspace root one level up, launch from that root instead so lean-lsp loads — the harness resolves `SK_EFT_Hawking` from there too. Either launch point is fine.)*
> 2. Arm a loop: **`/skeft-qa:goal-prompt <what the loop should achieve>`**. It prints a `/goal <condition>` — paste that to start the native loop.
> 3. The harness re-grounds the loop after every compaction and intercepts blocking questions automatically. You're hands-off until the goal is met.

---

## 1. What the harness is

`skeft-qa` is a Claude Code plugin that keeps a long-running autonomous **native `/goal`** loop on-track across compactions, without competing with `/goal` itself. (A private sibling plugin mirrors the same model for the private repo — lighter wrappers, documented on the private side.)

It ships **exactly two CC hooks** (both default-inert + fail-open, gated on a per-session marker):
- `SessionStart` — after every compaction/resume, re-injects the settled `/goal` condition + "re-read CLAUDE.md" + active System-2 issues + decision heuristics.
- `PreToolUse(AskUserQuestion)` — when the loop tries to block on a question (and you're not there), it denies + redirects with the same re-orientation payload, so the loop keeps moving instead of stalling.

Plus skills you invoke, a mechanical-sync layer, and an off-hot-loop System-2 "what went well/poorly about HOW the loop ran" harvest.

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
   The skill: composes a ≤4,000-char `/goal` condition (self-describing, with transcript-visible acceptance criteria incl. a zero-BLOCKER fresh-context review), **writes the session marker** to `<repo>/.claude/dev-harness/managed/<session_id>.json`, **facilitates the one-time harvest host**, prints **PASS/FAIL** that the marker armed, and prints the composed condition.
2. **Start the native loop** — paste the printed condition:
   ```
   /goal <the condition it printed>
   ```
   (The assistant can't set `/goal` for you — that's a native command.)
3. **Walk away.** The loop ships increments; after each compaction the SessionStart hook re-grounds it on the settled scope; blocking questions are intercepted and redirected. It ends only when the goal's acceptance criteria are met (or you `/clear`).

`role=lead` vs `role=solo`: pass `role=lead` only if you're orchestrating an agent team; default `solo`. (Descriptive metadata — the harness behaves identically either way.)

---

## 4. Slash-command reference (`/skeft-qa:<name>`)

| Command | Who invokes | What it does |
|---|---|---|
| **goal-prompt** | you (user-only) | The unified goal-mode skill. Composes the `/goal` condition + arms the marker + facilitates the harvest host. Its ≤5k core also **re-attaches after every compaction** (the durable anti-drift posture). |
| **goal-guard `<on\|off>`** | you (user-only) | Toggle the AskUserQuestion guard. **off** = let the loop ask you a question; **on** = resume autonomous redirect. Default on in goal mode. |
| **orient** | you | A ≤200-word compass from the marker + roadmap/notebook: Goal / Done / Next / Guardrails. |
| **sync** | you **or** the loop | Run the mechanical Stage-12 sync (counts/tables/deps/citation cache) in one command. Idempotent, regen-lock-serialized. |
| **wave-close `<wave-id>`** | you **or** the loop | Deterministic per-wave close: gate prereqs → dispatch the fresh-context adversarial review (zero BLOCKERs) → write `<wave>_close.md`. The loop runs this itself to satisfy its acceptance criteria. |
| **harvest** | scheduled task / second-terminal `/loop` — **never the goal session** | Off-hot-loop System-2 harvest (Haiku extract → Opus consolidate) of process/harness lessons. Self-aborts if run inside a managed loop. |
| **debrief** | you (user-only) | Interactively promote System-2 `agent-reviewed` findings → `human-reviewed`, triage GAP-A gate proposals. |

---

## 5. The System-2 harvest host (one-time setup)

The harvest reads finished/running loop transcripts off the hot loop and records process lessons into `docs/dev-loops/SYSTEM2_REGISTER.md`. `goal-prompt` facilitates it, but a skill **cannot** silently spawn a standing background process — you complete the host **once**:

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
- **Self-improving, never self-mutating:** findings are tagged by review tier and *proposed*; the agent never edits CLAUDE.md / roadmaps / hooks / gates on the fly.
- **Runs under the project's Python 3.14, from any cwd.** Harness scripts are invoked with **`uv run --no-sync python`** (which yields the uv-managed 3.14 even at the workspace root, via an ephemeral interpreter), **never bare `python3`** (that's the system 3.9.x). Repo *resolution* and *stdlib* helpers run from any cwd; *project-dependency* scripts (`validate.py`, `system2_register`→`src.core`, `update_counts`, `lake`) `cd` into the repo first so `uv` gives them the repo's deps/pythonpath. **Maintainers: keep `uv run --no-sync python`; do not switch to bare `python3`, and do not add a workspace-root uv project — the project scripts need *each repo's own* env, which a root project can't supply.**
- **The transcript path is captured deterministically, never guessed.** At arm time `goal-prompt` records the loop's transcript (`jsonl_path` in the marker) via `harness_common_cli.py jsonl-path ${CLAUDE_SESSION_ID}`. The **session id is not invented or predicted** — it's the real current id Claude Code supplies as `${CLAUDE_SESSION_ID}`, which is exactly the basename CC names the transcript by. Only the *path around that id* is assembled, and it's fully determined by the id + the cwd: `~/.claude/projects/<cwd-slug>/<sid>.jsonl` (slug = the cwd with every non-alphanumeric → `-`, CC's own encoding). The resolver returns an existing file if one is on disk (e.g. a resumed session), else the reconstructed path — so it works on a **first-turn arm**, when CC hasn't flushed the `.jsonl` yet (the harvest reads it later, by which point CC has written it to exactly that path). If `${CLAUDE_SESSION_ID}` is empty it returns `""` and `goal-prompt` STOPs rather than arm a marker pointing at the wrong/no transcript — it can never resolve a *different* session's file.

---

## 9. Parallel Lean apparatus (worktree fan-out)

For a `lead` orchestrating **independent** Lean sub-chains across subagents, the workspace
`.mcp.json` pre-defines three fixed worktree-slot MCP servers — `lean-lsp-wt1/2/3` — each a fast
(`--repl`) lean-lsp pinned to `SK_EFT_Hawking/.claude/worktrees/wt{1,2,3}/lean` (enabled in the
workspace `.claude/settings.local.json`; **a session restart loads them**). The server↔worktree
binding is **by the fixed name**: create the slot as `wtN` (`git worktree add .claude/worktrees/wt1
-b worktree-wt1`, or `EnterWorktree name=wt1`) and seed its Lean build (`lake exe cache get` +
`lake build` in the slot's `lean/`, or `.worktreeinclude` to copy `.lake`) before dispatching a
subagent there. A slot whose worktree doesn't exist yet just fails to connect, harmlessly. Don't
use `Agent isolation: worktree` for a slot — its random name matches no static server.
`SK_EFT_Hawking/.claude/worktrees/` is gitignored.

Dispatch each Lean subagent into one slot and tell it to use the **`lean4` skill + the matching
`mcp__lean-lsp-wtN__*` tools** (the MCP-first loop), **not** write→`lake build` cycles; stage its
own paths only; never push. **Fan out only when the proof DAG has genuinely branched** — a
tightly-coupled single-file chain is faster solo with one fast MCP. Full convention (slot table +
subagent contract): the **Parallel Lean development** section of
`.claude/plugins/skeft-qa/skills/goal-prompt/references/lean-dev.md`.

---

*State lives at `<repo>/.claude/dev-harness/` (gitignored): `managed/<sid>.json` markers, `watermarks/`, `active_issues.json`, `blocked_questions.jsonl`, `locks/`. The tracked, crash-recoverable source of each goal condition is `<repo>/docs/dev-loops/<roadmap>/goal_prompt_<goal_id>.md`.*
