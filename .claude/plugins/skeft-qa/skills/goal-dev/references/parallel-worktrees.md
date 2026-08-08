# Parallel Lean development — persistent worktree slots (per-worker LSP)

Loaded on demand when a `/goal` proof program **branches into independent sub-chains** and the `lead`
wants to fan bricks out. (A tightly-coupled single-file chain stays **solo** with one fast MCP — fan out
only when the DAG has genuinely branched.)

Each brick goes to the **`lean-worker` subagent** (`skeft-qa:lean-worker`), one per **persistent worktree
slot**. Each slot has its **own** build-isolated lean-lsp server, so several workers run **fully in parallel
with zero coordination**.

| Slot | Worktree (gitignored) | Its server |
|---|---|---|
| `wt1` | `SK_EFT_Hawking/.claude/worktrees/wt1/lean` | `mcp__lean-lsp-wt1__*` |
| `wt2` | `…/wt2/lean` | `mcp__lean-lsp-wt2__*` |
| `wt3` | `…/wt3/lean` | `mcp__lean-lsp-wt3__*` |

**Why persistent static slots (not inline per-subagent MCP):** inline `mcpServers` in subagent frontmatter
**do not surface** via the Agent tool in this environment (verified empirically). Only **inherited**
`.mcp.json` servers surface to subagents, and those attach at **session start** — so the slot worktrees must
already exist when you launch. Pre-create the slots once, keep them. Disk is cheap — each slot's `.lake` is an
APFS `cp -c` clone (copy-on-write): 3 slots ≈ **~500 MB real** (`du` shows ~43 GB *logical* — COW-blind).

**One-time setup:** `scripts/setup_lean_worktree_slots.sh` creates `wt1/2/3` and COW-clones the build into
each. The `lean-lsp-wt1/2/3` servers are defined in the workspace `.mcp.json` + enabled in
`.claude/settings.local.json`. **Restart after first setup** so the servers attach.

## Lead's flow (per independent sub-chain)

1. **Reset the slot to current `main` — do this IMMEDIATELY before dispatching *this* slot's worker**, per
   task, **not as a batch up front**. If `main` advances between the reset and the dispatch (e.g. you merged
   an earlier worker), the slot's **git tree** is left behind — and the `.lake` auto-re-clone fixes the
   *build*, not the *tree*. Run **`/reset-slot N`** (or `${CLAUDE_PLUGIN_ROOT}/scripts/reset_slot.py N`):
   the **guardrail-safe**
   `git -C .claude/worktrees/wtN checkout -B worktree-wtN main`, which **refuses if the slot holds commits not
   yet on `main`** (so unmerged work is never lost — merge/cherry-pick first, then re-run).
   - ⚠️ **Do NOT reach for `git reset --hard` / `git clean`.** Those are **denied by the auto-mode permission
     classifier** on a worktree the agent didn't create this session (a Claude Code permission heuristic —
     *not* a dev-harness hook; this plugin ships no Bash guardrail). `/reset-slot` exists precisely so the
     guardrail-safe `checkout -B` is the path of least resistance.
   - `/reset-slot` **auto-re-clones the slot's `.lake`** when main's build advanced since the slot's last
     sync — an APFS copy-on-write clone of main's `lean/.lake`, **staleness-gated** on main's HEAD SHA
     (recorded at `.claude/dev-harness/slot_lake/wtN.sha`), so resetting a slot repeatedly while main is
     unchanged skips the copy. The slot's LSP therefore always matches its git tree; you don't re-clone by hand.
2. **Dispatch** `Agent(subagent_type="skeft-qa:lean-worker", prompt="SLOT N=2, path=<abs …/wt2>, use
   mcp__lean-lsp-wt2__*. <the one independent brick + its Lit-Search refs + acceptance>")`.
3. The worker proves MCP-first via **its own `mcp__lean-lsp-wtN__*`** (never write→`lake build`), kernel-pure,
   and **commits on `worktree-wtN`**. **The worker runs no builds — you do** (next section).
4. **Harvest**: **`git merge --ff-only worktree-wtN`** into `main` (ancestry-preserving) — **NOT
   `cherry-pick`**, which mints a new SHA, so the slot's original commit is content-merged but not a
   SHA-ancestor of `main`, and the next `/reset-slot`'s ancestry-based unmerged-guard then refuses to
   reset the slot. FF-merge keeps ancestry intact so `/reset-slot` works cleanly on the next cycle.
   Then re-run the full gate (`lake build SKEFTHawking.ExtractDeps`, `validate.py`). The slot stays
   for the next task (`/reset-slot`, don't delete).

Dispatch up to 3 workers concurrently (one per slot) for genuinely independent bricks.

## ⛔ Build concurrency: the LEAD owns `lake build`. Workers do not. (binding)

Slot isolation is about **correctness** — each slot has its own `.lake`, so a slot build can't corrupt
main's. It buys you nothing on **contention**: Lake defaults to one job per core, so every slot that
builds tries to take the whole machine.

Measured 2026-07-28 on a 16-core box: three workers building concurrently pushed the lead's pre-commit
hook — ~15 s solo, ~90 % user-CPU — past **10 minutes**, and the lead started backgrounding its commits
to keep moving. Nothing was broken; the machine was oversubscribed, and the cost landed squarely on the
serialized process that gates everyone. It also reads exactly like a broken toolchain, so it burns
diagnosis time before anyone suspects load.

**The contract:**
- **Workers run no builds.** Their gate is `lean_diagnostic_messages` + `lean_goal` + `lean_verify` —
  per-file, near-free, and sufficient for "does this elaborate / close / stay kernel-pure". This is
  written into `agents/lean-worker.md` as a binding rule; **say it again in the dispatch brief** if a
  worker is likely to add a module.
- **The lead runs `lake build` / `lake build SKEFTHawking.ExtractDeps` / `validate.py`** — on `main`,
  after the merge. That is the run that counts; a slot's green build proves nothing about `main`.
- **Narrow exception:** a worker adding a NEW module that another file must `import` needs an `.olean`
  first. Then, and only then: `lake build -j4 SKEFTHawking.<ThatOneModule>` — a single named module,
  never the bare target, always job-capped (3 slots × 4 of 16 cores leaves headroom for your gate and
  the LSP servers). The worker reports that it ran one.
- **Don't run your own full gate while workers are live.** Merge first, then gate, then re-dispatch.
  If you must gate mid-flight, expect it to take several times its solo cost — that is load, not
  breakage, and it is not a reason to go looking for a broken cache.

> **Maintainer caveat (do not regress):** a worker's slot commit depends on `scripts/pre-commit-sync.sh`
> detecting a worktree (`git rev-parse --git-dir` ≠ `--git-common-dir`, env-resolved so it survives the shared
> hook's `cd` to main) and **skipping** the main-oriented sync gate — the pure-bash leak-guard still runs. Do
> **not** make that gate always-run: in a worktree it stitches a cloned dependency's top-level `.github/*`
> blobs (absent from SK's object store) into the slot's commit tree → `invalid object … Error building trees`,
> blocking every slot commit.

> **Launch note:** works from **either** launch point — the workspace root (where `.mcp.json` lives) or inside
> `SK_EFT_Hawking/`. The lead manages slots with plain `git -C <slot>` (no `isolation: worktree`), so there is
> no non-git-cwd problem; the slot servers use absolute paths and serve regardless of the lead's cwd.
