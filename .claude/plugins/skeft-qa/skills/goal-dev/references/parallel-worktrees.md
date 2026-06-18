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
   *build*, not the *tree*. Run **`/reset-slot N`** (or `scripts/reset_slot.py N`): the **guardrail-safe**
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
   and **commits on `worktree-wtN`**.
4. **Harvest**: merge / cherry-pick `worktree-wtN` into `main`, re-run the full gate (`lake build
   SKEFTHawking.ExtractDeps`, `validate.py`). The slot stays for the next task (`/reset-slot`, don't delete).

Dispatch up to 3 workers concurrently (one per slot) for genuinely independent bricks.

> **Maintainer caveat (do not regress):** a worker's slot commit depends on `scripts/pre-commit-sync.sh`
> detecting a worktree (`git rev-parse --git-dir` ≠ `--git-common-dir`, env-resolved so it survives the shared
> hook's `cd` to main) and **skipping** the main-oriented sync gate — the pure-bash leak-guard still runs. Do
> **not** make that gate always-run: in a worktree it stitches a cloned dependency's top-level `.github/*`
> blobs (absent from SK's object store) into the slot's commit tree → `invalid object … Error building trees`,
> blocking every slot commit.

> **Launch note:** works from **either** launch point — the workspace root (where `.mcp.json` lives) or inside
> `SK_EFT_Hawking/`. The lead manages slots with plain `git -C <slot>` (no `isolation: worktree`), so there is
> no non-git-cwd problem; the slot servers use absolute paths and serve regardless of the lead's cwd.
