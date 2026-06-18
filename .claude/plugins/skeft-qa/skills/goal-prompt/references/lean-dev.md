# Lean development reference (MCP-first)

Loaded on demand for hard Lean proof work in a `/goal` loop. (Project conventions also live
in `SK_EFT_Hawking/CLAUDE.md`; this is the in-loop quick reference. Project conventions
OVERRIDE the generic `lean4` skill where they differ.)

## The MCP-first loop (milliseconds/cycle, not the ~15s write→lake-build cycle)

1. `lean_file_outline` — orient in the file.
2. Write the statement with `sorry`; save.
3. `lean_goal` at the `sorry` — **see the actual goal** before writing tactics.
4. `lean_multi_attempt` with 4–6 candidate tactic sequences at the position — pick the winner.
5. Write the winner; repeat from 3 at the new state.
6. When `lean_goal` says **"no goals"**, drop the `sorry`; `lake build` to finalize.

## Hard rules (do NOT violate)

- **Kernel-purity is the bar.** Target axiom set `{propext, Classical.choice, Quot.sound}`.
  **No new project-local `axiom`** without explicit user sign-off (advisory DR recs are not
  sign-off). **No new `sorry` / `native_decide` regressions.** Verify with `lean_verify`.
- **No `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` in a proof body.** A
  heartbeat wall means a wrong proof architecture — **decompose into `have` sub-lemmas**
  (target ≤ 12-term sub-lemmas Aristotle/the kernel can chew). (Exception: O(project-size)
  metaprograms like `ExtractDeps.lean`.)
- **Search before prove:** `lean_local_search` first; then `lean_leansearch` / `lean_loogle`
  / `lean_leanfinder` / `lean_state_search` (rate-limited).
- **Read the deep-research directly for hard proofs.** Read the relevant
  `Lit-Search/Phase-*/` file yourself — never delegate depth-reading to a subagent
  (summaries lose load-bearing coefficient identities / sector architectures). Subagents are
  fine for breadth scans.
- **Non-commutative ring types** (`Uqsl2Aff`, `Uqsl3`, Clifford, …) are `Ring`, not
  `CommRing` — use `noncomm_ring` or manual rewrites, never `ring`/`ring_nf`.
- **`RingQuot`-based types:** when `rw` fails "did not find pattern", use `erw` (pipeline
  `rw` runs at `.reducible` where RingQuot instances aren't reducible).

## Aristotle (fallback only — Stage 4)

Use **sparingly**, only after the MCP loop is exhausted on a sorry AND the sorry is
decomposed into ≤ 12-term sector/sub-lemma targets. Aristotle runs Lean/Mathlib 4.28.0; we
run 4.29.x — compatibility differences possible. **The user gets first & last call** on
submissions (each pushes a whole-project batch, ~1-day turnaround). This is a *genuine
user-only decision* (a legitimate stop / ask-once), not an escape.

## Preemptive-strengthening (before writing each theorem statement)

Tie the statement to numerical content (falsifiable `norm_num` comparisons, not qualitative
claims); drop redundant conjuncts; back docstring cross-refs with an actual call; avoid
self-discharging tautologies (`rfl`/`decide`/identity-wrappers/within-own-±2σ bands).

## Parallel Lean development (persistent worktree slots — full parallel, per-worker LSP)

When a proof program **branches into independent sub-chains** (NOT a tightly-coupled single-file
chain — those stay solo with one fast MCP), a `lead` fans the bricks out to the **`lean-worker`
subagent** (`skeft-qa:lean-worker`, in `.claude/plugins/skeft-qa/agents/`), one per **persistent worktree slot**. Each slot has its
**own** build-isolated lean-lsp server, so several workers run **fully in parallel with zero
coordination** — exactly the point of the slots.

> ✅ **Validated end-to-end (2026-06-17):** slot-pinned isolated LSP → goal on a slot-only file →
> prove → kernel-pure (`lean_verify` axioms `[]`) → **commit** (worktree-safe hook) → ff-merge into
> `main` → guardrail-safe slot reset — all green.
> ⚠ **Maintainer caveat (do not regress):** a worker's slot commit depends on
> `scripts/pre-commit-sync.sh` detecting a worktree (`git rev-parse --git-dir` ≠ `--git-common-dir`,
> env-resolved so it survives the shared hook's `cd` to main) and **skipping** the main-oriented sync
> gate — the pure-bash leak-guard still runs. **Do NOT make that gate always-run:** in a worktree it
> stitches a cloned dependency's top-level `.github/*` blobs (absent from SK's object store) into the
> slot's commit tree → `invalid object … Error building trees`, blocking every slot commit.

| Slot | Worktree (gitignored) | Its server |
|---|---|---|
| `wt1` | `SK_EFT_Hawking/.claude/worktrees/wt1/lean` | `mcp__lean-lsp-wt1__*` |
| `wt2` | `…/wt2/lean` | `mcp__lean-lsp-wt2__*` |
| `wt3` | `…/wt3/lean` | `mcp__lean-lsp-wt3__*` |

**Why persistent static slots (and not inline per-subagent MCP):** inline `mcpServers` in subagent
frontmatter **do not surface** via the Agent tool in this environment (verified empirically — the tools
never appear). Only **inherited** `.mcp.json` servers surface to subagents, and those attach at
**session start** — so the slot worktrees must already exist when you launch. Hence: pre-create the
slots once, keep them. Disk is cheap — each slot's `.lake` is an APFS `cp -c` clone (copy-on-write):
3 slots ≈ **~500 MB real** disk (`du` shows ~43 GB *logical* — it's COW-blind).

**One-time setup:** `scripts/setup_lean_worktree_slots.sh` creates `wt1/2/3` and COW-clones the build
into each. The `lean-lsp-wt1/2/3` servers are defined in the workspace `.mcp.json` + enabled in
`.claude/settings.local.json`. **Restart after first setup** so the servers attach. (Re-run the script
to refresh a slot's clone after main's build advances.)

**Lead's flow (per independent sub-chain):**
1. **Reset the slot** to current `main`: `git -C .claude/worktrees/wtN checkout -B worktree-wtN main`
   (guardrail-safe — `git reset --hard` / `git clean` are blocked by the dev-harness guardrail by
   design). If main's build moved since the last clone, re-clone its `.lake`
   (`rm -rf …/wtN/lean/.lake && cp -c -R lean/.lake …/wtN/lean/.lake`).
2. **Dispatch** `Agent(subagent_type="skeft-qa:lean-worker", prompt="SLOT N=2, path=<abs …/wt2>, use
   mcp__lean-lsp-wt2__*. <the one independent brick + its Lit-Search refs + acceptance>")`.
3. The worker proves MCP-first via **its own `mcp__lean-lsp-wtN__*`** (never write→`lake build`),
   kernel-pure, and **commits on `worktree-wtN`**.
4. **Harvest**: merge/cherry-pick `worktree-wtN` into `main`, re-run the full gate (`lake build
   SKEFTHawking.ExtractDeps`, `validate.py`). The slot stays for the next task (reset, don't delete).

Dispatch up to 3 workers concurrently (one per slot) for genuinely independent bricks. **Fan out only
when the DAG has genuinely branched** — a tightly-coupled single-file chain is faster solo with one fast
MCP.

> **Launch note:** this works from **either** launch point — the workspace root (where `.mcp.json` lives)
> or inside `SK_EFT_Hawking/`. The lead manages the slots with plain `git -C <slot>` (no `isolation:
> worktree`), so there is no non-git-cwd problem. The slot servers use absolute paths, so they serve the
> slots regardless of the lead's cwd.
