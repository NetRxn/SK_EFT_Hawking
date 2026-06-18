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

## Parallel Lean development (worktree fan-out — a `lead` orchestrating Lean subagents)

When a proof program **branches into independent sub-chains** (NOT a tightly-coupled single-file
chain — those stay solo with one fast MCP), a `lead` fans the bricks out to the **`lean-worker`
subagent** (`.claude/agents/lean-worker.md`). Each `lean-worker`:
- runs in its **own git worktree** (`isolation: worktree`) — file-isolated from every other worker;
- carries its **own inline `lean-lsp-worker` MCP server** (frontmatter `mcpServers`), pinned to *its*
  worktree via the relative `--lean-project-path lean` (resolved against the worker's cwd — verified);
- connects that server **when the subagent starts** — so it works for worktrees created *mid-session*,
  with **no restart**. This is the fix for the static-`.mcp.json` gotcha (those servers only attach at
  session start, so they can't serve a worktree spun up mid-loop — see the note below).

**Why a dedicated agent, not `.mcp.json` slots:** inline subagent `mcpServers` connect at *subagent*
start (not session start) and are honored for **project-level** agents (`.claude/agents/`) — they are
**ignored for plugin agents**, which is why `lean-worker` lives in the repo's `.claude/agents/`, not in
`skeft-qa`. Requirements (already wired): `worktree.baseRef: "head"` in `.claude/settings.local.json`
(this repo has a stale `origin/HEAD`; without it the worktree branches from the wrong base), and the
agent file must be **loaded at session start** (agent defs are startup-scanned — a freshly-added one
isn't dispatchable until the next launch).

**Lead's flow (per independent sub-chain):**
1. **Dispatch** `Agent(subagent_type="lean-worker", prompt="<the one independent brick + its
   Lit-Search refs + acceptance>")`. The worktree + the worker's `lean-lsp-worker` server are created
   for you.
2. The worker **seeds its build** (`cp -c` APFS-clones the main tree's `lean/.lake` → instant,
   copy-on-write isolated), **self-checks** its MCP is pinned to its own worktree, then proves
   MCP-first (lean4 skill + `mcp__lean-lsp-worker__*`, never write→`lake build`), kernel-pure, and
   **commits on its worktree branch**.
3. **Harvest**: the worktree persists because it has commits — merge/cherry-pick the branch into `main`,
   re-run the full gate (`lake build SKEFTHawking.ExtractDeps`, `validate.py`), then `git worktree
   remove` the branch. (A worker that made *no* commits auto-cleans.)

**Fan out only when the DAG has genuinely branched** (independent files / sub-lemmas). A tightly-coupled
chain (each brick depends on the prior, one file) is faster solo with one fast MCP — fanning it out just
serializes through the dependency with extra coordination cost.

> ⚠ **Do not revert to static `.mcp.json` `lean-lsp-wtN` slot servers for goal-mode fan-out.** They
> attach only at *session* start, so a worktree created mid-loop never surfaces its tools (no
> hot-reload) — the showstopper this `lean-worker` design fixes. (Static slots only work if you
> pre-create + pre-seed persistent `wt1/2/3` *before* launching, which doesn't fit spin-up/tear-down.)
