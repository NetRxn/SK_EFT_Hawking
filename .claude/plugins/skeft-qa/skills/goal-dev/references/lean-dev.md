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

## Parallel Lean development (fan-out to worktree slots)

When the proof DAG branches into **independent sub-chains**, the `lead` fans bricks out to the
`skeft-qa:lean-worker` subagent, one per persistent worktree slot (`wt1/2/3`), each with its own
build-isolated `mcp__lean-lsp-wtN__*` server. **Reset a slot with `/reset-slot N`** (guardrail-safe
`checkout -B`; never `git reset --hard` — that's denied by the auto-mode classifier). Full flow,
the maintainer caveat, and why the slots are persistent: **see `parallel-worktrees.md`**.
