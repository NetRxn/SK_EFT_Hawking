# Codex guidance — SK_EFT_Hawking

Read `CLAUDE.md` and `docs/WAVE_EXECUTION_PIPELINE.md` before changing the
repository. Project correctness and verification rules in those files apply to
Codex as well as Claude Code.

## Codex instruction scope and autonomy

Apply the shared scientific, review and documentation contracts in CLAUDE.md. Its Claude-specific session trimming, slash commands, plugin lifecycle and Stop-hook behavior are not Codex procedures. Codex runtime and slot authority follow this file and ADR-008; do not stop shared processes based on legacy session instructions. Claude migration remains Claude-owned.

Carry authorized work through implementation, appropriate verification and its stated acceptance boundary. Resolve routine choices using the current task and repository evidence; request input only when it materially changes the outcome or authorization. Do not infer a new approval requirement from an ambiguous guideline. Continue independent work while a genuine decision is pending.

Use the existing planner for finding-driven work. Delegate coherent independent packages when allowed by the active runtime and useful for quality or elapsed time; the lead chooses the execution graph within current capacity and ownership limits. No repository instruction expands runtime permissions or agent capacity.

Run required gates for the actual change. Broaden or repeat checks when changes, failures or unresolved concerns justify it; a scoped test result is not full-tree or publication acceptance. Preserve independent review and scientific correctness requirements.

## ADR-008 Lean slots

- `wt1`, `wt2`, and `wt3` are the only parallel Lean capacity slots. Do not
  create Codex-only `wt4`–`wt6` worktrees.
- The primary, non-worktree orchestrator acquires and prepares a slot with
  `python3 scripts/slotctl.py ...` before spawning a `lean_wtN_worker`.
- A worker edits only its assigned worktree, uses only its matching
  `skeft_wtN` MCP server, commits its assigned paths, and reports the commit.
- Workers never run `lake build`, `lake clean`, `lean_build`, dependency/cache
  repair, integration commands, or raw Git plumbing. The orchestrator owns
  absorption and authoritative builds through `slotctl`.
- Never reset or reclaim a dirty slot. A controller quarantine is a stop signal,
  not permission to clean the worktree.
- The operator workflow and activation commands are in
  `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md`; the normative design is ADR-008.

## Validation

For ADR-008 infrastructure changes, run at minimum:

```bash
uv run python -m pytest tests/test_lean_slots.py -q
uv run python -m pytest tests/test_codex_lean_slot_policy.py -q
git diff --check
```

Run the broader fast suite before publishing. Lean or dependency changes still
require the full project gates in `docs/WAVE_EXECUTION_PIPELINE.md`.

## Dispatch and recovery continuity

Use [the Codex continuity contract](docs/dev-loops/CODEX_CONTINUITY.md) before dispatch and after interruption or compaction. Each assignment names its task/parent, scope, primary-checkout notebook path and writer, roadmap, candidate state and acceptance evidence. Workers read notebooks and report; they do not write the lead's notebook. A handoff snapshot never grants a lease or certifies completion. Reconcile changed source or authority before continuing. Use the existing remediation planner; do not create a second routing ledger.
