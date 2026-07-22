# Codex guidance — SK_EFT_Hawking

Read `CLAUDE.md` and `docs/WAVE_EXECUTION_PIPELINE.md` before changing the
repository. Project correctness and verification rules in those files apply to
Codex as well as Claude Code.

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
  `docs/dev-loops/CODEX_LEAN_SLOTS.md`; the normative design is ADR-008.

## Validation

For ADR-008 infrastructure changes, run at minimum:

```bash
uv run python -m pytest tests/test_lean_slots.py -q
uv run python -m pytest tests/test_codex_lean_slot_policy.py -q
git diff --check
```

Run the broader fast suite before publishing. Lean or dependency changes still
require the full project gates in `docs/WAVE_EXECUTION_PIPELINE.md`.
