---
description: Lab-notebook lifecycle ops for a /goal loop — new (bootstrap a correct active notebook + INDEX), sync (refresh the mechanical INDEX scaffold + flag staleness), shard (self-level the active shard under the ~25k-token budget), roll (freeze the whole active shard at a wave boundary / blob escape), check (read-only sizes + warnings). Auto-resolves the loop's notebook home from the marker if you omit it.
argument-hint: <new|sync|shard|roll|check> [home]
allowed-tools: Bash(uv run *)
---
<!-- A COMMAND (model-invocable, like reset-slot) so the autonomous lead can maintain the lab
     notebook from any context without loading the goal-dev skill. The deterministic logic lives in
     scripts/notebook_lib.py (unit-tested, stdlib-only, idempotent). The two-layer model + per-brick
     discipline are in goal-dev/references/lab-notebook.md. "<25k automatically" = `sync`/`shard`
     self-level on invoke; a read-only `check` also runs in SessionStart re-injection + the pre-commit
     gate so oversize/stale can't go silent. No hook ever mutates the notebook (self-improving, never
     self-mutating). If [home] is omitted it is resolved from the active marker's notebook_path. -->

Run the lab-notebook op `$ARGUMENTS`:

`` !`uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/notebook_lib.py" $ARGUMENTS --repo "$(uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" repo-root 2>/dev/null)" 2>&1` ``

Report the result. Ops:
- **`new [home]`** — bootstrap-if-missing: creates a correct active `LAB_NOTEBOOK.md` **and** `LAB_NOTEBOOK_INDEX.md` (FRONTIER / DELIVERABLES CHECKLIST / DECISIONS & DEAD-ENDS / SHARD INDEX). Idempotent — never clobbers existing files. (`goal-prompt` calls this at arm; you rarely call it by hand.)
- **`sync [home]`** — refresh the mechanical INDEX scaffold (shard rows; insert a missing DECISIONS block — the migration for pre-two-layer indexes) and flag FRONTIER staleness vs git HEAD. Does **not** write FRONTIER/CHECKLIST/DECISIONS prose — that judgement content is yours.
- **`shard [home]`** — if the active shard is over the token budget, roll its **oldest** sections into a new `LAB_NOTEBOOK_W<n>.md` until it is under budget (keeps recent bricks in the active shard). Needs the notebook to be headed per-brick (`##`/`###`); if it's one un-headed blob, it tells you to head the entry or use `roll`.
- **`roll [home]`** — freeze the **entire** active shard into a new `W<n>` and start a fresh active. Use at a clean wave boundary, or to escape a too-big un-headed active (the INDEX FRONTIER carries current state, so a fresh active is fine).
- **`check [home]`** — read-only: active/INDEX sizes, over-budget?, missing DECISIONS block?, FRONTIER stale vs HEAD? (advisory; never mutates).

Full model + per-brick discipline: `goal-dev/references/lab-notebook.md`.
