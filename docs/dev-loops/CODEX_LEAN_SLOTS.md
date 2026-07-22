# Codex Lean-slot operator guide

ADR-008 defines the normative design. This guide covers the Codex-first public
activation. Claude Code remains on its legacy configuration until the deferred
live-validation phase.

## One-time activation

From the primary `SK_EFT_Hawking` checkout:

```bash
eval "$(python3 scripts/slotctl.py session env --client codex --rotate-token)"
python3 scripts/slotctl.py config render --scope both
python3 scripts/slotctl.py supervisor start
python3 scripts/slotctl.py doctor
```

Run the `session env` command in the shell that will launch Codex. It stores the
credential outside Git and exports it as `LEAN_SLOT_CODEX_TOKEN`; generated
configuration refers to that environment variable and never embeds the token.
`--rotate-token` is for a coordinated first activation or restart: omit it when
joining an already-running installation, because rotation intentionally expires
the bearer value held by existing Codex processes.
`config render` creates gitignored Codex configuration in this repository and
the workspace root. It refuses to overwrite a locally modified generated file
unless `--force` is explicit.

Restart Codex after the first render so the HTTP MCP endpoints and the
`lean_wt1_worker`–`lean_wt3_worker` agent profiles load.

## Per-task orchestrator flow

```bash
# Reset/prepare immediately before dispatch. Choose a clean, available slot.
python3 scripts/slotctl.py acquire --slot 2 --client codex --base-ref main
python3 scripts/slotctl.py prepare --slot 2

# Spawn lean_wt2_worker with its exact absolute worktree path and one bounded task.
# For work exceeding 15 minutes, the orchestrator refreshes the heartbeat:
python3 scripts/slotctl.py heartbeat --slot 2

# After the worker commits and reports success:
python3 scripts/slotctl.py ready --slot 2
python3 scripts/slotctl.py absorb --slot 2
```

`absorb` is the serialized integration path: ancestry audit, orchestrator-only
rebase when required, fast-forward, authoritative build, successful-build epoch
publication, cache rewarm, and release. It quarantines rather than discards work
on any unexpected state.

For a no-change task, use `release` after confirming the worktree is clean and
has no unabsorbed commits:

```bash
python3 scripts/slotctl.py release --slot 2
```

An explicitly resolved quarantine may also be released by its owning session
after the worktree is clean and its HEAD is already contained in the base. The
controller never resets or deletes quarantined work.

## Recovery and diagnostics

```bash
python3 scripts/slotctl.py status
python3 scripts/slotctl.py status --json
python3 scripts/slotctl.py doctor
python3 scripts/slotctl.py reclaim --slot 2
python3 scripts/slotctl.py supervisor status
```

Heartbeat expiry or a dead owner never authorizes deleting work. Dirty files or
unabsorbed commits move the slot to `QUARANTINED`; resolve them deliberately in
the named worktree and rerun diagnostics.

Codex leases use a hash of `CODEX_THREAD_ID`; leases launched from a normal
terminal may instead use a verified parent PID. Reclaiming a stale Codex-session
lease also requires `--confirm-owner-gone`, after the operator verifies that the
recorded session has ended. The 15-minute heartbeat threshold still applies.

The shared runtime state defaults to `<workspace>/.lean-slots/` and may be
overridden for tests or alternate layouts with `LEAN_SLOT_STATE_DIR`.
