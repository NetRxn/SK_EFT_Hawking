# Codex Lean-slot operator guide

ADR-008 defines the normative design. This guide covers the Codex-first public
activation. Claude Code remains on its legacy configuration until the deferred
live-validation phase.

## One-time activation

From the primary `SK_EFT_Hawking` checkout:

```bash
python3 scripts/slotctl.py config render --scope both
python3 scripts/slotctl.py supervisor start
python3 scripts/slotctl.py doctor
```

The active workstation inventory uses `server.client_auth = "trusted-local"`:
the MCP front doors bind only to `127.0.0.1`, so normal Codex launches need no
token or shell bootstrap. Lease state, repository/worktree/endpoint identity,
the no-build policy, and the global backend limit remain enforced.

Bearer authentication is banked for a future shared-user deployment. To use it,
select `server.client_auth = "bearer"` in that deployment's inventory, render
configuration, and run `eval "$(python3 scripts/slotctl.py session env --client
codex --rotate-token)"` in the shell that launches Codex. Token rotation is
invalid in trusted-local mode and must never occur while leases are active.
`config render` creates gitignored Codex configuration in this repository and
the workspace root. It refuses to overwrite a locally modified generated file
unless `--force` is explicit.

Changing `server.client_auth` requires a front-door restart so existing proxy
processes load the new mode: run `slotctl.py supervisor stop`, then `supervisor
start`. The supervisor fingerprints the loaded proxy code and inventory; a plain
`supervisor start` fails closed rather than silently reusing stale policy.

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
