# Codex continuity rehearsal evidence

Date: 2026-09-08. Scope: explicit local assignment and interrupted-reader recovery. This record is not a merged-wave or full-tree certification; branch and PR review remain separate from the evidence below.

## Completed checks

- Existing `scripts/orchestrate.py --json` ran against the current corpus and returned dispatch/queued groups. Its slot suggestions were not treated as leases. Read-only `slotctl status --json` showed no active lease; no lease or build was started.
- `tests/test_codex_continuity.py`, `tests/test_orchestrate.py`, and `tests/test_codex_lean_slot_policy.py`: 64 tests passed together. The continuity portion contains 23 tests, including actual-file mutations, linked worktrees, missing inputs, dirty bytes, ignored assigned files, additive policy references and output protection.
- Downstream slot-policy tests: 9 passed. Worker TOML parsed and diff whitespace checks passed.
- Public real-source packet creation/check passed. A downstream real-source packet including explicit upstream policy references also passed. Packet content remains ignored and machine-local.
- Independent implementation review reproduced and verified repair of ignored-owned-file false freshness. It also independently verified mandatory base-policy retention and external policy invalidation. No blocking issue remained for this explicit mechanism.

## Real-agent interruption and review-return rehearsal

1. A new agent with no inherited conversation received the real local R1 packet. It ran the check (fresh), read the governing records and correctly identified root as notebook writer and the packet as non-authorizing context.
2. Root interrupted that running agent through the agent lifecycle tool.
3. Root changed the actual ignored notebook index to add a review-return requirement. The production adapter rejected R1 with `changed=[notebook]`.
4. On resumption, the agent reran the check before continuing, rejected R1, reported the new requirement and declined to refresh its own assignment.
5. Root reconciled the change and issued R2. The agent checked R2 successfully and returned evidence distinguishing explicit interrupted-reader recovery from untested native event delivery.

This exercised a real agent and real adapter inputs. The inserted requirement was a rehearsal review return, not a substantive scientific review or paper closure. No findings were falsely closed to demonstrate the loop. Later documentation edits appropriately make old packets stale; historical successful checks refer to their measured candidate, not the current tree.

## Acceptance boundary

Explicit handoff, stale-input rejection and deliberate reissue are demonstrated. Native desktop compaction-hook delivery, automatic reinjection and unattended recovery are NOT demonstrated. No exposed tool in this session can force a native desktop compaction event. A simulated event or separate CLI process would not establish delivery in this desktop session. Worker source definitions were updated; no runtime reload is claimed.

Broad autonomous scientific swarming remains gated on actual runtime continuity evidence and final integration. This increment introduces no new scheduler, task-status database, closure writer, slot or Claude configuration change. Broader harvesting and nested management remain separately scoped.

## Controller admission follow-up — 2026-09-09

The slot test fixture now removes inherited client session identities before each test selects its own identity. This preserves the explicit precedence and different-owner assertions without changing production ownership semantics. Independent review found no blocking issue in the four-line repair. Controller plus Codex policy tests passed (103); a controller rerun with conflicting inherited identities passed (87). Process inspection and local socket tests require execution outside the restricted shell sandbox; five sandbox-only failures passed there. Generated Codex configuration was refreshed after verifying its only difference was the source digest. This does not prove runtime attachment or Lean slot admission.
