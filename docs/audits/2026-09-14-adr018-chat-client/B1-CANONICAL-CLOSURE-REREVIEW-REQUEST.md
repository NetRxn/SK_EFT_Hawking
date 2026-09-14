# ADR-018 final residual B1 canonical-consistency re-review request

**Status:** requested; final narrow specification gate before runtime implementation.

**PR:** #75

**Base:** `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`

**Prior cloud-reviewed head:** `0e71346775028daa09eb90006be6c85c458b5388`

**Prior cloud verdict:** `ACCEPT_WITH_CHANGES`; substantive mismatch/preflight design accepted, B2–B6 remained closed; residual B1 was only the canonical D8/S18-9 bearer-cleanup contradiction plus deferred concrete credential operation.

Resolve the **current PR #75 head** immediately before review. Do not assume a head SHA from this file remains current.

## Scope

This is intentionally narrower than the prior B1 closure review. Determine only whether the current canonical architecture package now expresses one executable removal procedure and whether that edit regresses any already-closed B2–B6 boundary.

Do not reopen the accepted D13/S18-14 mismatch-preflight mechanism unless the canonical reconciliation creates a concrete contradiction with it.

## Read

- the cloud-dispatched residual-B1 COMMENT review(s) on PR #75 anchored to `0e713467...`;
- current parent ADR-018 D8 and Review gate;
- current parent spec S18-9, §3 file ownership, §5.2/§5.3 verification, and §7 review reconciliation;
- `docs/superpowers/plans/2026-09-14-adr018-b1-removal-preflight.md` Task B1.4;
- D13/D14 supporting addendum and S18-14..16 supporting supplement only to confirm no contradiction remains;
- current measured `Inventory.client_token_path`, `Inventory.token`, controller lease lookup/doctor/session-environment behavior, and CLI session command surface.

## Exact falsification questions

1. Do canonical ADR D8 and parent spec S18-9 now state the same order:
   `quiesce + removal-preflight → bearer credential revocation while still admitted → allowed_clients edit → supervisor restart → doctor + controller/proxy denial verification`?
2. Is the concrete operation fully specified as `slotctl session revoke-token --client <client>` rather than left to implementation choice?
3. Are its semantics sufficient to implement safely: bearer-only, still-admitted client, no live client lease, exact `Inventory.client_token_path(client)`, idempotent absent-file behavior, no token output, no caller-supplied path?
4. Does this preserve correct-owner ADR-008 lease cleanup and keep the mismatch predicate observational rather than making lifecycle commands roster-sensitive?
5. Does the later re-admission verification actually prove the pre-removal bearer credential cannot authenticate?
6. Do the supporting addendum/spec/plan agree with the canonical parent, with an explicit precedence rule if needed?
7. Did the canonical reconciliation create any concrete regression into B2–B6?

## Required result

Return and durably file:

- current reviewed head/base;
- independence statement;
- residual B1: exactly `CLOSED`, `PARTIALLY_CLOSED`, or `OPEN`;
- B2–B6 regression sweep;
- final verdict: exactly `ACCEPT`, `ACCEPT_WITH_CHANGES`, or `REJECT`;
- exact remaining change, if any.

File as a GitHub **COMMENT review** on PR #75. Do not use GitHub `APPROVE` or `REQUEST_CHANGES`; review evidence is not implementation/merge authorization. Do not modify repository files or execute live slots.