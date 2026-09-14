# ADR-018 residual B1 closure re-review request

**Status:** requested; narrow independent specification gate.

**PR:** #75

**Base:** `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`

**Previously focused-reviewed head:** `8407079f935ba3dd758a4f2c288b3cd43ec5239e`

**Focused verdict:** `ACCEPT_WITH_CHANGES`; B1 `PARTIALLY_CLOSED`, B2–B6 `CLOSED`; no new blocker beyond B1.

Resolve the **current PR #75 head** immediately before review. Do not assume the SHA above is still current.

## Scope

Review only whether the new residual-B1 specification closes the remaining blocker without weakening ADR-008 lifecycle/cleanup authority. Do not reopen B2–B6 unless the new B1 closure creates a concrete regression into those already-closed surfaces.

Read:

- the durable focused re-review COMMENT on PR #75 anchored to `8407079f...`;
- `FOCUSED-REREVIEW-RECONCILIATION.md`;
- `docs/adrs/ADR-018-b1-removal-preflight-addendum.md`;
- `docs/superpowers/specs/2026-09-14-adr018-b1-removal-preflight-design.md`;
- `docs/superpowers/plans/2026-09-14-adr018-b1-removal-preflight.md`;
- parent ADR-018 D8/D9 and spec S18-2/S18-3/S18-9;
- current `scripts/lean_slots/controller.py::doctor`, `_lease_for_command`, `session_environment`, `Inventory.token`, and relevant tests as measured code.

## Falsification questions

1. Does the proposed current/prospective roster-vs-live-lease predicate actually detect the invalid migration state the focused reviewer identified?
2. Is it explicitly non-disruptive, so it cannot revoke/strand the lease or block correct-owner cleanup?
3. Is there still any path where `doctor()` can report healthy while a live lease's recorded client is absent from the roster being evaluated?
4. Is the production-seeded test non-vacuous: real lease artifact + real roster input → red, with lease bytes/state unchanged?
5. Does the cleanup sequence prove correct-owner cleanup, restart, and post-restart denial rather than treating the red report as revocation?
6. Is bearer credential cleanup ordered before admission removal so it does not depend on post-removal `session env` token processing?
7. Can a removed/re-added bearer client silently regain the old credential under the proposed tests?
8. Did the residual-B1 closure introduce any new blocker in B2–B6?

## Required result

Return exactly:

- current reviewed head/base;
- independence statement;
- residual B1: `CLOSED`, `PARTIALLY_CLOSED`, or `OPEN`;
- any regression/new blocker introduced by the B1 closure;
- final verdict: `ACCEPT`, `ACCEPT_WITH_CHANGES`, or `REJECT`;
- exact remaining change, if any.

File the complete result as a GitHub **COMMENT review** on PR #75, not `APPROVE`/`REQUEST_CHANGES`. Do not modify repository files.