# ADR-018 residual B1 — removal-preflight implementation plan

**Status:** proposed plan supplement; implementation remains blocked on focused closure re-review.

**ADR addendum:** `docs/adrs/ADR-018-b1-removal-preflight-addendum.md`

**Design supplement:** `docs/superpowers/specs/2026-09-14-adr018-b1-removal-preflight-design.md`

## Global constraints

- extend ADR-008/ADR-018; do not add another lease/revocation state machine;
- the mismatch check is observational and must never mutate an issued lease;
- existing owner-gated cleanup remains legal even while doctor reports a roster/lease mismatch;
- bearer cleanup is pre-edit; trusted-local has no token cleanup step;
- implementation stays blocked until a fresh independent reviewer closes residual B1.

## Task B1.1 — one lease/client roster predicate

**Files:** `scripts/lean_slots/controller.py` and/or `scripts/lean_slots/state.py`, `tests/test_lean_slots.py`.

Implement one pure/read-only helper used by both ordinary health and prospective removal preflight. It compares each live lease's recorded `client` with an admitted-client set and returns structured mismatch evidence.

Do not wire the predicate into `_lease_for_command()` or any lifecycle mutation path.

## Task B1.2 — doctor reports current-roster mismatch

**Files:** `scripts/lean_slots/controller.py`, `tests/test_lean_slots.py`.

Extend the existing `wtN.lease`/adjacent health reporting so a non-`QUARANTINED` lease is not automatically healthy when its recorded client is absent from the current inventory roster.

The diagnostic must make the distinction clear:

- lease exists and is lifecycle-valid;
- migration/admission health is red;
- owner cleanup remains required/allowed.

### Non-vacuity

Seed a real lease artifact for a known-present client, then alter the production-shaped inventory roster the doctor reads. Assert doctor red and assert lease content/state is unchanged.

## Task B1.3 — prospective removal preflight

Expose the same predicate against the proposed roster before removal is treated as safe. Prefer a pure controller/CLI check over a persistent new mechanism.

Acceptance:

- prospective roster excluding client with live lease → red/refuse-to-declare-safe;
- same prospective roster after legitimate owner cleanup → green;
- no lease mutation by preflight.

## Task B1.4 — bearer cleanup ordering

Define the concrete existing/new narrow operation for deleting or rotating a client's bearer credential while it is still admitted and quiescent.

Tests must prove:

- post-removal `session env --client removed` is not needed for cleanup;
- old credential cannot authenticate after later re-admission;
- trusted-local mode skips credential cleanup without weakening roster/restart checks.

Never print real bearer token values in durable output.

## Task B1.5 — operator and ADR-008 documentation

Fold the accepted D13/D14 / S18-14..16 semantics into the shipping update to:

- ADR-018 canonical text;
- ADR-008 client/removal wording where affected;
- `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md`.

The operator sequence must say: quiesce/check → credential cleanup if bearer → roster edit → supervisor restart → doctor/negative verification.

## Task B1.6 — focused implementation review evidence

The later independent implementation reviewer must receive evidence for:

- production-seeded doctor red;
- no lease mutation;
- correct-owner cleanup success / wrong-owner failure;
- stale-proxy vs restarted-proxy distinction;
- bearer old-credential non-reuse;
- Codex/Claude regression controls.

## Current gate

No Phase-1 ADR-018 runtime code work begins until a fresh independent reviewer returns `ACCEPT` for this residual-B1 supplement, or an `ACCEPT_WITH_CHANGES` with no unresolved blocker. This supplement itself is specification work only.