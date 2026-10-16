# ADR-018 residual B1 — removal-preflight implementation plan

**Status:** proposed plan supplement; substantive B1 mechanism is reconciled, but implementation remains blocked on one narrow fresh closure re-review of the canonical ADR/spec/plan sequence.

**ADR addendum:** `docs/adrs/ADR-018-b1-removal-preflight-addendum.md`

**Design supplement:** `docs/superpowers/specs/2026-09-14-adr018-b1-removal-preflight-design.md`

## Global constraints

- extend ADR-008/ADR-018; do not add another lease/revocation state machine;
- the mismatch check is observational and must never mutate an issued lease;
- existing owner-gated cleanup remains legal even while doctor reports a roster/lease mismatch;
- bearer cleanup is pre-edit; trusted-local has no token cleanup step;
- canonical parent ADR-018 D8 and parent spec S18-9 now own the removal order and override older reconciliation prose if it differs;
- implementation stays blocked until a fresh independent reviewer closes residual B1 at the current head.

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

## Task B1.4 — exact bearer credential revocation operation

**Files:** `scripts/lean_slots/controller.py`, `scripts/lean_slots/cli.py`, `scripts/lean_slots/state.py` only for the existing exact token-path primitive if needed, plus `tests/test_lean_slots.py` and operator docs.

Implement the canonical project-owned command:

```text
slotctl session revoke-token --client <client>
```

Semantics:

- valid only when `server.client_auth == "bearer"`;
- require `<client>` is still in `Inventory.allowed_clients`;
- fail closed if any live lease records `<client>`;
- resolve exactly `Inventory.client_token_path(client)`; never accept a filesystem path from the caller;
- unlink that token file if it exists;
- be idempotent when it is already absent;
- never print or persist the token value;
- return only nonsecret structured evidence such as client, bearer mode, prior-token-present, and revoked status.

Trusted-local removal skips this operation because there is no bearer credential state.

Canonical operator ordering is now fixed:

`quiesce + removal-preflight → bearer revoke-token while still admitted → allowed_clients edit → supervisor restart → doctor + controller/proxy denial verification`.

Tests must prove:

- post-removal `session env --client removed` is not needed for cleanup;
- command rejects non-bearer mode and a client with a live lease;
- command cannot target an arbitrary path;
- no token bytes appear in output;
- later re-admission causes fresh token state and the pre-removal credential cannot authenticate;
- trusted-local mode skips credential cleanup without weakening roster/restart checks.

## Task B1.5 — operator and ADR-008 documentation

Fold the accepted mismatch/preflight + exact bearer revoke semantics into the shipping update to:

- ADR-018 canonical text;
- ADR-008 client/removal wording where affected;
- `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md`.

The operator sequence must match the canonical order above exactly.

## Task B1.6 — focused implementation review evidence

The later independent implementation reviewer must receive evidence for:

- production-seeded doctor red;
- no lease mutation;
- correct-owner cleanup success / wrong-owner failure;
- stale-proxy vs restarted-proxy distinction;
- exact pre-edit bearer revoke-token semantics;
- bearer old-credential non-reuse;
- Codex/Claude regression controls.

## Current gate

The cloud-dispatched B1 closure review against `0e71346775028daa09eb90006be6c85c458b5388` returned `ACCEPT_WITH_CHANGES`: the substantive D13/S18-14 mismatch design was accepted, but canonical D8/S18-9 still contradicted the pre-edit bearer cleanup rule and the concrete operation remained deferred.

Those two residuals are now reconciled in the canonical ADR/spec and this plan. No Phase-1 ADR-018 runtime code work begins until a fresh independent reviewer resolves the new exact head and confirms this one removal procedure closes B1 without regressing B2–B6. This supplement itself is specification work only.
