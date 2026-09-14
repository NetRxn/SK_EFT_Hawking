# ADR-018 addendum — removal preflight and bearer-token ordering

**Status:** PROPOSED closure addendum for the focused re-review residual B1 on PR #75.

**Parent:** `ADR-018-chat-client-for-shared-lean-slots.md`.

**Reviewed head that exposed the residual:** `8407079f935ba3dd758a4f2c288b3cd43ec5239e`.

**Focused re-review result:** `ACCEPT_WITH_CHANGES`; B1 `PARTIALLY_CLOSED`; B2–B6 `CLOSED`; no new blocker beyond residual B1.

This addendum narrows ADR-018 D8. It does not change ADR-008 lifecycle ownership, lease cleanup authority, slot count, worker privileges, or the no-worker-build rule.

## D13 — removal preflight is a non-disruptive health predicate

A client-roster removal is not considered ready merely because an operator intends to quiesce the client. Before the versioned roster edit, project-native health/removal-preflight logic must explicitly inspect every extant lease and compare its `client` value to the **prospective** admitted-client set.

The predicate stated in words is:

> after removing client `C` from the prospective roster, there must be no live non-terminal lease whose recorded client is `C` before the removal may proceed.

The check is observational. It must **not** mutate, quarantine, reclaim, release, or invalidate an issued lease. If it detects a lease for a client absent from the prospective roster, it reports the removal as blocked/red and preserves the existing owner session's normal cleanup authority so that `release`/`absorb`/quarantine recovery can complete under ADR-008.

`slotctl doctor` may expose this predicate directly or the implementation may provide a dedicated removal-preflight helper consumed by `doctor`; either way there is one implementation predicate and the operator procedure uses its result. The normal steady-state `doctor()` path must also report an already-present mismatch between a live lease's `client` and the currently loaded/versioned admission roster rather than treating every non-`QUARANTINED` lease as healthy.

A red roster/lease mismatch is therefore **migration-health evidence**, not lease revocation. Lifecycle operations on the already-issued lease remain owner-gated by ADR-008 until the operator quiesces it.

### Non-vacuity requirement

The production-shaped test seeds the defect into the artifact `doctor`/preflight actually reads:

1. create an active lease for an admitted client;
2. change the versioned/prospective roster so that client is absent without deleting the lease;
3. observe the health/removal-preflight predicate go red while leaving the lease untouched;
4. exercise the legitimate owner cleanup path;
5. restart the supervisor/proxy after the roster edit;
6. observe health green and the removed identity denied.

A fixture-only helper that never reads the real lease artifact does not satisfy this requirement.

## D14 — bearer credential cleanup ordering is explicit

Bearer-token cleanup must not depend on `session env --client <removed>` after the roster edit, because ADR-018 requires `session_environment()` to reject an unadmitted client **before** token processing.

The supported ordering is therefore one of these equivalent project-owned operations, chosen by implementation but tested explicitly:

- **delete-before-edit:** while the client is still admitted and quiescent, remove its token file/state, then edit the roster, restart, and verify denial; or
- **rotate-before-edit then delete stale state:** rotate/revoke the credential while still admitted, record the new/revoked state, then remove the client, restart, and ensure the pre-removal credential cannot become valid again on later re-admission.

The implementation must not document an impossible post-removal `session env` cleanup step. Re-admission after a removal must never silently resurrect the pre-removal credential.

## Acceptance delta

In addition to ADR-018's existing acceptance requirements:

- a live lease whose client is outside the current/prospective roster makes doctor/removal-preflight red without mutating the lease;
- the legitimate owner can still complete cleanup while that mismatch is reported;
- after cleanup + roster edit + restart, doctor is green and the removed client is denied;
- bearer-mode tests prove the chosen pre-edit credential cleanup ordering and prove old credential non-reuse after re-admission.

No runtime implementation is authorized until a fresh independent reviewer accepts this residual-B1 closure.