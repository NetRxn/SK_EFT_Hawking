# ADR-018 residual B1 — removal-preflight design

**Status:** proposed specification supplement; implementation blocked on independent closure re-review.

**Parent ADR:** `docs/adrs/ADR-018-chat-client-for-shared-lean-slots.md`

**Normative addendum:** `docs/adrs/ADR-018-b1-removal-preflight-addendum.md`

## Measured residue

At the measured ADR-018 base, `Controller.doctor()` records `wtN.lease` as healthy whenever the lease is absent or its state is not `QUARANTINED`. It does not compare `lease.client` with an admission roster. Therefore a future roster edit that removes client `C` while a lease for `C` remains can be reported healthy by the existing lease-health predicate even though ADR-018 declares that migration state invalid.

The focused independent re-review of PR #75 at head `8407079f935ba3dd758a4f2c288b3cd43ec5239e` returned `ACCEPT_WITH_CHANGES`: B2–B6 were `CLOSED`, B1 was `PARTIALLY_CLOSED`, and no new blocker was introduced. The residual is exactly the missing non-disruptive mismatch predicate plus bearer-token cleanup ordering.

## S18-14 — one non-disruptive lease/roster mismatch predicate

Implement one project-native predicate with inputs:

- current lease artifact, if any;
- admitted-client set being evaluated (current loaded roster for ordinary doctor; prospective roster for removal preflight).

It returns red when a live/non-terminal lease records a `client` absent from that set.

Properties:

- read-only;
- no release/reclaim/quarantine/reset side effect;
- does not make lifecycle commands roster-sensitive mid-flight;
- preserves owner-gated cleanup authority;
- produces a stable, explicit diagnostic naming slot, lease state, recorded client, and roster mismatch without exposing secret token material.

`Controller.doctor()` consumes the predicate against the current inventory roster. A removal-preflight operation consumes the same predicate against the prospective roster before a versioned edit is declared safe.

If implementation can express prospective-roster preflight as a pure controller/helper call, prefer that to adding another state machine or daemon. Do not create a second lease authority.

## S18-15 — removal preflight and effective removal are distinct states

Removal progresses through these observable states:

1. **eligible to quiesce** — client currently admitted;
2. **blocked by live lease** — prospective roster excludes client but mismatch predicate is red; no edit/restart is called complete;
3. **quiescent** — no live lease for client;
4. **credential-cleaned** — bearer mode only, using the pre-edit operation in S18-16;
5. **roster edited** — versioned inventory no longer admits client;
6. **stale process possible** — old proxy may still serve its loaded policy;
7. **restarted** — supervisor/proxies load new code/inventory;
8. **verified removed** — doctor/preflight green and controller/proxy negative controls deny removed identity.

No state transition here revokes an issued lease by mutation. If an operator creates the invalid state "roster excludes C while lease C remains", doctor must report red and cleanup proceeds under the existing lease owner.

## S18-16 — bearer credential cleanup occurs before admission removal

Because `Controller.session_environment(client)` will validate admission before token handling, token cleanup cannot rely on invoking session-environment behavior after the roster no longer admits the client.

The implementation must choose and test a pre-edit credential operation:

- delete/revoke token state while client is still admitted and quiescent; or
- rotate/revoke before the edit, then ensure stale pre-removal credentials are removed and cannot be reused.

The operator guide must state the exact chosen command/path. A later re-add of the client must generate/use fresh credential state rather than silently accepting the pre-removal credential.

Trusted-local mode has no bearer credential-cleanup step; it still uses quiesce → roster edit → restart → deny verification.

## Verification design

### V14 — production-seeded doctor red

Use the real lease artifact path consumed by `Inventory.lease()`/`Controller.doctor()`:

- known-present admitted client + active non-quarantined lease is healthy;
- remove that client from the roster artifact without deleting lease;
- doctor reports the exact lease/client admission mismatch red;
- lease bytes/state are unchanged by doctor.

### V15 — owner cleanup remains possible

With the mismatch present, the correct `LEAN_SLOT_OWNER_SESSION` can still run the existing legal cleanup transition. A different owner cannot. The new health predicate must not be used inside `_lease_for_command()` as a hidden admission re-check.

### V16 — completed removal

After owner cleanup, bearer credential cleanup if applicable, roster edit, supervisor restart, and health check:

- no mismatched lease remains;
- stale proxy fingerprint is gone;
- removed client cannot acquire;
- removed client cannot dispatch through trusted-local/bearer proxy;
- Codex/Claude positive controls remain green.

### V17 — bearer re-admission non-reuse

Capture the pre-removal credential identifier/value in an isolated test environment, complete removal, re-add the client, and prove the old credential does not authenticate. Do not log real secret material in test output.

## No new authority

This supplement does not authorize Chat execution, implementation merge, source mutation, worker build, slot repair, or integration. It only closes specification residual B1 so the existing ADR-018 implementation gate can be re-reviewed.