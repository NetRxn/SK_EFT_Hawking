# ADR-018 residual B1 — removal-preflight design

**Status:** supporting specification supplement; parent ADR-018 D8 and parent spec S18-9 are now canonical and supersede this supplement if any older wording conflicts. Implementation remains blocked on a narrow fresh closure re-review.

**Parent ADR:** `docs/adrs/ADR-018-chat-client-for-shared-lean-slots.md`

**Supporting addendum:** `docs/adrs/ADR-018-b1-removal-preflight-addendum.md`

## Measured residue

At the measured ADR-018 base, `Controller.doctor()` records `wtN.lease` as healthy whenever the lease is absent or its state is not `QUARANTINED`. It does not compare `lease.client` with an admission roster. Therefore a future roster edit that removes client `C` while a lease for `C` remains can be reported healthy by the existing lease-health predicate even though ADR-018 declares that migration state invalid.

The focused independent re-review of PR #75 at head `8407079f935ba3dd758a4f2c288b3cd43ec5239e` returned `ACCEPT_WITH_CHANGES`: B2–B6 were `CLOSED`, B1 was `PARTIALLY_CLOSED`, and no new blocker was introduced. The residual was the missing non-disruptive mismatch predicate plus bearer-token cleanup ordering. A later cloud-dispatched closure review at `0e71346775028daa09eb90006be6c85c458b5388` accepted the substantive mismatch design and narrowed the remaining issue to canonical removal-order consistency plus the exact bearer cleanup operation.

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
4. **credential-revoked** — bearer mode only, using the exact pre-edit operation in S18-16;
5. **roster edited** — versioned inventory no longer admits client;
6. **stale process possible** — old proxy may still serve its loaded policy;
7. **restarted** — supervisor/proxies load new code/inventory;
8. **verified removed** — doctor/preflight green and controller/proxy negative controls deny removed identity.

No state transition here revokes an issued lease by mutation. If an operator creates the invalid state "roster excludes C while lease C remains", doctor must report red and cleanup proceeds under the existing lease owner.

## S18-16 — bearer credential cleanup is one exact pre-edit project operation

Because `Controller.session_environment(client)` will validate admission before token handling, token cleanup cannot rely on invoking session-environment behavior after the roster no longer admits the client.

The canonical operation is:

```text
slotctl session revoke-token --client <client>
```

Required semantics:

- valid only when `client_auth == "bearer"`;
- require the client remains in `Inventory.allowed_clients`;
- fail closed if any live lease records that client;
- resolve only `Inventory.client_token_path(client)`; caller supplies no filesystem path;
- unlink the token file if present and succeed idempotently if absent;
- never emit token bytes;
- return only nonsecret structured result metadata.

The operator runs it after quiescence/removal-preflight and **before** the roster edit. Trusted-local mode has no bearer credential-cleanup step.

Later re-admission must create fresh credential state; the pre-removal credential must fail authentication.

Parent spec S18-9 now contains this canonical procedure and controls if older supplement language differs.

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

After owner cleanup:

- bearer mode runs the exact `session revoke-token` operation while the client is still admitted;
- roster is edited only after credential revocation;
- supervisor/proxies restart;
- no mismatched lease remains;
- stale proxy fingerprint is gone;
- removed client cannot acquire;
- removed client cannot dispatch through trusted-local/bearer proxy;
- Codex/Claude positive controls remain green.

### V17 — bearer re-admission non-reuse

Capture the pre-removal credential in an isolated test environment, complete canonical removal, re-add the client, and prove the old credential does not authenticate. Do not log real secret material in durable output.

Also prove the revoke command rejects bearer cleanup when a live lease exists and cannot target an arbitrary path.

## No new authority

This supplement does not authorize Chat execution, implementation merge, source mutation, worker build, slot repair, or integration. It records the residual B1 reasoning; canonical implementation requirements live in parent ADR D8, parent spec S18-9, and the B1 plan supplement.