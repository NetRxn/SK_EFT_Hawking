# ADR-018 specification review reconciliation

**First review target:** PR #75 head `332f44f5e4ba557ae1d119a55018aa51fd923ce8`

**First verdict:** `ACCEPT_WITH_CHANGES`

**Purpose:** give a fresh reviewer a durable map from each blocking finding to the revised design. This document records dispositions; it is not itself acceptance evidence.

## B1 — removal/revocation, stale proxy, bearer token

**Review problem:** an inventory edit is not immediate revocation because the live proxy snapshots inventory; active leases and bearer token files made removal semantics ambiguous.

**Disposition:**

- ADR-018 D8;
- spec S18-9;
- plan Phase 1.2.

Removal is now explicitly **quiescent + restart-bound**: no active lease for the client, versioned roster edit, bearer token delete/rotation, supervisor/proxy restart, health/doctor verification, then negative identity proof. A stale running proxy is expected to remain on old policy until restart and must be tested as such. Existing issued leases are not made roster-sensitive mid-flight.

## B2 — lifecycle owner, heartbeat, ready → absorb

**Review problem:** WP-010 used one owner session for acquire/prepare/ready but lacked heartbeat/absorb; handing `READY_TO_ABSORB` to an unrelated lead would fail owner checks, while granting the worker bridge absorb would expand authority.

**Disposition:**

- ADR-018 D5/D11;
- spec S18-5/S18-10/S18-12;
- plan Phase 6.5.

There is no implicit ownership transfer. One durable `LEAN_SLOT_OWNER_SESSION` remains the project-lifecycle owner. Gate A terminates through no-change release and does not claim heartbeat coverage. Before any real source mutation, WP-010 must expose heartbeat and a separately authorized/reviewed lead/integration continuation must prove same-owner `ready → absorb` without treating worker authority as integration authority.

## B3 — private/downstream migration

**Review problem:** migration behavior was deferred despite the paired private overlay sharing the public controller.

**Measurement performed:** active `NetRxn/NetRxn-RD` branch `codex/frontier-first-deliverables` @ `47b380f6e233a0fd70662640422b3652e6d3191a` has `config/lean-slots.private.json` schema 1, trusted-local auth, no `allowed_clients`; `tests/test_lean_slot_overlay.py` verifies the private wrapper reuses the public controller.

**Disposition:**

- ADR-018 D9;
- spec S18-8;
- plan Phase 1.1.

Schema-1 missing `allowed_clients` means exactly `{codex, claude}`. It never implies Chat. Public inventory explicitly opts in to Chat; private inventory remains Chat-denied until a separate private change. Mixed-version paired tests are mandatory.

## B4 — renderer capability can be confused with admission

**Review problem:** removing all CLI `choices` could make `config render --client chat` fall through to the current Codex `else` branch.

**Disposition:**

- ADR-018 D6/D10;
- spec S18-4/S18-6/S18-11;
- plan Phase 2.3.

Only acquire/session admission delegates to inventory. Renderer support remains an exhaustive Codex/Claude capability set. `config render --client chat` must fail without writing; catch-all renderer dispatch is replaced by exhaustive named dispatch.

## B5 — Gate A could bypass the production bridge

**Review problem:** manual slotctl acquire/prepare/release could validate SK_EFT while leaving WP-010 activation/session propagation broken.

**Disposition:**

- ADR-018 D11;
- spec S18-12;
- plan Phase 6.

Gate A now requires the production path: durable preflight → bridge `activate()` → independent lease observation → bridge domain-MCP diagnostics/verify → mismatched-client negative control → unchanged HEAD/status proof → bridge `release_no_change()`. Manual slotctl is observation/debug only. Before a real source task, a disposable production-shaped write/checkpoint/ready path is required.

## B6 — ADR-008/operator-guide contradiction

**Review problem:** ADR-008 remains normative but currently enumerates only Codex/Claude; the original plan made reconciliation conditional.

**Disposition:**

- ADR-018 D12;
- spec S18-13;
- plan Phase 3.

The implementation/shipping commit must reconcile ADR-008 S-A/S-C and the Lean slot operator guide. The lifecycle/build/integration decisions remain ADR-008-owned; only client-enumeration/admission prose becomes inventory-owned. Architecture registration/claim checks are mandatory.

## Re-review scope

The focused fresh-reader re-review should answer:

1. Does each B1–B6 disposition close the original failure mode without weakening ADR-008?
2. Does the exact schema-1 fallback fit the measured private overlay?
3. Does the no-owner-transfer posture create any new lifecycle dead end?
4. Is quiesce + restart a sufficiently explicit and testable removal boundary?
5. Are renderer capability and admission now unambiguously separate?
6. Does Gate A genuinely test the production bridge?
7. Is any new blocker introduced by the reconciliation?

Implementation remains blocked until this focused re-review is acceptable.
