# ADR-018 implementation hardening request

**Status:** author/control-plane pre-review hardening; not independent review evidence.

**Implementation PR:** #76

**Accepted specification base:** PR #75 @ `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`.

## Purpose

Before requesting the distinct independent implementation review, close the remaining shipping obligations visible from static inspection of PR #76. Do not invoke live slots, supervisor restart, Lean MCP, builds, or local project execution.

## Required edits

### H1 — mandatory ADR-008 reconciliation

Update `docs/adrs/ADR-008-shared-lean-slot-control-plane.md` in the same implementation wave so the normative lifecycle ADR is true after Chat admission ships.

At minimum:

- make the title/current decision framing client-neutral rather than Codex/Claude-exclusive;
- add a short ADR-018 amendment note stating that versioned inventory owns lease/dispatch client admission and that ADR-018 does not change ADR-008 lifecycle/build/integration authority;
- S-A: every admitted client reuses the same global three-slot pool; no per-client capacity;
- S-C: the lease `client` is an admitted inventory-owned identity rather than the hard-coded `codex|claude` pair; an issued lease remains owner-gated through cleanup;
- S-D: fixed-root endpoints are shared by admitted clients, not only two products;
- make the top-level Decision paragraph say one admitted client per slot rather than "either client";
- extend the controller command contract to include the new admission/removal admin/read-only surfaces where appropriate (`session env`, `session removal-preflight`, `session revoke-token`) while preserving renderer capability as a separate interface;
- make the `doctor` consumer wording client-neutral where it currently names only Codex/later Claude.

Do not rewrite historical Phase-4/Claude records merely because they name the clients involved in that historical tranche.

### H2 — empty prospective roster is not a valid removal target

In `Controller._lease_roster_mismatches`, distinguish `admitted_clients is None` from an explicitly supplied empty iterable. The current `admitted_clients or self.inventory.allowed_clients` expression incorrectly maps an empty prospective set back to the current roster.

In `removal_preflight`, refuse an operation that would leave `server.allowed_clients` empty, consistent with `Inventory.allowed_clients` requiring a non-empty roster.

Add a regression test that would fail with the current truthiness bug.

### H3 — mixed-version pairing must be tested through the actual pairing seam

ADR-018 requires mixed public/private schema-1 pairing evidence. The current standalone private-style test proves fallback semantics but does not exercise `paired_inventory()`.

Add a production-shaped regression in `tests/test_lean_slots.py` using the existing `downstream_repo` fixture (or an equivalently real paired fixture) that proves:

- public paired inventory can explicitly admit `codex`, `claude`, `chat`;
- downstream/private-style schema-1 inventory omitting `allowed_clients` remains exactly `{codex, claude}`;
- resolving the pair does not cause the downstream inventory to inherit Chat admission.

### H4 — inspect routing/claim documentation for false current statements

Inspect the architecture index and any load-bearing current operator/claim documentation affected by the implementation. Do not rewrite historical audits. Update only current documents made false by the shipping change.

### H5 — minimize unrelated operator-guide churn

Review the existing `LEAN_SLOT_OPERATOR_GUIDE.md` diff before treating it as final. Keep the ADR-018-required client-admission/removal/owner changes, and keep a correction only where the **current authoritative inventory/mechanism proves the old operator text is false**. Do not opportunistically shorten historical rationale or rewrite unrelated operating guidance merely because the file is already open. In particular, preserve useful port/session/history explanations unless the new mechanism actually makes the statement false. The implementation review should see a narrow architecture change rather than an accidental guide rewrite.

## Verification posture

This hardening task is static/Git-only. It may add or edit tests, but must not claim they passed unless an actual hosted/mechanical run exists. Record hosted-CI absence as `NOT_MEASURED` rather than success.

After these edits, refresh PR #76 metadata and prepare a durable independent implementation-review request. Implementation review remains read-only and must precede any live Gate A.