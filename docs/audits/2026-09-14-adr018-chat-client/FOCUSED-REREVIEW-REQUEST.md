# ADR-018 focused independent re-review request

**Status:** requested; this is dispatch metadata, not a verdict.

**PR:** #75

**Base:** `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`

**First reviewed head:** `332f44f5e4ba557ae1d119a55018aa51fd923ce8`

**First verdict:** `ACCEPT_WITH_CHANGES`

## Purpose

A fresh reviewer should determine whether the **current PR #75 head** adequately resolves blocking findings B1–B6 from the first independent review, and whether the reconciliation introduced any new blocker.

Resolve the current head SHA immediately before reviewing. Do not assume a SHA from this file or the prompt remains current.

## Required durable inputs

Read:

- the first GitHub COMMENT review on PR #75 (`pullrequestreview-5199476588`);
- `docs/audits/2026-09-14-adr018-chat-client/SPEC-REVIEW-RECONCILIATION.md`;
- revised ADR-018;
- revised ADR-018 design spec;
- revised ADR-018 implementation plan;
- issue #74;
- ADR-008 and `LEAN_SLOT_OPERATOR_GUIDE.md` as the unchanged lifecycle authorities;
- actual implementation surfaces relevant to any disputed disposition.

For B3, independently verify the measured private/downstream facts in `NetRxn/NetRxn-RD` if accessible: active branch `codex/frontier-first-deliverables`, `config/lean-slots.private.json`, and `tests/test_lean_slot_overlay.py`.

For B2/B5, inspect current `NetRxn/chat-control-plane` PR #37 only as caller-boundary evidence. SK_EFT remains authoritative for slot semantics.

## Focus questions

For each original blocker B1–B6, report exactly one disposition:

- `CLOSED` — revised design closes the failure mode sufficiently for implementation;
- `PARTIALLY_CLOSED` — specific residual blocker remains;
- `OPEN` — failure mode is not adequately resolved.

Specifically test:

### B1

Does quiesce → roster edit → bearer-token cleanup → supervisor restart → doctor/negative verification define an honest, testable removal boundary? Can stale proxy or active lease behavior still contradict the claimed semantics?

### B2

Does the one-durable-owner-session design avoid the `READY_TO_ABSORB` dead end without silently giving worker/bridge authority to integrate? Are heartbeat and future same-owner continuation boundaries stated precisely enough?

### B3

Is the exact schema-1 missing-field fallback `{codex, claude}` justified by the measured private overlay, and does it avoid accidental private Chat admission or rollout breakage?

### B4

Are renderer capability and lease/dispatch admission now unambiguously separate? Could `config render --client chat` still fall through to Codex under the planned change?

### B5

Does Gate A now test the actual production bridge rather than manual slotctl substitutes, and are mutation APIs tested on disposable production-shaped state before live source?

### B6

Is reconciliation of ADR-008/client enumeration and the operator guide now a mandatory shipping obligation rather than optional cleanup?

## New-blocker sweep

Also check whether the reconciliation creates a new defect, especially:

- incompatible ownership assumptions between SK_EFT and WP-010;
- ambiguous authority for the future `ready → absorb` continuation;
- a compatibility fallback that weakens public admission;
- token cleanup that is impossible or misleading under trusted-local mode;
- tests that can still pass without exercising the production boundary;
- a changed PR head that invalidates a claim carried from the first review.

## Required result

Return and file as a GitHub **COMMENT review** on PR #75:

1. current reviewed head/base SHA;
2. independence statement;
3. B1–B6 closure table (`CLOSED | PARTIALLY_CLOSED | OPEN`) with evidence;
4. any new blocking findings;
5. non-blocking findings/unknowns;
6. final verdict: `ACCEPT`, `ACCEPT_WITH_CHANGES`, or `REJECT`;
7. exact remaining changes required before implementation, if any.

Do not modify repository files. Do not use GitHub APPROVE/REQUEST_CHANGES; the Chat review is evidence, not merge authorization.
