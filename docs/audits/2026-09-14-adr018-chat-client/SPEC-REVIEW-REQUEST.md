# ADR-018 independent specification review request

**Status:** review requested; this file is a dispatch artifact, not a verdict.

**Target PR:** #75 — `design/adr018-chat-slot-client` → `codex/memory-process-clocks`

**Measured base:** `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`

## Review target

Independently adversarially review the proposed third-client extension to the existing ADR-008 shared Lean slot control plane.

Primary design package:

- `docs/adrs/ADR-018-chat-client-for-shared-lean-slots.md`
- `docs/superpowers/specs/2026-09-14-adr018-chat-slot-client-design.md`
- `docs/superpowers/plans/2026-09-14-adr018-chat-slot-client.md`

Existing authority/context to inspect rather than assume:

- `CLAUDE.md`
- `.claude/plugins/skeft-qa/skills/architecture-change/SKILL.md`
- `docs/architecture/README.md`
- `docs/adrs/ADR-008-shared-lean-slot-control-plane.md`
- `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md`
- `config/lean-slots.public.json`
- `scripts/lean_slots/state.py`
- `scripts/lean_slots/controller.py`
- `scripts/lean_slots/proxy.py`
- `scripts/lean_slots/cli.py`
- relevant `tests/test_lean_slots.py`
- issue #74

The reviewer may inspect `NetRxn/chat-control-plane` WP-010 / PR #37 only to understand the proposed caller/bridge boundary. The SK_EFT repository remains authoritative for slot admission/lifecycle semantics.

## Required adversarial posture

Try to falsify the design rather than improve its prose. In particular test whether:

- another client-admission owner already exists;
- inventory is the correct single owner;
- programmatic controller calls can bypass admission;
- stale bearer token state can preserve removed-client access;
- CLI changes broaden unintended inputs;
- `LEAN_SLOT_OWNER_SESSION` is sufficient for the intended bridge lifecycle;
- private/downstream paired inventory migration is underspecified or unsafe;
- Chat identity changes concurrency/resource semantics rather than merely adding a contender for the same slots;
- the no-mutation acceptance test can pass vacuously;
- a transport or bridge layer accidentally acquires project authority;
- any proposed change contradicts ADR-008, the operator guide, or architecture-change process;
- implementation/testing obligations are missing.

## Required output

Return:

1. **Verdict:** `ACCEPT`, `ACCEPT_WITH_CHANGES`, or `REJECT`.
2. **Blocking findings**, each with evidence path/code location and required disposition.
3. **Non-blocking findings**.
4. **Unknowns / measurements required before implementation**.
5. **Existing mechanism overlap or duplicate-mechanism risk**.
6. **Non-vacuity / acceptance-test weaknesses**.
7. **Downstream/private compatibility risks**.
8. A concise statement of what would need to change for acceptance if the verdict is not `ACCEPT`.

## Durable filing

After completing the review, submit the report as a GitHub **COMMENT review on PR #75**. Do **not** submit `APPROVE` or `REQUEST_CHANGES`: the Chat review is evidence for the project process, not merge authorization.

Also return the same report in the Chat response for operator visibility. Downstream control-plane work should consume the durable PR review rather than relying on manual copy/paste of the transcript.

Do not implement or modify repository files during this review. Do not rely on prior conversation history.
