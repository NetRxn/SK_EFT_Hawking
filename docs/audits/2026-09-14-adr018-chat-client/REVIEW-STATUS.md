# ADR-018 review gate status

- Design branch: `design/adr018-chat-slot-client`
- Base: `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`
- First reviewed head: `332f44f5e4ba557ae1d119a55018aa51fd923ce8`
- First independent adversarial review: **COMPLETE — `ACCEPT_WITH_CHANGES`**
- First durable review: PR #75 COMMENT review `pullrequestreview-5199476588`
- First blockers: **B1–B6**
- First reconciliation: **COMPLETE**
- Focused reviewed head: `8407079f935ba3dd758a4f2c288b3cd43ec5239e`
- Focused independent re-review: **COMPLETE — `ACCEPT_WITH_CHANGES`**
- Focused closure: **B1 `PARTIALLY_CLOSED`; B2–B6 `CLOSED`; no new blocker beyond residual B1**
- Residual B1 specification reconciliation: **COMPLETE** — D13/D14 + S18-14..16 + implementation-plan supplement
- Residual B1 closure re-review: **REQUIRED / PENDING**
- Private/downstream measurement: **COMPLETE** — NetRxn-RD `codex/frontier-first-deliverables` @ `47b380f6e233a0fd70662640422b3652e6d3191a`; schema-1 private inventory has no `allowed_clients` and reuses the public controller
- Implementation authorized: **NO**
- Live slot acceptance authorized: **NO**

The first review remains historical evidence anchored to `332f44f...`. The focused re-review is anchored to `8407079f...` and closed B2–B6 while retaining one residual B1 blocker: the design needed an explicit non-disruptive doctor/removal-preflight lease-client/roster mismatch predicate and unambiguous pre-edit bearer credential cleanup ordering.

Those residual semantics are now specified document-first in:

- `docs/adrs/ADR-018-b1-removal-preflight-addendum.md`;
- `docs/superpowers/specs/2026-09-14-adr018-b1-removal-preflight-design.md`;
- `docs/superpowers/plans/2026-09-14-adr018-b1-removal-preflight.md`;
- `docs/audits/2026-09-14-adr018-chat-client/FOCUSED-REREVIEW-RECONCILIATION.md`.

Because B1 was still blocking, runtime implementation does not begin until the narrow closure request in `B1-CLOSURE-REREVIEW-REQUEST.md` is independently accepted.

This status file is a routing/status artifact; it does not substitute for review evidence or grant implementation/merge authority.
