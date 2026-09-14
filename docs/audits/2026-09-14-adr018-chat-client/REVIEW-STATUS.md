# ADR-018 review gate status

- Design branch: `design/adr018-chat-slot-client`
- Base: `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`
- First reviewed head: `332f44f5e4ba557ae1d119a55018aa51fd923ce8`
- First independent adversarial review: **COMPLETE — `ACCEPT_WITH_CHANGES`**
- First durable review: PR #75 COMMENT review `pullrequestreview-5199476588`
- First blockers: **B1–B6**
- Focused reviewed head: `8407079f935ba3dd758a4f2c288b3cd43ec5239e`
- Focused independent re-review: **COMPLETE — `ACCEPT_WITH_CHANGES`**
- Focused closure: **B1 `PARTIALLY_CLOSED`; B2–B6 `CLOSED`; no new blocker beyond residual B1**
- Residual B1 reviewed head: `0e71346775028daa09eb90006be6c85c458b5388`
- Cloud-dispatched residual B1 review: **COMPLETE — `ACCEPT_WITH_CHANGES` / B1 `PARTIALLY_CLOSED`**
- Durable cloud filing: GitHub COMMENT review reported as `#5201956869`, independently read back by the cloud task
- Duplicate observation: GitHub currently contains **two** substantially equivalent residual-B1 COMMENT reviews on the same head within roughly two minutes; treat this as dispatcher idempotency dogfood, not extra independent acceptance evidence
- Substantive B1 mismatch/preflight design: **ACCEPTED BY REVIEW**
- Remaining B1 finding from cloud review: **canonical D8/S18-9 credential-removal order + exact bearer cleanup operation**
- Canonical reconciliation: **COMPLETE IN CURRENT ADR/SPEC/PLAN** — pre-edit bearer revocation, exact `slotctl session revoke-token --client <client>` semantics, and parent precedence are now explicit
- Final narrow canonical-consistency re-review: **REQUIRED / PENDING**
- Private/downstream measurement: **COMPLETE** — NetRxn-RD `codex/frontier-first-deliverables` @ `47b380f6e233a0fd70662640422b3652e6d3191a`; schema-1 private inventory has no `allowed_clients` and reuses the public controller
- Implementation authorized: **NO**
- Live slot acceptance authorized: **NO**

## Review lineage

The first review remains historical evidence anchored to `332f44f...`. The focused review at `8407079f...` closed B2–B6 and narrowed B1. The cloud-dispatched review at `0e713467...` accepted the non-disruptive roster/lease mismatch predicate and owner-cleanup preservation, then found one documentary-but-normative contradiction: residual addendum/spec required bearer cleanup before roster removal while canonical parent D8/S18-9 still had the inverse order, and the concrete cleanup operation remained deferred.

The current design removes that contradiction:

`quiesce + removal-preflight → bearer session revoke-token while client is still admitted → allowed_clients edit → supervisor restart → doctor + controller/proxy denial verification`.

The exact bearer command is project-owned and narrow:

`slotctl session revoke-token --client <client>`

It is bearer-only, admission-aware, refuses a live client lease, resolves only `Inventory.client_token_path(client)`, deletes credential state idempotently, and never emits token bytes.

Because these edits move the PR head again, the favorable portions of the `0e713467...` review remain historical evidence; implementation does not start until a fresh reviewer checks only that the canonical ADR/spec/plan now agree and that no B2–B6 regression was introduced.

This status file is routing/status evidence only; it does not grant implementation, merge, live-slot, publication, or other authorization.
