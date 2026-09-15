# ADR-018 post-audit repair checkpoint

Status: AUTHOR_CODE_REPAIR_PRESENT; mechanical verification and independent re-review remain pending.

## Scope and lineage

The accepted specification remains PR #75 head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`, with COMMENT review `5202241729`. The existing PR #76 implementation review `5203396570` is historical evidence at `42803dfc2baa5e5a26b152557e0c7e0d8c9504aa`; it cannot transfer to a changed head automatically.

The author spot-check finding is filed under `papers/AutomatedReviews/2026-09-14-adr018-roster-null/ADR018.md`. No historical finding/closure record is rewritten by this repair.

## Implementation

`Inventory.allowed_clients` now distinguishes absence of the key from explicit JSON null before selecting legacy compatibility. Every present value reaches existing nonempty-array validation. No lease, proxy, token, build or integration mechanism is added or broadened.

`tests/test_adr018_roster_validation.py` exercises the actual file-loading path with explicit null and neighboring malformed JSON values in both authentication modes, plus absent-field compatibility, explicit narrow admission and valid immutable public-roster positive controls. The tests use only disposable inventory files; they do not call a controller, Git, Lean, server, MCP or slot lifecycle.

## Evidence and remaining work

- Source change and regression tests: authored together in this commit.
- Test execution: NOT_MEASURED. No pytest, live slot or project runtime was invoked by the author.
- Current ADR/spec/plan/audit status reconciliation from review B1: still pending; update current statements without rewriting historical review bodies.
- Independent implementation re-review: pending; the author is not the reviewer.
- Reviewer launch isolation: not established by creating a scheduled task; do not infer it from task identity or a self-attestation.
- Gate A, live runtime use, source-mutating proof tasks, build/absorb/merge and formal finding closure: not authorized by this checkpoint.

The repair implements an already stated admission contract; it does not settle a new architecture decision or claim the wave complete. Required verification is the finding's native command plus the applicable existing regression/document suite on the exact resulting head.
