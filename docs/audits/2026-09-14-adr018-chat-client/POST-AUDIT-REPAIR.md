# ADR-018 post-audit repair checkpoint

Status: AUTHOR_DOC_REPAIRS_COMPLETE_PENDING_VERIFICATION_AND_REVIEW.

## Scope and lineage

The accepted specification remains PR #75 head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`, with COMMENT review `5202241729` (`ACCEPT`, residual B1 closed, no B2–B6 regression). The existing PR #76 implementation review `5203396570` is historical evidence at `42803dfc2baa5e5a26b152557e0c7e0d8c9504aa`; it cannot transfer to a changed head automatically.

The author spot-check finding is filed under `papers/AutomatedReviews/2026-09-14-adr018-roster-null/ADR018.md`. No historical finding/closure record is rewritten by this repair.

Coordinator handoff arrived through code/test repair `fbfeb76e3ed5736ec95268e3ede9acd0dad59d44` and audit-routing commit `eae41dac6ef8a0e6c7205014b5269e02f2a8ba3b`. The D1–D3 author document reconciliation is commit `01bacd198ef20e496a8d9ba01d2cc6661017e0fe`. The author documentation lane re-resolved PR #76 at the handoff head before editing and observed no intervening writer move.

## Implementation

`Inventory.allowed_clients` now distinguishes absence of the key from explicit JSON null before selecting legacy compatibility. Every present value reaches existing nonempty-array validation. No lease, proxy, token, build or integration mechanism is added or broadened.

`tests/test_adr018_roster_validation.py` exercises the actual file-loading path with explicit null and neighboring malformed JSON values in both authentication modes, plus absent-field compatibility, explicit narrow admission and valid immutable public-roster positive controls. The tests use only disposable inventory files; they do not call a controller, Git, Lean, server, MCP or slot lifecycle.

## Post-audit document work

- D1 current-state reconciliation: AUTHOR COMPLETE. Canonical ADR-018, the B1 addendum, both specifications and both plans now record specification ACCEPT at exact head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f` / COMMENT `5202241729`, implementation-in-progress, and the still-pending mechanical + exact-head implementation-review gates. Historical review records and canonical D8/S18-9 removal semantics remain intact.
- D2 focused re-review request: PREPARED at `POST-AUDIT-IMPLEMENTATION-REREVIEW-REQUEST.md`. It is not enqueued while reviewer launch isolation remains unresolved.
- D3 mechanical feasibility: COMPLETE as read-only reconnaissance. No repository GitHub Actions workflow exists; exact candidate commands, environment requirements and evidence gaps are recorded in `POST-AUDIT-DOC-RECONCILIATION-STATUS.md`.

## Evidence and remaining work

- Source change and regression tests: AUTHORED, not independently accepted.
- Test execution: NOT_MEASURED. No pytest, local/project runtime, slotctl, Lean, MCP, build or executor was invoked by this author documentation wave.
- Hosted execution on the author handoff head: none observed; the exact-head workflow-runs query returned zero and `.github/workflows/` is absent.
- Independent implementation re-review: pending; the author is not the reviewer and scheduled-task identity alone does not establish independent context.
- Formal finding closure: pending through the project-owned single writer after required verification/review evidence.
- Gate A, live runtime use, source-mutating proof tasks, build/absorb/merge and publication: not authorized by this checkpoint.

The repair implements an already accepted admission contract and the documentation reconciliation restores current truth; neither action settles a new architecture decision or claims the wave complete.
