# ADR-018 post-audit document reconciliation

Status: READY_FOR_AUTHOR_DOC_REPAIR. This request authorizes no independent acceptance or live project execution.

## Starting point

PR #76, branch `implementation/adr018-chat-slot-client`. Code/test repair `fbfeb76e3ed5736ec95268e3ede9acd0dad59d44` implements the existing missing-versus-null roster contract and adds `tests/test_adr018_roster_validation.py`. Do not undo it or broaden the runtime mechanism.

Read `CLAUDE.md`, the architecture-change skill, architecture ownership index and relevant pipeline rules; read accepted PR #75 review `5202241729` at `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f` and implementation review `5203396570` at `42803dfc2baa5e5a26b152557e0c7e0d8c9504aa`. Read the current files before editing. Reconstruct from durable source, not transcript claims.

## D1 — reconcile current status, not historical evidence

Update the present-tense status and gate statements in all current ADR-018 normative/specification/plan surfaces to say the specification was accepted at the exact head above and author implementation is in progress, with mechanical verification and exact-head independent implementation re-review still pending. Inspect at minimum:

- `docs/adrs/ADR-018-chat-client-for-shared-lean-slots.md`;
- `docs/adrs/ADR-018-b1-removal-preflight-addendum.md`;
- `docs/superpowers/specs/2026-09-14-adr018-chat-slot-client-design.md`;
- `docs/superpowers/specs/2026-09-14-adr018-b1-removal-preflight-design.md`;
- `docs/superpowers/plans/2026-09-14-adr018-chat-slot-client.md`;
- `docs/superpowers/plans/2026-09-14-adr018-b1-removal-preflight.md`.

`REVIEW-STATUS.md` and the audit README already have the initial current-state correction; reconcile them if needed but preserve exact lineage. Update `POST-AUDIT-REPAIR.md` when D1 is complete. Read the whole relevant file so current pending statements deeper in a plan are not missed. Do not globally replace words in historical quotations or past review requests. Do not change accepted D8/S18-9 sequencing, ownership, roster compatibility, or gate semantics. Do not call the entire ADR shipped, the implementation accepted, or the finding closed.

Prefer a single coherent multi-file commit using the existing GitHub tree/commit/ref capability if practical. Never force-push. Re-resolve the branch first; unexpected other-writer changes must be reconciled or returned as CONCURRENT_CHANGE.

## D2 — exact-head focused review request

Prepare `POST-AUDIT-IMPLEMENTATION-REREVIEW-REQUEST.md` after current-document reconciliation. Include implementation-review B1 and the newly filed explicit-null case, original failure / nearby malformed values / valid missing and narrow-roster controls, negative bearer/trusted-local controls, no new runtime authority, and the requirement to distinguish tests authored from tests run. The reviewer must resolve current head/base, inspect actual code/test files, remain read-only and file COMMENT evidence only. Do not enqueue it in central review intake until independent context is established by the coordinator.

## D3 — mechanical evidence feasibility, read-only only

Inspect the repository's actual workflow configuration, dependency declarations and test fixtures to identify an existing permitted hosted mechanical path for the roster/admission/document regressions. Do not confuse a no-live-slot constraint with proof that no safe parser tests are possible. Record exact existing workflows, triggers, dependencies, commands, evidence and gaps. Do not create/enable a workflow, invoke a workflow dispatch, run local/project code, tests, slotctl, Lean, MCP, build or executor. Naturally triggered existing hosted checks may be read; PASS requires the actual run on the exact code head. If none exists, report NOT_MEASURED plus the smallest proposed next verification step rather than a generic infrastructure project.

## Boundaries and handoff

One author lane writes this branch after coordinator handoff. No other repository, source/runtime module, parent branch, review verdict, closure ledger, notebook substitute or automation may be altered. Public artifacts must not introduce private-repository identifiers, private paths or secrets. Preserve local-only notebook/worktree state as unobserved rather than absent.

Use `POST-AUDIT-DOC-RECONCILIATION-STATUS.md` to record current run ownership/handoff, per-D1..D3 progress, exact commits and evidence, limitations and remaining work. If a prior run is still active or ownership cannot be established, stop rather than race. On interruption persist a coherent checkpoint. On completion use AUTHOR_DOC_REPAIRS_COMPLETE_PENDING_VERIFICATION_AND_REVIEW, not ACCEPT. Re-read changed files/current PR and update only PR #76 metadata accurately; keep draft. Do not post intake, attach an executor, close a finding, merge or enable live acceptance. Scheduled continuation is author work and does not require a blind reviewer context.
