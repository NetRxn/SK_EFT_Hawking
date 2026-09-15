# ADR-018 Chat-client review and implementation evidence

This directory contains specification-review requests, reconciliation, and implementation-preparation evidence for the distinct Chat client. The current state is in `REVIEW-STATUS.md`; dated review requests and reconciliations describe their own historical heads, not a perpetual implementation prohibition.

The specification received ACCEPT in PR #75 COMMENT review `5202241729` at exact head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`. Bounded author implementation on PR #76 is in progress. The implementation review, mechanical verification, no-mutation live acceptance, source-mutation prerequisites and merge authorization remain separate gates.

Relevant routing:

- `SPEC-REVIEW-REQUEST.md` and the focused/B1 requests: historical specification-review scopes.
- `REVIEW-STATUS.md`: current gate state and exact reviewed-head lineage.
- `IMPLEMENTATION-REVIEW-REQUEST.md`: existing implementation-review contract.
- `POST-AUDIT-REPAIR.md`: explicit-null roster repair and authored regression-test checkpoint.
- `POST-AUDIT-DOC-RECONCILIATION-REQUEST.md`: remaining current-document reconciliation and mechanical-evidence reconnaissance.

No live slot, Lean, MCP, build, absorb, merge or publication is authorized by the presence of these artifacts. Source inspection and readback prove neither executed tests nor independent-review acceptance.
