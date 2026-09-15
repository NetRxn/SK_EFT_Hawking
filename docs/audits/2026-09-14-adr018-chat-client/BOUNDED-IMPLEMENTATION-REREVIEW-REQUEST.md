# ADR-018 bounded implementation re-review

Status: READY_FOR_REVIEW_ADMISSION; independent reviewer-launch requirement remains OPEN. This is an operator-requested scope contract and author preparation, not review evidence, finding closure, or merge/execution authorization.

The operator requested diff-bounded follow-up review and a maximum of two substantive re-review cycles per finding before explicit escalation. This request applies that policy to PR #76 without replacing the repository's architecture-change, verification, finding, or closure mechanisms.

## Exact target and comparison boundary

- Repository / PR: `NetRxn/SK_EFT_Hawking` #76.
- Target branch: `implementation/adr018-chat-slot-client`.
- PR base at preparation: `design/adr018-chat-slot-client` @ `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`.
- Prior reviewed implementation head: `42803dfc2baa5e5a26b152557e0c7e0d8c9504aa`, COMMENT `5203396570`.
- Observed repaired head before this request-only commit: `d0c21413f5f5133d71f9c4e4d1616c520cb094ea`.
- Stable review case: `skeft-pr76-adr018-implementation`.

Resolve current head/base independently, pin the exact head in the intake, and recheck before filing. Primary review delta is prior reviewed implementation head -> exact requested current head. The full PR base -> head diff is context for judging introduced or newly exposed interactions, not an invitation to audit the whole repository. Missing/truncated diffs are limitations, not complete inspection.

## Fixed closure set

1. **IMPL-B1:** current-document contradiction reported in COMMENT `5203396570`. Verify the repaired ADR/spec/plan/audit status expresses the actual accepted specification lineage without rewriting historical verdicts, and preserves canonical D8/S18-9 and pending implementation/mechanical/live gates.
2. **ROSTER-NULL:** `papers/AutomatedReviews/2026-09-14-adr018-roster-null/ADR018.md`, repaired in `fbfeb76e3ed5736ec95268e3ede9acd0dad59d44`. Verify absent-key compatibility is distinct from explicit null and other malformed present values, with intended narrow/full/legacy membership preserved.
3. **Repair-induced regressions** in those changed predicates, their direct consumers, and changed normative statements.

Use the detailed original-failure / neighboring-value / positive-control questions in `POST-AUDIT-IMPLEMENTATION-REREVIEW-REQUEST.md`, especially R1, R2 and R4. Its R3 sweep is constrained by the causal boundary below. This wrapper narrows review scope; it does not waive that request's independence or mechanical-evidence requirements.

## Scope and blocker rules

Read the project-owned rules and the actual repair delta first. Surrounding unchanged code may be inspected only to resolve a specific dependency, invariant, or failure path affected by the delta; record why that context is necessary. Discovery context is not automatic remediation scope.

A blocking finding must establish at least one of:

- a fixed-set finding is not actually repaired;
- an identified changed hunk introduces, worsens, or newly exposes a concrete failure in the supported path;
- the change cannot land under an explicit existing project requirement, with the exact requirement and missing evidence named.

For every blocker give the changed hunk or existing fixed finding, causal path, concrete counterexample/failure, impacted accepted requirement, and smallest sufficient disposition. 'Same file', 'would be better', or a hypothetical future capability is insufficient. Unknowns are not defects unless proving that fact is an explicit acceptance obligation.

Unrelated pre-existing debt, optional hardening, stylistic preferences and future-stage implementation work belong in a separate FOLLOW_UP section and do not block this scope. Record actionable evidence and the native follow-up destination; do not silently drop them or implement them during review. A credible severe out-of-scope safety/security finding goes to SAFETY_ESCALATION for an explicit owner decision, not silent approval and not automatic conversion into a repository-wide repair project.

Already-closed findings stay closed unless a concrete changed hunk or new counterexample falsifies their closure. Do not demand a new full audit merely because a repair moved the head.

## Evidence and stop condition

For each fixed finding: original failure, at least one relevant nearby variant, a valid positive control, and exact evidence path/expression. Label source reasoning NOT_EXECUTED; identify actual executed test head/command/result separately. Do not require every possible hypothetical variant.

Mechanical verification remains a separate prerequisite. At preparation there is no hosted result for the repaired head. In particular, this request does not run or waive `uv run python -m pytest tests/test_adr018_roster_validation.py tests/test_adr018_chat_client.py -q` or other applicable native checks. Report evidence unavailable once; do not generate repeated adversarial rounds just to rediscover it.

Stop substantive review once the fixed-set dispositions and the causally scoped regression check are complete. `ACCEPT` means no unresolved in-scope review blocker, not merge readiness, verification PASS, or authorization. Preserve the native verdict vocabulary `ACCEPT`, `ACCEPT_WITH_CHANGES`, `REJECT`.

## Bounded convergence

Maximum two completed substantive focused re-reviews per stable finding after its initial review, and at most two rounds for this fixed repair package before a scope/budget decision. Count the durable review lineage; transport retries, stale-head aborts, duplicates and admission failures are not additional substantive reviews. This is the first planned focused re-review following implementation COMMENT `5203396570`; independently confirm no intervening substantive review exists.

Record stable finding IDs and prior review IDs. A rename, new request ID, changed head, or repair-induced child finding must not reset the package budget. After the final allowed round, any remaining blocker produces ESCALATION_REQUIRED with the smallest remaining issue and options: targeted repair, split/revert/defer the affected increment, or explicitly approve additional scoped review. The cap bounds automatic looping; it never makes a failed check pass or forces a merge. A successful round ends review without mandatory extra rounds.

## Launch, filing, and non-authority

Preserve the existing independent reviewer-only launch gate. Scheduled-task identity, different task title, an instruction to ignore context, or reviewer self-attestation alone does not establish isolation. Admission may be checked now; do not perform substantive independent review or publish an ACCEPT verdict unless the launch requirement is met. Otherwise report BLOCKED_INDEPENDENCE with nonsecret evidence and stop without consuming a review round. Prior durable review lineage is permitted; author-private transcript/solutions are not review authority.

The substantive reviewer is read-only: no source/docs edits, native finding closure, local code/tests, slots, supervisor, Lean/MCP, build, absorb, merge, or publication. A completed eligible review is filed as COMMENT anchored to the exact commit, with review_case_id, fresh request_id, reviewed_head, comparison_base, stable finding dispositions, causal justification for every blocker, FOLLOW_UP/SAFETY_ESCALATION sections, round count, remaining budget, mechanical limitations and `authorization_effect: none`. Read the exact review back before marking transport VERIFIED. Preserve historical claims; a changed head gets a new request, not an overwritten old claim.
