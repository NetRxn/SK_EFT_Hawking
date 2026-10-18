# Extractor cache serialization implementation plan

Root owns this bounded infra package under the existing required finding and remediation planner. No proof statements, dependency pins, runtime limits, canonical writer or cache readers change. Independent reviewers remain read-only. Mathematical round acceptance remains pending.

1. Localize first-cache failure and retain original --run evidence plus byte-preserved primary inputs.
2. Independently review ADR-005 D-G.3 and the matching design, including source pin invalidation and reader semantics.
3. Pilot compact serialization against the actual cache corpus, with redirected files and exact parsed-value and original-reader checks. Preserve raw child results; do not substitute #eval transport status for --run success.
4. Edit only the four persistence expressions in lean/SKEFTHawking/ExtractDeps.lean. Update ADR status and the cache mechanism in docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md with the same commit as the implementation. Retain this spec/plan with that commit.
5. Independently review the actual diff. Use controller integration/build and the normal wrapper for cold/warm canonical extraction. Reconcile all declaration changes and ordinary axiom sets against the accepted baseline, treating extractor self-changes separately.
6. Run existing extraction wrapper/scope tests and the owning round gate. Close the existing finding with its single writer, update the owning audit and notebook, and resume the reviewed growth targets after round acceptance.

Owned implementation paths: lean/SKEFTHawking/ExtractDeps.lean; docs/adrs/ADR-005-derived-proof-atlas.md; docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md; this plan and matching spec. The primary finding, canonical outputs, counts, closure ledger, aggregate builds and owning audit remain root integration paths. No new validation check or writer is introduced.
