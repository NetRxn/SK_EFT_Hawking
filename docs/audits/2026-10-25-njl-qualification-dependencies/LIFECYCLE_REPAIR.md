# Lifecycle vocabulary repair — October 25

D6, D8 and D10 require fresh Stage-10 qualification after their redrafts. Their
metadata now uses the existing `pending-redo` lifecycle value instead of the
undeclared values `redrafted`, `redrafted-2026-08-15` and
`redrafted-2026-08-17`, respectively. This records pending work; it supplies no
review verdict and closes no scientific finding.

## Authority and conservation

The existing `scripts/bundle_readiness.py` stage enum and
`bundle_reviewer_stage_ordering` check declare this value. The historical D7
correction at `8d22af19c91985789ce59389a9f49809b413bcd1` independently shows the
existing vocabulary repair; its unrelated compiled-pages change was not copied.
`record_review.py` records actual reviewer verdicts and was not invoked to
fabricate a new review. All three historical Stage-10 dates, notes, source
references, other stage values, key order and theorem rosters are conserved.
The existing `bundle_json.write_bundle_json` is the writer. Inverting just the
three changed strings restores each complete original byte image; repeated
writing is byte-idempotent. No enum, test, predicate, gate, ceiling, floor or
scientific source was changed.

Original findings remain at
[papers/AutomatedReviews/2026-08-15-d6-stage10-redraft/D6.md](../../../papers/AutomatedReviews/2026-08-15-d6-stage10-redraft/D6.md),
[papers/AutomatedReviews/2026-08-15-d8-stage10-redraft/D8.md](../../../papers/AutomatedReviews/2026-08-15-d8-stage10-redraft/D8.md) and
[papers/AutomatedReviews/2026-08-17-d10-stage10-redraft/D10.md](../../../papers/AutomatedReviews/2026-08-17-d10-stage10-redraft/D10.md).
Their substantive acceptance requirements and operator decisions remain owed.

## Actual verification

At `df42dc907c78b209ff716faae781888662f0c1f3` before the repair, the complete
`TestUnmeasuredIsDistinctFromYellow` class reports one failure and two passes;
the failure names exactly the three undeclared values. The existing no-memo
`bundle_reviewer_stage_ordering` check also fails on exactly those values.
After the repair, this command reports **82 passed, one existing skip**:

```sh
.venv/bin/python -B -m pytest tests/test_d5_bundles_readiness.py::TestUnmeasuredIsDistinctFromYellow tests/test_d5_bundles_readiness.py::TestBundleReviewerStageOrdering tests/test_bundle_json_serializer.py tests/test_record_review.py -q
```

The unchanged ordering fixtures include actual green-after-prerequisites,
either missing prerequisite, typo, missing metadata and empty-population controls.
The canonical no-memo check reports measured=true, passed=true, 21 bundles
checked and zero ordering violations. Every tracked byte outside the three
metadata files was conserved during the run.

Raw argv, UTC, return codes, stdout/stderr and original metadata images remain
in `outputs/continuity/NJL-stage-vocabulary-20261025-r1/`. REPORT.json SHA-256:
`2f89f071d3bc801d603394214bd9915b32d11e9d6989b2fabca86c5117e2f9de`. The existing skip is the serializer suite's non-bundle compile-cache
writer case. The documentation here was written after the test run.

One of the 17 source failure identities in the preceding broad run now passes.
The other 16 identities have not been rerun since this narrow metadata repair.
The original broad 23-failure record and six passing environmental reruns remain
immutable in FAST_QUALIFICATION.json. Full CI/main qualification, inherited
MAJOR R1 and all original scientific BUILDs remain open. No newly green bundle
or refreshed 231-gate portfolio is claimed.
