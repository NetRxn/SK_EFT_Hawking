# Independent namespace-guard implementation review

ACCEPT the narrow implementation and supplied scoped verification. No actionable code discrepancy found. This acceptance is of the existing dependency guard repair, new meaningful regression/production controls and source composition; it does not assert canonical closure, full qualification, main merge, publication acceptance or physical closure.

Initial publication-l1-namespace-implementation-review-r1 continuity check returned fresh/changed=[]. Actual tests/test_dependency_declaration.py hash is43e91d0d16fae8cc4b2d12d1015f10f467b589230d7554d838afbcb760441785, matching the packet. Reviewed actual tracked test/architecture/counts diffs, accepted ADR/spec/plan and supplied red/after/counts receipts. Reviewer owns only this scratch report; ROOT remains candidate/notebook writer, with other scientific work left untouched.

## Actual implementation versus accepted intent

The production helper change is exactly the accepted three lines: derive p.relative_to(REPO).parts; if nested and identifier-valued first component, add that component. It uses the existing pruned _walk_py and preserves all old stem/parent behavior. Root files keep stem handling; no fake dependency, import execution, hardcoded papers exception or scope/exclusion relaxation is introduced.

Independent stdlib AST comparison removed precisely this addition and proved the ENTIRE previous test file AST otherwise unchanged before the appended new helpers/fixtures/tests. Original declaration assertion, aliases, UNDECLARABLE policy, scan roots, skip rules, third-party resolution and previous tests remain intact. tests/test_gravitational_waves.py is byte-identical to HEAD, including actual papers.D3.tables import and exact natural/(4*cap) comparison at rel=3e-16/abs=0.0. No scientific regression was substituted or weakened.

The nested fixture tests a namespace/deep/producer.py without root __init__.py, root ordinary.py, data-only directory and pruned node_modules tree. It asserts the desired namespace/root module are local and all chosen unrelated/pruned names remain absent. It meaningfully detects the old mechanism: /tmp/l1-namespace-red.txt records the test failing specifically because namespace is missing,1failed0.04s before the helper repair.

The production seed targets the actual tests/test_gravitational_waves.py read by the guard. It appends a syntactically valid absent sentinel import via existing scripts.seed_journal.seeded_mutation, measures sentinel membership in real third_party_imports and calls the actual test_every_third_party_import_is_declared under pytest.raises matching that sentinel. Baseline and restored actual assertions both pass in the supplied suite. The scientific module/sentinel is not imported or executed by this scanner test. A future accidental local/declaration exemption of the sentinel would fail its expected rejection rather than silently weakening coverage.

## Cache and restoration discipline

Both lru caches are cleared by _clear_import_caches. The real production test clears before baseline, before seeded measurement and immediately after journal restoration. Its fresh_import_caches dependency also clears at pytest teardown, including after an ordinary assertion failure. The namespace fixture uses monkeypatch.context to restore REPO before its post-yield clear; the outer fresh_import_caches fixture provides final cleanup after dependent fixture teardown. Thus normal test failures cannot leak fixture or seeded cached names into later tests.

Actual source restoration uses the journal context, not a bare finally artifact restore. Existing seeded_mutation writes durable restoration evidence before the target write and restores original bytes/mtime by default. The new test explicitly checks bytes and st_mtime_ns equal their captured originals after context exit, verifies sentinel absent, then rechecks the actual production assertion. Its cache cleanup and journal restoration are distinct mechanisms with the appropriate responsibilities. No additional concurrent production seeding was performed by reviewer; ROOT's supplied receipt is sufficient for this tested scope.

## Verification, collection and documentation

/tmp/l1-namespace-after.txt records116passed13.06s for seven dependency cases,81 GW cases and28 seed guards as dispatched. This is direct supplied runtime evidence, not a new reviewer rerun; I performed no tests, mutation, graph/DB/native/Lean action. It qualifies those cases, not the prior broad failure population. Current real scientific file being byte-identical to HEAD additionally confirms no surviving source seed.

The added architecture paragraph accurately describes local namespace classification within the existing pytest guard and explicitly denies registered-validate-check status. Existing pytest collection is preserved. The earlier generic registration_sites output does not require manufacturing scripts/validation/checks registration, canonical-order/re-export state, new gate or registry. Existing exclusion and declaration policy remain the mechanism.

/tmp/l1-namespace-counts.txt records the existing writer regenerated counts. Independent JSON comparison confirms the only counts.json changes are generated timestamp and pytest_cases7005to7007, exactly the two new unparametrized tests. counts.tex mirrors that change; Lean/other populations are untouched. No manual check-floor or unrelated registry alteration is present.

ADR/spec/plan currently remain proposed pending implementation acceptance and canonical closure. ROOT can now record this independent acceptance, run any remaining required freshness/closure verification through existing writers, and update the same finding/queue/checkpoint. Infra1.4 closure must preserve its actual Verify evidence and scope; no merge/main or broader scientific qualification follows merely from this review. Existing broad local stem/parent heuristic limitations remain as documented, without expanding this repair into a complete Python resolver.

Reviewer wrote only /tmp/l1-namespace-implementation-review.md. No candidate/notebook/Git changes, production seeding, tests, graph generation, DB/native operation or Lean build. The other untracked scientific evaluator visible in shared status is outside this review and was not edited or assessed.
