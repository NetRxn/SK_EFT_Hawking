# Module-ID proposal P1–P3 readback — 2026-10-25

## Decision

**ACCEPTED as the corrected bounded proposal, before implementation. P1–P3 are addressed; no remaining mandatory documentary/design correction was found.** This releases the proposal barrier for ROOT's existing authorized Python repair process after ROOT reads this report. It does not accept an implementation, new tests, a measured population reduction, ratchet change, finding closure, main integration or scientific/publication result.

Read notebook r120 and all three revised documents in full: CHAIN_RESOLUTION_SPEC.md, the canonical module-reference infra finding and the complete QA owner. Reconciled them against the complete original review, SHA-256 `1920ba62af6a2166bed6d4cf88004461e1426de00c7e99042da8a1ade32c5c38`, which remains byte-exact. ROOT remains the sole source/notebook writer; this reviewer owns only this ignored B report. No project import, evaluator, test, seed, writer, native/Lean/PG operation, closure or Git mutation was performed.

## P1 correction

The revised scope explicitly permits typed-ID dispatch and refusal in the existing build_graph and chain_canonicalize functions, including the BACKED_BY producer and canonicalizer/adapter. It no longer restricts the implementation to the two helpers while leaving declaration suggestions reachable. The required behavior is now unambiguous:

- Strip only outer whitespace from an already typed module ID, retain exact identity and require membership in the current module-node set.
- Apply legacy suffix/annotation/namespace compatibility normalization only to unprefixed forms.
- A known typed module ID remains that module even when declarations share its last component.
- Valid unknown, repeated-prefix and foreign-unknown typed IDs remain UNRESOLVABLE, with neither declaration resolution nor declaration suggestions. Malformed path-like references may retain INVALID.
- Preserve existing unprefixed declaration/full-name/short-name/ambiguity and module behavior, historical source and scientific meanings.

The revised test-first plan requires the actual shared helper, production GraphIndex adapter and BACKED_BY extractor in tests/test_chain_canonicalize.py. It explicitly includes positive membership, unique/ambiguous declaration collisions, unknown/repeated/foreign IDs, both current nonmembers, legacy forms and actual missing_target/no-retarget/no-suggestion assertions. It forbids substituting a corrected fake resolver. Essential edge cases live in the selected default-fast module rather than the slow EdgeIntegrity class, so the unchanged declared Verify includes them. Both actual consumers and all existing chain-check controls remain required.

This corrects the demonstrated SUGGESTED escape in the design. It does not assert that current production code already implements the new contract. That code remains unchanged and the planned failing-before observations are still owed.

## P2 correction

The specification now gives the actual separate anchors and times: the2,313/111 canonical diagnostic at df42dc90,15:41:36 UTC; the16-ID pilot at f997cff0,15:48:09 UTC. It explicitly preserves both immutable receipts and explains that the earlier population carries forward through byte-identical53 inputs, rather than becoming a newly dated run. The all49 claims-review files, graph implementation, canonicalizer, current check and index qualification matches the independent static verification recorded in the original review.

The original diagnostic and pilot are unchanged. No rerun, replacement receipt or fabricated timestamp was introduced by the documentary correction. The14 positive occurrences/eight distinct module identities and two nonmembers retain their original scope.111→97 remains explicitly a prediction pending implementation and whole-population measurement.

## P3 correction

The QA owner now defines theorem-absent as failure of the current index/resolution path, with source, semantic/LSP, branch, import and built-dependency reconciliation required before asserting substrate absence. Its ambiguity paragraph correctly says SUGGESTED results do not contribute to this particular UNRESOLVABLE counter. The exact-membership typed-ID contract remains normative and count-free. The complete HEAD diff is confined to these intended claim-lineage paragraphs; the rest of the owner document is conserved.

The correction is consistent with the current code's status classification and the original positive-membership pilot. It introduces no new graph type, resolver, gate, registry or ADR and makes no global Lean-absence claim.

## Preservation and acceptance conditions

Compared the current authority hashes against the original proposal packet. Exactly the three intended documentary authorities differ; all previously pinned production code, tests, diagnostic REPORT, explicit module pilot and other authorities are unchanged. K HEAD remains `f997cff002b5a02379c6c0f86d7975f82af8db71`. Read-only Git enumeration shows only the QA owner modification and the two new proposal/finding documents, apart from the conserved preexisting stub. No scripts, tests, src or Lean diff exists. The ceiling is unchanged; no ledger closure has been appended by this derivative.

Current accepted documentary images:

| Path | SHA-256 |
| --- | --- |
| docs/audits/2026-10-25-njl-qualification-dependencies/CHAIN_RESOLUTION_SPEC.md | df9bae599d9d3ed9958a72ecd44604dbda8a86cb523432ab2847086998b06e6e |
| papers/AutomatedReviews/2026-10-25-njl-module-reference-resolution/infra.md | 23469594a3a1ac28fc37ab84043f9b7b130ed7c8c53c25dc1914cd40c7c85d5e |
| docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md | 672d3c18145fcd1e3be398e564cd66a4be503243139cdc4394cde1ed803ef49f |

The original stub remains SHA-256 `0891b617824dd9865905de2f87d2dc8cb1952186de1da69ffba423d872daae6c`, mtime_ns1792434225809712977. Notebook r120 is the issued current authority; no runtime/native/resource grant is inferred from it.

The full original acceptance remains: test-first actual failures; minimal shared-helper/caller repair; both consumer observations; complete affected tests and prior refusal controls; exact historical claims/scientific source/index conservation; complete unchanged link-population and status/target accounting before any earned down-only ceiling; serialized existing-journal actual production fault and exact bytes/fullmode/nsmtime restoration to a green baseline; retained raw receipts; configured broad fast qualification with every remaining failure disclosed; existing count writer if needed; independent complete source/current-evidence review before a supported canonical closure and ordinary checkpoint. This readback waives none of those steps.

All original21-bundle scientific BUILDs, inherited MAJOR R1 propagation, operator decisions/holds, full CI/current admission, main integration and final human publication review remain open. Container resolution supplies no cosmological calibration, vacuum-magnitude derivation, theorem-claim acceptance or ADW/KV closure. The separate56-command enabling work remains outside this review.

## FIRST / FINAL

The literal FIRST action from B used P's prepared Python with -B and scripts/codex_continuity.py check against the original publication-njl-module-id-proposal-readback-20261025-r1.json packet. Actual FIRST: rc0, fresh=true, changed=[]. No packet was refreshed. The same original check is run after writing this report; its actual result is appended below.

Actual FINAL used that exact original command and packet from B: rc1, fresh=false, changed=["owned-files"] only. This is the expected assigned report creation; no source, authority, original evidence/review, notebook, index or other checkout discrepancy was reported. No snapshot was refreshed. ROOT must inspect the completed report before proceeding; corrected-proposal acceptance is released at this conservation boundary.
