# Whole module-ID implementation review — 2026-10-25

## Decision

**The implemented resolver/test/down-only-bound composition and retained production controls are ACCEPTED at their bounded source/control scope. One MAJOR orchestration integration finding I1 remains mandatory.** Whole-change delivery qualification, canonical closure and checkpoint acceptance remain pending I1 and the already-required broader qualification. No new runtime resolver defect was found in the reviewed seven-path composition.

This is independent report-only review. ROOT owns all candidate source, tests, notebook and ledger. I ran no test, project import/evaluator, seed, writer, closure, native/Lean/PG operation or Git mutation. Only this ignored B report was written. K remained frozen. The original proposal review1920ba62 and accepted correction readback4410a6b3 were reused and hash-checked exact; their original scientific and refusal obligations were not reduced.

## Mandatory I1 — MAJOR: existing scoped verification does not route the check on its real inputs

**Location:** scripts/verify_scope.py::_plan, particularly papers scope at139–169 and Lean scope at170–186; tests/test_chain_canonicalize.py for the bounded regression contract. Current CHAIN_RESOLUTION_SPEC.md:118–124 correctly leaves this observation open.

ROOT's actual registration probe returned1 for the missing verify_scope mapping. This is not merely the probe's string-membership heuristic: personally reading the complete `_plan` shows that a papers-only claims-review edit runs bundle checks without chain_backing_targets_resolve, and a Lean-input change also omits that check. A chain target or module membership can therefore change while scoped verification never invokes this existing guard. Code/test edits happen to trigger a fast suite; that does not cover the papers-only input case.

**Exact minimal repair:** in the existing `_plan`, invoke the existing chain_backing_targets_resolve check once when either the existing papers scope or existing Lean scope is touched. Use its existing validate.py command with fresh/no-memo measurement; do not add a resolver, gate, registration type, command interface or exemption. Preserve every existing step and the existing Lean-build classification. The actual derived index is `lean/lean_deps.json`, which is in the existing Lean scope; `docs/lean_deps.json` does not exist and must not become a dead mapping.

Add focused production `_plan` argv assertions in the already-selected tests/test_chain_canonicalize.py: a claims-review path, a real Lean-source-shaped path, exact `lean/lean_deps.json`, an unrelated negative input, and mixed positives invoking this check exactly once. These inspect the real plan without launching its commands. Preserve existing build and count requirements; no routing optimization or new test file is necessary. Run the affected scopes and registration probe after repair with retained actual raw receipts, then obtain bounded derivative review before treating I1 as resolved. Adding the name to a comment would satisfy the lexical probe but would not repair this defect.

**Optional rows:** no cannot-measure PASS-baseline addition is justified. That file freezes exceptions which return PASS when input cannot be measured; this check already returns FAIL/measured=false on graph/import failure, with an existing refusal test. Adding it would invent a new exemption. The sync-edge row is inapplicable: this check reads/canonicalizes and does not own a derived artifact writer. The diagnostic reader's ignored output is not a production sync artifact. Existing registry order/export/mutation obligations and numeric floors need no count change because no check was added or removed. The probe must not be called passing until its required routing omission is actually repaired.

## Source implementation and complete test contract

Read the entire actual diff, complete changed test module, original finding/spec, accepted normative owner and relevant complete lookup/canonicalizer/edge/check behavior. Independent AST comparison with HEAD finds only `_module_id_for_ref` and `extract_backed_by_edges` changed among build_graph's functions, and only canonicalize_link changed in its module. The declaration resolver, GraphIndex adapter and legacy branches remain unchanged. The check's substantive implementation is unchanged; its constant109→97 and explanatory comment are the only check-file changes.

The helper handles typed IDs before legacy annotation/suffix/namespace normalization, strips outer whitespace and accepts only exact membership. The canonicalizer terminates the typed branch before both declaration resolution and ambiguity suggestions. The graph edge producer similarly bypasses declaration lookup and preserves an unknown typed ID as a missing_target rather than prepending lean:. Thus known modules retain identity under unique or ambiguous declaration collisions; valid unknown/repeated-prefix/foreign-unknown IDs cannot rebind or become suggestions. Path-like targets retain INVALID in canonicalization and missing-target representation in graph output. A legitimate `_module` suffix is preserved on typed IDs. Legacy declaration-first behavior and unprefixed module forms remain intact.

The new50 parameterized cases use the actual shared helper, real GraphIndex methods over finite supplied data and actual BACKED_BY extraction. They test theorem and axiom links, positive/unknown/repeated/foreign/collision cases, the two real nonmembers, literal suffix preservation, whitespace, legacy module forms, declaration precedence and legacy ambiguity. The old fake-index tests are preserved; they are not substituted for production tests. The new cases live in the existing default-fast module selected by the finding's declared Verify. No old test or refusal is removed.

## Actual test evidence and provenance limits

Read TEST_FIRST.json, REPAIRED_CHAIN_TESTS.json, the retained test-first and repaired-chain raw channels, and all failure identities/assertions. Independently checked their channel hashes. Actual before result: **30 failed/35 passed in0.16s**, exit1, October25 16:09:56–16:09:58 UTC. The failures include positive exact membership, unique declaration misbinding, ambiguous declaration suggestions and incorrect missing-target identity. Actual repaired complete chain module: **65 passed in0.09s**, exit0 at16:10:54 UTC. This is meaningful failing-before/passing-after evidence, not a test rewritten to duplicate the new resolver.

AFFECTED_TESTS.json records the actual larger session48740 command selecting the complete chain module, TestChainBackingTargetsResolve, build_graph and build_graph_memo under unchanged default markers: **155 passed, one skipped,15 deselected in107.76s**, exit0. ROOT identifies actual terminal tool chunk8090b5 and faithfully records its summary. No complete affected stdout/stderr/JUnit artifact was saved, so this is ROOT session evidence, not an independently inspectable raw replay. The15 deselections are retained and it is not an unfiltered full-module/full-project pass. Likewise registration rc1 is ROOT session chunkc0b7f7, not a retained raw registration artifact. The source routing omission independently corroborates its required failure.

These provenance limits are explicit, not retrospective fabrication. They do not invalidate the independently retained core TDD and production control evidence. Before closure/delivery qualification, retain full raw channels for the already-owed current broader run and the I1 follow-up. This review does not demand an unnecessary repeat of session48740 while the source is frozen.

## Full population and graph conservation

Independently compared all complete old/current/restored population snapshots. Every one of the2,313 canonical source-link identity tuples remains in exact order. The before/current unresolved totals are111→97. Exactly14 captured canonical results change, all the original positive module pilot occurrences, from UNRESOLVABLE to their exact module IDs with no suggestions. No unrelated captured result changes. The eight module identities are existing container nodes, not newly constructed mathematical or physical results.

All49 claims-review JSON hash maps are identical across the three snapshots and match current files. The built index remains SHA-256 e8d769f0e28e2c9357328604c163069a773fbb32d1de5f35ecb5cf52471c306e. The measured current population snapshot at16:13:28 precedes the constant change: its check-source hash is the old109 image, while later controls/restored snapshots carry the97 image. Thus the bound was lowered after measuring the repayment. It is109→97, not111→97; the original population was already two over its old bound.

All3,557 BACKED_BY edges are accounted for with multiplicity. Independent complete multiset comparison finds exactly16 removed/16 replacement edge records, identical to the complete recorded diff. Fourteen replace lean:module:... missing targets by the exact module:... resolved identity. The Python-path-like module and docs/counts.tex cases remove only the erroneous lean: wrapper and remain missing_target. Every replacement preserves source, type, link kind, computed_value and delta_pct; every other edge is unchanged. Those two targets are not silently accepted as Lean modules. Canonicalization still classifies the Python-shaped unknown UNRESOLVABLE and the path-like target INVALID.

## Real production faults and restoration

Read all control argv/UTC/exit records and complete raw channels; every recorded channel SHA matches. The saved old graph/canonicalizer source files independently equal HEAD f997's original bytes. The retained fresh reader asserts actual K import origins and invokes production GraphIndex, canonicalization and edge extraction; no pytest fake or conftest substitutes for this population reader.

The canonical production checker ran with --json --no-memo each time:

| Observation on October25 UTC | Exit / measured result |
| --- | --- |
|16:15:44–16:15:53 repaired baseline |0;2,313 links,97 unresolved at ceiling97; measured=true |
|16:15:54–16:16:03 actual old-source full population |111 unresolved;2,313 links and3,557 edges |
|16:16:03–16:16:12 actual old-source check |1;111>97, measured=true; intended unresolved leg RED |
|16:16:12–16:16:22 exact source restoration |0;97/97, measured=true |
|16:16:22–16:16:31 real unknown-module corpus fault |1;98>97 with2,313 links, measured=true |
|16:16:31–16:16:41 exact corpus restoration |0;97/97, measured=true |
|16:16:41–16:16:50 restored full population |97; all canonical results and edges equal the repaired snapshot |

The repeated stderr contains the same existing ambiguous-name warnings; it is not an import/derivation crash or a false unmeasured RED. Journal use and runtime restoration assertions are recorded in CONTROLS/ROOT's execution; I did not execute the controls myself. Independently, all4,889 before-controls tracked hashes match current files, current graph/canonicalizer/paper17 hashes, full modes33188 and nsmtimes exactly match the recorded restored states, and no journal mutation record remains. The before-tests manifest differs only by the two intentional production source corrections and later down-only constant. Every other tracked byte is conserved.

## Images, chronology and boundaries

The seven-path composition is three retained proposal/owner/finding documents, two production modules, one existing check constant/comment and the appended test fixture/cases. No src/Lean proof, scientific metadata, historical claims-review, ledger or original stub change appears against HEAD f997. QA owner remains the accepted4410 image. The specification truthfully records implementation/affected evidence, pending whole review/broad qualification and the failed registration probe. The frozen notebook r120 and dated recovery r74 are preserved; r74's live affected-session observation is superseded by the terminal AFFECTED record, not a new runtime admission.

Key current sources:

- build_graph.py: dc70097408cfc3933f165570796064536f88d4d5316489de3273cf37f3bd6017.
- chain_canonicalize.py: c440534ed3d56f86f918c5e3b215854ff22bcdcea0665c22d33141a9d5ac2126.
- reviews.py:41ac903e29564b10b58b4abf5a3c74ec2fc33bda0b4f7af366db6afa07345908.
- test_chain_canonicalize.py:2abd601ea2916af1ea607ad8d9fee01197bfb1d70cae7a43ad7602d65d468d3d.

Evidence bindings: CONTROLS b9d8e6fee41e4db070d01af1575ae8c48f7a15f4c579126ae618a3cef940bb58; AFFECTED_TESTS2d5d9764fb49c31282488b237e8de009074f5c62c0fdef08dfd9a3b9174e645c; old population b4464003f9e2636a1646c060c5f54cce9d994bfec6cda31e1b9ef126ec059ae8; current population afe0981bb16dbf240289f9c0a9b79653cf6f0644012a6f04ee2f6d3b31fc4881; restored population654ba691ba00fadbb774d67b5c025320c15390e2f1c2121521ad66f53d279004.

I1 must be repaired and actually requalified. Broad fast with full raw receipts, any required existing count synchronization, subsequent independent evidence reconciliation and the exact declared canonical closure remain owed. This report grants no closure or checkpoint authority by itself. Full CI/main/native-resource and publication gates remain separate. The inherited MAJOR scientific R1 and all original21-bundle physical BUILDs, ADW/KV scientific claims and operator/human decisions remain open. Resolving existing containers does not establish scientific truth or mathematical absence.

## Supplemental actual routing baseline

After the source review, ROOT supplied a separate ignored read-only planner receipt without changing any frozen input. Read its complete argv, current source SHA, UTC/rc and raw channels. At16:33:57 UTC the real `_plan` returns zero chain-check invocations for each of the claims-only, Lean-source-only, exact lean/lean_deps.json-only and mixed claims/index cases, where one is required; unrelated docs correctly returns zero. The child exits1 with empty stderr. No generated plan command/build was executed. This independently inspectable actual baseline corroborates I1 and is not a repaired or passing registration receipt.

Supplemental BASELINE.json SHA c09c0da3fd185c0c5769701ae1fcc80d33c9345fa0ac6ab3b7d445833cc12f84; stdout b8000a6445cbe41aa7d5a5b2ce8441ae81edb2988a02e992e29752dda05583c9. Its verify_scope source SHA66977a6dac44920ad7ced3a193f854a46e9676098f2d70cb75d2df8c953d0795 matches current K. This supplemental evidence was read without refreshing the original review packet.

## FIRST / FINAL

Actual literal FIRST from B used prepared P Python -B with the original publication-module-id-whole-review-20261025-r1.json adapter: rc0, fresh=true, changed=[]. All pinned authorities independently hash-match during review. No snapshot was refreshed. The same original command/packet is checked after this report; its actual result is appended below.

Actual FINAL used the exact original FIRST command/packet from B: rc1, fresh=false, changed=["owned-files"] only. This is the expected assigned report creation; no source, authority, pinned evidence, notebook, index or other checkout discrepancy was reported. No snapshot was refreshed. ROOT must inspect the complete report; the source/control review boundary is released with mandatory I1 and broader qualification still open.
