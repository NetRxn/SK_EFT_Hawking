# Module-ID proposal review — 2026-10-25 r1

## Decision

**REQUIRES THE SPECIFICATION CORRECTIONS P1–P3 BELOW before implementation.** The existing-bug diagnosis, original-goal alignment and choice to repair existing resolution under the established BACKED_BY/LeanModule contract are accepted. A new ADR, graph type, registry, gate, command or parallel resolver is unnecessary. This is proposal review only: no implementation, executed new test, ratchet change, scientific acceptance or finding closure is accepted here.

ROOT is the sole source/notebook writer. I wrote only this assigned ignored B report. No project import, evaluation, test, seed, writer, native/Lean/PG operation, closure or Git mutation was performed. A malformed read-only display script initially had a Python parenthesis syntax error; it read or changed no project state and was corrected for the subsequent static read.

## Mandatory corrections

### P1 — MAJOR: the two-helper-only scope cannot enforce the complete typed-ID contract

**Location:** CHAIN_RESOLUTION_SPEC.md:27–38,55–67,77–80; current chain_canonicalize.py:130–142,213–222; build_graph.py:288–321,3192–3204,3421–3432.

The proposal correctly forbids converting explicit module IDs into declarations, but its implementation scope names only build_graph's two existing lookup functions. That is insufficient. Even after `_resolve_lean_short` refuses a module-prefixed ID and `_module_id_for_ref` refuses an unknown module, `canonicalize_link` still calls `idx.lean_short_candidates(t)` at138. The production adapter independently takes the final dotted component and returns its declaration candidates at216–218. If the suffix has two declarations, the typed unknown is classified SUGGESTED rather than UNRESOLVABLE. The existing check at reviews.py:970 counts only UNRESOLVABLE, so that debt disappears from the ratchet without a valid module resolution. This is a static trace through actual source, not an executed new counterexample.

The unique-declaration collision is also real: the declaration-first lookup can return the unique unrelated suffix declaration before the module fallback. Both hazards must be fixed without altering legacy unprefixed declaration precedence.

**Required fix:** amend the scope to permit the minimal typed-ID dispatch/refusal in the existing canonicalizer/adapter and corresponding existing edge path, alongside the shared module lookup. A typed module target must reach exact known module membership and terminate as a module resolution or refusal; it must not enter either declaration resolution or declaration suggestions. Do not manipulate the short-name index or return a fabricated successful sentinel to avoid correcting the caller. This remains a repair of existing functions, not a second resolver.

Make normalization explicit: an already canonical typed ID retains its identity. Apply the old suffix/annotation/namespace compatibility rules to unprefixed legacy forms; do not let normalization strip a legitimate typed-ID suffix or manufacture membership in a different module. Unknown and repeated-prefix valid identifiers remain UNRESOLVABLE, even with one or multiple declaration-name collisions. Malformed path-like targets may retain INVALID; neither classification may become a resolved declaration or declaration suggestion. A known exact module ID wins its typed identity even when declarations share its last component.

Pin failing-before/passing-after controls through the actual shared helper, production GraphIndex adapter and actual BACKED_BY edge extractor. Include known typed membership with no collision and with one/multiple declaration collisions; unknown/repeated-prefix/foreign-unknown IDs with those collisions; the two current nonmember pilot IDs; legacy bare/nested/qualified/`X (module)`/`X_module` forms; and existing full/short/ambiguous declaration behavior. For refusal, assert no declaration retarget or suggestion and a graph missing_target edge rather than a fabricated resolved edge.

The current tests/test_chain_canonicalize.py FakeIndex reimplements the old module algorithm; fixing that fake alone would not test production. Define where the production edge controls will live, and ensure the finding's declared Verify actually executes those essential cases. They can live in the selected chain test module, or the Verify must add their real scope. Existing TestEdgeIntegrity is slow-marked, so the default fast suite alone cannot qualify newly added tests placed there. Preserve and run all existing chain-check refusal/empty/graph-unavailable/zero-headroom controls and complete affected scopes with explicit marker handling where needed.

### P2 — MINOR: the diagnostic and pilot have different recorded source anchors

**Location:** CHAIN_RESOLUTION_SPEC.md:16–24.

The text calls the2,313/111 canonical diagnostic an actual f997 measurement. The retained REPORT.json records `head=df42dc907c78b209ff716faae781888662f0c1f3`, UTC15:41:36.279344. The separate complete module pilot records `source_commit=f997cff002b5a02379c6c0f86d7975f82af8db71`, UTC15:48:09.152006. These are distinct receipts.

**Required fix:** preserve both immutable originals and state their actual chronology. Carry the earlier population forward only with the unchanged relevant-input qualification, not a relabelled run. I independently verified that all53 carrying files—the shared graph implementation, canonicalizer, current check, retained built index and all49 claims-review JSON files—are byte-identical from df42 to current f997. Thus a truthful documentary reconciliation is sufficient; this review does not require rerunning the diagnostic or fabricating a newer timestamp.

### P3 — MINOR: the modified normative owner still defines resolver classes as absence

**Location:** QA_QI_INFRASTRUCTURE_MAP.md:537–543,596–599.

Line537 says theorem-absent means the named Lean theorem does not exist, while the proposal's positive evidence demonstrates existing module targets misclassified by that same resolution machinery. Lines596–599 also say ambiguous short names are counted theorem-absent. Actual canonicalize_link returns SUGGESTED for multiple candidates; the current check counts only UNRESOLVABLE. These inherited statements are inaccurate in the very owner section being reconciled and obscure the P1 failure mode.

**Required fix:** narrowly define theorem-absent as failure of the current index/resolution path, requiring separate source/semantic/branch/import/built-dependency reconciliation before any absence assertion. State accurately that declaration ambiguity produces suggestions and is excluded from this particular unresolved counter. Retain the artifact/genuine-reference distinction and all scientific holds. No broad historical owner rewrite or policy change is required.

## Evidence personally checked

Read the entire specification and canonical finding, the full normative QA owner, the closed target schema, both actual resolution callers and shared functions, real GraphIndex adaptation, full canonicalize_link core, existing chain test module and complete affected TestChainBackingTargetsResolve class, and relevant production graph edge integrity tests/fixtures. The readiness check delegates to canonicalize_link; it owns no independent resolver. Its existing graph-unavailable and empty-corpus refusals must survive. The graph producer intentionally retains missing_target edges instead of silently dropping unresolved chains.

Read the complete diagnostic, including every one of111 unresolved records, and all16 pilot records. Independently enumerating the source JSON gives exactly2,313 theorem/axiom/lemma links and16 explicit module links; all16 tuples of paper/sentence/kind/target match the pilot. The14 positive occurrences are all in paper17 and span eight exact module names. Those eight module paths occur in the retained declaration index. The current source helper constructs a second namespace/prefix for a canonical `module:SKEFTHawking.X`, explaining the positive-membership failure. The pilot additionally reports exact current node membership. This is positive resolution evidence, not a theorem-absence inference.

The two nonmembers are `module:sk_eft.dark_sector.sfdm_merger_forecast` and `module:docs/counts.tex`. The former is reported UNRESOLVABLE; the path-like latter is INVALID and is not one of the111 counted unresolved links. Neither is authority to invent a LeanModule, infer missing physical code or rewrite the historical claims-review JSON. All14 positive pilot occurrences are members of the recorded111 unresolved records, so111→97 is a reasonable prediction, not a measured post-repair result.

Diagnostic REPORT SHA-256: `980868c913cd88ae085da40a97b79cf2eb7f9a98a166a9dd6726a072a24f5a05`.
Pilot SHA-256: `e29f0117d528284eb0aeb40ebfae41aba15da21ef7a2593cf731fc09be999052`.
Retained lean_deps SHA-256: `e8d769f0e28e2c9357328604c163069a773fbb32d1de5f35ecb5cf52471c306e`.
These are read-only diagnostic data; I did not replay their GraphIndex computation or execute proposed Verify commands.

## Accepted direction and required implementation evidence

The minimum coherent goal is to repay the existing NJL qualification dependency by correctly binding canonical container IDs already present in the built node set. A container's existence does not prove a historical sentence, calibrate cosmology, derive a vacuum magnitude or accept ADW/KV science. Preserve all historical claims-review bytes, verdicts, quotes, ratification metadata, metadata rosters, defaults, Lean/Python scientific bodies and index images.

The plan's before-implementation independent review, test-first failures, two-consumer agreement and down-only ratchet are appropriate once P1 is specified. Measure the whole unchanged source-link population and complete resulting status/target distribution before choosing a new ceiling. Preserve the original111/ceiling109 RED. Explain every changed resolution, including any change beyond the predicted14; do not obtain a smaller count by moving an unknown typed reference to SUGGESTED, omitting links, editing historical science or raising a bound. The actual new ceiling must be the earned measured value;97 is not yet accepted.

The existing journalled real production fault/restore requirement is retained. Start from a genuinely green repaired baseline; use a fresh source-bound reader and existing no-memo production check, observe the intended resolution/population RED, then restore exact bytes, full mode and nsmtime and observe GREEN with no mutation record. A monkeypatched seam test alone does not discharge that separate real-artifact control. No writer should regenerate the expected answer while mutated, and source mutation must remain serialized.

Require complete affected tests, actual graph-edge and canonical target observations, all prior refusal controls, original claims/source/index conservation and independent whole source/current-evidence review. Then run the configured broad fast suite, retain every failure and use the existing count writer if the test census changes. The new finding's declared command must genuinely include its essential production regression cases as specified above. Any eventual narrow infra closure remains after these acceptance steps through the existing canonical writer, not through report wording or an exit0 diagnostic alone.

All inherited MAJOR R1 propagation, original21-bundle physical BUILDs, operator holds, full CI/current resource admission, main integration and publication/human review remain open. No new scientific finding closure or green bundle follows from this proposal review. No new ADR is needed for using the already documented LeanModule target type.

## Source and continuity boundary

Actual FIRST from B used prepared P Python with -B and the original `publication-njl-module-id-proposal-review-20261025-r1.json` adapter: rc0, fresh=true, changed=[]. No snapshot was refreshed. Current K HEAD is f997cff0. Read-only Git scope is exactly the three draft documentation paths: new CHAIN_RESOLUTION_SPEC.md, new canonical infra finding and the QA owner edit; the protected preexisting stub remains separate. No production, test, ceiling, claims, scientific source or index change exists in this proposal.

Frozen draft hashes:

- CHAIN_RESOLUTION_SPEC.md: `63d4c0fc0b856f93009f23e08683a1eaa1e7be1c74d61b79013e046a6f129ec7`.
- Canonical infra finding: `1d52dc081680f931dcd2741c05ff7e5b7221fc8181e7d00d4de05dc118ca89e0`.
- QA owner: `909e584af6d0f47a732f16f44a1f43b3a163d4d46623215a6cafba3d8f22caa7`.

The stub remains SHA0891b617824dd9865905de2f87d2dc8cb1952186de1da69ffba423d872daae6c, mtime_ns1792434225809712977. Notebook r119 remains frozen. The original packet is checked after writing this report; the actual FINAL outcome is appended below.

Actual FINAL used the same prepared-P interpreter/original packet command from B: rc1, fresh=false, changed=["owned-files"] only. This is the expected assigned report creation; no source, authority, raw evidence, notebook, index or other checkout discrepancy was reported. No snapshot was refreshed. ROOT must inspect the full report and correct P1–P3 before implementation; the frozen review boundary is released here.
