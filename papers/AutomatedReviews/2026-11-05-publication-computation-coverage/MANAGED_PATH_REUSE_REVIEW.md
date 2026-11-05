# Managed-path accepted-history reuse review

Recommendation: REUSE THE EXISTING COHERENT PORTABILITY REPAIR only after frozen-suite85890 is actually terminal. No new resolver or infrastructure design is needed. Do not merge the29-file citation/manuscript checkpoint wholesale. This is history/source/preimage review, not current execution acceptance.

## Authority and evidence boundary

First action checked publication-managed-path-reuse-review-r1.json: fresh=true, changed=[]. All source, reports and ledger comparisons used immutable Git objects at16fde9b08 and donor commits, avoiding transient seeds during the live suite. No candidate/primary/notebook/Git writes, project imports, tests, scientific evaluation, seeding, graph, DB/native/Lean/slot actions. Only assigned scratch reports/manifest written. A scratch-report command initially used workspace cwd and its git rev-parse failed before any report write; corrected repo cwd was used. No source observation relied on that failed call.

## Proven ancestry, preimages and missing repair

Original9edf7c8fa3a4495c0508615371a9240c5c5dae11 has parent ce194cdc4bf939b108c17edc9530a7f0a14565f9. Cherry-pick0b6012549428b3a5b40c3e51e0c8a787defaf812 has parent e7047b7aa75e753922bfad63daff66ae15fd90df. Their stable patch-id is identical1481393907e26602db029265c73bf56b93d365a5; all ten postimages are byte-identical. Later e340bf425756c0c69aa80b79e207d93a2f2ba61b (parent b92e8db5c326262a5259e7a51be6bb9f8752e75a) includes29 paths, many unrelated metadata/citation/constants/manuscript changes.

None of0b,9edf,e340 or437546236f1d18d871a8cdc2526bb6581f163a9d is an ancestor of16fde. Current target_files AST equals donor preimage, not repaired postimage; current cache invariant still uses parent walking. The managed docs and original managed closure rows are absent. No equivalent repair is integrated.

Nine of ten donor paths have exact current preimages or expected absence. The only divergence is tests/test_architecture_claims.py, whose sole changed existing function is the accepted stronger test_the_submission_gate_ignores_p2_advisories. Preserve that G4 test and append the donor ADR/path runtime test; do not replace the whole file. These preimages support normal reuse; no actual Git application was attempted.

## Smallest coherent reuse boundary

Reuse the complete ten-path0b package:

- docs/adrs/ADR-012-finding-lifecycle-routing-and-closure.md
- docs/superpowers/plans/2026-10-19-managed-worktree-paths.md
- docs/superpowers/specs/2026-10-19-managed-worktree-paths-design.md
- papers/AutomatedReviews/2026-10-19-managed-worktree-paths/SCOPED_REVIEW.md
- papers/AutomatedReviews/2026-10-19-managed-worktree-paths/infra.md
- scripts/orchestrate.py
- tests/test_architecture_claims.py
- tests/test_orchestrate.py
- tests/test_phase6i_wave1.py
- tests/test_workspace_resolver.py

This keeps the accepted source, regression controls, ADR clarification, design/plan/findings and independent managed SCOPED_REVIEW together. target_files removes one exact leading logical SK_EFT_Hawking/ prefix inside the existing parser and retains active-root canonical containment, actual-file existence, complete enumeration and stable dedup. Canonical sibling content cannot substitute for an absent active copy. Existing strongest-lane and concurrent-file grouping remain unchanged and tested. Refusal controls cover missing files, directories, bare basenames, foreign absolute paths, actual traversal, prefixed traversal, symlink escapes and other prefixes.

The cache invariant uses existing find_workspace for shared files and keeps SK_ROOT/docs/primary_sources_state.json active-checkout-local. Full registry iteration, null handling, nonempty condition and success-only tolerated sync drift remain; missing/empty without success still fails. Controls call the actual invariant over good-plus-bad populations and opposing active/canonical state. src/core/workspace.py is byte-identical current/donor/e340 and needs no change.

Include the accepted43754623 slow-extractor isolation. It is NOT currently present at16fde. Independent reconstruction proves e340's entire tests/test_phase6i_wave1.py equals0b's postimage with ONLY the complete43754623 test_extract_missing_bibkeys_emits_no_orphans function substituted. The already accepted e340 phase postimage therefore supplies this exact coherent composition, without unrelated files. It retains slow marker, ext.main, rc and zero-stub/zero-orphan assertions while writing tmp_path/missing_stubs.json, avoiding overwrite/unlink of a repository artifact. Preserve any existing docs/.test_missing_stubs.json; no cleanup deletion is authorized.

0b's design/plan/finding have known historical pending-review wording subsequently corrected in e340. Reuse those corrections or clearly label donor October19/25 history while keeping current integration/Verify/closure status separate. Do not relabel e340's historical closures as current execution proof.

## Accepted historical review and canonical closure boundary

Read exact tracked managed infra/design/plan/SCOPED_REVIEW and e340 docs/audits/2026-10-25-njl-qualification-dependencies/{SCOPED_REVIEW,CHECKPOINT_REVIEW,README}. The managed independent review accepts source/control composition: original two old-red/fixed-green identities;96 path controls;12 cache controls; twelve production-poison/restoration outcomes; initial broader106pass/1fail/1default-slow-deselection retaining a distinct missing-citation failure. These are attributed historical receipts, not tests rerun here; detailed original streams were in ignored evidence and were not independently revalidated by this Git-only review.

The independent whole24 review verifies nine portability files exact plus the exact donor/437 phase-file composition. Its later six-module221pass/1existing-skip depends also on separate citation/ratchet repair; it is not permission to transplant those unrelated changes. The focused checkpoint review preserves scientific/source MAJOR R1 and physical BUILDs.

Exactly two e340 canonical closure rows exist;16fde has neither:

- review:2026-10-19-managed-worktree-paths:infra:1.1
  Declared/enforced: python -B -m pytest -q -p no:cacheprovider tests/test_orchestrate.py
  October25 exit0/enforced=true; README attributes47pass.
- review:2026-10-19-managed-worktree-paths:infra:1.2
  Declared/enforced: python -B -m pytest -q -p no:cacheprovider tests/test_phase6i_wave1.py tests/test_workspace_resolver.py
  October25 exit0/enforced=true; README attributes33pass/1default-slow-deselection.

Both cite docs/audits/2026-10-25-njl-qualification-dependencies/SCOPED_REVIEW.md and retain full merge/science duties. Never replace the current whole ledger with e340's old ledger: preserve later L1/IMPORTS/namespace/other history. Preserve original finding IDs/dates/evidence. For current adoption use the existing writer after actual current declared commands pass, citing donor and current independent integration evidence. Any imported historical row must retain a resolvable review and historical verified_by timestamps. Target-only success cannot close1.2 while its whole declared Verify is red.

## Next safe action after actual85890 terminal

1. ROOT obtains actual terminal result and preserves frozen16fde source/raw/JUnit/failure identities; confirms seed journal restored/quiet. No completion or permission to interrupt is inferred here.
2. Reconcile actual candidate owners/Git state, then apply0b's coherent package through normal Git, preserving stronger G4 test. Compose the exact already accepted e340/437 phase file and corrected historical doc wording. Inspect final diff and conservation of unrelated scientific, IMPORTS/gate, index and ledger bytes.
3. Prepared runtime, no dependency sync/install; verify candidate import origins. Run original prefixed target identity and complete tests/test_orchestrate.py, tests/test_phase6i_wave1.py, tests/test_workspace_resolver.py plus existing ADR architecture runtime pin/full affected four-file scope. Preserve canonical/managed active-copy, containment/existence/multiplicity/lane/refusal and missing/empty/state-root controls. Explicitly include slow extractor once only after tmp_path isolation. Historical counts are provenance, not current expected totals.
4. Independent whole source/control/evidence composition acceptance, canonical derived writers for actual changes, checkpoint and existing closure writer/protected delivery. Preserve unrelated red identities; no raised ceilings, forged cache success or dropped assertions.

The frozen4b disposition explicitly routes its single managed_path failure to this existing repair. It separately records test_no_missing_from_registry failing for13 missing cited keys. Path repair does not fix that citation obligation, so current full Phase6i/closure1.2 may remain red pending independently accepted citation work. Do not import unrelated e340 manuscripts/citations merely to green the test. File presence does not establish full text, scientific fidelity/acquisition or full-cache acceptance.

No present85890 outcome,37/remaining frozen4b failures, physical BUILDs, SOURCE137, main/full/native/security/human/publication obligation is discharged.

## Exact immutable base and source hashes

Current base: 16fde9b0803019d55d0b10250fed52e6258c1d42

- docs/adrs/ADR-012-finding-lifecycle-routing-and-closure.md; current 6d2a161af13926745d1b17cd9c53065f95667198d53c641a4cdeeffcc1922005; donor 85324638f59548e2ef8b85d8f0dbe663b53b51ccb8592a45fb5a28fe14e3a3c8; e340 85324638f59548e2ef8b85d8f0dbe663b53b51ccb8592a45fb5a28fe14e3a3c8
- docs/superpowers/plans/2026-10-19-managed-worktree-paths.md; current None; donor a6ae81ca87355f3968e9f523d6e7a8da389a5ac4e3af8bf49062af66c6bf2fc2; e340 d6eaf607cc773fbd9e6aa2005261c35aae75ae338effb5b4864225d18005a10d
- docs/superpowers/specs/2026-10-19-managed-worktree-paths-design.md; current None; donor c1743620a9bfc8a44aef652427a97f3a7a48a38e45b5bcedbfa65af314fce2ed; e340 bf79b7d1acccc97fc58cb6c70e23dfd947723f9a6a4a982ace3f5a397e6f5a06
- papers/AutomatedReviews/2026-10-19-managed-worktree-paths/SCOPED_REVIEW.md; current None; donor 78af0d59b8d0a70bdfe47f1191a87a5384eef38729e6a3920774f674c4062a8f; e340 78af0d59b8d0a70bdfe47f1191a87a5384eef38729e6a3920774f674c4062a8f
- papers/AutomatedReviews/2026-10-19-managed-worktree-paths/infra.md; current None; donor 2c53b9565ab59aa6297fed2346782a173cd06565f8a18e0bbf0825de0b7b74db; e340 efbbe0ad4e48c59e937799e8c9775cb86805dc05cbb781fe5fbe28a8a4e7bf50
- scripts/orchestrate.py; current 4aa821b1d6634240cad2fe9ef3e724a3b3890e6f2e66a55d358cd7bf02ecd3d6; donor b5f44d3ee4b75b48a107844417cef56b8b1a39abd88ea3885d3059db21a6a39f; e340 b5f44d3ee4b75b48a107844417cef56b8b1a39abd88ea3885d3059db21a6a39f
- tests/test_architecture_claims.py; current a35e41158751bf8fab5d3f5ad92e47e510d3e248f3782cd821bc7bda1b7ffe34; donor d6b971c6ebe158cfd44ec1b44aca0fd3437f6777244952a881f52ce366abab6d; e340 d6b971c6ebe158cfd44ec1b44aca0fd3437f6777244952a881f52ce366abab6d
- tests/test_orchestrate.py; current 6ba127a591e4e64b0b79f67c73ffb68bc6fdabfede49e91c04c8e4479b730c20; donor d2ef209645077b5362d124b004fb4de72ff5e99a840f372c5c8b0144ceaff324; e340 d2ef209645077b5362d124b004fb4de72ff5e99a840f372c5c8b0144ceaff324
- tests/test_phase6i_wave1.py; current 997e53abaf13b038de620c03376510e054484e458fb8489189cf367e96ef9b91; donor 83b6744806071825033d5ece05fed987722fd2405f209446d779d136f25a9546; e340 37a70787f4e1cfe2084d97805edfc45f43192f19fb123a7eec85c1cedb3fbf1d
- tests/test_workspace_resolver.py; current 402adae1880cc57ceb70e5bfc76e42e6e63051c553b231fec1f1b249408f2699; donor c93bb654a520b66bbc31a152dac5dd79b6ef9477574d2f1afe388e9a3a75276a; e340 c93bb654a520b66bbc31a152dac5dd79b6ef9477574d2f1afe388e9a3a75276a
