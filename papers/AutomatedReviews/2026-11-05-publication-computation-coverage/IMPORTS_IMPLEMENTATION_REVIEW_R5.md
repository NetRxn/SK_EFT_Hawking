# IMPORTS implementation review — R5

Verdict: ACCEPT SCOPED IMPLEMENTATION. All I1-I4 defects are resolved at the exact hashes below. No remaining actionable defect was found within the accepted R2 bounded static-call contract. This is not science/main/native/publication acceptance or review of ROOT's independent scientific audit-path changes.

## Authority and frozen acceptance identity

First action checked publication-imports-implementation-review-r5.json from the assigned candidate: fresh=true, changed=[]. Candidate base HEAD26d2545c44b806fb2f417fcfc8b237cb33d490f4; implementation remains an uncommitted bounded repair.

- scripts/build_graph.py: df32bfede07cf4177d11017c7783177772fb8be5495d58a5036550cfba593ccb
- tests/test_build_graph.py: 522c6898ef8ce5e02400cd0b052ba970abd45b59f21575fc61e7772e4b87c35f
- docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md: 3e81f812a246519c8ce5eb57ae02322f94412b299b9ebb070cf8d28ce2d93626
- src/core/formulas.py unchanged: deaa9898b4463360d26479dd65014ae884d511391df17cbd86fe4b429b7a568e

Read accepted R2 design, actual source/test revisions, owning QA paragraph, all prior defect/evidence reports and current red/whole-module output. R1-R4 reports are preserved. Only review-owned /tmp artifacts were written.

## Contract and defect resolution

I1: comprehension target traversal visits evaluated subscript/attribute/unpacked-target expressions and shadows only Store-bound names. Actual load names in targets no longer create false shadows.

I2: compiler-only inlined-comprehension local/assignment flags are accepted as transient only with is_comp_iter, no annotation and no real function-body writers, after parameter/free/nonlocal/import exclusions. AST shadow stacks retain genuine per-comprehension scopes and first-iterable evaluation behavior.

I3: caller AST type-parameter names cannot use the module-global fallback merely because compiler comprehension bookkeeping masks their binding. Explicit legitimate local self-import handling remains earlier and is conserved.

I4: a compiler-declared read-only global overrides that spelling-only type-parameter exclusion; actual global writers remain rejected by the existing binding inventory. ROOT's current red records the exact positive failing before the correction, alongside its global-writer negative.

The complete producer continues to reuse structural public-definition eligibility; preserves source-read/parse/duplicate and compiler-scope diagnostics, literal self-import agreement/conflict rules, conservative module overrides, private/self/endpoint/dedup semantics; excludes attribute-tail matching/arbitrary variable aliases, nested callable/class bodies and deferred annotations/type aliases; visits ordinary eager nested defaults/decorators/class headers; explicitly refuses unsupported generic class headers. It remains a bounded static declaration-reference extractor. No parallel registry, new registered check/gate, runtime alias system, scientific formula mutation or whole-program analysis is introduced.

## Independent execution and current evidence

Prescribed shared environment used: UV_NO_SYNC=1, UV_OFFLINE=1, UV_CACHE_DIR=/tmp/l1-window-uv-cache, UV_PROJECT_ENVIRONMENT=/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.venv.

Reviewer actual command `uv run python -m pytest tests/test_build_graph.py::TestDirectFormulaImports -q -k 'not production_call_omission'` passes50 with1 deselected in0.38s. The canonical source mutation was excluded from reviewer execution to keep the review tree frozen. Reviewer independently executes24 candidate-origin-asserted source-data probes:24 match, zero failures, including every I1-I4 case, parameter/local/annotation/import/type-parameter negatives, self-import overrides, real global writer negatives, cross-comprehension preservation, evaluated targets and eager nested default/decorator positives. Scientific function bodies were not executed. Receipts: /tmp/l1-imports-review-r5-probes.py/.json.

ROOT's exact current whole-module raw receipt /tmp/l1-imports-r5-whole-module.txt reports130passed1skipped15deselected20.39s. Reviewer independently parsed /tmp/l1-imports-r5-whole-module.xml:131 executed cases, zero failures/errors, one skip; actual production_call_omission_with_text_decoy test appears exactly once and passes. XML SHA25617173216f3e0d46490518ad43e7abb50df466cd3bc097e9a12105c229d28d725. The production test runs the actual known-present assertions, changes the real mixed-case call with a retained spelling decoy, catches the intended assertion failure and verifies exact bytes/mtime restoration, restored assertions and node dictionaries. This is actual production-path evidence, not a fixture-only substitute. ROOT's current red before I4 correction is1fail39pass11deselected. No reviewer production mutation was performed.

Independent actual current extraction again confirms all436 complete Formula node dictionaries exactly equal the pre-change receipt; all93 old IMPORTS dictionaries conserved;109 total edges; exactly the independent pilot's16 new pairs; no other producer AST change outside extract_imports_edges/new stdlib symtable import. Source hash remains exact. Receipt /tmp/l1-imports-review-r5-composition.json. Dictionary-set comparison correctly avoids treating historical sorted receipt order as the edge identity contract; traversal remains deterministic. `git diff --check` passes.

## Documentation, registration and downstream applicability

Owning QA-map paragraph accurately describes the current bounded mechanism, diagnostics, exclusions and freshness/dashboard consumers while separating IMPORTS from G4/test evidence or physical derivation. Existing extractor registration_sites OWED rows do not mean a new validation check should be invented; no new check registration is owed. Canonical derived test-count regeneration is expected for genuine added tests and remains ROOT-owned. The existing controlled removal of exact16 edges from one R1 graph with zero recomputed freshness deltas is qualified correctly; current exact edge-set equivalence supports its relation-population applicability, without claiming a second full baseline build, new runtime evidence, database synchronization or G4 coverage.

Acceptance applies only to this producer/test/QA-map source and its bounded evidence. ROOT still owns canonical count/finding writers, final whole-composition/current-gate checks, closure/checkpoint and protected integration. Scientific evaluator/archive changes, remaining L1 scientific obligations, main/native/full/publication/human gates are separate. No candidate/Git/notebook changes, graph build, DB/native/Lean/slot action or scientific source-body execution by reviewer. Source-sensitive probes are finished.
