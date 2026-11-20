# IMPORTS implementation review — R2

Verdict: CHANGES REQUIRED. R1's evaluated-target defect is repaired. One additional inlined-comprehension scope defect remains within the originally accepted contract; no design expansion is required.

First action checked publication-imports-implementation-review-r2.json: fresh=true, changed=[]. Actual frozen hashes: producer f069f5461438e057df3ac3457c8c5905379fb14199143d14dbd227506f96bf9d; tests df1f1249607d2b30d873e8ef41c2296eb1b9aa1657cc4f5efbc391a6ff5dc822; QA map3e81f812a246519c8ce5eb57ae02322f94412b299b9ebb070cf8d28ce2d93626. R1 report is preserved separately.

## Required correction — compiler comprehension artifacts must not leak between comprehensions

Actual candidate-origin producer misses caller -> Target for this valid source:

```python
def Target(): pass
def caller():
    [x for Target in items for x in others]
    return [Target() for x in items]
```

The first Target is confined to the first comprehension. The second comprehension calls module Target. Python3.14.7 symtable reports the enclosing Target symbol is_local=True, is_assigned=True, is_comp_iter=True owing to inlined-comprehension bookkeeping. Calls.resolve rejects those flags even after the AST shadow set is restored. A nonexecuting compiler bytecode probe confirms the second comprehension emits LOAD_GLOBAL Target, not a local load. This is the same bounded scope class the specification explicitly promises to preserve, not an arbitrary runtime alias.

Required minimal correction: discriminate comprehension-only compiler binding artifacts from genuine enclosing-function binding facts. Preserve real parameters, annotation-only local bindings, assignments/deletions, import/conflict rules, nested definitions, and free/nonlocal variables as shadows; do not broadly ignore compiler-local symbols. AST binding inventory plus compiler comprehension facts can make the distinction without bytecode analysis or whole-program machinery. Add this actual-producer positive and a negative with a real enclosing local/annotation to guard the distinction. Maintain first-iterable, later-iterable and per-comprehension target scoping. ROOT alone owns the fix and renewed evidence.

## Verified corrections, tests and conservation

The target-expression implementation now visits evaluated targets and limits comprehension bound names to Store contexts. BindingFacts explicitly visits subscript/attribute target expressions without recording comprehension Store targets as outer bindings. Both original failing fixtures now pass. Additional attribute-target, unpacked-target, actual-target-shadow and later-target cases also pass. Of14 independent candidate-origin scratch probes,13 match and only the new inter-comprehension case fails. Corrected probes are /tmp/l1-imports-review-r2-probes.py/.json; they parse/compile source data without executing scientific bodies.

Independent scoped command under prescribed shared venv/environment: `uv run python -m pytest tests/test_build_graph.py::TestDirectFormulaImports -q -k 'not production_call_omission'` gives43passed1deselected0.36s. Production seed excluded in reviewer run to keep source frozen. ROOT's raw target regression shows2fail31pass11deselected before the fix. ROOT class output44pass and whole-module123pass1skip15deselected20.62s are consistent with both new cases. Independently parsed both JUnit XML files: exactly one production_call_omission test in each, with no failure/error/skip child. Whole XML SHA256063dcc63f273bd157304ad0a92ed260ba4824f494b1ec1da2994de9afb4859ea. This is real-source mutation/decoy/assertion/restoration test evidence; reviewer did not rerun it or mutate source.

Independent current actual-producer extraction again confirms436 exact old Formula dictionaries,93 exact old IMPORTS dictionaries retained,109 total edges, exactly the same16 independently predicted additions; AST outside producer plus stdlib import unchanged. Receipt /tmp/l1-imports-review-r2-composition.json. Canonical formula hash remains deaa9898b4463360d26479dd65014ae884d511391df17cbd86fe4b429b7a568e. Edge dictionary set comparison is appropriate: prior evidence order was sorted and the new producer preserves deterministic source traversal; required dictionary/dedup/endpoints contract is conserved. ROOT's original order-only failed assertion is disclosed, not silently promoted.

The owning QA-map paragraph accurately documents the bounded static producer, deferred bodies/annotations, literal self-import and diagnostic-refusal limits, downstream freshness/dashboard roles and G4 separation, subject to fixing the remaining implementation defect so its comprehension promise becomes true. Existing registration_sites probes are designed for checks; OWED rows from passing an existing extractor name do not authorize inventing registrations or a new check. Derived test census/count-only updates are expected after adding genuine tests, through existing writers; they are not scientific source or coverage acceptance.

Read ROOT downstream diagnostic: removing exact16 edges from one R1-built graph and recomputing existing freshness annotation produces zero last_modified deltas. Correctly qualified as a controlled same-population diagnostic, not a second complete baseline build or R2 runtime/DB acceptance. R2 exact edge-set equivalence supports its relation-population applicability. No G4 test evidence or physical derivation follows from IMPORTS.

Source-sensitive probes are finished. No candidate/Git/notebook edits, production seeding, full graph build, DB/native/Lean/slot actions or scientific body execution. Fresh packet and renewed narrow tests/conservation/implementation readback are required after the remaining fix. No science/main/native/publication acceptance.
