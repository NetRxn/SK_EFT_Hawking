# IMPORTS implementation review — R3

Verdict: CHANGES REQUIRED. I1 and I2 are resolved, but a nearby existing generic-function shadow contract still creates a false edge after the new comprehension fallback.

First action checked publication-imports-implementation-review-r3.json: fresh=true, changed=[]. Frozen producer SHA256 b360fc790946947f1ea012e5b1287b81580697e55d06b86d78abb7a8c593219d; tests84b6c69bf248da9de6604a9fd024d9ef255daa5c7f29a89ac5741074af5f4897; QA map unchanged3e81f812a246519c8ce5eb57ae02322f94412b299b9ebb070cf8d28ce2d93626. R1/R2 reports retained.

## I3 — Generic caller type parameter can be mistaken for a module Formula

The actual candidate-origin producer emits caller -> module Target for:

```python
def Target(): pass
def caller[Target]():
    [0 for Target in items]
    return [Target() for x in items]
```

Expected: no module Formula edge. Target is the caller's type-parameter spelling, and this source has no module-name load for that call. Python3.14 symtable marks the function-level Target is_comp_iter=True/is_local=True/is_free=False. The enclosing type-parameters table has its own Target binding. Compiler bytecode for the caller contains LOAD_FAST_CHECK Target for the second comprehension, never LOAD_GLOBAL Target. The new comp_iter fallback therefore cannot equate absence of a function-body BindingFacts writer with global resolution for generic callers.

Minimal correction: preserve caller type-parameter binding facts when allowing a transient-comprehension symbol to resolve globally. AST function.type_params gives the bounded names directly; no new compiler project or runtime alias analysis is needed. Keep already supported explicit local import semantics if the function intentionally binds that spelling through a legitimate literal self-import. Add this actual-producer negative and retain non-generic cross-comprehension positive, generic function ordinary-default positive, annotation/assignment/parameter/import negatives. This is the existing generic function shadow rule, not additional scope.

## Verified R3 behavior

The four-line fix resolves I2's original positive and preserves ordinary annotated-local/assignment negatives. I1's two evaluated-target cases remain fixed. Independent prescribed-env actual class run excluding the canonical seed gives46passed1deselected0.37s. ROOT's R3 class gives47passed0.65s; XML independently confirms the real production omission/decoy/restoration test is present once and has no error/failure/skipped child. ROOT's red for I2 is1fail35pass11deselected as recorded.

Independent21 source-data probes through the candidate-origin producer give20 expected results and only I3 fails. Nearby passing probes include cross-comprehension ordinary globals, annotation-only local, actual assignment, parameter, literal self-import, unrelated import, nested local definition, evaluated attribute/subscript/unpacked targets, actual comprehension shadow, eager nested default/decorator and real-writer generator controls. Probe source is parsed/compiled but scientific bodies never executed. Receipts: /tmp/l1-imports-review-r3-probes.py and .json.

Independent actual corpus extraction confirms436 exact old node dictionaries,93 exact old edge dictionaries retained,109 total edges and exactly16 independently predicted additions. AST outside the producer/new symtable import remains unchanged from HEAD. Canonical formulas hash remains deaa9898b4463360d26479dd65014ae884d511391df17cbd86fe4b429b7a568e. Receipt /tmp/l1-imports-review-r3-composition.json. Current corpus conservation is valid scoped evidence but does not waive the false-edge fixture defect.

Prior QA-map/registration/counts/downstream findings from R2 remain applicable: map describes the intended bounded contract; registration_sites does not turn an existing extractor into a new registered check; genuine added tests require only canonical derived count changes; controlled zero-delta freshness comparison is not a new complete graph/runtime/DB qualification or G4 test/physical evidence.

Source-sensitive probes finished. No candidate/Git/notebook writes, canonical seeding, scientific-body execution, graph build, DB/native/Lean/slot operations. ROOT owns the narrow repair, fresh packet and renewed evidence. No science/main/publication acceptance.
