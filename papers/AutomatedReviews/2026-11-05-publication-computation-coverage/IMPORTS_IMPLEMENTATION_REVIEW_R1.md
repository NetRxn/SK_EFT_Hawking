# IMPORTS implementation review — revision 1

Verdict: CHANGES REQUIRED. One bounded comprehension traversal defect prevents implementation acceptance. No science/main/publication acceptance is granted.

## Frozen source and authority

First checked publication-imports-implementation-review-r1.json from the assigned candidate: fresh=true, changed=[]. Read primary ROOT notebook, accepted R2 design, complete build_graph/test diff and supplied red/green/whole-module/composition evidence. Candidate producer SHA256: 3b5d486626f157d43341d7d1bc8bed92d987b13e6e9ce3e2531ad0eab6938a62. Test SHA256: aa01470acd6094c05888151f7aa8237de0f7d8e751b28e03bb1f0e5ad3d03733. Canonical formulas SHA256 unchanged: deaa9898b4463360d26479dd65014ae884d511391df17cbd86fe4b429b7a568e.

## Required correction — comprehension evaluated targets and binding names

scripts/build_graph.py:4853-4867 collects every ast.Name under generator.target as a shadow and never traverses generator.target for evaluated expressions. Only actual Store-bound names introduce comprehension bindings. Loads inside subscript/attribute assignment targets retain their normal lookup, and calls evaluating those targets are genuine caller-body expressions under the accepted R2 contract.

Two independent source-data fixtures, parsed and compiled without executing their bodies, call the actual candidate-origin-verified extract_imports_edges and both incorrectly omit caller -> Target:

```python
def Target(): pass
def caller():
    return [0 for data[Target()] in items]
```

The target's subscript index calls Target but is never visited.

```python
def Target(): pass
def caller():
    return [Target() for data[Target] in items]
```

Here Target in the subscript is a Load, not a bound comprehension name. Treating it as a shadow suppresses the valid result call.

Required minimal fix: collect only actual Store names from comprehension targets; traverse each target's evaluated expressions in the comprehension scope, after its iterable and before its conditions/result. Keep the first iterable's outer scope, all genuine comprehension target shadows, generator-only global preservation and existing deferred-body exclusions. Add both cases to actual-producer fixtures and retain red/green evidence. This extends the current traversal only, with no new resolver/check/gate/compiler project. ROOT acknowledged the defect and owns the repair; reviewer made no candidate edits.

## Independent checks and conservation

Using the prescribed shared environment, actual scoped command `uv run python -m pytest tests/test_build_graph.py::TestDirectFormulaImports -q -k 'not production_call_omission'` passed41 with1 deselected in0.39s. Production seed deliberately excluded to preserve the frozen review source and live graph qualification. Environment: UV_NO_SYNC=1, UV_OFFLINE=1, UV_CACHE_DIR=/tmp/l1-window-uv-cache, UV_PROJECT_ENVIRONMENT=/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.venv.

Eight candidate-origin-verified scratch probes gave six expected results and the two failures above. Passing probes covered ordinary/annotated assignment-target calls, nested decorator calls, generic function ordinary defaults, generator global writes and comprehension assignment-expression shadows. Initial scratch launch resolved the editable primary package because its script lived in /tmp; that result was discarded. The corrected script explicitly prepended the assigned checkout, printed/asserted the actual candidate producer origin, and reproduced the two reported failures. Only corrected output is retained in /tmp/l1-imports-review-probes.json.

Independent read-only producer conservation, with canonical formulas hash asserted before/after, confirms all436 Formula node dictionaries exactly equal /tmp/l1-imports-before-nodes.json; all93 old edge dictionaries conserved;109 current edges; exactly16 added pairs equal the independent pre-change pilot; and the AST outside extract_imports_edges plus its new stdlib symtable import is unchanged from HEAD. Receipt: /tmp/l1-imports-review-composition.json. This verifies current corpus behavior but does not excuse the fixture-scoped contract defect.

Code review otherwise found the intended bounded handling for lexical symbol facts, literal self-import agreement/conflicting writers, module overrides, ordinary nested defaults/decorators/headers, generic-class refusal, deferred annotation/type-alias exclusion, endpoint/private/self/dedup semantics. No independent whole-graph run or freshness acceptance is claimed; IMPORTS has downstream freshness/traversal consumers but does not supply G4 test coverage.

## Evidence limits and follow-through

Supplied raw red shows19fail22pass; supplied initial green shows41pass. ROOT confirmed the initial green predates the production-control addition. Supplied whole-module output shows121pass1skip15deselected and ROOT states it includes the added42nd source-mutation test; stdout alone does not identify that command/source binding. ROOT will rerun the exact production control with explicit command, source hashes/JUnit/exit and restoration evidence after the independent full-graph lane is terminal. Reviewer did not rerun or authorize a competing production seed.

After the narrow fix, require a fresh packet, both new red/green cases, scoped/whole-module evidence, renewed exact corpus conservation and journalled production omission/decoy/red/exact-byte+mtime restore evidence at the accepted source hashes. Owning QA-map/count updates remain ROOT-owned follow-through. No candidate/Git/notebook writes, scientific body execution, graph build, DB/native/Lean/slot or production seeding occurred in this review. Source-sensitive probes are now finished.
