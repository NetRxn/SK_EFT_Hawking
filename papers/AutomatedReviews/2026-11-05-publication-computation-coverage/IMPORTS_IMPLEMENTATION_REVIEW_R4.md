# IMPORTS implementation review — R4

Verdict: CHANGES REQUIRED. I1/I2/I3 are resolved; one overbroad generic type-parameter fallback exclusion now hides an explicitly global read. This remains a bounded compiler-scope contract correction, not new architecture.

First action checked publication-imports-implementation-review-r4.json: fresh=true, changed=[]. Producer5e4cecafdfb4002e2d318f84a0bc7adebbf01d59a15094bfef7129005d0f3cd3; tests287ee38b1fc23133fceb88482c64fc08422d1e59891c05686885be37a9b1165e; QA map unchanged3e81f812a246519c8ce5eb57ae02322f94412b299b9ebb070cf8d28ce2d93626.

## I4 — Explicit global declaration must override the type-parameter spelling exclusion

Actual candidate-origin producer omits caller -> Target for valid source:

```python
def Target(): pass
def caller[Target]():
    global Target
    return Target()
```

The function's compiler symbol marks Target is_declared_global=True/is_free=False. Its call denotes module Target; a bare global declaration is not a global write. Final `return None if name in self.type_params else globals_by_name.get(name)` incorrectly suppresses this explicitly global reference after all real writer guards have passed. This differs from I3's unresolved/local generic shadow. The accepted contract excludes explicit global writes, not explicit read-only global declarations.

Minimal fix: permit compiler-declared global resolution despite the type-parameter name, after retaining existing parameter/free/nonlocal/import and conflicting-writer exclusions. Add the actual-producer read-only-global positive and keep the same source with `Target=other` as a negative. No branch, statement-order, arbitrary alias, runtime dispatch or whole-program analysis is necessary. The explicit same-module local import override already passes.

## Current evidence and preservation

Independent prescribed-env scoped class excluding production seed:48passed1deselected0.37s. ROOT's actual49class pass receipt includes production source mutation test; independently parsed R4 class XML confirms exactly one matching production test and no error/failure/skip. ROOT I3 red shows1fail37pass11deselected. All previous I1/I2/I3 probes pass now, including genuine generic shadows and ordinary cross-comprehension globals. Independent24 probes give23 expected results and only I4 fails. Generic global-writer negative and local self-import override positive both pass. Probe scripts/results: /tmp/l1-imports-review-r4-probes.py/.json. No scientific bodies executed.

Independent extraction again verifies436 complete Formula dictionaries exact,93 old edge dictionaries exact,109 total edges and exactly16 pre-predicted additions; AST outside extract_imports_edges/new symtable import unchanged from HEAD. Formula source hash unchanged deaa9898b4463360d26479dd65014ae884d511391df17cbd86fe4b429b7a568e. Receipt /tmp/l1-imports-review-r4-composition.json.

Owning QA paragraph remains accurate for intended semantics once I4 is corrected. R2 qualifications remain: existing-extractor registration probes do not authorize a new check; added real tests justify canonical count-only regeneration; zero-delta same-graph freshness diagnostic is bounded and not new whole graph/runtime/DB or G4 test/physical evidence. Science audit-path changes by ROOT are outside this source review; no authority inferred for reviewer changes.

Probes finished; old reports retained. No candidate/Git/notebook edits, canonical seeding, scientific execution, full graph/DB/native/Lean/slot action. ROOT owns correction/fresh packet and required final whole-module/current evidence. No main/science/publication acceptance.
