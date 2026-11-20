# Residual IMPORTS specification review

Decision: AMEND BEFORE IMPLEMENTATION. The existing-producer repair is appropriate and buildable; two bounded lexical-policy clarifications below must be settled before code. This is not a request for a whole-program compiler, new resolver, registry, gate, check, or service.

## Authority and scope

Reviewed packet publication-imports-spec-review-r1.json: fresh=true, changed=[]. Candidate HEAD26d2545c44b806fb2f417fcfc8b237cb33d490f4 has only ROOT's three documentation modifications. Read primary ROOT notebook, workspace/repository AGENTS and CLAUDE, wave/continuity contracts, architecture-change SKILL and ADR-012 worked example, architecture ownership index, gate/QA maps and reviewer roster, current infra1.2, reconciliation, actual producer/helper and existing tests. ROOT remains sole candidate/Git/notebook writer. No candidate edits, tests, scientific imports/execution, seeding, graph build, DB/native/Lean or slot actions performed. Only assigned /tmp review artifacts written.

## Intent and overlap

Original current infra1.2 requires representing actual public mixed-case functions and direct call relations while preserving private/alias protections. Structural Formula emission is already integrated. D6.7 and plan6 correctly reuse that eligibility and extend extract_imports_edges rather than recreating the donor repair or adding a coverage layer. AST Name-call syntax removes text/comment/attribute false edges. Compiler function bindings and scoped comprehension targets are justified by real same-module local imports and the real generator call, not a speculative alias system. Claims/adversarial reviewers retain scientific backing/inference ownership. Existing G4 does not traverse IMPORTS; no numerical coverage, main, native, science or publication acceptance follows.

Independent live source-only remeasurement matches the supplied pilot exactly: 436 public module definitions, 109 non-self bare-Name syntactic pairs, supplied 93 old dictionaries, 16 missing pairs, zero old pairs outside the syntactic set; exact pair-list agreement. Formula SHA256 deaa9898b4463360d26479dd65014ae884d511391df17cbd86fe4b429b7a568e; producer SHA256 173710e48b9ade0c93e95cb81c94178165616d7aa0d0c92c25e85bde3fc23dce. Counts are syntax diagnostics, not a second lexical proof. Current source contains ten nested functions (not zero nested functions); reconciliation correctly claims no relevant nested Formula-call candidate rather than no nested bodies at all.

## Required pre-code amendments

### A1: State the correct class-header scope, or diagnose unsupported generic headers

D6.7 lines240-245 says all nested class headers are visited in the outer scope. Python3.14 type-parameter class scopes violate that universal rule. A stdlib-only symtable probe of `def F(): pass; def caller(): class Nested[F](F()): pass` (written as normal indented lines) places header F in a `type parameters` child scope where F is locally bound; it is not a reference to module Formula F. Compiler matching by child index is also unsound: Python3.14 emits annotation tables even for ordinary function definitions.

Minimal correction: eager nested defaults/decorators and non-generic class headers are traversed in their actual definition-evaluation scope; type-parameter names shield generic class headers, with any unsupported compiler-scope construct producing a diagnosed refusal. The implementation may conservatively refuse nonempty nested-class type_params instead of adding generic scope support. Do not scan type-parameter bounds/defaults or deferred annotations as eagerly executed bodies. Generic function ordinary defaults remain outer-evaluated in the measured probe; do not move all defaults into type-parameter scope. Add a real-producer negative fixture or diagnosed-refusal fixture for this case, plus an ordinary header/default/decorator positive. This affects no current corpus pair and needs no new subsystem.

### A2: Make conflicting-binding precedence explicit

D6.7 lines225-232 says self-import aliases can resolve and ordinary assignments must not manufacture edges, but does not explicitly settle a binding with both facts or an explicitly global write. Compiler flags are not exclusive: `from src.core.formulas import F; F=other; return F()` has F both imported and assigned. `global F; F=other; return F()` has F global and assigned. An implementation that treats is_imported or is_global as sufficient creates a false Formula edge in either case.

State a conservative precedence rule: an explicit self-import is eligible only when that binding has no conflicting parameter, store/delete, nested-definition or unrelated-import writer in its relevant lexical scope; explicit global binding writes also suppress direct module resolution in that caller. Define known static module overrides as syntactically detected bindings/deletions of the eligible module name outside its own declaration, without descending into unrelated local bodies. Ordinary comprehension targets must remain confined to their comprehension scope; assignment expressions follow compiler binding scope. No statement-order, branch-sensitive or arbitrary alias propagation is needed. At minimum test imported-then-assigned and global-written negatives through the actual producer, alongside both real local self-import positives. Resolve plan global line11's bare prohibition on 'alias' to mean fabricated/arbitrary variable aliases, preserving explicitly authorized self-import aliases in D6.7.

## Accepted implementation boundary after amendments

Smallest implementation: retain the existing structural eligibility helper, optionally accept one private preparsed AST while preserving its default signature behavior and all metadata windows; replace only the regex call-edge collection with AST Name calls plus bounded compiler/function and AST comprehension binding exclusions, explicit self-module import facts and conservative overrides. Deterministic ordering/dedup, endpoint membership, exact edge dictionaries, source-to-target direction, self/private exclusions and all other edge producers stay intact. Compiler/parse/read/duplicate ambiguity fails explicitly rather than returning an empty successful population. No numerical source body changes persist.

The specification already requires the right primary acceptance controls. Keep actual-producer fixtures for mixed case/Unicode/decorated/multiline/async; strings/comments/definition decoys/attributes; parameters/locals/imports/nested callable shadows; ordinary eager nested headers/defaults/decorators; list/set/dict comprehensions and generators, first iterable and later target scope, real generator-only global; explicit absolute/relative self-imports and aliases; self/private/absent endpoints and dedup; read/parse/duplicate/lexical refusal. Add A1/A2 cases rather than weakening positives.

For actual corpus acceptance, independently compare complete old Formula dictionaries and all93 old IMPORTS dictionaries, require exactly the independently attributed sixteen additions, and retain G_N_emergent -> G_N_sakharov plus both actual self-import dependencies and diff_invariance_holds_order_by_order -> diff_invariance_holds_at_order. Review downstream graph consumers: IMPORTS participates in freshness propagation (scripts/last_modified.py) and graph/dashboard traversal even though G4 does not consume it. Compare typed graph differences and any derived freshness metadata, without calling propagated metadata change new computation evidence.

The journalled production control must run against real formulas.py only when ROOT owns the exclusive mutation lane: remove the real mixed-case call, retain a spelling decoy, observe the actual known-present assertion fail for that edge, restore exact bytes/mtime_ns and observe green with clean journal. No fixture-only/fake Formula/ceiling control substitutes. Existing registration probes are interpreted for this extractor, not a reason to invent a registered check. Canonical writers, independent whole implementation/evidence review, existing closure and later release/qualification remain ROOT-owned.

No science/main/publication acceptance is granted. With A1/A2 incorporated and reviewed, no further architectural blocker is identified for the bounded implementation.


## R2 amendment confirmation — ACCEPT FOR IMPLEMENTATION

Checked primary packet publication-imports-spec-review-r2.json first: fresh=true, changed=[]. Read the actual amended D6.7 lexical and acceptance paragraphs and plan global contract. No producer or scientific source changed: their hashes match the initial review exactly.

A1 is resolved: ordinary defaults/decorators and class headers follow actual definition-evaluation scope; generic class bases/keywords honor type-parameter shadows; generic function ordinary defaults and decorators remain outer; unsupported scope is diagnosed instead of guessed. Deferred annotations, type-parameter bounds/defaults and TypeAlias RHS are excluded while assignment values/evaluated target expressions remain supported. Actual-producer positive/negative controls are specified.

A2 is resolved: conflicting parameter/store/delete/nested-definition/unrelated-import/explicit-global writers override self-import eligibility; every literal import fact for a spelling must agree on its eligible target. The module inventory explicitly covers potential bindings in control blocks, excludes unrelated local bodies and comprehension targets, and distinguishes type-only annotations from value overrides. Any additional affected module writer is conservatively excluding; no order/branch/dynamic inference is promised. The plan explicitly permits only literal self-module import aliases and rejects arbitrary variable aliases/fabricated identities.

Decision: ACCEPT FOR IMPLEMENTATION at these exact documentation hashes, with no remaining specification blocker identified. This accepts the bounded plan only. Actual code, real-producer fixtures, complete corpus conservation, production mutation/restore evidence, downstream typed graph/freshness effects and whole independent implementation acceptance remain required. ROOT alone owns those actions; no new resolver/check/gate/registry/service or whole-program analysis is authorized. No science/main/native/publication acceptance follows.

- docs/adrs/ADR-009-validation-suite-modularization.md: 0950a5edeac7e5dee54bd790e42036b30f57ccde1b9ec8655ffe063e10d8b6d9
- docs/superpowers/specs/2026-10-19-g4-declared-population-design.md: ce61aaf381e447d14d642c48ecbf4b996ad2267fa78859aac8ecb25be096b80f
- docs/superpowers/plans/2026-10-19-g4-declared-population.md: 35a5f108914ac7b1966d91caf686dc66175396970b1e0768960cee0010469c8f
- scripts/build_graph.py: 173710e48b9ade0c93e95cb81c94178165616d7aa0d0c92c25e85bde3fc23dce
- src/core/formulas.py: deaa9898b4463360d26479dd65014ae884d511391df17cbd86fe4b429b7a568e

R2 actions: continuity check, read-only paragraph/diff/hash inspection, append these assigned scratch reports. No candidate edit/test/seed/graph build/DB/native/Lean/slot/scientific-code execution.
