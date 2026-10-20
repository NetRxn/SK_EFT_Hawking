# Existing G4 producer, evaluator and consumer repair design

Status: DESIGN ACCEPTED; implementation under review under the separate ROOT allocation.
Whole design review does not establish runtime, production-control, scientific or
release acceptance. ADR-009 D6 and these owner documents precede code.

## Purpose, owners and existing evidence

Extend the existing `scripts/build_graph.py` producer,
`scripts/readiness_gates.py::_eval_computation_correctness`,
`GateResult.to_node_payload` serialization and
`scripts/validation/checks/bundles_readiness.py` submission consumer coherently.
Do not add a service, gate, registry, roster, new test-kind classifier or dispatcher.

The original branch-pinned root pilots and independent whole review are retained
as actual evidence at their own source hashes. Source-only r2 remeasurement compares
the complete canonical module AST with the current producer's exact name predicate,
separately for the candidate and primary sources. Full identities, counts, source
hashes and omissions belong in the evidence artifact, not an architecture census
literal. They corroborate a case-filter omission, not numerical/physical correctness
or a fresh graph build. Never transfer primary/frontier populations to exact-main.

Claims/adversarial reviewers still own source-backed sentence substance and inference;
figure/prose reviewers retain rendering and argument. Static coverage neither replaces
their reviews nor completes original scientific mapping or physical BUILD obligations.

## D6.1 — Complete existing producer population (M1)

Parse canonical `src/core/formulas.py` as Python source and enumerate direct
module-body `FunctionDef` and `AsyncFunctionDef` definitions in source order whose
names do not start with underscore. Use the existing AST facility in build_graph;
do not execute/import formulas to discover functions. Include legal mixed-case and
Unicode identifiers and decorated definitions. Exclude private helpers, nested
functions, class methods, imported aliases, assignments and definition-looking text.
A parse/read failure must propagate as a diagnosed cannot-build/refusal, not an
empty successful population. Diagnose duplicate public identities explicitly rather
than silently overwriting or manufacturing another identity.

Preserve exact `formula:<name>`, name/label/type, order among existing nodes,
verification/detail and every existing meta field. Keep the existing source-window
doc/ref extraction and Lean cleaning/resolution/definitional-record/fallback semantics.
AST locates the definition's own line; it does not justify a simultaneous docstring
parser cleanup. Old node dictionaries must compare completely, not merely by ID/count.
No formula function body, constant, test-kind policy, alias allow-list or grounding
helper changes are authorized. Existing legacy metadata-parser limitations remain
visible as limitations; new source metadata must not be silently promoted.

Expected population is an independent direct module-body source walk in the test,
not the producer's own helper or a frozen list of omitted names. Compare identities
both directions, multiplicity, exact name case, order and nonempty population.
Known-present mixed-case and lowercase witnesses plus private/nested/method/text
negative controls prevent proxy regressions. Fixture syntax cases are useful but
cannot substitute for actual canonical-source equality and conservation.

A real-source before/after manifest must preserve every complete old Formula node
and identify every new node's actual source location and metadata. Attribute every
newly reachable `VERIFIES`, `VERIFIED_BY`, `GROUNDED_IN`, claim and gate effect
to its source and existing resolver. Existing aliases remain constrained; do not
use blanket dotted-tail resolution. Recovered emission does not imply a supported
test, true proof, fresh execution or numerical correctness. Other evaluator bodies
stay exact; any changed results caused by newly visible inputs require explicit
source attribution rather than forced old counts.

## D6.2 — Complete declared population

Use the existing union of paper metadata formula names and CLAIMS→GROUNDED_IN
formula-target identities. Preserve current exact namespace formation and target
spelling, deduplicate the same target reached through either path, and partition
the full union deterministically. Do not change paper discovery or fabricate claim
precision: current GROUNDED_IN construction is paper-level Cartesian backing, not
a per-sentence scientific assertion.

Every target must resolve as an actual Formula node. Absence and wrong node type
are distinct internal blocker reasons. Any such member makes G4 priority1,
`state=blocked`, `measured=False`, including mixed populations that also contain
supported or unsupported resolved members. Preserve resolved-member evidence too:
incomplete population means incomplete measurement, not necessarily that nothing
was read. Include every unresolved identity before existing serialization caps.

An entirely undeclared population is `state=open`, `measured=False`; notes say
coverage was not assessed and source-grounded mapping remains owed. Do not substitute
absence of claims for proof of no computation, exemptions or dummy numerical registrations.

## D6.3 — Typed supported test evidence and measurement

A resolved Formula counts as supported only if an incoming VERIFIES edge has a
source resolving as PythonTest and its explicit test_kind is golden, identity or
roundtrip. Missing source nodes, non-test nodes and arbitrary unsupported kinds do
not count. Multiple edges count the formula once. Distinguish no valid PythonTest
edge from valid but insufficient kinds. A supported valid edge can coexist with
invalid/unsupported edges without being negated by them.

The complete union must partition into missing/wrong-type, supported, valid-but-
insufficient coverage and no-valid-test groups. Coverage subcategories may give
more detail, but no member disappears from the partition. Complete populations
with no valid tests, bounds, unknown or unsupported kinds are blocked/measured.
Complete supported populations are passed/measured. No sixth GateState or new
meaning for the other evaluators is introduced.

Preserve existing unresolved/definitional-grounding warnings and exact identities.
Test_kind is the existing heuristic assertion/name classification; an identity or
roundtrip label is not itself an independent numerical oracle or completed domain,
tolerance, resource, source or consumer review.

## D6.4 — Serialization and actual consumer (M2)

Keep GateResult, GraphIndex, node payload fields, state vocabulary and existing
single serialization cap. Internal evidence/blockers remain complete; serialized
lists retain actual total/truncated flags. Missing-member blockers must not be
pre-sliced. Large populations above the cap must remain distinguishable from complete
short lists, and measured/state/notes must survive exact serialization.

Preserve `classify_readiness` bucket keys and tuple shape,
`partition_readiness`, their public APIs and aggregate verdict: literal blocked
at either priority makes RED; other outstanding states can remain YELLOW/advisory;
all passed is GREEN. Do not strengthen enforcement through a reporting change.
Human submission still requires GREEN. P1 OPEN/unmeasured is not passed.

Correct the existing consumer's YELLOW text to describe actual outstanding gates,
states and measurement; it must never say all P1 passed unless that is true.
Use original serialized ReadinessGate nodes, keyed by paper/gate within the existing
check, to retain measurement/notes and capped evidence totals. Do not infer measurement
from lossy classifier tuples or add a parallel status registry. Existing Detail and
CheckResult fields suffice. Emit a targeted G4 detail for each paper's G4 result,
including state, measured, notes, disclosed blocker/evidence totals and truncation.
Its passing/warning shape follows the existing aggregate/report convention; it
does not create an extra blocker or hide a blocked G4 beneath another global RED.
This also makes missing/wrong-type unmeasured, empty OPEN/unmeasured and complete
negative measured results distinguishable in the actual check output.

Correct current registered-description/docstring claims in the existing consumer
to match the blocked rule. Replace the architecture-claim test's bucket-substring
proxy with exact production classifier/partition and actual consumer-detail
behavior bound to the new owner sentence. Preserve existing framework interfaces
and other checks. No new measurement floor or severity exemption is authorized.

## D6.5 — Meaningful controls and complete corpus comparison

| seam | required observations through the existing code |
|---|---|
| producer | complete actual canonical AST population equals actual emitted identities in both directions; old complete node dictionaries unchanged; mixed-case/lowercase/private/nested/method/text/decorated/async/Unicode and duplicate/parse refusal controls |
| declarations | metadata-only, claim-only, both/duplicate; missing-only, mixed, wrong-type and undeclared-empty; exact identity/partition/source kind |
| test edges | no edges, orphan source, non-test source, bounds-only, unknown, arbitrary unsupported kind; every supported kind positive and mixed valid/invalid edges |
| measurement | incomplete blocked/unmeasured, undeclared OPEN/unmeasured, complete negative blocked/measured, complete supported passed/measured |
| serialization | complete internal identities and lists above cap; exact totals/truncated flags, notes, priorities and unchanged payload keys |
| consumer | all-passed GREEN; P1 G4 OPEN/unmeasured YELLOW with truthful warning; missing G4 BLOCKED/unmeasured RED; complete bounds/no-tests BLOCKED/measured RED; P2 advisory YELLOW and P2 blocked RED; G4 details visible even with unrelated RED |
| conservation | existing other evaluator bodies/roster/priorities/floors/caps/APIs exact; every input-driven graph/verdict delta source-attributed; all original tests retained |

Test actual functions and returned details, not copied implementations, name
substrings or only the aggregate boolean. Small controlled graph inputs are unit
controls, not the production mutation obligation. Existing tests remain intact.

Before/after actual full-corpus pilots must independently derive each branch's
complete paper declarations, types and test-source/kind partition. Emit every paper
row with exact declared/resolved/missing/wrong-type and strong/insufficient/no-valid-
test sets, measurement/state/notes, serialization and consumer classification.
Reconcile original pilots at their actual hashes; no promise that all recovered
functions or papers become PASS. Canonical bundle mapping work remains scientific
work outside this static repair.

## D6.6 — Real production RED, restoration and release

Use existing seed_journal under an exclusive ROOT runtime allocation. Capture hard
unseeded baseline, changed source hash, source origins, raw argv/streams/rc, intended
assertion/refusal, exact bytes/fullmode/nsmtime restoration and journal empty, including
exception paths. Fresh source-bound subprocesses with isolated empty bytecode caches
must read seeded source; -B alone must not be mistaken for ignoring preexisting pyc.
Audit import/lazy loader/native/datastore preparation before any graph call; no
production PostgreSQL writes or unallocated refresh/build.

Two independent production controls are required:
- Reintroduce a case-exclusion into the actual Formula producer while canonical
  formula source stays exact. The independent whole-population assertion must RED
  through the real extractor with known-present mixed-case omissions; exact restore
  must restore the complete population and all old metadata. A real canonical-source
  public-function removal/private-rename control must also reach its declared paper
  as a missing target, not be hidden by GROUNDED_IN's absent-edge suppression.
- Seed a genuinely absent target in real PAPER_DEPENDENCIES provenance while the
  repaired producer remains correct. Real paper extraction must retain that metadata
  declaration, evaluator must block/unmeasure it and actual serialized G4 consumer
  detail must expose it. Exercise missing-only/mixed paths in unit controls too;
  production does not gain a fake formula/test node to turn baseline green.

For each control, GREEN means the exact intended assertions and restored targeted
baseline, not a claim that an already-red corpus became globally green. Require an
observable intended delta; unrelated global RED before/after is not a successful
mutation demonstration. Record scope explicitly.

Run existing architecture registration_sites probe for readiness_submission_gate
and update its existing mutation-obligation entry to reference actual production
controls once demonstrated. Do not claim registration/mutation coverage from a
future command or create another check. Appropriate whole existing tests/current
gates, genuinely nonauthor WHOLE implementation and intent review, canonical writers
only for real changed inputs, existing closure writer and protected Git/main remain
ROOT-owned release requirements. This design supplies no scientific, native,
physical, bundle-stage, human-submission or publication acceptance.
