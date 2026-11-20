# Residual direct Formula-call repair

The existing `extract_imports_edges` producer now uses the existing structural
Formula eligibility plus Python AST/compiler binding facts. It adds the exact
sixteen previously measured direct Formula relationships, retaining all436
Formula dictionaries and all93 previous edge dictionaries. Total direct edges
are109. No new gate, registry, check, edge type or physics formula is added.
Static dependency coverage does not establish runtime execution or physical
correctness.

The [specification review](IMPORTS_SPEC_REVIEW.md) accepted the amended design
before code. Independent implementation reviews
[R1](IMPORTS_IMPLEMENTATION_REVIEW_R1.md),
[R2](IMPORTS_IMPLEMENTATION_REVIEW_R2.md),
[R3](IMPORTS_IMPLEMENTATION_REVIEW_R3.md),
[R4](IMPORTS_IMPLEMENTATION_REVIEW_R4.md) and
[R5](IMPORTS_IMPLEMENTATION_REVIEW_R5.md) retain all discovered scope defects
and their repairs. R5 accepts the bounded implementation after actual-producer
adversarial probes. Comprehension target expressions, transient inlined
compiler symbols, generic type parameters, explicit read-only globals, real
writers and literal self imports have separate positive/negative controls.
The initial [red receipt](IMPORTS_RED.txt) and subsequent target/scope/generic
red receipts preserve the observed failures; passing fixtures were not
substituted for the original cases.

The [complete graph test module](IMPORTS_AFTER.txt) reports130 passed, one
skipped and fifteen deselected in20.39 seconds. Its [JUnit](IMPORTS_AFTER.xml)
contains the actual production mutation test: removing the real
`G_N_emergent` call to `G_N_sakharov` while leaving a comment decoy turns the
real assertion red. The journal restores exact source bytes and mtime, and the
positive assertion and complete Formula dictionaries pass afterward. The
[composition receipt](IMPORTS_COMPOSITION.json) records exact source/test
hashes, dictionary-set conservation and the actual command. An initial ROOT
comparison incorrectly required evidence-list order instead of the specified
edge-set equality; this diagnostic correction is explicitly retained.

Existing typed G4, submission, measured-gate and architecture consumer tests
report [163 passes](IMPORTS_CONSUMERS.txt). The full canonical graph was built
read-only without Postgres sync or Lean refresh. A controlled diagnostic removes
exactly the sixteen new edges from that one built population and reruns the
existing freshness annotation: [no timestamp changes](IMPORTS_FRESHNESS_DIAGNOSTIC.json).
That diagnostic is scoped to the recorded dirty-source graph, not a second
complete baseline build or fresh runtime qualification.

The architecture-change registration probe treats its argument as a new
validation check and reports missing check sites. This repair changes an
existing edge producer, not a registered check; those new-check sites do not
apply. Existing edge assembly already invokes the producer. The owning QA map,
ADR-009 D6, specification and plan describe the bounded mechanism. Counts are
regenerated through the existing writer; Lean sources and live slots are
unchanged. The existing closure writer records finding1.2 fixed atd5585d16 after
running its declared Verify command; [receipt](IMPORTS_CLOSURE.txt). Exact-head
all-bundle readback and main/full/native/security/human/publication gates remain
separate.
