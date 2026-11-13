# Existing module-ID resolution repair — specification and plan

Status: core implementation and routing correction independently accepted; broad qualification pending. Owner ROOT, NJL qualification dependency;
independent acceptance reviewer njl_dependencies_whole_review. The original
21-bundle scientific objective and all existing physical BUILDs remain intact.

## Existing authority and observed defect

The closed BACKED_BY target set in docs/KNOWLEDGE_GRAPH.md already includes
LeanModule. build_graph._module_id_for_ref is the shared production module
resolver; chain_canonicalize.GraphIndex delegates to it. The readiness check
uses the existing canonicalizer. No parallel resolver, graph type, check,
registration or architectural decision is required. This is implementation
repair of the documented existing module-prefix defect, not a new pipeline.

The actual canonical diagnostic at df42dc90 (15:41:36 UTC) reads 2,313 Lean
chain links and reports 111 unresolved. The separate complete explicit-ID pilot
at f997cff0 (15:48:09 UTC) inspects 16 links:
14 already name exact module IDs present in the existing node set, while two
name IDs not present in that set. All 14 positive links are in the historical
paper17 claims review; eight distinct module IDs are represented. The existing
helper nevertheless prepends another namespace and module prefix, so they
fail. The pilot is EXPLICIT_MODULE_PILOT.json under
outputs/continuity/NJL-chain-backing-diagnosis-20261025-r1/, SHA-256
e29f0117d528284eb0aeb40ebfae41aba15da21ef7a2593cf731fc09be999052.
These are distinct immutable receipts. All 53 carrying inputs (graph code,
canonicalizer, check, built index and all 49 claims-review JSON files) are
byte-identical across df42dc90 and f997cff0. The earlier population carries
forward on that input identity; it is not a newly dated run. This is positive
source/index evidence, not a global theorem-absence finding.

The declaration short-name resolver runs before the module fallback. An
explicit module ID must not accidentally resolve to a declaration merely
because its final component matches a unique declaration name. That typed-ID
collision and unknown-ID refusal must be tested along with the positive repair.

## Required behavior

1. A `module:`-prefixed target is a typed module reference. After stripping
   outer whitespace, retain its exact identity and accept it only when that ID
   exists in the current module-node set. Apply suffix/annotation/namespace
   compatibility normalization only to unprefixed legacy forms. Unknown,
   repeated-prefix and foreign unknown IDs remain UNRESOLVABLE; malformed
   path-like targets may remain INVALID.
2. Explicit module IDs must never enter declaration resolution or declaration
   suggestions. Both unique and ambiguous suffix collisions must refuse an
   unknown module ID; a known exact module ID retains its typed identity even
   when declarations share its last component. Preserve all existing
   unprefixed declaration and module forms.
3. The graph edge producer, canonicalizer and current validation consumer must
   agree on the same module IDs through the existing shared helper. Preserve
   current relation semantics: module existence proves no sentence's science.
4. Preserve every historical claims-review byte, verdict, quote, ratification
   state, physical default, theorem and built-index byte. No metadata rewriting
   is needed to repair these already canonical references.
5. Measure the complete resulting population before lowering the existing
   down-only ceiling. Expected repair is 111 to 97; this is a prediction until
   actual execution. If reality differs, reconcile it before choosing a bound.
   Never raise a ceiling or delete a genuine unresolved proof obligation.

## Ordered work and acceptance

- Independently review this complete proposal, source call chain, pilot and
  existing owner change before implementation. No new ADR supersedes the
  established closed-target decision.
- Extend tests/test_chain_canonicalize.py with the actual shared helper,
  production GraphIndex adapter and BACKED_BY edge extractor. Essential edge
  cases live in this default-fast selected module, so the declared finding
  Verify executes them; do not hide them in slow EdgeIntegrity. Observe
  known-present typed-ID and unique/ambiguous collision failures before
  production correction. Cover unknown/repeated-prefix/foreign IDs, both
  current nonmembers, legacy bare/nested/qualified/annotation/suffix forms,
  and existing full/short/ambiguous declaration behavior. For refusal assert
  no declaration retarget or suggestion and an actual missing_target edge.
  Use the real resolver functions, not a repaired fake. Retain existing tests.
- Implement only existing declaration/module lookup behavior needed above;
  run complete affected tests and all old chain-check controls.
- Re-run the complete canonical population. Lower the existing ceiling to the
  measured value only after positive module membership and exact unchanged
  link population are established.
- Use the existing mutation journal for an actual source/consumer regression
  or corpus fault; observe targeted RED and exact bytes/mode/nsmtime restore
  GREEN with an empty journal. Serialize all source mutations.
- Verify both actual graph edges and canonical resolver targets, complete
  refusal/missing/collision controls, and current raw receipt conservation.
- Run the configured broad fast suite, disclose every remaining failure, then
  use the existing count writer if the test census changed. No native Lean or
  PG operation is authorized or needed for this Python/index reference repair.
- Independent complete source/current-evidence review precedes any narrow
  canonical finding closure and ordinary draft checkpoint. Full CI/main and
  scientific publication acceptance remain separate and required.

## Scope

### Current execution evidence

The independent proposal review and corrected readback accepted the contract
before source edits (reports `1920ba62` and `4410a6b3`). Test-first execution
observed 30 failures and 35 passes before correction, followed by 65 passes.
Complete affected chain, graph and memo modules/class then reported 155 passes,
one existing skip and 15 default-marker deselections in 107.76 seconds.

Fresh production reads retained all 2,313 canonical link identities/order,
all 49 claims-review JSON byte images and the built index. Fourteen exact known
module references changed from unresolved to resolved: 111 unresolved became
97. The existing ceiling was lowered to 97 only after that measurement. The
complete graph-edge comparison changes 16 typed-ID edge representations,
including two still-missing targets; every other edge is unchanged.

Serialized production controls observed old resolver source fail at 111 and
restored source pass at 97. A real unknown-module corpus mutation failed at 98,
then restored source passed at 97. Exact bytes, full mode and nanosecond mtime
were restored; the journal is empty. Raw commands, population, edge changes and
restoration evidence are in
`outputs/continuity/NJL-module-id-implementation-20261025-r1/CONTROLS.json`
(SHA-256 `b9d8e6fee41e4db070d01af1575ae8c48f7a15f4c579126ae618a3cef940bb58`).

Whole independent review `82ac74e8` accepts the core source/control composition
and requires the existing planner to route this check for paper and Lean inputs.
Actual test-first routing cases fail for claims-only, Lean-source-only,
`lean/lean_deps.json`-only and mixed inputs; the unrelated-doc case passes.
The corrected `_plan` invokes the existing check once with `--no-memo` for
papers or Lean edits. Every original plan step and uncertified-scope statement
is conserved across the five complete before/after plans. No existing build
or count requirement is reduced.

The complete selected chain module and original check class now report
76 passes in 26.19 seconds, with retained raw channels. The registration probe
reports all required sites satisfied. Its optional cannot-measure PASS-exemption
roster and artifact sync edge are inapplicable: this check fails when it cannot
measure, and it writes no derived artifact. No exemption, check or writer was
added. Receipts are under
`outputs/continuity/NJL-module-scope-routing-20261025-r1/`.
Independent derivative review `2ebd4c74` accepts the routing correction with
no remaining mandatory issue in that scope. The complete original reports are
retained byte-exact in `MODULE_RESOLUTION_REVIEW.md` and
`MODULE_ROUTING_REVIEW.md`; prior proposal review/readback are also retained.
Broad fast qualification, required count synchronization, canonical closure
and protected checkpoint remain owed.

Implementation owner: existing module membership lookup and typed-ID dispatch
in scripts/build_graph.py and scripts/chain_canonicalize.py, including the
BACKED_BY producer and canonicalizer/adapter refusal path. Add no parallel
resolver. Declaration resolution and suggestions remain unchanged for legacy
unprefixed inputs. Existing tests: tests/test_chain_canonicalize.py, including
actual production graph-edge controls; reuse production functions rather than
duplicating resolution. Existing ratchet: scripts/validation/checks/reviews.py. Normative
owner: docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md. This dated audit carries
evidence and plan; source/findings/closures continue through existing writers.

The actual scientific meaning and stale historical PASS statements in paper17
remain subject to the existing ADW/KV findings. Resolving a container reference
does not derive a vacuum magnitude, calibrate a cosmology, accept a theorem
claim or close those findings. No new green bundle or 231-gate matrix follows.
