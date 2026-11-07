---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: Codex-publication-lead
model: Codex
review_date: 2026-10-20T15:04:20.382423+00:00
readiness_gates_version: 1
kind: targeted-infra
---

# Computation population and architecture inventory: canonical repair record

The original defects below have source repairs in local checkpoint `1550f5ff11ab6c350081abf607d4431e28e02ef1`.
Genuinely nonauthor whole review accepted that bounded source/canonical/control composition.
This is a ROOT-authored public filing and reconciliation, **not a new independent review or
canonical closure**. Each finding remains OPEN until its declared command passes and the existing
closure writer records the disposition. Full integrated qualification and main delivery remain owed.
See [scope and reconciliation](SCOPED_REVIEW.md) and [selected actual control metadata](CONTROL_EVIDENCE.json).

ROOT accepts implementation/integration accountability for these machine repairs. The next
substantive action is independent review of this filing, then actual declared verification and
`scripts/close_finding.py`; the acceptance reviewer must be genuinely nonauthor. Scientific
mapping, calibration and physical derivations remain separate BUILD obligations.

### 1.1 — MAJOR — lowercase-only formula emission omitted real public canonical functions

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `uv run python -m pytest -q tests/test_build_graph.py::TestStructuralFormulaPopulation`
- **Gate:** ComputationCorrectness
- **Location:** `scripts/build_graph.py::extract_formula_nodes`, `src/core/formulas.py`
- **Observed:** The original name regex omitted legal public names containing uppercase letters.
  The exact main-based corpus contained 436 public functions but emitted 410; the 26 omissions
  include `G_N_sakharov` and `higher_curvature_R_sq_coefficient`. Existing scientific function
  bodies were not missing. The correct repair is structural source enumeration, not renaming
  functions, adding aliases, weakening the expected population or declaring them validated.
- **Repair evidence:** The actual extractor now follows module-body public function AST identities
  in order, preserves every complete old Formula dictionary, and diagnoses parse/duplicate/read
  failure. Actual production case-filter regression observes intended RED, then exact restoration
  GREEN. The selected control artifact records real child outcomes and original-channel hashes.
- **Expected:** All and only canonical public module-body functions are emitted with exact identity;
  private/nested/method/import/text lookalikes remain excluded. Emission is not correctness proof.
- **Remaining:** Actual declared Verify, independent filing review, canonical closure and protected
  integration; all scientific mappings and the existing D12 public-function zero-reference duty.
- **Cache:** Existing graph regeneration owns later propagation; this filing performs none.

### 1.2 — MAJOR — absent or mistyped declared computations could disappear from the G4 verdict

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `uv run python -m pytest -q tests/test_readiness_gate_evaluators.py::TestG4DeclaredTypedCoverage`
- **Gate:** ComputationCorrectness
- **Location:** `scripts/readiness_gates.py::_eval_computation_correctness`
- **Observed:** The original evaluator filtered unresolved Formula targets out before checking the
  surviving population. A nonempty declared population could therefore receive a vacuous pass;
  real paper39/paper40 source pilots exposed it. An empty undeclared population is different.
- **Repair evidence:** The existing metadata-plus-grounding union is explicitly partitioned into
  absent, wrong-type, unsupported and supported members. Missing/wrong-type members block with
  measured=false; truly undeclared remains OPEN/unmeasured. Actual canonical public-definition
  private rename and actual absent-dependency seeds each produce targeted BLOCKED/unmeasured
  RED and exact-restored PASSED/measured GREEN. Aggregate RED is not the discriminator.
- **Expected:** Every declared target is accounted for; valid typed test edges remain static support,
  not fresh execution, theorem relevance, physical validity or formula-specific independent proof.
- **Remaining:** Actual declared Verify, independent filing review, canonical closure and full delivery.
- **Related:** Existing D12 anti-vacuity obligations remain distinct and are not closed here.
- **Cache:** No cached or external graph state is accepted by this filing.

### 1.3 — MAJOR — an OPEN priority-one result could be described as all priority-one gates passing

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `uv run python -m pytest -q tests/test_readiness_submission_gate.py`
- **Gate:** FixPropagation
- **Location:** `scripts/validation/checks/bundles_readiness.py::check_readiness_submission_gate`
- **Observed:** The existing YELLOW classification permits an OPEN priority-one gate, while the
  original consumer message claimed all priority-one gates passed. Correct the message and
  expose state/measurement evidence; do not silently change the classifier or submission policy.
- **Repair evidence:** Whole review reconstructed all 64 actual serialized paper results and
  independently checked policy vectors, including OPEN P1, either-priority BLOCKED and complete
  PASSED. Existing tuple/bucket shapes, aggregate verdict, thresholds and human-GREEN rule remain.
- **Expected:** Output says what was actually measured and retains G4 detail under unrelated RED.
- **Remaining:** Actual declared Verify, independent filing review, canonical closure and full delivery.
- **Related:** The historical reconstructed-round6 D12:8.1 false-all-P1 lineage is linked below;
  this precise current consumer repair does not establish its full closure.
- **Cache:** N/A; no output population is manually regenerated here.

### 1.4 — MAJOR — a physical .git/hooks lookup dropped the hook catalog in linked worktrees

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `uv run python -m pytest -q tests/test_architecture_inventory.py`
- **Gate:** FixPropagation
- **Location:** `scripts/architecture_inventory.py::hooks`, `docs/architecture/END_TO_END_MAP.md`
- **Observed:** Treating a checkout .git file as a directory silently omitted the genuine Git hook
  row. The inventory must use anchored Git administrative metadata, preserve ordinary hooksPath
  configuration, and distinguish a known empty catalog from refused or unavailable observation.
  The end-to-end schema description also pointed at historical generated authority incorrectly.
- **Repair evidence:** Existing collector/render/writer now use the target Git context and logical
  metadata-only row. Actual old-physical-path regression and separate actual canonical-row deletion
  each produce targeted RED/exact-restored GREEN with nonhook families conserved. The complete
  inventory test module passed 57 cases; genuine whole source/control review accepted its scope.
- **Expected:** Anchored metadata and honest refusal through existing owners; no private hook body
  inspection, copied hook, config rewrite, new scanner or claim of actual hook activation.
- **Remaining:** Actual declared Verify, independent filing review, canonical closure and full delivery.
- **Cache:** Only the existing canonical inventory writer owns derived output; no writer ran under seeds.
