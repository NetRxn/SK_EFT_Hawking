---
paper: infra
bundle_target: L1
reviewer: publication-computation-assessment
review_date: 2026-11-05
kind: focused-coverage
readiness_gates_version: 1
---

# Existing computation-gate coverage defects

Independent assessment by `/root/l1_transport` identified these defects.
ROOT separately reproduced the missing registry population, mixed-case
extraction omission and absent-target false pass. ROOT also reproduced
the local namespace-classification failure in finding1.4. The targeted
[runtime receipt](REPRODUCTION.json) and [source binding](SOURCE_BINDING.json)
are source/extractor/evaluator evidence, not a full graph or native run.
Current disposition: findings1.1 and1.3 have canonical fixed records.
Finding1.1 is anchored at71f93c7f7;1.3 propagates the independently
reviewed existing checkpoint. Finding1.2 has an independently accepted residual IMPORTS implementation, pending
canonical closure; finding1.4 is canonically fixed at06aacc0e2.
The Formula-emission part of1.2 is restored. Its residual IMPORTS repair
now has [accepted implementation evidence](IMPORTS_IMPLEMENTATION.md). Residual machinery changes require the existing
architecture-change workflow.

## Existing repair recovered and integrated

The [history reconciliation](EXISTING_REPAIR_REUSE.md) identified
`1550f5ff11ab6c350081abf607d4431e28e02ef1`, parent exact main
`ce194cdc4`. It already repairs structural Formula emission,
typed G4 missing/wrong-type handling, the existing submission
consumer and worktree inventory resolution. `dcb9a2c5a` carries
its evidence and original enforced closures. Normal merge
`f2fca05a` brings that coherent package into this candidate;
it does not merge the later unrelated cache repair.

The [independent integration review](INTEGRATION_REVIEW.md) verifies
all donor paths, both unchanged closure histories and canonical
count regeneration. Its [current verification](INTEGRATION_VERIFICATION.json)
records7+23+25+57 passing cases. The [freshness readback](INTEGRATION_FRESHNESS.txt)
passes all three selected checks. The [targeted producer/gate measurement](INTEGRATION_MEASUREMENT.json)
emits436 Formula nodes, retains L1 OPEN/unmeasured with no declared
formula roster, measures all five source Paper25 formulas as statically
supported, and blocks/unmeasures the absent-target control. This is
not a full graph/native run, numerical correctness proof or publication
acceptance. The original failure receipt and source binding above
describe the pre-integration diagnosis, not the current implementation.

### 1.1 — MAJOR — L1 computational claims have no registered G4 formula population

- **Severity:** major
- **Lane:** infra
- **Gate:** ComputationCorrectness
- **Location:** `src/core/provenance.py::PAPER_DEPENDENCIES`, `scripts/build_graph.py::extract_paper_nodes`, `scripts/readiness_gates.py::_eval_computation_correctness`
- **Observed:** The actual L1 Paper node has an empty formula roster and `has_provenance_entry=false`. The source Paper25 entry does not populate the distinct L1 bundle. Sentence BACKED_BY links do not feed the evaluator's Paper/CLAIMS/GROUNDED_IN route. The separately accepted 81-case numerical evidence therefore does not establish a G4 pass.
- **Expected:** Reconcile actual current manuscript consumers into the existing dependency registry, preserving the source Paper25 entry. Do not populate the roster by copying unreviewed legacy consumers. Keep wrapper and independent scientific-script evidence explicit where outside current core-Formula extraction scope.
- **Current disposition:** Independently reviewed reconciliation at71f93c7f7 registers seven actual Formula consumers, twenty existing parameters and four modules. Two backing paths resolve the existing W6Ext theorem; all114 sentence IDs/verdicts and human state are preserved. The existing writer records this finding fixed. The full canonical graph measures all seven G4 consumers supported; G3 is blocked for lack of human parameter verification. [Gate readback](L1_REGISTRY_GATE_READBACK.json) precedes closure and retains that timing explicitly. Static coverage does not discharge physical B3, mode or transport obligations. Finding1.2 still owns the separate IMPORTS defect.
- **Verify:** `uv run python -c "import sys; sys.path.insert(0,'scripts'); from build_graph import extract_paper_nodes; p=next(p for p in extract_paper_nodes() if p['id']=='paper:L1'); assert p['meta']['has_provenance_entry'] and p['meta']['formulas'], p['meta']"`

### 1.2 — MAJOR — Formula and import extraction omit mixed-case public functions

- **Severity:** major
- **Lane:** infra
- **Gate:** ComputationCorrectness
- **Location:** `scripts/build_graph.py::extract_formula_nodes`, `scripts/build_graph.py::extract_imports_edges`
- **Observed:** Lowercase-only identifier expressions omit 26 of 436 public source functions. Four omitted GW functions are `c_GW_from_chi_vest`, `c_GW_deviation_from_c`, `c_GW_natural_range`, and `dispersion_correction_from_GammaH`. Actual extraction emits 410 Formula nodes. This is a producer omission, not evidence that the functions or their Lean substrate are missing.
- **Expected:** The existing producer must represent actual public mixed-case identifiers and their direct import/call relations, while retaining private-helper exclusions and alias-resolution protections.
- **Next action:** Lead records the accepted residual repair through the canonical closure writer after its source checkpoint, then refreshes exact-head graph/gate evidence. Full qualification and main integration remain separate.
- **Current disposition:** Existing structural Formula repair emits all436 public functions unchanged. The independently reviewed existing IMPORTS producer now emits109 direct edges: all93 prior dictionaries and the exact16 measured additions. Original scope defects, real production red/restoration and passing consumer evidence are preserved in [the implementation record](IMPORTS_IMPLEMENTATION.md). Closure is pending the source commit and writer enforcement; no runtime/scientific/full qualification is inferred.
- **Verify:** `uv run python -c "import sys; sys.path.insert(0,'scripts'); from build_graph import extract_formula_nodes,extract_imports_edges; nodes=extract_formula_nodes(); expected={'c_GW_from_chi_vest','c_GW_deviation_from_c','c_GW_natural_range','dispersion_correction_from_GammaH'}; assert expected <= {n['name'] for n in nodes}; edges=extract_imports_edges({n['id'] for n in nodes}); assert any(e['source']=='formula:G_N_emergent' and e['target']=='formula:G_N_sakharov' for e in edges)"`

### 1.3 — MAJOR — G4 reports PASSED when its declared formula is absent

- **Severity:** major
- **Lane:** infra
- **Gate:** ComputationCorrectness
- **Location:** `scripts/readiness_gates.py::_eval_computation_correctness`
- **Observed:** A Paper node with one registered missing Formula and no other graph evidence receives `passed`. Its evidence explicitly reports one Formula NOT IN GRAPH and not examined. The existing absent bucket is informational and does not prevent this false pass.
- **Expected:** A missing required Formula cannot establish computation coverage. Withhold PASSED and retain explicit evidence using the existing state and blocker vocabulary. Complete supported formula/test populations must retain valid outcomes.
- **Next action:** Lead records the verified propagation closure through the existing writer. Retain the integrated absent-only, partially missing, wrong-type and complete-population controls and current real-paper measurement. No replacement evaluator is owed. Static test classification remains distinct from test execution and physical derivation.
- **Current disposition:** Existing repair and controls from original finding `review:2026-10-20-g4-population-and-inventory:infra:1.2` are integrated at `f2fca05a`. The current absent-only control blocks and is unmeasured; current typed coverage and consumer suites pass. Record the propagation closure through the existing writer, preserving the original donor finding and its scope.
- **Verify:** `uv run python -c "import sys; sys.path.insert(0,'scripts'); from readiness_gates import GraphIndex,_eval_computation_correctness; p={'id':'paper:control','type':'Paper','meta':{'formulas':['missing_control']}}; r=_eval_computation_correctness(p,GraphIndex({'nodes':[p],'links':[]})); assert r.state!='passed', r.evidence"`

### 1.4 — REQUIRED — Dependency scanner classifies the local papers namespace as a third-party distribution

- **Severity:** required
- **Lane:** infra
- **Location:** `tests/test_dependency_declaration.py::_local_module_names`, `tests/test_gravitational_waves.py::TestWindowNumericalPrecision.test_d3_width_ratio_uses_the_exact_algebraic_width`
- **Observed:** The declaration suite fails with `papers <- tests/test_gravitational_waves.py`. That regression imports the actual local `papers.D3.tables` producer. The repository contains a namespace directory rather than a top-level papers.py or a direct papers/__init__.py. The scanner collects file stems and immediate parent names and does not recognize this namespace root. No external papers distribution supplies the producer.
- **Expected:** Recognize actual local namespace packages without hiding genuinely undeclared third-party imports. Preserve the exact-width regression's numerical strength; the publication renderer's rounded scalar output is insufficient to replace its full-precision assertion.
- **Next action:** Lead owns the minimal scanner repair through architecture-change review, with independent real namespace and undeclared-external controls. This is a full-qualification blocker, distinct from the independently accepted scalar speed repair.
- **Evidence:** `DEPENDENCY_FAILURE.txt` records one failure and four passes in the existing declaration suite. No repair or acceptance is asserted.
- **Verify:** `uv run python -m pytest tests/test_dependency_declaration.py::test_every_third_party_import_is_declared -q`

The Verify commands assert the original missing requirements. Their original
failures are preserved in the reproduction evidence; current passing results,
independent reviews and canonical closure records must be read separately.
Producer and evaluator regressions are part of the accepted repairs documented
above. L1 sentence targets were separately corrected to exact source identifiers
with scope qualifications. That sentence repair alone did not close these
machinery findings.

- **Current implementation evidence for1.4:** [Accepted design](NAMESPACE_SPEC_REVIEW.md)
  and [independent implementation review](NAMESPACE_IMPLEMENTATION_REVIEW.md)
  cover the minimal root-component extension to the existing helper. The
  [original failure](NAMESPACE_BEFORE.txt), [new red regression](NAMESPACE_RED.txt)
  and [116 passing focused cases](NAMESPACE_AFTER.txt) preserve both directions,
  including a real external-import seed, restored bytes/mtime and the unchanged
  exact D3 regression. The [population pilot](NAMESPACE_POPULATION.json) affects
  only the imported papers root. [Freshness checks](NAMESPACE_FRESHNESS.txt)
  pass3/3. The existing writer records1.4 fixed at06aacc0e2; its declared seven-case suite passes. [Closure receipt](NAMESPACE_CLOSURE.txt) preserves the actual writer result.
- **Verify:** `uv run python -m pytest tests/test_dependency_declaration.py -q`
