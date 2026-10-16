---
paper: infra
bundle: infra
bundle_target: infra
review_date: 2026-10-16
kind: targeted-infra
readiness_gates_version: 1
---

# Dashboard artifact and read-query boundaries

Source observations at `db72be9d79eb8729eb95d481ddea05e6261fdeb4` require a reviewed
specification and isolated verification. This record does not establish an exploit,
security closure or scanner waiver. The current aggregate CodeQL failure remains.

### 1.1 — Dashboard artifact and read-query guarantees stop before their final consumers

- **Severity:** minor
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `scripts/provenance_dashboard.py`, `docs/architecture/DASHBOARD.md`, `tests/test_paper_provenance_v2.py`, `tests/test_graph_dashboard.py`, `scripts/build_graph.py`, `docs/KNOWLEDGE_GRAPH.md`, `scripts/readiness_gates.py`, `scripts/sentence_state.py`, `src/core/paper_artifacts.py`, `src/core/dashboard_queries.py`, `tests/test_paper_artifact_boundaries.py`, `tests/test_dashboard_read_queries.py`, `tests/test_readiness_cannot_measure.py`, `tests/test_readiness_gate_evaluators.py`, `tests/e2e/conftest.py`, `tests/e2e/test_paper_provenance_tab.py`, `tests/e2e/dummy_paper_server.py`, `tests/e2e/test_readiness_tab.py`
- **Observed:** `_safe_paper_dir` validates and confines the selected directory. The direct claims, figure, prose-state, audit and TeX readers and related graph-ingestion readers append fixed children without resolving and confining the final target. An escaping child symlink is therefore a conditional filesystem boundary gap; no HTTP-input-only traversal is demonstrated. The free-form Cypher endpoint rejects listed writes, stacking and selected SQL comments and checks its dollar delimiter, but uses the configured database credential without explicit read-only transaction or execution bounds. Its comments claim parameter binding and accepted triage beyond the observed implementation.
- **Evidence:** `scripts/provenance_dashboard.py:85`, `:1958`, `:2021`, `:2800`, `:2813`, `:2842`, `:2866`, `:3525`. The complete dashboard/QA/gate owner reads leave final-child and database-capability policy unspecified. Existing controls are material; scanner titles alone do not establish exploitability.
- **Expected:** Extend the existing reader/query boundaries under the existing dashboard owner. Specify final artifact containment and writer/race trust; preserve supported free-form reads while demonstrating enforced read capability and execution bounds on disposable matching AGE. Preserve sole JSON/audit writers and normal response behavior.
- **Reader scope:** Include paper-derived claims/prose/audit reads delegated to the sentence-state writer and its independent papers root. Promote read confinement without retargeting lexical writer helpers; preserve lock/validation/audit-first/atomic-replacement/replay semantics and controlled prerequisite refusal. Explicit supplied CLI source files have a distinct input contract.
- **Candidate status:** Canonical owner/spec were updated before the implementation package. Source is present with worker isolated tests and ROOT disposable actual helper/Flask-route evidence; fresh independent implementation review, full reader/writer/browser gates and newest exact-head CodeQL/main acceptance remain. No Verify or closure is claimed.
- **Verification status:** A closure command is deliberately not declared before the specification and meaningful regression/pilot coverage are reviewed. This finding is nonclosable at intake. Existing passing tests alone do not establish the missing boundaries.
- **Limits:** No production graph, real paper mutation, host reload or permission/suppression change is authorized by this finding. Source observations describe control-policy gaps, not proven SQL breakout, data disclosure or arbitrary side effects. Severity here describes the evidenced process/control gap.

### 1.2 — Sentence controls omit their required verification state

- **Severity:** minor
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `scripts/provenance_dashboard.py`, `scripts/templates/partials/paper_provenance_tab.html`, `docs/architecture/DASHBOARD.md`, `tests/test_paper_provenance_v2.py`, `tests/e2e/test_paper_provenance_tab.py`, `tests/e2e/dummy_paper_server.py`
- **Observed:** Real dummy Chromium click sends only dashboard signals and receives HTTP400 because required state is missing. Generated buttons, keyboard shortcuts and cluster propagation use an unsupported action `body` option with the pinned Datastar v1.0.1.
- **Expected:** Use the supported object payload and await the mutation before refreshing provenance, keeping schema validation and the sole writer.
- **Verification status:** Open. Real dummy browser writer/audit/reload and independent review required; no closure claimed.

### 1.3 — Window shortcuts dispatch competing verification actions

- **Severity:** minor
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `scripts/templates/partials/paper_provenance_tab.html`, `docs/architecture/DASHBOARD.md`, `tests/e2e/test_paper_provenance_tab.py`, `tests/e2e/conftest.py`, `tests/e2e/dummy_paper_server.py`
- **Observed:** After four successful actual dummy button writes, a keyboard v event yields an Interpretive POST. Existing window shortcut modifier spelling does not perform the intended filtering with the pinned runtime.
- **Expected:** Explicit exact evt.key guards precede each existing action, including navigation and reset. Only matching arrow shortcuts prevent default. One verification state and audit event per state key.
- **Verification status:** Open; actual red regression preserved. Fresh real-browser and independent review required; no closure.

### 1.4 — Disposable browser audit loses lexical artifact identity

- **Severity:** minor
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `tests/e2e/dummy_paper_server.py`, `tests/test_paper_artifact_boundaries.py`, `docs/architecture/DASHBOARD.md`
- **Observed:** The audit sentinel resolves a path before testing its artifact basename and corpus origin. A lexical claims-review link to a differently named outside target can evade the sentinel. Independent review CTRL-R1-MIN1 establishes a fixture guard gap; no actual outside read is established.
- **Expected:** Preserve lexical origin and identity separately from resolved confinement; record refusals before assertions and refuse ambiguous relative artifact opens. Actual-hook negative controls must preserve allowed ordinary and in-root linked reads.
- **Verification status:** Open. Existing browser pass remains historical evidence; corrected guard, negative controls, fresh browser run and independent review are required. Whole-template wrapper isolation remains unaccepted separately.

### 1.5 — Shared SSE responses advertise conflicting connection semantics

- **Severity:** minor
- **Lane:** infra
- **Gate:** FixPropagation
- **Location:** `scripts/datastar_helpers.py`, `docs/architecture/DASHBOARD.md`, `tests/e2e/dummy_paper_server.py`, `tests/e2e/test_paper_provenance_tab.py`
- **Observed:** Actual SSE responses advertise `Connection: keep-alive, close`. In a failing dummy browser run, reload is requested without reaching Flask; the owned Werkzeug server is blocked draining the preceding connection. Its local implementation explicitly assumes close semantics when draining. A single-variable dummy pilot removing the helper's keep-alive header passes the unchanged full browser workflow with close semantics and completed requests.
- **Expected:** Leave hop-by-hop connection framing to the HTTP server while preserving event type, cache/buffering policy and generator behavior. Verify normal product responses without an experimental fixture override.
- **Verification status:** Open. Pilot is evidence for the scoped correction, not full acceptance. Current normal browser, shared helper review, infra gates and closure remain required. Earlier keyboard waits are not independently assigned a cause.
