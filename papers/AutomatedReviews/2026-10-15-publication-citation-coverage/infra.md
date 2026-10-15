---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: publication-chat-lead
review_date: 2026-10-15T00:00:00Z
kind: focused-citation-coverage
---

# Current cited-key identity and source-fidelity coverage

Base: `7f7888101e29a1a2c6ea63822db2c991e9588bb5`. Independent final scientific/source/artifact review accepted the bounded package; see SCOPED_REVIEW.md. The separate ledger audit accepted the supported closure; see SCOPED_REVIEW.md. No test or acquisition was performed by this evidence author. Set REPO to the candidate root and use the existing project environment as python3 on PATH. The exact declared command passed in lead and independent review.

### 1.1 — REQUIRED — Resolve the twelve current missing cited keys without conflating manuscript identities or source editions

- **Severity:** required
- **Lane:** `pyrust`
- **Target:** `src/core/citations.py`, `docs/primary_sources_state.json`, `papers/D8/bibliography.bib`, citation-bearing passages and bibliographies in `papers/D1/paper_draft.tex`, `papers/D2/paper_draft.tex`, `papers/D3/paper_draft.tex`, `papers/D4/paper_draft.tex`, `papers/D9/paper_draft.tex`
- **Location:** `src/core/citations.py` exact twelve missing-key registrations and source paths; `papers/D8/bibliography.bib` three existing companion entries; affected citing passages/bibliographies named above.
- **Gate:** CitationIntegrity
- **Verify:** `cd "$REPO" && python3 -m pytest tests/test_phase6i_wave1.py::test_no_missing_from_registry tests/test_phase6i_wave1.py::test_extract_missing_bibkeys_emits_no_orphans -m '' -q && python3 -c 'import sys; sys.path.insert(0,"scripts"); from validate import check_citation_primary_sources_present; r=check_citation_primary_sources_present(); assert r.passed, r'`
- **Observed at base:** The two existing coverage tests fail: 517 cited keys, 505 registered, nine extracted stubs and three apparent orphans. Eight keys identify internal manuscripts; four identify external sources. The three D8 orphan entries already exist in BibTeX, which the inline-bibitem extractor does not read. Several stale titles or directly cited statements require source-identity reconciliation.
- **Expected:** Preserve citing keys and historical entries while registering actual internal manuscript titles/authors and explicit in-preparation status. Reconcile existing BibTeX rather than adding parallel inline entries. Register the four external identities with truthful held-source fidelity. Correct only the directly unsupported citation-bearing statements. Use real pinned acquisitions where the existing key-based cache lookup requires new-key artifacts; preserve old files and fetch histories. Do not alter tests, assertions, ceilings, exemption classes, formulas or proofs.
- **Baseline:** The lead actually ran both targeted tests at the base: two failures in 1.23 seconds, nine stubs and three orphans. The historical ten-stub observation is not this baseline. The final compound Verify also asserts the existing complete citation check, so registry coverage alone cannot hide a new key-based cache fault.
- **Evidence:** SOURCE_ASSESSMENT.md identifies all twelve keys, actual source editions and hashes, three real pinned PDF fetches, metadata-only Verlinde acquisition, preserved historical entries, focused tests, six manuscript compiles and lead pixel inspection. Initial shared-path aliases introduced three new cache-resolution faults; these were repaired by actual existing-writer fetches, not classified as unrelated debt. Final combined focused tests report fourteen passes, and the existing complete citation check reports no missing registry keys or needed cache artifacts.
- **Limits:** Passing coverage/cache checks is not full-body coverage, scientific acceptance or publication readiness. Metadata-only and abstract-only fidelity warnings remain explicit, and all reported overfull boxes remain unwaived. Final independent source/whole-claim/artifact review is accepted; the separate ledger audit accepted preservation of prior records and the single supported addition.
