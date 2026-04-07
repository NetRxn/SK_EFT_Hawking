# Phase 5o: Community Value — Bridges, Verification, and Extraction

## Technical Roadmap — April 2026

*Prepared 2026-04-07 | Follows Phase 5l (topological quantum computation)*

**Entry state:** Complete verified pipeline: quantum groups → MTCs → braiding gates → universality. 101 Lean modules, 8145 jobs, 31 sorry. The infrastructure has value beyond this project — this phase extracts and amplifies that value.

**Motivation:** We've built the world's first verified topological quantum computation pipeline. Phase 5o asks: how do we maximize the impact of this work for others?

---

## Wave 1 — Kazhdan-Lusztig Bridge
**Goal:** Connect our quantum group pillar to our MTC pillar via the KL equivalence.

**Deep research:** `Phase-5o-W1_Kazhdan_Lusztig_equivalence_formalizability.md` — SUBMITTED

- [ ] Assess formalizability from deep research results
- [ ] State Rep(u_q(sl_2)) ≅ SU(2)_k-MTC as a Lean structure (possibly with sorry)
- [ ] Verify the data-level equivalence: simples, fusion rules, braiding match
- [ ] For k=1,2,3: exhaustive verification that both sides produce identical data

**Dependencies:** RestrictedUq.lean, RepUqFusion.lean, SU2kMTC.lean, FibonacciMTC.lean

---

## Wave 2 — Literature Error Survey
**Goal:** Systematically verify or falsify algebraic identities from the braiding literature.

**Deep research:** `Phase-5o-W2_braiding_literature_error_survey.md` — SUBMITTED

- [ ] Collect explicit identities from top 20 papers
- [ ] Verify each against our native_decide infrastructure
- [ ] Document convention differences vs genuine errors
- [ ] Publish findings (would be a high-impact standalone result if errors found)

**Dependencies:** IsingBraiding.lean, QCyc5.lean, FibonacciBraiding.lean, QCyc5Ext.lean

---

## Wave 3 — Experimental Predictions
**Goal:** Connect verified braiding data to measurable quantities.

**Deep research:** `Phase-5o-W3_experimental_interferometry_predictions.md` — SUBMITTED

- [ ] Compute interferometric phases from our verified R-matrices
- [ ] Thermal Hall conductance from Gauss sum / central charge
- [ ] Topological entanglement entropy from total quantum dimension D
- [ ] Specific predictions for ν=5/2 (Ising) vs ν=12/5 (Fibonacci)
- [ ] Add experimental prediction functions to formulas.py with Lean refs

**Dependencies:** IsingBraiding.lean (Gauss sum), WRTComputation.lean (D²), QCyc5.lean

---

## Wave 4 — Mathlib Extraction
**Goal:** Contribute the most useful infrastructure back to the community.

**Deep research:** `Phase-5o-W4_Mathlib_extraction_strategy.md` — SUBMITTED

- [ ] Assess gap between our typeclasses and Mathlib's categorical hierarchy
- [ ] Extract PivotalCategory / RibbonCategory as standalone PR candidates
- [ ] Extract decidable number field library (or bridge to Mathlib's AdjoinRoot)
- [ ] Coordinate with Mathlib maintainers on PR strategy

**Dependencies:** SphericalCategory.lean, RibbonCategory.lean, FusionCategory.lean, QSqrt2/QSqrt5/QCyc5/QCyc16/QCyc5Ext

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | Kazhdan-Lusztig formalizability | Phase-5o-W1_... | SUBMITTED |
| 2 | Literature error survey | Phase-5o-W2_... | SUBMITTED |
| 3 | Experimental predictions | Phase-5o-W3_... | SUBMITTED |
| 4 | Mathlib extraction strategy | Phase-5o-W4_... | SUBMITTED |

---

*Phase 5o roadmap. Created 2026-04-07. All 4 deep research tasks submitted. This phase focuses on EXTERNAL VALUE: bridging our two pillars (quantum groups ↔ MTCs), catching literature errors, connecting to experiment, and contributing to the open-source ecosystem.*
