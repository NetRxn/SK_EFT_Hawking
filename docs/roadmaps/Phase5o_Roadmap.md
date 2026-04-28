# Phase 5o: Community Value — Bridges, Verification, and Extraction

## Technical Roadmap — April 2026

*Prepared 2026-04-07 | Updated 2026-04-07. Follows Phase 5l (topological quantum computation)*

**Entry state:** Complete verified pipeline: quantum groups → MTCs → braiding gates → universality. ~103 Lean modules, 8145 jobs, ~27 sorry (down from 33 after Aristotle 986b9f66). The infrastructure has value beyond this project — this phase extracts and amplifies that value.

**Motivation:** We've built the world's first verified topological quantum computation pipeline. Phase 5o asks: how do we maximize the impact of this work for others?

---

## Wave 1 — Kazhdan-Lusztig Bridge
**Goal:** Connect our quantum group pillar to our MTC pillar via the KL equivalence.

**Deep research:** `Lit-Search/Phase-5o/Formalizing Kazhdan-Lusztig in Lean 4- a feasibility assessment.md` — **COMPLETE**

**Key findings:** Full categorical KL equivalence infeasible (200-page analytic proof). Strategy 1 (data verification for k=1,2,3) achievable now. Strategy 2 (Andersen-Paradowski algebraic pipeline) is 6-12 month project.

- [ ] Assess formalizability from deep research results
- [ ] State Rep(u_q(sl_2)) ≅ SU(2)_k-MTC as a Lean structure (possibly with sorry)
- [x] Verify the data-level equivalence: Verlinde formula for k=1,2 (lean-tensor-categories/VerlindeFormula.lean)
- [ ] For k=3: exhaustive verification that both sides produce identical data

**Dependencies:** RestrictedUq.lean, RepUqFusion.lean, SU2kMTC.lean, FibonacciMTC.lean

---

## Wave 2 — Literature Error Survey (**COMPLETE**)
**Goal:** Systematically verify or falsify algebraic identities from the braiding literature.

**Deep research:** `Lit-Search/Phase-5o/Algebraic identities in anyonic braiding- a cross-literature audit.md` — **COMPLETE**

**Result: ZERO genuine errors found across 13 major papers.** All apparent disagreements reduce to:
- **Chirality convention** (Fibonacci R-matrix: e^{±4πi/5}) — our choice (B) matches Wang, Rowell, Simon, Preskill
- **Gauge freedom** (R^{σψ}_σ = ±i) — both valid, sign is Z₂ vertex gauge
- **Number field obstruction** (√φ ∉ Q(ζ₅)) — only Rowell-Stong-Wang 2009 addresses this; our QCyc5Ext is the first formalization

- [x] Collect explicit identities from top 13 papers
- [x] Verify each against our native_decide infrastructure
- [x] Document convention differences vs genuine errors — **all CONVENTION_DIFFERENCE, zero MISMATCH**
- [ ] Publish findings as appendix to Paper 14 (convention taxonomy has standalone value)

**Dependencies:** IsingBraiding.lean, QCyc5.lean, FibonacciBraiding.lean, QCyc5Ext.lean

---

## Wave 3 — Experimental Predictions
**Goal:** Connect verified braiding data to measurable quantities.

**Deep research:** `Lit-Search/Phase-5o/From verified braiding algebra to laboratory observables.md` — **COMPLETE**

**Key findings:** 5 observables distinguish Ising from Fibonacci (interferometric visibility, thermal Hall, TEE, quasiparticle charge, GSD). Banerjee 2018 confirmed κ_xy/T = 2.5κ₀ for ν=5/2 (Ising c=1/2). Fibonacci predictions at ν=12/5 await experiment.

- [x] Compute interferometric phases from our verified R-matrices — `interferometric_visibility()` in formulas.py
- [x] Thermal Hall conductance from Gauss sum / central charge — `thermal_hall_conductance()` in formulas.py
- [x] Topological entanglement entropy from total quantum dimension D — `topological_entanglement_entropy()` in formulas.py
- [x] Specific predictions for ν=5/2 (Ising) vs ν=12/5 (Fibonacci) — `distinguishing_observables_table()` in formulas.py
- [x] Add experimental prediction functions to formulas.py with Lean refs — 10 functions, 24 tests (test_braiding.py), all pass
- [x] 3 figures: fig_ising_braiding_data, fig_fibonacci_braiding_data, fig_experimental_predictions in visualizations.py

**Dependencies:** IsingBraiding.lean (Gauss sum), WRTComputation.lean (D²), QCyc5.lean

---

## Wave 4 — Mathlib Extraction (**COMPLETE**)
**Goal:** Contribute the most useful infrastructure back to the community.

**Deep research:** `Lit-Search/Phase-5o/Mathlib contribution strategy for categorical and number field infrastructure.md` — **COMPLETE**

**Deliverable:** `lean-tensor-categories` library at `/OpenSourceContrib/MathLib/lean-tensor-categories/`
- 20 files, 2026 lines, 114 theorems, 78 defs/classes
- Zero sorry, zero warnings, zero errors
- Categorical hierarchy: Pivotal → Spherical → Balanced → Ribbon → Semisimple → Fusion → Modular
- Hopf modules: QuasitriangularBialgebra, RibbonHopfAlgebra, DiagonalAction
- Number fields: QSqrt2, QSqrt5, QCyc5, QCyc16, QCyc5Ext, ComputableAdjoinRoot
- Instances: SU(2)_k fusion (k=1-4), Ising MTC, Fibonacci MTC, Verlinde formula

- [x] Assess gap between our typeclasses and Mathlib's categorical hierarchy
- [x] Extract PivotalCategory / RibbonCategory as standalone PR candidates
- [x] Extract decidable number field library (+ ComputableAdjoinRoot bridge)
- [x] Build QuasitriangularBialgebra / RibbonHopfAlgebra
- [x] Build Verlinde formula verification (KL data level)
- [ ] Coordinate with Mathlib maintainers on PR strategy (Zulip discussion)

**Dependencies:** SphericalCategory.lean, RibbonCategory.lean, FusionCategory.lean, QSqrt2/QSqrt5/QCyc5/QCyc16/QCyc5Ext

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | Kazhdan-Lusztig formalizability | Lit-Search/Phase-5o/Formalizing Kazhdan-Lusztig... | **COMPLETE** |
| 2 | Literature error survey | Lit-Search/Phase-5o/Algebraic identities in anyonic braiding... | **COMPLETE** |
| 3 | Experimental predictions | Lit-Search/Phase-5o/From verified braiding algebra... | **COMPLETE** |
| 4 | Mathlib extraction strategy | Lit-Search/Phase-5o/Mathlib contribution strategy... | **COMPLETE** |

---

*Phase 5o roadmap. Created 2026-04-07, updated 2026-04-07. All 4 deep research complete. W2 COMPLETE (zero errors found). **W3 COMPLETE** (10 prediction functions + 3 figures + 24 tests). W4 COMPLETE (lean-tensor-categories library built). W1 partial (Verlinde k=1,2 done).*

---

## Append-only Wave: Mathlib lean-tensor-categories Upstream PR Cycle

*Appended 2026-04-28 | Trigger: post-Phase 6 gap analysis (`temporary/Research-Overview/research_overview_analysis.md`, 2026-04-28). Status: **OPEN — relationship-building gate**.*

### Wave 5 — `Mathlib_Upstream_PR_Cycle` [5o.5] [Pipeline: Stage 1 + community engagement]

**Goal.** Move the `lean-tensor-categories` library (W4 deliverable: 20 files, 2026 lines, 114 theorems, 78 defs/classes, zero sorry) from project-local artifact to upstream Mathlib4 contributions. Establish the relationship-building / Zulip / GitHub PR pipeline that Mathlib's AI-content policy requires before any PR is accepted.

**Rationale (Phase 6 gap-analysis).** Each Mathlib merge of project-extracted infrastructure multiplies the program's citation footprint and forces external sanity-checking. The 114-theorem library (categorical hierarchy: Pivotal → Spherical → Balanced → Ribbon → Semisimple → Fusion → Modular; QuasitriangularBialgebra + RibbonHopfAlgebra; decidable number fields Q(√2), Q(√5), Q(ζ_5), Q(ζ_16); Verlinde formula + SU(2)_k k=1-4 + Ising MTC + Fibonacci MTC) sits ready but not upstreamed. This is the highest-leverage outreach action available to the program.

**Trigger condition (relationship-building gate):** This wave activates after:
- (R1) Mathlib Zulip introduction — the project's principal investigator (or designated maintainer) introduces the lean-tensor-categories work in `#mathlib4 > new contributors` and `#mathlib4 > maths > category theory` streams. Establishes context, gathers initial reactions.
- (R2) AI-content disclosure conversation — the project's pipeline (Lean theorems generated with substantive AI-tool assistance under human direction) is openly disclosed; consensus reached with Mathlib maintainers on how to attribute / review / accept such contributions.
- (R3) PR-strategy discussion — sub-PR sequencing agreed: smallest atomic PRs first (e.g., `QSqrt2` decidable number field), then larger ones (PivotalCategory, RibbonCategory typeclasses, then Hopf-algebra pieces, then full MTC instances).

**Status (2026-04-28):** **GATED on R1/R2/R3.** No PRs filed yet. The W4 todo-checkbox "Coordinate with Mathlib maintainers on PR strategy (Zulip discussion)" is restated here as the active blocker.

### Sub-waves

#### Sub-wave 5.1 — Zulip introduction + AI-content disclosure (R1 + R2)

**Goal.** Open the conversation. Post in `#mathlib4 > new contributors` and `#mathlib4 > maths > category theory` introducing the lean-tensor-categories work and disclosing the project's AI-assisted formalization pipeline. Gather feedback on:
- Structural fit with Mathlib's existing categorical hierarchy.
- AI-content policy interpretation for substantive theorem-proving (not just docstring polishing).
- Recommended PR cadence and reviewer assignments.

**Output.** Working memo: `temporary/working-docs/phase5o_W5_mathlib_zulip_intro.md` documenting the conversation, maintainer reactions, agreed cadence.

**Estimated LOE:** 1 PM (asynchronous; multi-week elapsed time for community-response cycle).

#### Sub-wave 5.2 — Atomic PR 1: QSqrt2 + decidable number field bridge (post R1+R2)

**Goal.** First atomic PR — the smallest piece. `QSqrt2` decidable equality + `ComputableAdjoinRoot` bridge. Self-contained, broad utility (number theory + algebraic geometry contexts), low review-overhead.

**Module:** Mathlib `Mathlib/NumberTheory/QuadraticField/Basic.lean` extension or new file.

**Acceptance criteria:** PR merged or revisions-cycle complete with reviewer agreement on path forward.

**Estimated LOE:** 1–2 PM (PR drafting + review iterations).

#### Sub-wave 5.3 — Atomic PR 2: PivotalCategory + RibbonCategory typeclasses (post 5.2)

**Goal.** Second PR — categorical-hierarchy infrastructure. PivotalCategory and RibbonCategory typeclasses extending Mathlib's existing `MonoidalCategory`, `BraidedCategory`. Sphericalcategory follows in its own PR if reviewers prefer.

**Module:** Mathlib `Mathlib/CategoryTheory/Monoidal/Pivotal.lean` (new) and `Mathlib/CategoryTheory/Monoidal/Ribbon.lean` (new).

**Acceptance criteria:** PR merged with reviewer sign-off on the typeclass hierarchy.

**Estimated LOE:** 2–3 PM.

#### Sub-wave 5.4 — Atomic PR 3+: HopfAlgebra extensions (QuasitriangularBialgebra, RibbonHopfAlgebra)

**Goal.** Third PR cluster — Hopf-algebra structure. QuasitriangularBialgebra and RibbonHopfAlgebra typeclasses; depends on existing Mathlib Hopf-algebra infrastructure.

**Module:** Mathlib `Mathlib/RingTheory/HopfAlgebra/Quasitriangular.lean` (new) etc.

**Estimated LOE:** 2–3 PM.

#### Sub-wave 5.5 — Atomic PR 4+: MTC instances (Ising, Fibonacci, SU(2)_k)

**Goal.** Fourth PR cluster — concrete MTC instances. Lower priority for upstreaming since these are physics-flavored; may stay project-local based on reviewer preference.

**Estimated LOE:** 2–4 PM (only if reviewers accept the MTC scope upstream).

#### Sub-wave 5.6 — Iterative review cycle + project-local sync

**Goal.** Mathlib pinned commit may bump as PRs land; project's `lean/lakefile.toml` Mathlib commit pin (`8850ed93` as of 2026-04-28) needs periodic update. Sub-wave 5.6 covers each Mathlib re-pin + downstream module re-build verification.

**Estimated LOE:** 0.5 PM per Mathlib re-pin × N re-pins.

### Strengthening checklist

- (Process integrity): every PR must follow Mathlib's contribution guide (`docs/CONTRIBUTING.md` upstream).
- (AI-content disclosure): every PR description must transparently state "drafted with AI-tool assistance under human review and direction" per the agreed disclosure language from sub-wave 5.1.
- (Zero-regression): each PR must not introduce new sorry / axiom / unsafe content.

### Total LOE estimate

- Sub-wave 5.1 (R1+R2 introduction): 1 PM
- Sub-waves 5.2–5.5 (atomic PRs): 7–13 PM
- Sub-wave 5.6 (iterative re-pin): 0.5 PM × N
- **Total: 8–14+ PM**, spread over 6–12 months elapsed (community-pace)

### Cross-phase impact

- Project's `lean/lakefile.toml` Mathlib pin advances on each merged PR.
- Each merged PR is a citation multiplier for the project's papers (Mathlib publication credit + external sanity-check signal).
- `lean-tensor-categories` library: stays project-local until each piece lands upstream; once fully upstreamed, the project-local copy is deprecated in favor of `import Mathlib.CategoryTheory.Monoidal.Pivotal` etc.

### Deliverables

- Mathlib PRs (per sub-wave).
- `temporary/working-docs/phase5o_W5_mathlib_zulip_intro.md` (sub-wave 5.1 memo).
- Updated `lean/lakefile.toml` Mathlib pin (per sub-wave 5.6 cycle).
- `Phase 6_Deferred_Targets.md` entry deprecation as PRs land.

*Append-only addition 2026-04-28. Status: GATED on Mathlib relationship-building (sub-wave 5.1). Highest-leverage near-term outreach action per Phase 6 gap-analysis.*
