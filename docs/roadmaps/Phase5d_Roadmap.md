# Phase 5d: ADW Tetrad Gap Equation — Emergent Gravity Feasibility

## Technical Roadmap — April 2026

*Prepared 2026-04-04 | Follows Phase 5c (quantum groups, MTC, E8, verified statistics)*

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read this roadmap for wave assignments
> 3. Read deep research (see §0 below) — extensive prior corpus exists
> 4. Read Aristotle reference: `docs/references/Theorm_Proving_Aristotle_Lean.md`

---

## 0. Entry State and Research Corpus

### What Phase 5c established:
- 1084 theorems, 0 axioms, 74 Lean modules, 39 sorry pending Aristotle
- Quantum group chain: Onsager → O_q → U_q(sl₂) Hopf → U_q(ŝl₂) → u_q → SU(2)_k MTC
- First RibbonCategory/MTC definitions in any proof assistant
- E8 lattice verified, algebraic Rokhlin disproved (σ=8 ≢ 0 mod 16)
- Hypothesis tracking infrastructure (HYPOTHESIS_REGISTRY, graph integration)
- Verified statistical estimators (jackknife, autocorrelation)

### Existing ADW/gravity infrastructure (71 theorems across 5 modules):
- `ADWMechanism.lean` — 21 theorems: critical coupling G_c, NG modes, gap equation structure
- `WetterichNJL.lean` — 18 theorems: Fierz completeness, scalar/pseudoscalar/vector channels, NJL-ADW correspondence
- `VestigialSusceptibility.lean` — 16 theorems: gamma trace, bubble integral Π₀, RPA susceptibility, vestigial_before_tetrad, exponential window
- `FermionBag4D.lean` — 16 theorems: SO(4) integration, 8-fermion bounds, bag positivity
- `GaugeFermionBag.lean` — 9 theorems: tetrad gauge covariance, metric invariance, bag weight real

### Existing Python infrastructure:
- `src/vestigial/hs_rhmc_torch.py` — PyTorch RHMC production code (Wave 7C)
- `src/vestigial/fermion_bag.py` — Fermion-bag MC algorithm
- `src/vestigial/phase_scan.py` — 4D coupling scan with Binder cumulant
- `src/adw/gap_equation.py` — Coleman-Weinberg V_eff
- `src/adw/fluctuations.py` — SSB, NG modes, Vergeles check

### Deep research corpus (read these — ordered by relevance):

**Phase 5c (newest, most directly relevant):**
- `Lit-Search/Phase-5c/Bridging Wen's emergent QED with ADW tetrad gravity.md` — **PRIMARY REFERENCE.** Full Wen+ADW chain. Explicit gap equation: e^a_μ = G ∫ Tr[γ^a p_μ S(p; e)] d⁴p/(2π)⁴. NJL reduction: Δ = G·Δ·I(Δ), G_c = 1/I(0). Lean formalization via IVT + Banach contraction. Three parallel workstreams defined.

**Phase 5 (computational details):**
- `Lit-Search/Phase-5/Vestigial metric susceptibility from ADW tetrad condensation.md` — Explicit V_eff, G_c = 8π²/(N_f Λ²), vestigial window exponentially narrow in 4D. RPA bubble formalism. Lean formalizability assessed.
- `Lit-Search/Phase-5/HS+RHMC for ADW tetrad condensation with 8×8 Majorana fermions on Spin(4) lattice.md` — Complete RHMC algorithm specification. O(V√κ) scaling. Zolotarev rational approximation. Force computation. Cost estimates L=4 through L=16.
- `Lit-Search/Phase-5/ADW tetrad condensation lattice formulation.md` — 8×8 Majorana formulation. Tetrad bilinear is complex, Option A metric gives real result. Quaternionic Cl(4,0) structure.
- `Lit-Search/Phase-5/The 8×8 Majorana formulation for ADW fermion-bag Monte Carlo.md` — Kramers degeneracy → sign-free MC. Block structure.
- `Lit-Search/Phase-5/Phase_5_follow-up_Effective nearest-neighbor action in ADW tetrad condensation after SO(4) Haar integration.md` — SO(4) Haar → full multi-fermion tower. Leading 4-fermion coupling is attractive.
- `Lit-Search/Phase-5/Hybrid fermion-bag + gauge-link Monte Carlo for ADW tetrad condensation.md` — Hybrid algorithm combining fermion-bag with gauge links.

**Phase 3 (foundational):**
- `Lit-Search/Phase-3/The ADW mean-field gap equation for tetrad condensation with emergent Dirac fermions.md` — Original identification: no explicit HS decomposition published. Vladimirov-Diakonov lattice phases. Volovik vestigial hierarchy.

**Task prompts (for context on what was asked):**
- `Lit-Search/Tasks/complete/ADW_gap_equation_emergent_gravity.txt` — Original research prompt
- `Lit-Search/Tasks/complete/Phase5_5A_fang_gu_adw_calculation_chain.txt` — Fang-Gu topological supergravity chain
- `Lit-Search/Tasks/complete/Phase5_vestigial_correlator_simulation_scoping.txt` — MC scoping
- `Lit-Search/Tasks/complete/Phase5_vestigial_analytical_susceptibility.txt` — Analytical susceptibility

### Key physics finding across the entire corpus:
> **The tetrad gap equation has never been explicitly written down in the published literature.** The equation is structurally determined by the NJL-ADW correspondence. The critical coupling G_c is O(1) in lattice units (Vladimirov-Diakonov found this for the chiral channel in 2D). The 4D tetrad channel is untested. No published work combines Wen's emergent QED with ADW tetrad gravity. This is genuinely unexplored territory.

### Cross-validation:
Phase-5 vestigial research gives G_c = 8π²/(N_f Λ²). Phase-5c gap equation gives G_c = 1/I(0) = 2/(c₄Λ²). These are consistent (c₄ = 1/(8π²) with N_f = 1). The two independent derivations agree.

---

## 1. Wave 1 — Analytic Gap Equation [~15-20 theorems]

**Goal:** Derive and solve the explicit continuum gap equation for the tetrad VEV.

### 1A. Gap Equation Formulation (Lean)
- [ ] Define `gapOperator G Λ Δ := G * Δ * ∫ p in Icc 0 Λ, ρ p / (p² + Δ²)` using Bochner integral
- [ ] Prove continuity of gapOperator in Δ (via dominated convergence)
- [ ] Prove gapOperator maps [0, Δ_max] → [0, Δ_max] (self-mapping for IVT)
- [ ] Define critical coupling G_c = 1/I(0)
- [ ] Prove G_c > 0 and explicit bounds via `MeasureTheory.integral_mono`

### 1B. Phase Transition (Lean)
- [ ] Trivial solution Δ = 0 always exists
- [ ] For G < G_c: trivial solution is unique (via Banach contraction — subcritical)
- [ ] For G > G_c: nontrivial solution exists (via IVT on g(Δ) = f_G(Δ)/Δ - 1)
- [ ] Monotonicity: Δ*(G) is increasing in G for G > G_c
- [ ] Phase transition characterization at G = G_c (bifurcation)

### 1C. ADW Connection (Lean)
- [ ] NJL-ADW correspondence: gap solution Δ ↔ tetrad VEV e^a_μ
- [ ] Connect to existing `ADWMechanism.lean` critical coupling theorem
- [ ] Connect to existing `VestigialSusceptibility.lean` r_e = 1/G - 1/G_c

**Template:** Picard-Lindelöf in Mathlib (`Mathlib.Analysis.ODE.PicardLindelof`) — same architecture (contraction mapping on integral operator).

**Estimated:** ~15-20 new theorems connecting to existing 71-theorem infrastructure.

### Deliverables:
- [ ] `lean/SKEFTHawking/TetradGapEquation.lean` — ~15-20 theorems
- [ ] `src/core/formulas.py` — `tetrad_gap_operator`, `tetrad_critical_coupling`, `tetrad_gap_solution` functions with Lean refs
- [ ] `tests/test_tetrad_gap.py` — tests for gap operator properties, G_c computation, phase transition
- [ ] Aristotle submission for sorry stubs (IVT/contraction proofs)
- [ ] Sorry gap registry entries in `aristotle_interface.py`

---

## 2. Wave 2 — Python Computation [~10 tests]

**Goal:** Solve the gap equation numerically for 4D tetrad channel and compare to vestigial susceptibility.

### 2A. Gap Equation Solver
- [ ] Implement 1D nonlinear integral equation solver (scipy.optimize or direct iteration)
- [ ] Compute G_c for d=4 tetrad channel with physical density of states ρ(p) = c₄·p³
- [ ] Compare to existing V_eff computation in `adw/gap_equation.py`
- [ ] Verify G_c consistency with Phase-5 vestigial result: G_c = 8π²/(N_f Λ²)

### 2B. Phase Diagram
- [ ] Map Δ*(G) curve: order parameter vs coupling
- [ ] Identify vestigial window G_ves < G < G_c from metric (4-point) condensate
- [ ] Compare to Vladimirov-Diakonov 2D results (scaling check)

### 2C. New MC Observables
- [ ] Tetrad order parameter: O_tet = (1/V) Σ_x ⟨Ê^a_μ(x)⟩
- [ ] Metric (vestigial) order parameter: O_met = η_ab ⟨Ê^a_μ Ê^b_ν⟩_conn
- [ ] Binder cumulant U₄ = 1 − ⟨O⁴⟩/(3⟨O²⟩²)
- [ ] Spatial correlator C(r) = ⟨Ê^a_μ(0) Ê^a_μ(r)⟩
- [ ] Add to existing `phase_scan.py` infrastructure

**Tests:** ~10 new tests validating gap equation solver, G_c computation, and observable definitions.

### Deliverables:
- [ ] `src/adw/tetrad_gap_solver.py` — 1D nonlinear integral equation solver, Δ*(G) curve
- [ ] `src/adw/tetrad_observables.py` — O_tet, O_met, U₄ Binder, spatial correlator C(r) definitions
- [ ] `tests/test_tetrad_gap_solver.py` — ~10 tests (G_c value, Δ curve, vestigial window, observable sanity)
- [ ] `src/core/formulas.py` updates — tetrad_gap_operator, tetrad_critical_coupling with Lean refs
- [ ] `src/core/constants.py` updates — any new physical parameters with provenance
- [ ] Figures: `fig_tetrad_phase_diagram` (Δ vs G), `fig_vestigial_window` (metric vs tetrad condensate) in `visualizations.py`

---

## 3. Wave 3 — Monte Carlo Production [computation-heavy]

**Goal:** Run lattice MC at L=4, 6, 8 targeting the gap equation's predicted critical region.

### Strategy (from deep research):
1. **L=4 broad scan:** Map coupling space with tetrad susceptibility and metric correlator
2. **L=4,6,8 targeted:** Binder cumulant analysis near identified transitions
3. **Cross-validate:** MF gap equation predicts G_c; MC confirms or refutes

### Key parameters:
- At d=4 (upper critical dimension), mean-field exponents are exact up to log corrections
- Pseudo-critical coupling shift: ΔG_c ~ L⁻² (6.25% at L=4, 1.56% at L=8)
- Vestigial window is exponentially narrow (BCS-like) — may require L≥8 to resolve
- Use existing RHMC production code with new observables from Wave 2C

### Deliverables:
- [ ] L=4 broad coupling scan data (stored in `data/tetrad_scan_L4/`)
- [ ] L=4,6,8 Binder cumulant crossing analysis
- [ ] Phase boundary map (coupling space with transition identified)
- [ ] Vestigial phase detection (or upper bound on window width)
- [ ] `notebooks/Phase5d_TetradGap_Technical.ipynb` — analysis notebook
- [ ] `notebooks/Phase5d_TetradGap_Stakeholder.ipynb` — accessible narrative

### Success criteria:
- **Confirms feasibility:** Nontrivial Binder crossing at O(1) coupling, spatial correlator C(r) ~ 1/r² or slower
- **Rules out:** No transition at any coupling, or only first-order (no continuum limit)
- **Vestigial detection:** Metric order parameter nonzero with zero tetrad order parameter

---

## 4. Wave 4 — Papers and Publication

**Goal:** Update existing paper drafts and finalize for submission.

### Paper 5 (ADW Gap) — UPDATE existing `papers/paper5_adw_gap/paper_draft.tex`
- Current state: Draft exists with title "Mean-field gap equation for tetrad condensation in the ADW mechanism: A fermion bootstrap test at Level 2"
- Updates needed:
  - [ ] Add explicit gap equation derivation for tetrad channel (first in literature)
  - [ ] Add mean-field phase diagram figures from Wave 2
  - [ ] Add Lean formalization section (IVT + Banach, ~15-20 theorems)
  - [ ] Add G_c numerical value and comparison to Vladimirov-Diakonov 2D result
  - [ ] Run claims-reviewer agent (physics-qa:claims-reviewer)
- Venue: Physical Review D

### Paper 6 (Vestigial) — UPDATE existing `papers/paper6_vestigial/paper_draft.tex`
- Current state: Draft exists with title "Vestigial Metric Phase in Emergent Gravity: Lattice Evidence from the ADW Model"
- Updates needed:
  - [ ] Add L=4,6,8 MC results from Wave 3
  - [ ] Add vestigial detection (or upper bound) figures
  - [ ] Add Binder cumulant crossing analysis
  - [ ] Update Lean theorem counts (VestigialSusceptibility + new TetradGapEquation)
  - [ ] Run claims-reviewer agent
- Venue: Physical Review D or PRL (if vestigial phase detected)

### Paper 12 (NEW, if warranted) — Wen+ADW connection paper
- Only if Wave 3 produces definitive results (positive or negative)
- Would be the first paper combining emergent QED with emergent gravity
- [ ] `papers/paper12_wen_adw/paper_draft.tex`
- Venue: PRL (if positive), PRD (if negative but informative)

### Notebooks:
- [ ] `notebooks/Phase5d_TetradGap_Technical.ipynb` — full computation chain
- [ ] `notebooks/Phase5d_TetradGap_Stakeholder.ipynb` — accessible narrative

### Stakeholder docs:
- [ ] `docs/stakeholder/Phase5d_Implications.md`
- [ ] `docs/stakeholder/Phase5d_Strategic_Positioning.md`

### Doc sync (Stage 12):
- [ ] Full Inventory + Index update
- [ ] README update
- [ ] Companion guide update

---

## 5. Assessment: Risk and Reward

### What makes this high-leverage:
- **Genuinely unexplored:** No published work combines Wen + ADW
- **The gap equation has never been written for the tetrad channel** — first explicit derivation
- **Publishable either way:** Positive → emergent gravity feasible. Negative → rules out a major route.
- **Maximum infrastructure reuse:** 71 existing Lean theorems + production MC code
- **Three independent workstreams** can proceed in parallel (analytic/computational/formal)

### Risks:
- Gap equation may have subtleties in the tetrad channel (derivative structure changes UV behavior)
- Vestigial window in 4D is exponentially narrow — may be unresolvable at L≤8
- Wen's emergent fermions may lack the correct spin-connection coupling for ADW
- The Vergeles unitarity proof requires fundamental Grassmann spinors — emergent fermions may not satisfy this

### Hypothesis tracking:
Any new hypotheses introduced should be registered in `HYPOTHESIS_REGISTRY` (constants.py) following the Phase 5c convention: explicit statement, eliminability assessment, dependent theorems, risk evaluation.

---

## 6. Dependencies and Non-Dependencies

| Item | Depends on Phase 5c? | Notes |
|------|----------------------|-------|
| Wave 1 (Lean gap equation) | NO | Uses existing ADW/NJL infrastructure |
| Wave 2 (Python computation) | NO | Uses existing gap_equation.py + phase_scan.py |
| Wave 3 (MC production) | NO | Uses existing RHMC + fermion-bag code |
| Wave 4 (Paper) | YES (Aristotle results) | Needs final theorem counts |
| Wen connection (future) | Partially | Needs effective coupling matching |

**Key principle:** Waves 1-3 can start immediately. The Wen connection (matching effective coupling to G_c) is the long-term physics question; the gap equation computation is self-contained.

---

*Phase 5d roadmap. Created 2026-04-04. Research basis: 10+ deep research files spanning Phases 3-5c, all converging on the same open question. All waves follow WAVE_EXECUTION_PIPELINE.md.*
