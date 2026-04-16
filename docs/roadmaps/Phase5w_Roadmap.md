# Phase 5w: Graphene Dirac Fluid — SK-EFT Transport & Analog Hawking Radiation

## Technical Roadmap — April 2026

*Prepared 2026-04-16 | Triggered by: Majumdar et al. (arXiv:2501.03193) demonstrating precision quantum critical transport in ultraclean graphene with η/s approaching KSS bound — a natively relativistic 2+1D fluid where our SK-EFT framework directly applies.*

**Scope:** Extend the SK-EFT dissipative framework from 1+1D BEC phonon hydrodynamics to 2+1D relativistic Dirac fluid hydrodynamics in graphene. Three tracks: (A) adapt the analog gravity / Hawking computation to graphene velocity horizons, (B) apply SK-EFT transport coefficient counting and FDR constraints to quantum critical transport, (C) formally verify the 2+1D generalizations in Lean 4.

**Separate from:**
- Phase 1-4 (BEC-specific pipeline — complete, untouched)
- Phase 5u (paper revisions — content track)
- Phase 5v (knowledge graph / process — infrastructure track)
- Phase 5p/s/m/i (categorical + quantum group Lean — proof track)

**Why a separate phase:** The graphene Dirac fluid is a *distinct physical system* from BEC, requiring its own analog metric, its own transport coefficient classification, and its own experimental parameter set. However, it shares the same SK-EFT theoretical framework — so the generalization is a natural extension, not a new project. The 2+1D relativistic case is arguably more fundamental than the 1+1D phonon case (closer to actual QFT in curved spacetime), and the experimental data from Majumdar et al. provides immediate testable predictions.

**Key insight:** Our existing formulas are 1+1D-specific. The 2+1D generalization is not just "add a spatial dimension" — the transport coefficient counting changes (more independent coefficients at each order due to tensor structure), the analog metric acquires angular degrees of freedom, and the WKB connection formula must be adapted for 2+1D turning surfaces (not points). But the *machinery* (SK doubling, KMS constraints, CGL transform, FDR) is dimension-independent.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read this roadmap for wave assignments
> 3. Read deep research results in `Lit-Search/Phase-5w/` as they arrive
> 4. Read existing modules that generalize:
>    - `lean/SKEFTHawking/AcousticMetric.lean` — BEC analog metric (→ Dirac fluid metric)
>    - `lean/SKEFTHawking/SecondOrderSK.lean` — transport counting (→ 2+1D counting)
>    - `lean/SKEFTHawking/CGLTransform.lean` — CGL FDR (→ 2+1D FDR)
>    - `lean/SKEFTHawking/HawkingUniversality.lean` — universality (→ 2+1D universality)
>    - `lean/SKEFTHawking/WKBConnection.lean` — WKB spectrum (→ 2+1D turning surface)
>    - `src/core/formulas.py` — canonical formulas (→ graphene formulas section)
>    - `src/experimental/predictions.py` — platform predictions (→ graphene platform)
>    - `src/experimental/polariton_predictions.py` — tier system pattern (→ graphene tier)

---

## Track A: Analog Hawking Radiation in Graphene Dirac Fluid

### Wave 1 — Deep Research: Graphene Analog Gravity Landscape [MANUAL — John]

**Task:** `Lit-Search/Tasks/Phase5w_graphene_dirac_fluid_analog_gravity_sk_eft.md`

**Goal:** Comprehensive survey covering analog metric for Dirac fluid, existing proposals, T_H estimates, dispersion corrections, dissipation mechanisms, transport counting in 2+1D, experimental groups, and collaboration landscape.

**Deliverables:**
- [ ] Parameter table: graphene Dirac fluid experimental parameters in SI
- [ ] Explicit 2+1D analog metric for Dirac fluid flow
- [ ] T_H estimates for realistic constriction geometries
- [ ] Transport coefficient count at orders 1-3 for 2+1D relativistic fluid
- [ ] Feasibility matrix for all subsequent waves
- [ ] Annotated bibliography

**Status:** Prompt written. Ready for execution.

**Gate:** Waves 2-8 blocked until Wave 1 deep research returns and is reviewed.

---

### Wave 2 — Dirac Fluid Analog Metric [Pipeline: Stages 1-5]

**Goal:** Derive the analog spacetime metric for Dirac fluid flow in graphene. The BEC acoustic metric (Unruh 1981) maps density + flow velocity → effective metric. The graphene analog metric maps charge/energy density + drift velocity → effective metric for electron-hole quasiparticles.

**Prerequisites:** Wave 1 deep research (need explicit metric from literature or first-principles derivation).

**Key physics questions (informed by deep research):**
- In BEC: g_μν = (ρ/c_s)[−(c_s²−v²), −v_j; −v_i, δ_ij]. The Dirac fluid version replaces ρ → enthalpy density ℋ, c_s → v_F, v → drift velocity u_μ. The 2+1D metric has a richer structure.
- Conformal invariance of the Dirac equation at the Dirac point simplifies the metric (Weyl rescalings are gauge).
- The Dirac cone is exact to leading order — corrections (trigonal warping, many-body renormalization of v_F) play the role of Bogoliubov dispersion in BEC.

**Deliverables:**
- [ ] `src/graphene/analog_metric.py` — Dirac fluid analog metric computation
- [ ] `src/graphene/transonic_flow.py` — Dirac fluid transonic flow solver (constriction geometry)
- [ ] `tests/test_graphene_metric.py` — metric properties: signature, determinant, horizon condition
- [ ] `lean/SKEFTHawking/DiracFluidMetric.lean` — metric theorem, determinant, horizon criterion
- [ ] Comparison to BEC metric: identify what's universal vs. system-specific

---

### Wave 3 — Hawking Temperature for Graphene Constrictions [Pipeline: Stages 1-8]

**Goal:** Compute the analog Hawking temperature for electron flow through graphene constrictions, including SK-EFT dissipative corrections.

**Prerequisites:** Wave 2 (analog metric defined).

**Key physics:**
- T_H = (ℏ/2πk_B)|∂v/∂x|_horizon × (geometric factor)
- The surface gravity κ depends on the constriction geometry (smooth nozzle vs. sharp step)
- Dissipative corrections δ_disp, δ_diss from our existing framework, adapted to 2+1D
- Compare to accessible temperature range: Majumdar et al. work at 10-300K

**Deliverables:**
- [ ] `src/graphene/hawking_temperature.py` — T_H for parametric constriction geometries
- [ ] `src/graphene/dissipative_corrections.py` — δ_disp, δ_diss adapted to Dirac fluid
- [ ] `lean/SKEFTHawking/GrapheneHawking.lean` — T_H formula, correction bounds
- [ ] Feasibility assessment: is T_H experimentally accessible? What bias voltage / geometry is needed?
- [ ] `notebooks/graphene_hawking_feasibility.ipynb` — parameter space exploration

---

### Wave 4 — WKB Spectrum in 2+1D [Pipeline: Stages 1-8]

**Goal:** Adapt the exact WKB connection formula from 1+1D (complex turning point) to 2+1D (turning surface). Compute the full Hawking spectrum for graphene.

**Prerequisites:** Wave 3 (T_H known, geometry characterized).

**Key challenges:**
- 1+1D: single complex turning point → Stokes phenomenon → Bogoliubov coefficients. Well-understood.
- 2+1D: turning *surface* with angular modes. Each angular momentum channel has its own turning point. The spectrum is a sum over channels.
- Partial-wave decomposition may reduce to a family of 1+1D problems (one per angular mode) — if so, our existing WKB machinery applies per-channel.
- Alternatively, the 2+1D conformal symmetry may provide shortcuts.

**Deliverables:**
- [ ] `src/graphene/wkb_spectrum.py` — Hawking spectrum for graphene, per angular mode
- [ ] `lean/SKEFTHawking/DiracFluidWKB.lean` — connection formula generalization
- [ ] Comparison: graphene spectrum vs. BEC spectrum (shape, corrections, noise floor)

---

## Track B: SK-EFT for Quantum Critical Transport

### Wave 5 — Transport Coefficient Counting in 2+1D [Pipeline: Stages 1-5]

**Goal:** Generalize the counting formula count(N) = floor((N+1)/2) + 1 from 1+1D to 2+1D relativistic hydrodynamics. The tensor structure is richer: in 2+1D, spatial indices can form traceless symmetric tensors, giving more independent coefficients at each derivative order.

**Prerequisites:** Wave 1 deep research (need literature classification, e.g., Romatschke, Baier-Romatschke-Son-Starinets-Stephanov).

**Key physics:**
- At first order in gradients (Navier-Stokes): shear viscosity η, bulk viscosity ζ (= 0 for conformal), and conductivity σ. Compare to our 1+1D: γ₁, γ₂.
- At second order: 5 independent coefficients for conformal fluid in 2+1D (Baier et al. 2008). Our counting formula gives count(2) = 2 in 1+1D. The 2+1D generalization encodes the additional tensor channels.
- KMS / CGL constraints: how many of the 5 are independent after imposing dynamical KMS?

**Deliverables:**
- [ ] `src/graphene/transport_counting.py` — generalized counting for 2+1D
- [ ] `lean/SKEFTHawking/DiracFluidSK.lean` — 2+1D counting theorem, KMS constraints
- [ ] Table: independent coefficients at orders 1-3, with CGL/FDR relations
- [ ] Comparison to holographic results (Son, Policastro-Son-Starinets)

---

### Wave 6 — FDR Constraints on Wiedemann-Franz Violation [Pipeline: Stages 1-8]

**Goal:** Use the CGL transform / dynamical KMS to derive constraints on the ratio κ_e/σT (Lorenz number). The giant WF violation measured by Majumdar et al. arises from the decoupling of charge and heat transport — the SK-EFT framework should predict the functional form of this decoupling.

**Prerequisites:** Wave 5 (transport coefficients classified).

**Key physics:**
- In a single-component fluid, WF law holds: L = L₀ = π²k_B²/3e².
- In the Dirac fluid, charge current (J) and energy current (Q) are independent hydrodynamic modes. The SK-EFT has separate retarded Green's functions for each.
- The CGL FDR relates G_R and G_A for each mode → constrains the Lorenz number deviation.
- Prediction: L(n, T) = f(T_F/T, l_ee/l_mr) with specific functional form from SK-EFT.

**Deliverables:**
- [ ] `src/graphene/wiedemann_franz.py` — SK-EFT prediction for L(n, T)
- [ ] `lean/SKEFTHawking/DiracFluidFDR.lean` — FDR constraint on WF ratio
- [ ] Comparison to Majumdar et al. data: does the SK-EFT prediction match the measured 200-300× violation?
- [ ] `notebooks/graphene_wf_comparison.ipynb` — data overlay with theory curves

---

### Wave 7 — Viscosity Bound and Strong-Coupling Regime [Pipeline: Stages 1-8]

**Goal:** Analyze what the η/s → ℏ/4πk_B result means for the SK-EFT expansion. If the coupling α ≈ 0.3-0.9, the derivative expansion may need resummation.

**Prerequisites:** Wave 5 and Wave 6.

**Key questions:**
- What is the EFT expansion parameter? (α_graphene = e²/ℏv_F, renormalized by substrate screening)
- At what derivative order does the expansion become unreliable?
- Connection to holographic calculations: the KSS bound is exact at infinite coupling in N=4 SYM. The graphene Dirac fluid at α ~ 0.3-0.9 interpolates between weak and strong coupling — does the SK-EFT bridge these?
- Connection to our ADW mechanism: the Dirac fluid approaching the viscosity bound is a candidate system for emergent gravity signatures.

**Deliverables:**
- [ ] `src/graphene/strong_coupling.py` — expansion parameter analysis, convergence radius
- [ ] `lean/SKEFTHawking/DiracFluidViscosity.lean` — viscosity bound theorem
- [ ] Assessment: does the SK-EFT need resummation for graphene, or is truncation reliable?
- [ ] Connection to ADW: is there an emergent gravity signal in η/s → minimum?

---

## Track C: Platform Integration & Paper

### Wave 8 — Graphene Platform Predictions [Pipeline: Stages 1-12]

**Goal:** Add graphene as a Tier 2 analog gravity platform alongside BEC and polariton systems. Generate prediction tables with experimental parameters from Majumdar et al. and other groups.

**Prerequisites:** Waves 2-7 (need metric, T_H, spectrum, transport predictions).

**Deliverables:**
- [ ] `src/experimental/graphene_predictions.py` — platform prediction tables
- [ ] `src/core/constants.py` — graphene experimental parameters section
- [ ] `src/core/formulas.py` — graphene-specific formulas (with Lean refs)
- [ ] `src/core/visualizations.py` — graphene figure functions
- [ ] `lean/SKEFTHawking/GrapheneTier2.lean` — platform predictions verified
- [ ] Update `experimental/predictions.py` — unified multi-platform comparison

---

### Wave 9 — Paper 16: SK-EFT for Graphene Dirac Fluid [Pipeline: Stages 1-12]

**Goal:** Draft Paper 16 presenting the SK-EFT framework applied to graphene Dirac fluid transport and analog Hawking radiation.

**Prerequisites:** All of Waves 2-8.

**Paper structure (tentative):**
1. Introduction: analog gravity beyond BEC — the graphene Dirac fluid as a natively relativistic platform
2. SK-EFT framework recap (cite Papers 1-2) and 2+1D generalization
3. Analog metric and Hawking temperature for graphene constrictions
4. Transport coefficient counting and FDR constraints in 2+1D
5. Wiedemann-Franz violation from SK-EFT: comparison to Majumdar et al. data
6. Hawking spectrum with dissipative corrections
7. Strong-coupling regime and viscosity bound
8. Experimental predictions and proposal
9. Formal verification summary

**Deliverables:**
- [ ] `papers/paper16_graphene_sk_eft/paper_draft.tex`
- [ ] All figures via `visualizations.py` (reviewed by figure-reviewer agent)
- [ ] All claims traced to computation (CHECK 14) and Lean theorems (CHECK 4)
- [ ] Full 12-stage pipeline closure

---

## Dependencies and Sequencing

```
Wave 1 (deep research) ──┬──→ Wave 2 (metric) ──→ Wave 3 (T_H) ──→ Wave 4 (WKB)
                          │                                                  │
                          ├──→ Wave 5 (counting) ──→ Wave 6 (WF) ──→ Wave 7 (viscosity)
                          │                                                  │
                          └──→ (both tracks) ──────────────────────→ Wave 8 (platform)
                                                                             │
                                                                      Wave 9 (paper)
```

Tracks A and B can proceed in parallel after Wave 1. Wave 8 merges both tracks. Wave 9 is the capstone.

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| T_H too low for current experiments | Medium | High — undermines experimental motivation | Deep research (Wave 1) will give honest numbers. Even if T_H is inaccessible now, the transport predictions (Track B) are independently valuable. |
| 2+1D WKB turning surface intractable | Medium | Medium — affects Wave 4 | Partial-wave decomposition likely reduces to family of 1+1D problems. Conformal symmetry may provide further simplification. |
| SK-EFT expansion breaks down at α ~ 1 | Medium | Medium — affects Wave 7 | This is itself a publishable result. Breakdown characterization is valuable, not just convergent expansions. |
| Transport counting already done (Baier et al.) | High | Low — our framework adds formal verification | The counting may be known; the Lean verification and FDR constraints are not. |
| Graphene analog gravity already well-studied | Low-Medium | Low — our contribution is SK-EFT + verification | Literature survey (Wave 1) will clarify. The verified EFT corrections are our unique angle regardless. |

---

## Success Criteria

**Minimum viable (Waves 1-3 + 5-6):**
- 2+1D analog metric formalized
- T_H estimates for graphene with honest feasibility assessment
- Transport counting generalized to 2+1D with CGL/FDR constraints
- WF violation predicted from SK-EFT and compared to data

**Full scope (all 9 waves):**
- Complete Hawking spectrum with dissipative corrections for graphene
- Strong-coupling / viscosity bound analysis
- Graphene as verified Tier 2 platform
- Paper 16 through full pipeline

---

## Connection to Existing Phases

| Phase | Connection |
|-------|-----------|
| Phase 1-2 | SK-EFT framework generalizes from 1+1D → 2+1D |
| Phase 3 (gauge erasure) | Graphene has no gauge fields — erasure theorem not needed, but universality theorem extends |
| Phase 3 (WKB) | Connection formula adapts to 2+1D partial waves |
| Phase 4 (platforms) | Graphene joins BEC + polariton as Tier 2 |
| Phase 5d (ADW/RHMC) | Viscosity bound connection to emergent gravity |
| Phase 5u (paper revisions) | Independent — 5w does not modify Papers 1-15 |
| Phase 5v (KG/readiness) | Paper 16 enters KG + readiness system when drafted |
