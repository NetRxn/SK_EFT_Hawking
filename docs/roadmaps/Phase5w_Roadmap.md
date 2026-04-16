# Phase 5w: Graphene Dirac Fluid — SK-EFT Transport & Analog Hawking Radiation

## Technical Roadmap — April 2026

*Prepared 2026-04-16 | Updated 2026-04-16 (post deep research) | Triggered by: Majumdar et al. (arXiv:2501.03193) on universal quantum critical transport in graphene + Geurs et al. (arXiv:2509.16321, Dean group) demonstrating the first electronic sonic horizon in bilayer graphene.*

**Scope:** Extend the SK-EFT dissipative framework from 1+1D BEC phonon hydrodynamics to 2+1D relativistic Dirac fluid hydrodynamics in graphene. Three tracks: (A) adapt the analog gravity / Hawking computation to graphene velocity horizons, (B) apply SK-EFT transport coefficient counting and FDR constraints to quantum critical transport, (C) formally verify the 2+1D generalizations in Lean 4.

**Separate from:**
- Phase 1-4 (BEC-specific pipeline — complete, untouched)
- Phase 5u (paper revisions — content track)
- Phase 5v (knowledge graph / process — infrastructure track)
- Phase 5p/s/m/i (categorical + quantum group Lean — proof track)

**Why a separate phase:** The graphene Dirac fluid is a *distinct physical system* from BEC, requiring its own analog metric, its own transport coefficient classification, and its own experimental parameter set. However, it shares the same SK-EFT theoretical framework — so the generalization is a natural extension, not a new project. The 2+1D relativistic case is arguably more fundamental than the 1+1D phonon case (closer to actual QFT in curved spacetime), and the convergence of precision transport data (Majumdar et al.) with a realized sonic horizon (Dean group) creates a concrete experimental target.

**Critical strategic finding (from deep research):** The Dean group at Columbia (Geurs, Webb, Guo et al., arXiv:2509.16321, Sept 2025) demonstrated supersonic electron flow through an electronic de Laval nozzle in hBN-encapsulated bilayer graphene — the first sonic horizon ever created in an electronic system. Co-author Andrew Lucas (CU Boulder) has deep engagement with SK-EFT (co-authored CGL papers with Glorioso). **Nobody is combining SK-EFT + graphene analog gravity + formal verification.** The niche is completely open.

**Key structural simplification (from deep research):** For a quasi-1D constriction geometry (flow along x with translational symmetry in y), the 2+1D acoustic metric block-diagonalizes. The (t,x) block reproduces our existing 1+1D BEC structure with c_s → v_F/√2. **Our existing WKB machinery, connection formula, and dissipative corrections apply directly** to quasi-1D graphene constrictions, with only the transverse greybody factor as a genuinely new 2+1D effect.

**Lean infrastructure reuse (from module-by-module audit, 2026-04-16):** Of 109 theorems across the 10 core SK-EFT modules, **100 (92%) are directly reusable with zero changes**, 9 (8%) need minor adaptation (matrix dimension Fin 2 → Fin 3 or parity-context clarification), and **0 require rewriting**. This is dramatically higher than the initial 60-80% estimate. Estimated Lean formalization effort for full Phase 5w: **4-5 weeks, ~1500-2000 LOC**, building on all 109 existing theorems. See §Lean Reuse Audit below.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read this roadmap for wave assignments
> 3. **Read deep research result:** `Lit-Search/Phase-5w/5w-SK-EFT Hawking framework meets the graphene Dirac fluid.md` — contains the analog metric derivation (both Landau-frame and CGL), T_H estimates for 5 geometries, transport coefficient counting tables, feasibility matrix, collaboration landscape, and annotated bibliography. This is load-bearing for all waves.
> 4. **Read cross-referenced deep research** (see §Cross-References below): Phase-2 (FDR/KMS), Phase-3 (WKB gap analysis), Phase-4 (transport counting), Phase-5 base (T_H robustness), Phase-1 (dissipative-correction gap identification)
> 5. Read existing modules that generalize:
>    - `lean/SKEFTHawking/AcousticMetric.lean` — BEC analog metric (→ Dirac fluid metric)
>    - `lean/SKEFTHawking/SecondOrderSK.lean` — transport counting (→ 2+1D counting)
>    - `lean/SKEFTHawking/CGLTransform.lean` — CGL FDR (→ 2+1D FDR)
>    - `lean/SKEFTHawking/HawkingUniversality.lean` — universality (→ 2+1D universality)
>    - `lean/SKEFTHawking/WKBConnection.lean` — WKB spectrum (→ 2+1D partial waves)
>    - `src/core/formulas.py` — canonical formulas (→ graphene formulas section)
>    - `src/experimental/predictions.py` — platform predictions (→ graphene platform)
>    - `src/experimental/polariton_predictions.py` — tier system pattern (→ graphene tier)

---

## Key Parameters (from deep research §1)

| Parameter | Graphene (bilayer, Dean nozzle) | Graphene (monolayer, Majumdar) | BEC (Steinhauer) |
|---|---|---|---|
| Sound speed c_s | 4.4 × 10⁵ m/s | 7.1 × 10⁵ m/s | 5 × 10⁻⁴ m/s |
| Predicted T_H | **~2-3 K** | ~9-17 K (constriction) | ~0.35 nK |
| Effective coupling | α_g ≈ 0.5-0.9 (hBN) | α_g ≈ 0.5-0.9 (hBN) | O(1) |
| Hydrodynamic window | 100-300 K | 100-300 K | Below T_c |
| Dissipation ratio ω_H/Γ_mr | ~10-100 | ~10-100 | >>1 |
| Dispersion type | **Subluminal** (more robust) | **Subluminal** | Superluminal (Bogoliubov) |
| Sonic horizon | **REALIZED** (Sept 2025) | Not yet | Realized (2016) |

---

## Wave 1 — Deep Research [COMPLETE]

**Task:** `Lit-Search/Tasks/Phase5w_graphene_dirac_fluid_analog_gravity_sk_eft.md`
**Result:** `Lit-Search/Phase-5w/5w-SK-EFT Hawking framework meets the graphene Dirac fluid.md`

**Key findings incorporated into this roadmap:**
- [x] Parameter table: graphene Dirac fluid experimental parameters in SI (§1)
- [x] Explicit 2+1D analog metric for Dirac fluid flow — two derivations reconciled (§2)
- [x] T_H estimates for 5 constriction geometries spanning 2-120 K (§3)
- [x] Transport coefficient count at orders 1-3 for 2+1D relativistic charged fluid (§4)
- [x] Feasibility matrix for all subsequent waves (§5)
- [x] Collaboration landscape with tiered priority (§6)
- [x] Annotated bibliography, 45+ references (§7)

**Status: COMPLETE.** All subsequent waves unblocked.

---

## Track A: Analog Hawking Radiation in Graphene (Critical Path)

### Wave 2 — Dirac Fluid Analog Metric [Pipeline: Stages 1-5]

**Goal:** Formalize the 2+1D analog acoustic metric for Dirac fluid flow. The deep research (§2) derives it via both Landau-frame stress-tensor linearization and CGL effective-action expansion, showing they converge on the same universal structure.

**Prerequisites:** Wave 1 (COMPLETE).

**Metric (from deep research §2a):** For 1D flow along x with velocity v(x) in the Dirac fluid:

```
              ⎛ −(c_s² − v²)/v_F²     −v/v_F²     0 ⎞
G_μν = Ω²    ⎜    −v/v_F²               1          0 ⎟
              ⎝       0                  0          1 ⎠
```

with Ω² = (n₀/w₀c_s)², c_s = v_F/√2 (conformal), horizon at v = c_s.

**Key insight (§2c):** For quasi-1D constrictions, the (t,x) block reproduces the BEC 1+1D metric with c_s → v_F/√2. The y-y component decouples. Our existing 1+1D Hawking calculation infrastructure applies directly.

**Deliverables:**
- [ ] `src/graphene/analog_metric.py` — 3×3 Dirac fluid acoustic metric, determinant, horizon condition
- [ ] `src/graphene/transonic_flow.py` — de Laval nozzle flow solver (parametric constriction geometry matching Dean group device: throat width, nozzle angle, bias voltage → velocity profile)
- [ ] `tests/test_graphene_metric.py` — signature (−,+,+), det, block-diagonalization, BEC limit recovery
- [ ] `lean/SKEFTHawking/DiracFluidMetric.lean` — 3×3 metric, det theorem, horizon criterion v = c_s = v_F/√2, conformal factor, block-diag theorem for quasi-1D. **New theorems (~4-6, ~200 LOC):** `diracFluidMetric_3D`, `diracFluidMetric_symmetric`, `diracFluidMetric_det`, `diracFluidMetric_blockDiag` (proving (t,x) block = BEC metric with c_s → v_F/√2), `diracFluidMetric_horizon`. **Reused directly:** `soundSpeed_from_eos`, `gtt_vanishes_at_horizon`, `hawking_temp_from_surface_gravity` from AcousticMetric.lean.
- [ ] Comparison table: universal features (horizon location, T_H, causal structure) vs. formalism-dependent (conformal factor, dissipative corrections, noise spectrum)

**Estimated timeline:** 1-2 months (compressed from 2-4: only 5 theorems need adaptation in AcousticMetric, plus ~200 LOC new DiracFluidMetric.lean)
**Infrastructure reuse:** 92% overall; AcousticMetric specifically 38% direct + 62% minor adapt (Fin 2 → Fin 3 matrix dimension)

---

### Wave 3 — Hawking Temperature & Dissipative Corrections [Pipeline: Stages 1-8]

**Goal:** Compute analog Hawking temperature for realistic graphene geometries with SK-EFT dissipative corrections. Primary target: the Dean group bilayer nozzle (T_H ≈ 2-3 K).

**Prerequisites:** Wave 2 (metric formalized).

**T_H estimates (from deep research §3):**

| Geometry | c_s (m/s) | Gradient scale L | T_H (K) | T_H/T_ambient |
|---|---|---|---|---|
| **Bilayer nozzle (Dean)** | 4.4 × 10⁵ | ~200 nm | **~2.4** | ~0.01-0.02 |
| Monolayer W ~ 100 nm | 7.1 × 10⁵ | 100 nm | ~8.7 | ~0.03-0.09 |
| Monolayer W ~ 50 nm | 7.1 × 10⁵ | 50 nm | ~17 | ~0.06-0.17 |
| p-n junction d ~ 10 nm | v_F | 10 nm | ~120 | ~0.4-1.0 |

**Key physics (from deep research §3):**
- Dissipation window is narrow but open: ω_H/Γ_mr ~ 10-100 in clean samples
- Subluminal dispersion (opposite to BEC) makes T_H formula *more robust*
- Trigonal warping corrections negligible below ~0.5 eV (~6000 K), far above any T_H
- Detection channel: current noise S_I(ω) near the nozzle throat, correlation analysis following Steinhauer methodology

**Deliverables:**
- [ ] `src/graphene/hawking_temperature.py` — T_H(geometry_params) for 4 geometries, with δ_disp and δ_diss corrections from existing framework (adapted c_s → v_F/√2, Bogoliubov → subluminal renormalization)
- [ ] `src/graphene/noise_spectrum.py` — predicted current noise power spectrum S_I(ω) near sonic point
- [ ] `lean/SKEFTHawking/GrapheneHawking.lean` — T_H formula, positivity, correction bounds, subluminal robustness. **Reused directly (41 theorems):** all 9 from HawkingUniversality (`hawking_universality`, `dispersive_correction_bound`, etc.), all 17 from WKBConnection (`unitarity_deficit_eq_decoherence`, `noise_floor_eq_delta_diss`, etc.), all 15 from WKBAnalysis (`dissipative_occupation_planckian`, `turning_point_shift`, etc.). **New:** `subluminal_dispersion_robustness` (F(x) ≤ 1 strengthens correction bound), `graphene_T_H_positivity`.
- [ ] `notebooks/graphene_hawking_feasibility.ipynb` — parameter space sweep: (nozzle geometry) × (bias voltage) × (temperature) → T_H/T_ambient contour plots
- [ ] Feasibility memo: detection signal-to-noise for Dean geometry, required integration time

**Estimated timeline:** 1-2 months (after Wave 2)
**Infrastructure reuse:** HawkingUniversality (9/9 = 100% direct), WKBConnection (17/17 = 100% direct), WKBAnalysis (15/15 = 100% direct). Just substitute c_s → v_F/√2 and supply subluminal F(x) ≤ 1.
**Cross-ref:** Phase-3 deep research provides 5-step WKB methodology; Phase-1 identifies the dissipative-correction gap this wave fills.

---

### Wave 4 — Noise Spectrum Signature S_I(ω) [Pipeline: Stages 1-8]

**Goal:** Compute the full noise spectrum prediction for analog Hawking radiation in the Dean group's bilayer nozzle. This is the experimentally testable deliverable — the analog of Steinhauer's density-density correlator, but for electronic current noise.

**Prerequisites:** Wave 3 (T_H and corrections known).

**Key physics:**
- Adapt WKB connection formula to quasi-1D Dirac fluid (block-diagonal reduction)
- Per-channel Bogoliubov coefficients from existing framework with c_s → v_F/√2
- Transverse greybody factor from the y-y metric component (genuinely new 2+1D effect)
- Full spectrum: sum over transverse modes, including dissipative damping at high frequency
- Comparison: graphene spectrum shape vs. BEC — subluminal dispersion changes the UV tail

**Deliverables:**
- [ ] `src/graphene/wkb_spectrum.py` — Hawking spectrum per angular/transverse mode, sum over channels
- [ ] `lean/SKEFTHawking/DiracFluidWKB.lean` — connection formula for quasi-1D Dirac fluid, transverse greybody
- [ ] `src/graphene/detection_protocol.py` — measurement protocol for Dean group: frequency window, integration time, expected S/N ratio, thermal background subtraction
- [ ] Comparison plot: graphene vs. BEC Hawking spectra (normalized by T_H)
- [ ] `notebooks/graphene_noise_spectrum.ipynb` — interactive exploration

**Estimated timeline:** 2-3 months (after Wave 3; compressed from 3-4 — WKB machinery is 100% reusable)
**Infrastructure reuse:** WKBConnection (17/17 = 100% direct), WKBAnalysis (15/15 = 100% direct). New work: transverse greybody factor from y-y metric component, S_I(ω) noise spectrum computation.
**Cross-ref:** Phase-3 WKB gap analysis (complex turning point, Stokes geometry) provides full methodology; Phase 5w extends to 2+1D via block-diag reduction.

---

## Track B: SK-EFT for Quantum Critical Transport (Parallel with Track A)

### Wave 5 — Transport Coefficient Counting in 2+1D [Pipeline: Stages 1-5]

**Goal:** Classify independent transport coefficients for a 2+1D relativistic charged conformal fluid, order by order in the derivative expansion, with CGL/FDR constraints.

**Prerequisites:** Wave 1 (COMPLETE).

**Transport counting (from deep research §4):**

| Derivative order | 1+1D BEC (existing) | 2+1D Dirac conformal charged | Notes |
|---|---|---|---|
| 1st (Navier-Stokes) | 2 (γ₁, γ₂) | **2** (η, σ_Q); ζ = 0 by conformal | Match at 1st order is striking |
| 2nd | 2 (γ₂,₁, γ₂,₂) | **8-12** (τ_π, λ₁-₃, κ_curv, τ_J, τ_q, cross-couplings) | Haack-Yarom identity reduces by 1 |
| 3rd | 3 | **~30-50** (estimated) | Many constrained by entropy positivity |

**Key finding (§4):** No closed-form counting formula exists for 2+1D — must enumerate tensor structures per BRSSS classification. The 1+1D formula count(N) = floor((N+1)/2) + 1 is specific to the scalar sector. In 2+1D, tensor/vector/scalar sectors contribute independently.

**Deliverables:**
- [ ] `src/graphene/transport_counting.py` — systematic enumeration of tensor structures at each order, with CGL/FDR constraint counting
- [ ] `lean/SKEFTHawking/DiracFluidSK.lean` — first-order coefficient classification (η, σ_Q, ζ=0), conformal constraint, comparison to 1+1D counting. **Reused directly (34 theorems):** 20 from SecondOrderSK (`transport_coefficient_count`, `firstOrder_count`, `secondOrder_uniqueness`, `gammaH_def`, `gammaH_nonneg`, `deltaDissFromTransport_eq`, `fullSecondOrder_uniqueness`, `combined_normalization`, `combined_positivity_constraint`, `fdr_second_order_consistent`, etc.), all 14 from ThirdOrderSK (`parity_preserving_at_odd_order`, `spectral_parity_alternation`, etc.). **New:** `conformal_bulk_viscosity_vanishes` (ζ=0 for ε=2p), `charged_first_order_count` (2 for conformal, 3 for non-conformal), tensor structure enumeration at orders 2-3.
- [ ] Table: independent coefficients at orders 1-3, before and after KMS/entropy constraints
- [ ] Comparison to holographic results: Policastro-Son-Starinets (η/s = 1/4π), Kovtun (BDNK stability)

**Estimated timeline:** 2-3 months
**Infrastructure reuse:** SecondOrderSK (20/24 = 83% direct), ThirdOrderSK (14/14 = 100% direct). Parity alternation theorem applies universally. New work: enumerate 2+1D tensor structures per BRSSS; no closed-form counting formula exists (confirmed by Phase-4 deep research on fracton SK-EFT).
**Cross-ref:** Phase-2 deep research (dynamical KMS, FDR Ward identities — dimension-independent); Phase-4 deep research (Glorioso-Huang-Lucas: no simple counting formula in higher D; must enumerate tensor structures).

---

### Wave 6 — FDR Constraints on Wiedemann-Franz Violation [Pipeline: Stages 1-8]

**Goal:** Derive the Lorenz ratio L(n, T) from the SK-EFT two-channel structure and compare to Majumdar et al.'s >200× WF violation.

**Prerequisites:** Wave 5 (transport coefficients classified).

**Key physics (from deep research §4):** The WF violation is a *constitutive-relation* feature, not a FDR constraint. It arises because the Dirac fluid has two nearly decoupled transport channels: charge (conductivity σ_Q, from electron-hole asymmetry) and heat (κ ∝ (ε+p)²v_F²/(Tσ_Q), from total momentum). At CNP:

> L = v_F² s² / σ_Q² × (1/T) → ∞ as n → 0

The CGL/FDR framework does not predict the value of σ_Q (microscopic input), but ensures thermodynamic consistency of the two-channel structure and constrains higher-order corrections to L.

**Deliverables:**
- [ ] `src/graphene/wiedemann_franz.py` — L(n, T) from two-channel SK-EFT, with higher-order corrections
- [ ] `lean/SKEFTHawking/DiracFluidFDR.lean` — FDR constraint on WF ratio, thermodynamic consistency of two-channel structure
- [ ] `notebooks/graphene_wf_comparison.ipynb` — overlay SK-EFT prediction with Majumdar et al. data
- [ ] Assessment: what does the SK-EFT add beyond leading-order hydrodynamics?

**Estimated timeline:** 4-6 months (highest risk wave — Onsager relations have never been formalized in any proof assistant)
**Infrastructure reuse:** CGLTransform (6/6 = 100% direct for FDR structure), SKDoubling (9/9 = 100% direct for abstract SK axioms). New work: Onsager reciprocal relations from scratch (~35-40% overall reuse for this wave). Phase-5a Onsager algebra provides algebraic foundation via Dolan-Grady presentation in Mathlib Lie algebra infrastructure.
**Cross-ref:** Phase-2 deep research (CGL transformation, transport coefficient pairing); Phase-1 deep research (U(1) charge symmetry survives hydrodynamization → validates σ_Q as independent coefficient).
**Note:** This is the hardest Lean target. If formalization stalls, the Python + paper deliverables are independently valuable. The CGLTransform + SKDoubling theorems still apply to the two-channel structure; only the Onsager bridge is new.

---

### Wave 7 — Viscosity Bound and Strong-Coupling Analysis [Pipeline: Stages 1-8]

**Goal:** Analyze the SK-EFT expansion parameter and convergence for the graphene Dirac fluid at α_g ≈ 0.5-0.9.

**Prerequisites:** Waves 5-6.

**Key questions (from deep research §3, §5):**
- EFT expansion parameter: ωl_ee/c_s ~ k_BT·l_ee/(ℏc_s). At T = 100K: l_ee ~ 76 nm, c_s ~ 7.1 × 10⁵ m/s → ωl_ee/c_s ~ 0.1 at ω ~ ω_H. Expansion is marginally convergent.
- η/s ≈ 4× KSS bound means we're at intermediate coupling. Holographic (infinite coupling) and perturbative (weak coupling) limits bracket the graphene value.
- Connection to ADW mechanism: the Dirac fluid approaching the viscosity bound is a candidate for emergent gravity signatures.

**Deliverables:**
- [ ] `src/graphene/strong_coupling.py` — expansion parameter analysis, convergence radius estimate
- [ ] `lean/SKEFTHawking/DiracFluidViscosity.lean` — viscosity bound theorem, expansion parameter bounds
- [ ] Assessment: does truncation at 2nd order suffice, or is resummation needed?

**Estimated timeline:** 2-3 months
**Parity-odd extension (Hall viscosity η_H, Hall conductivity σ_H):** Deferred — requires magnetic field, lower priority.

---

## Track C: Platform Integration & Paper

### Wave 8 — Graphene Platform Predictions [Pipeline: Stages 1-12]

**Goal:** Add graphene as a Tier 2 analog gravity platform. Generate prediction tables with experimental parameters from Dean group (bilayer nozzle), Majumdar et al. (monolayer transport), and Kim group (noise thermometry).

**Prerequisites:** Waves 2-7 (need metric, T_H, spectrum, transport predictions from both tracks).

**Deliverables:**
- [ ] `src/experimental/graphene_predictions.py` — platform prediction tables (5 geometries × corrections)
- [ ] `src/core/constants.py` — graphene experimental parameters section (v_F, α_g, c_s, l_ee, l_mr, T_imp, n_min)
- [ ] `src/core/formulas.py` — graphene-specific formulas with Lean refs
- [ ] `src/core/visualizations.py` — graphene figure functions (metric visualization, T_H parameter sweep, noise spectrum, WF comparison, platform comparison)
- [ ] `lean/SKEFTHawking/GrapheneTier2.lean` — platform predictions verified
- [ ] Update `experimental/predictions.py` — unified 3-platform (BEC + polariton + graphene) comparison table

---

### Wave 9 — Paper 16: SK-EFT for Graphene Dirac Fluid [Pipeline: Stages 1-12]

**Goal:** Draft Paper 16. The paper has two audiences: (1) analog gravity community (the graphene Hawking prediction), (2) graphene transport community (SK-EFT framework for quantum critical transport). Dean/Lucas/Kim collaboration target — the experimental proposal section should be written with them in mind.

**Prerequisites:** Waves 2-8.

**Paper structure (tentative):**
1. Introduction: analog gravity beyond BEC — the graphene Dirac fluid as a natively relativistic platform with a realized sonic horizon
2. SK-EFT framework recap (cite Papers 1-2) and 2+1D generalization
3. Analog acoustic metric: Landau-frame and CGL derivations, reconciliation (§2 of deep research)
4. Hawking temperature for graphene constrictions: 5 geometries, dissipative corrections
5. Noise spectrum prediction: S_I(ω) for the Dean group bilayer nozzle
6. Transport coefficient counting and classification in 2+1D
7. Wiedemann-Franz violation from two-channel SK-EFT: comparison to Majumdar et al.
8. Strong-coupling regime: expansion parameter, viscosity bound, convergence
9. Experimental proposal: detection protocol, measurement requirements, timeline
10. Formal verification summary: Lean 4 theorems, zero sorry
11. Appendix: complete parameter tables, Lean module index

**Deliverables:**
- [ ] `papers/paper16_graphene_sk_eft/paper_draft.tex`
- [ ] All figures via `visualizations.py` (reviewed by figure-reviewer agent)
- [ ] All claims traced to computation (CHECK 14) and Lean theorems (CHECK 4)
- [ ] Full 12-stage pipeline closure

---

## Dependencies and Sequencing

```
Wave 1 (deep research) ─── COMPLETE
         │
         ├──→ Wave 2 (metric) ──→ Wave 3 (T_H) ──→ Wave 4 (noise spectrum)
         │         ↓                                        │
         │    [quasi-1D block-diag                          │
         │     enables 1+1D reuse]                          │
         │                                                  │
         ├──→ Wave 5 (counting) ──→ Wave 6 (WF) ──→ Wave 7 (viscosity)
         │                                                  │
         └──→ (Tracks A+B merge) ─────────────────→ Wave 8 (platform)
                                                            │
                                                     Wave 9 (paper)
```

**Critical path:** W2 → W3 → W4 (4-7 months to first experimentally testable noise spectrum prediction — compressed from 5-10 by 92% Lean reuse).
**Parallel track:** W5 → W6 → W7 (8-12 months, with W6 as highest-risk item).
**Merge and paper:** W8 → W9 (after both tracks complete).
**Lean formalization overlay:** 4-5 weeks total across all waves (~1500-2000 LOC new), leveraging 109 existing theorems. Can be front-loaded into Stage 1 (1-2 weeks) and integrated per-wave thereafter.

---

## Lean Reuse Audit (2026-04-16 module-by-module analysis)

### Reusability Matrix

| Module | Theorems | Direct Reuse | Minor Adapt | Rewrite | Notes |
|---|---|---|---|---|---|
| **HawkingUniversality.lean** | 9 | **9 (100%)** | 0 | 0 | All dimension-independent. `hawking_universality`, `dispersive_correction_bound`, etc. Just substitute c_s → v_F/√2. |
| **CGLTransform.lean** | 6 | **6 (100%)** | 0 | 0 | `cgl_fdr_general`, `einstein_relation`, etc. FDR Ward identity structure is dimension-independent. |
| **SKDoubling.lean** | 9 | **9 (100%)** | 0 | 0 | `firstOrder_uniqueness`, `zeroTemp_nontrivial`, `fdr_from_kms`. Abstract SK action structure. Extend `SKFields` → `SKFields2D` for full 2+1D (new file, same proof strategy). |
| **WKBConnection.lean** | 17 | **17 (100%)** | 0 | 0 | `unitarity_deficit_eq_decoherence`, `noise_floor_eq_delta_diss`, `total_occupation_nonneg`. Only γ₁, γ₂ → graphene transport coefficients. |
| **WKBAnalysis.lean** | 15 | **15 (100%)** | 0 | 0 | `dampingRate_firstOrder_nonneg`, `dissipative_occupation_planckian`, `turning_point_shift`. Supply graphene dispersion F(x) ≤ 1 (subluminal). |
| **ThirdOrderSK.lean** | 14 | **14 (100%)** | 0 | 0 | `parity_preserving_at_odd_order`, `spectral_parity_alternation`. Parity alternation is universal. |
| **KappaScaling.lean** | 11 | **11 (100%)** | 0 | 0 | `kappa_scaling_crossover_balance`, `crossover_formula`. Instantiate with graphene ξ, c_s, γ. |
| **PolaritonTier1.lean** | 6 | **6 (100%)** | 0 | 0 | Attenuation/validity theorems. Pattern for GrapheneTier2. |
| **SecondOrderSK.lean** | 24 | **20 (83%)** | 4 (17%) | 0 | 20 counting/FDR/uniqueness theorems reuse directly. 4 parity-related theorems need context clarification ("parity" = spatial parity ⊥ flow in 2+1D). |
| **AcousticMetric.lean** | 8 | **3 (38%)** | 5 (62%) | 0 | `soundSpeed_from_eos`, `gtt_vanishes_at_horizon`, `hawking_temp_from_surface_gravity` reuse. 5 need `Matrix (Fin 2)` → `Matrix (Fin 3)` with block-diag proof. |
| **TOTAL** | **109** | **100 (92%)** | **9 (8%)** | **0** | |

### Key Adaptations Required

1. **AcousticMetric → DiracFluidMetric:** Define `acousticMetric_3D` as 3×3 matrix, prove `acousticMetric_blockDiagonal` showing `g³ˣ³ = diag(g²ˣ²_BEC, g_yy)` for quasi-1D flow. Existing 2×2 theorems apply to (t,x) block via `Matrix.blockDiagonal_det`. ~200 LOC.

2. **SKDoubling → SKDoubling2D:** Create `SKFields2D` structure with ∂_y, ∂_{ty}, ∂_{xy}, ∂_{yy} fields. Reprove axioms (normalization, positivity, KMS) for 2D fields — same proof strategy, just more field components. ~300 LOC.

3. **SecondOrderSK parity clarification:** Rename/extend `secondOrder_requires_parity_breaking` to clarify that "parity" = (x,y)-plane rotational symmetry for 2+1D. Add `secondOrder_isotropic_2D_count` (= 0 for isotropic flow). ~50 LOC.

4. **Basic.lean extension:** Add `Spacetime2D`, `FluidBackground2D` (velocity_y component). Keep all existing 1D infrastructure. ~100 LOC.

### Lean Development Stages

**Stage 1 — Minimal Reuse Path (1-2 weeks):**
- Copy/import all 100 directly-reusable theorems
- Extend Basic.lean with 2D spacetime types
- Create `DiracFluidMetric.lean`: 3×3 metric + block-diag proof (4-6 new theorems)
- Create `SKDoubling2D.lean`: 2D field extension (9 reproven theorems)

**Stage 2 — Full 2+1D Analysis (2-3 weeks):**
- `DiracFluidSK.lean`: transport coefficient classification for 2+1D charged conformal fluid
- `DiracFluidTransport.lean`: charge/heat channel decomposition, FDR constraints
- `DiracFluidFDR.lean`: WF ratio constraint from two-channel structure (highest risk — Onsager relations from scratch)
- `QuasiParticle1DReduction.lean`: formal proof that quasi-1D limit recovers BEC-like 2D metric

**Stage 3 — Subluminal Dispersion & Platform (1 week):**
- `SubluminalDispersion.lean`: instantiate HawkingUniversality with F(x) ≤ 1
- `GrapheneHawking.lean`: T_H formula + correction bounds for graphene
- `GrapheneTier2.lean`: platform predictions

**Total: ~4-5 weeks, ~1500-2000 LOC new Lean, 109 theorems reused.**

---

## Cross-References to Existing Deep Research

The following deep research files from earlier phases contain directly applicable content for Phase 5w. Agents must read the relevant files before working on the corresponding wave.

### HIGH relevance

| Deep Research File | Phase 5w Waves | Key Content |
|---|---|---|
| `Lit-Search/Phase-2/Dynamical KMS symmetry and the fluctuation-dissipation relation in Schwinger-Keldysh EFT.md` | W5, W6 | CGL transformation in r-a basis is **dimension-independent**. FDR at quadratic level: K_N(ω,k) = [K_R(ω,k) − K_R(−ω,k)]/(β₀ω). Transport coefficient pairing: γ₁ = β₀·i₁. SymPy algorithm for imposing KMS constraint. All extends directly to 2+1D charged fluid. |
| `Lit-Search/Phase-3/WKB connection formulas for dissipative analog Hawking radiation- a gap analysis.md` | W3, W4 | Five-step WKB methodology. Complex turning point: d⁴w/dz⁴ + (z + iδ̃)d²w/dz² + λdw/dz = 0. Modified Bogoliubov: \|β_ω\|² ≈ exp(−2πω/κ) × exp(−2πΓ_H/(κ²c_s)·ω). Unitarity: \|α_k\|² − \|β_k\|² = 1 − δ_k. **Directly applicable** to quasi-1D graphene; 2+1D generalization adds off-diagonal metric components and transverse mode coupling. |
| `Lit-Search/Phase-1-and-Background/Tier-1/EFT corrections to acoustic Hawking radiation in BEC analog gravity.md` | W3, W4 | **Explicitly identifies the dissipative-EFT gap that Phase 5w fills.** No SK-EFT calculation of dissipative T_H modifications existed as of Phase 1 scoping. Also: dispersive correction hierarchy δT/T_H ~ O((ξ/λ_H)²), broadened horizon scale d_br. Subluminal dispersion (graphene) makes these bounds **more robust** than superluminal (BEC). |

### MEDIUM-HIGH relevance

| Deep Research File | Phase 5w Waves | Key Content |
|---|---|---|
| `Lit-Search/Phase-4/From string-nets to fracton hydrodynamics- the coarse-graining chain.md` | W5 | Glorioso-Huang-Lucas SK-EFT for multipole conservation. **Key finding for W5:** "No simple counting formula analogous to count(N) = floor((N+1)/2) + 1 exists [in higher D] because the transport tensor carries two types of indices." Must enumerate tensor structures per BRSSS. CGL/FDR pairing at each order: dissipative terms at derivative order 2n+1 paired with noise at order 2n. |
| `Lit-Search/Phase-5/Extending Schwinger-Keldysh EFT to driven-dissipative polariton condensates.md` | W3 | T_H = ℏκ/(2πk_B) **survives non-equilibrium** (kinematic effect). Three caveats on temperature (hydrodynamic approx, mass gap, spatial attenuation). **Key difference for graphene:** KMS is restored microscopically by e-e scattering in the hydrodynamic window, unlike polaritons where KMS is macroscopically broken. Degeneracy-breaking strategies not needed for graphene. |

### MEDIUM relevance

| Deep Research File | Phase 5w Waves | Key Content |
|---|---|---|
| `Lit-Search/Phase-1-and-Background/Tier-2/Non-Abelian gauge structure is universally erased by hydrodynamization.md` | W5, W6 | U(1) charge symmetry **survives** hydrodynamization (1-form Goldstone). Validates treating σ_Q as independent transport coefficient. Charge/heat decoupling in WF violation has firm theoretical grounding. |
| `Lit-Search/Phase-5a/The Onsager algebra- from lattice integrability to chiral fermions and fusion categories.md` | W6 | Algebraic framework for Onsager relations. Dolan-Grady presentation fits Mathlib Lie algebra infrastructure. Phase 5w W6 uses only linear Onsager reciprocal-relation symmetry, not the full algebra. |
| `Lit-Search/Phase-5/Walker-Wang finite-temperature η:s simulation- technical scoping assessment.md` | W7 | Transport coefficient extraction from MC: 50-100% systematic uncertainty on η/s. Analytical SK-EFT predictions (Phase 5w) bypass the analytic-continuation problem entirely. |

---

## Identified Research Gaps (requiring new deep research or targeted investigation)

1. **Complex turning-point WKB for 2+1D Dirac fluid** — Phase-3 covers 1+1D Belgiorno-Cacciatori-Trevisan 4th-order ODE. Phase 5w needs adaptation to 2+1D flows with off-diagonal metric. The quasi-1D block-diag reduces this to the known case, but transverse greybody factors require the full 2+1D Laplacian structure. *Addressed in W4; may need targeted deep research if quasi-1D approximation proves insufficient.*

2. **Onsager reciprocal relations in Lean 4** — No formalization exists in any proof assistant. Phase 5w W6 would be the first. The Phase-5a Onsager algebra infrastructure provides the algebraic foundation. *Highest-risk Lean target; fallback is Python+paper without Lean WF module.*

3. **SK-EFT dissipative corrections to T_H** — Phase-1 explicitly identifies this as a major open problem. Phase 5w fills this gap for both BEC and graphene via the WKB-FDR connection. *Core deliverable of W3-W4.*

4. **Transport counting for 2+1D charged conformal fluids (explicit enumeration)** — Phase-4 establishes no closed-form formula exists. Must follow BRSSS classification. *W5 deliverable; may need targeted deep research on Diles et al. (JHEP 2020) third-order structures.*

5. **WF violation at second order in SK-EFT** — No published calculation of how CGL constraints modify L = κ/(σT) beyond leading-order hydrodynamics. *W6 deliverable; novel theoretical result if achieved.*

6. **Graphene-specific backreaction** — Phase-1 shows acoustic holes cool as they radiate (BEC). Graphene dissipation channels energy to the electron-phonon bath, giving a qualitatively different steady-state. *Deferred to post-W4 extension.*

---

## Risk Assessment (updated from deep research §5)

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| T_H too low for detection in Dean geometry | Medium | High | T_H ≈ 2-3 K with T_H/T_ambient ~ 0.01-0.02. Correlation-based detection (Steinhauer method) can extract sub-thermal signals. Kim group's 5.5 mK Johnson noise sensitivity helps. |
| Bilayer vs. monolayer physics differs | Medium | Medium | Bilayer has lower c_s (favorable for horizon creation) but different band structure. The acoustic metric derivation is universal — only c_s and v_F change. |
| SK-EFT expansion marginally convergent (α ~ 0.5-0.9) | Medium | Medium | Expansion parameter ωl_ee/c_s ~ 0.1 at relevant frequencies — marginally OK. Breakdown characterization is itself publishable (Wave 7). |
| WF-violation Lean module (Wave 6) intractable | Medium-High | Medium | Onsager relations never formalized. Fallback: Python + paper without Lean WF module. Core Hawking prediction (Track A) is independent. |
| Competing group publishes first | Low | Medium | No group currently combines SK-EFT + graphene analog gravity + verification. The Dean group could publish Hawking predictions independently, but without the EFT framework. Speed matters: contact Lucas early. |
| Quasi-1D approximation insufficient | Low | Medium | Dean nozzle is genuinely quasi-1D (throat width >> l_ee). If transverse effects matter, they enter as greybody corrections, not qualitative changes. |

---

## Collaboration Strategy (from deep research §6)

### Tier 1 — Immediate outreach

| Group | Why | Action |
|---|---|---|
| **Dean/Lucas/Hone (Columbia + CU Boulder)** | Lucas co-authored SK-EFT papers with Glorioso AND the Dean nozzle paper. The bridge already exists. Geurs described the nozzle as enabling ability to "mimic a black hole" (Feb 2026 Columbia SPS talk). | Contact Lucas with T_H prediction for bilayer nozzle geometry. Propose joint paper on noise spectrum signature. **HIGHEST PRIORITY.** |
| **Philip Kim / Amir Yacoby (Harvard)** | Kim's Johnson noise thermometer: 5.5 mK sensitivity, 120-250 MHz bandwidth. Yacoby's NV magnetometry images flow fields. Together they can detect thermal Hawking signatures while imaging the flow. | Propose measurement protocol for S_I(ω) near sonic point. |
| **Denis Bandurin (NUS Singapore)** | Pioneer of constriction-flow experiments. New lab offers flexibility. | Propose bilayer nozzle geometry optimized for c_s crossing. |

### Tier 2 — Strong complementary

| Group | Connection |
|---|---|
| **Majumdar/Ghosh/Mukerjee (IISc)** | σ_Q and WF data as SK-EFT inputs. Transport measurement partners. |
| **Geim/Ponomarenko (Manchester)** | World's best graphene fabrication. Can produce any nozzle geometry. |
| **Weinfurtner (Nottingham → Manchester 2026)** | Analog gravity expertise + Manchester connection. |
| **Sorbonne (Jacquet/Bramati)** | Polariton analog gravity — existing SK-EFT polariton predictions connect. |

### Tier 3 — Key theorists

| Theorist | Relation to Phase 5w |
|---|---|
| **Andrew Lucas (CU Boulder)** | Natural collaborator — SK-EFT + Dirac fluid. Very high. |
| **Paolo Glorioso (MIT)** | Co-creator of CGL framework. Endorsement value. |
| **Subir Sachdev (Harvard)** | Central figure in graphene quantum critical transport. Complementary approach. |
| **Pavel Kovtun (U Victoria)** | SK-EFT formal properties — ideal Lean verification targets. |
| **Alfredo Iorio (Prague)** | Pioneer of graphene-as-analog-gravity (geometric approach, complementary to hydrodynamic). |
| **Dam Thanh Son (Chicago)** | Hydrodynamic EFT pioneer, KSS bound co-author. Advisory role. |

**Funding note (§6):** No existing grants for "analog Hawking radiation in graphene" — the field is pre-competitive. Opportunity for KITP workshop proposal.

---

## Success Criteria

**Minimum viable (Waves 2-3 + 5, ~3-5 months):**
- 2+1D analog metric formalized in Lean with block-diag theorem (~200 LOC new)
- T_H predictions for 4 graphene geometries with dissipative corrections (41 WKB/Hawking theorems reused directly)
- Transport coefficient classification for 2+1D charged conformal fluid (34 counting/FDR theorems reused directly)
- Feasibility memo sufficient for collaboration outreach to Lucas/Dean

**High-impact deliverable (+ Wave 4, ~5-8 months):**
- Full noise spectrum prediction S_I(ω) for Dean bilayer nozzle
- Detection protocol with S/N estimates for Kim group noise thermometry
- Sufficient for joint experimental proposal
- (Compressed from 8-10 months by 92% Lean reuse)

**Full scope (all 9 waves, ~10-15 months):**
- WF violation from two-channel SK-EFT, compared to data (W6 remains highest-risk: 4-6 months)
- Strong-coupling / viscosity bound analysis
- Graphene as verified Tier 2 platform
- Paper 16 through full 12-stage pipeline

---

## Connection to Existing Phases

| Phase | Connection |
|-------|-----------|
| Phase 1-2 | SK-EFT framework generalizes from 1+1D → 2+1D; counting formula is 1+1D-specific but KMS/CGL machinery is dimension-independent |
| Phase 3 (gauge erasure) | Graphene has no gauge fields at the hydrodynamic level — erasure theorem not needed, but universality theorem extends |
| Phase 3 (WKB) | Connection formula applies directly to quasi-1D Dirac fluid via block-diag reduction |
| Phase 4 (platforms) | Graphene joins BEC + polariton as Tier 2; existing prediction infrastructure reused |
| Phase 5d (ADW/RHMC) | Viscosity bound connection: Dirac fluid approaching η/s minimum is a candidate system for emergent gravity signatures |
| Phase 5u (paper revisions) | Independent — 5w does not modify Papers 1-15 |
| Phase 5v (KG/readiness) | Paper 16 enters KG + readiness system when drafted |

---

## Key References (from deep research §7, abridged — see full bibliography there)

**Experimental cornerstones:**
- Geurs et al. arXiv:2509.16321 (2025) — electronic de Laval nozzle, supersonic flow, sonic horizon
- Majumdar et al. arXiv:2501.03193 (2025) — σ_Q ≈ 4e²/h, >200× WF violation, η/s ~ 4× KSS
- Zhao et al. Nature 614, 688 (2023) — first measurement of c_s = v_F/√2

**Theoretical foundations:**
- Crossley/Glorioso/Liu arXiv:1511.03646 (2017) — CGL SK-EFT framework
- Lucas/Fong arXiv:1710.08425 (2018) — comprehensive Dirac fluid hydrodynamics review
- Baier et al. arXiv:0712.2451 (2008) — BRSSS second-order conformal hydrodynamics
- Bilić gr-qc/9908002 (1999) — relativistic acoustic geometry

**Analog gravity in graphene:**
- Iorio/Lambiase arXiv:1108.2340 (2012) — Hawking-Unruh on graphene (geometric approach)
- Morresi et al. arXiv:1907.08960 (2020) — tight-binding simulation, T_H ~ tens of K
