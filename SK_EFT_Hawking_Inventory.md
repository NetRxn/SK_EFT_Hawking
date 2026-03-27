# SK-EFT Hawking Project: Comprehensive Inventory

**Repository Root:** `SK_EFT_Hawking/`

**Project Summary:** Formal verification of dissipative effective field theory corrections to analog Hawking radiation in BEC sonic black holes. Six papers (Phases 1-4) with complete Lean 4 formalization (216 theorems + 1 axiom, zero sorry, 16 modules). 822 tests, 45 pipeline figures, 16 notebooks. 56 Aristotle-proved, 160 manual.

**Last verified:** March 27, 2026 (Wave 5 quality hardening)

---

## 1. PYTHON SOURCE FILES (30 modules + 11 __init__.py)

### 1.1 Core Module: `src/core/`

#### `src/core/constants.py` (242 lines)
**Purpose:** Single source of truth for all physical constants, experimental parameters, and the Aristotle theorem registry. **No other file may hardcode physical constants or experimental values.**

**Contents:**
- `HBAR`, `K_B` — SI physical constants
- `ATOMS` dict — Atomic properties (mass, scattering length) for Rb87, K39, Na23
- `EXPERIMENTS` dict — Experimental parameters (density, velocity, omega_perp) for Steinhauer, Heidelberg, Trento
- `ARISTOTLE_THEOREMS` dict — 56 theorem→run_id mappings across 18 runs + 1 manual
- `ARISTOTLE_PROVED_COUNT = 56`
- `COLORS` dict — Plotly color palette for consistent visualization

---

#### `src/core/formulas.py` (605 lines)
**Purpose:** Canonical Python implementations of every physics formula verified by Lean/Aristotle. **No other file may reimplement these formulas.** Each function documents its Lean theorem name and Aristotle run ID.

**Functions (19):**
- `count_coefficients(N)` — Transport coefficient counting: floor((N+1)/2) + 1
- `enumerate_monomials(N)` — List monomials at order N
- `damping_rate(gamma_1, gamma_2, k, omega, c_s)` — Γ(k,ω) at given wavenumber
- `dispersive_correction(D)` — δ_disp = -(π/6)·D²
- `hawking_temperature(kappa)` — T_H = ℏκ/(2πk_B)
- `first_order_correction(Gamma_H, kappa)` — δ_diss = Γ_H/κ
- `second_order_correction(...)` — δ^(2)(ω) frequency-dependent
- `third_order_correction(...)` — Third-order parity structure
- `effective_temperature_ratio(...)` — T_eff/T_H with all corrections
- `turning_point_shift(...)` — Complex WKB turning point displacement
- `decoherence_parameter(...)` — Modified unitarity deficit
- `fdr_noise_floor(...)` — FDR-mandated noise baseline
- `adw_effective_potential(C, G, Lambda, N_f)` — Coleman-Weinberg V_eff
- `adw_critical_coupling(Lambda, N_f)` — G_c = 8π²/(N_f·Λ²)
- `adw_curvature_at_origin(G, Lambda, N_f)` — d²V_eff/dC²|_{C=0}
- `tetrad_broken_generators(d)` — d²-1 broken generators in d dimensions
- `graviton_polarization_count(d)` — d(d-3)/2 massless gravitons
- `beliaev_damping_rate(...)` — Microscopic UV matching: Γ_Bel(ω_H)
- `beliaev_transport_coefficients(...)` — Extract γ₁, γ₂ from Beliaev

---

#### `src/core/transonic_background.py` (417 lines)
**Purpose:** 1D BEC transonic flow solver. Parameterizes velocity as smooth tanh transition through horizon.

**Key Types:** `BECParameters` (dataclass), `TransonicBackground` (dataclass)

**Factory Functions (import from constants.py):**
- `steinhauer_Rb87()` — ⁸⁷Rb BEC (Steinhauer 2016/2019)
- `heidelberg_K39()` — ³⁹K with Feshbach tuning (projected)
- `trento_spin_sonic()` — ²³Na spin-sonic (projected)

**Key Functions:**
- `solve_transonic_background(params, ...)` → `TransonicBackground`
- `compute_dissipative_correction(bg, params, gamma_1, gamma_2)` — Computes δ_diss, δ_disp using imports from `formulas.py`
- `experimental_survey()` — Print parameter survey for all 3 platforms

---

#### `src/core/visualizations.py` (3432 lines)
**Purpose:** All Plotly figures (42 functions) + full COLORS palette. **Only place figure functions live.**

**Color Palette:** Steel blue (Steinhauer), berry (Heidelberg), amber (Trento), sage (dispersive), carmine (dissipative), warm tan (noise), cool grey (cross-terms)

**Figure Functions by Phase:**
- Phase 1 (6): transonic_profiles, correction_hierarchy, parameter_space, spin_sonic_enhancement, temperature_decomposition, kappa_scaling
- Phase 2 (6): cgl_fdr_pattern, even_vs_odd_kernel, boundary_term_suppression, positivity_constraint, on_shell_vanishing, einstein_relation
- Phase 3a Third-Order (3): parity_alternation, damping_rate_third_order, spectral_correction_comparison
- Phase 3b Gauge Erasure (2): sm_scorecard, erasure_survey
- Phase 3b Kappa Crossing (2): kappa_crossing_phase3, spin_sonic_enhancement_phase3
- Phase 3c WKB Connection (6): bogoliubov_connection, complex_turning_point, effective_surface_gravity, decoherence_and_noise, hawking_spectrum_exact, exact_vs_perturbative
- Phase 3d ADW (7): adw_effective_potential, adw_phase_diagram, adw_ng_mode_decomposition, adw_he3_analogy, adw_structural_obstacles, adw_coupling_scan (+ stakeholder variant)
- Phase 4a Experimental (4): prediction_table_comparison, detector_requirements, kappa_scaling_phase4, noise_floor_crossover
- Phase 4b Chirality+GL (3): chirality_wall_status, gl_phase_diagram, he3_comparison_table
- Phase 4b Vestigial (3): vestigial_effective_potential, vestigial_phase_diagram, backreaction_cooling
- Phase 4b Fracton (1): information_retention

**Stakeholder variants** use `stakeholder=True` parameter for simplified versions.

---

#### `src/core/aristotle_interface.py` (893 lines)
**Purpose:** Interface to Aristotle automated theorem prover. Registry of 56 sorry gaps (all filled).

**Key Types:** `SorryGap` (dataclass), `AristotleResult` (dataclass), `AristotleRunner` (class)

**Sorry Gap Registry (56 total, all filled):**
- Phase 1: 14 gaps (AcousticMetric, SKDoubling, HawkingUniversality)
- Phase 2: 9 gaps (SecondOrderSK, WKBAnalysis)
- Phase 2 Stress Tests: 9 gaps (KMS optimality, FDR sign tests, limit checks)
- Phase 2 Round 5: 3 gaps (total-division strengthening)
- Direction D CGL: 5 gaps (einstein_relation, cgl_fdr, cgl_implies_KMS)
- Phase 3: 1 gap (curvature_zero_at_Gc)
- Phase 4: 13 gaps (fracton, vestigial, chirality batch b1ea2eb7)
- Wave 5: 2 gaps (gs_nogo_requires_all, zeroTemp_nontrivial, run f35ca767)

---

### 1.2 Second-Order Module: `src/second_order/`

#### `src/second_order/enumeration.py` (441 lines)
**Purpose:** Transport coefficient counting at arbitrary EFT order via SK axioms. Formula: count(N) = floor((N+1)/2) + 1.

#### `src/second_order/coefficients.py` (541 lines)
**Purpose:** Second-order data structures, action constructors, correction formulas. Imports `first_order_correction` from `formulas.py`.

#### `src/second_order/wkb_analysis.py` (636 lines)
**Purpose:** WKB mode analysis through the dissipative horizon. Frequency-dependent Bogoliubov coefficients.

#### `src/second_order/cgl_derivation.py` (762 lines)
**Purpose:** CGL dynamical KMS derivation of the FDR at arbitrary EFT order. Key finding: CGL pairs noise with odd-ω dissipative retarded terms only.

---

### 1.3 Phase 3 Modules

#### `src/gauge_erasure/erasure_theorem.py` (341 lines)
**Purpose:** Non-Abelian gauge erasure universal structural theorem. Proves that non-Abelian gauge symmetries produce discrete (domain wall) defects in the condensed phase, while Abelian U(1) produces continuous (Goldstone) modes.

**Key Result:** In the Standard Model, only U(1)_EM survives gauge erasure → only electromagnetic Goldstone modes in the superfluid phase.

#### `src/wkb/connection_formula.py` (517 lines)
**Purpose:** Exact WKB connection formula for the dissipative horizon. Complex turning point analysis, Stokes geometry, modified Bogoliubov coefficients.

**Key Result:** The exact connection formula replaces the perturbative δ_diss expansion with a non-perturbative Bogoliubov calculation through the complex turning point.

#### `src/wkb/bogoliubov.py` (206 lines)
**Purpose:** Modified unitarity and decoherence from dissipation. |α|² - |β|² < 1 with the deficit set by the decoherence parameter.

#### `src/wkb/spectrum.py` (546 lines)
**Purpose:** Observable Hawking spectrum with all corrections (exact WKB + noise floor).

#### `src/wkb/backreaction.py` (798 lines)
**Purpose:** Acoustic black hole cooling via backreaction. Key result: acoustic BHs cool and approach extremality (opposite of Schwarzschild). Imports `HBAR`, `K_B`, `ATOMS` from `constants.py` and `hawking_temperature` from `formulas.py`.

#### `src/adw/wen_model.py` (222 lines)
**Purpose:** Wen's lattice QED model — the microscopic UV completion for emergent gravity.

#### `src/adw/hubbard_stratonovich.py` (299 lines)
**Purpose:** Hubbard-Stratonovich decomposition introducing the composite tetrad field.

#### `src/adw/gap_equation.py` (401 lines)
**Purpose:** Coleman-Weinberg effective potential and critical coupling G_c = 8π²/(N_f·Λ²). Imports canonical formula from `formulas.py`.

#### `src/adw/fluctuations.py` (475 lines)
**Purpose:** SSB analysis, Nambu-Goldstone mode counting (2 massless gravitons in 4D), Vergeles consistency check.

#### `src/adw/ginzburg_landau.py` (1139 lines)
**Purpose:** Ginzburg-Landau expansion and He-3 analogy. A-phase instability, B-phase stability, phase diagram.

---

### 1.4 Phase 4 Modules

#### `src/experimental/predictions.py` (669 lines)
**Purpose:** Platform-specific spectral predictions for experimentalists. Generates prediction tables (Steinhauer/Heidelberg/Trento), computes shot requirements, κ-scaling test parameters.

#### `src/chirality/tpf_gs_analysis.py` (687 lines)
**Purpose:** TPF vs GS chirality wall compatibility analysis. Evaluates 4 GS no-go conditions against TPF construction: TPF evades 2 of 4 (translation invariance, ancilla fields), making the breach conditional.

#### `src/fracton/sk_eft.py` (711 lines)
**Purpose:** Fracton SK-EFT with higher-moment conservation laws. Binomial charge counting.

#### `src/fracton/information_retention.py` (1017 lines)
**Purpose:** UV information comparison: fracton hydrodynamics retains exponentially more UV structure than standard hydro due to additional conserved charges.

#### `src/fracton/gravity_connection.py` (1194 lines)
**Purpose:** Kerr-Schild bootstrap connection to gravity. DOF gap analysis, route achievements and obstacles.

#### `src/fracton/non_abelian.py` (537 lines)
**Purpose:** Non-Abelian fracton obstruction analysis — a **negative result**. Non-Abelian gauge structure is incompatible with fracton symmetry constraints.

#### `src/vestigial/mean_field.py` (361 lines)
**Purpose:** Mean-field gap equation for the vestigial metric phase. Curvature-based phase classification: pre-geometric (G/G_c < 0.8), vestigial (0.8-1.0), full tetrad (>1.0). Imports `adw_curvature_at_origin` from `formulas.py`.

#### `src/vestigial/lattice_model.py` (284 lines)
**Purpose:** Euclidean lattice formulation of the ADW tetrad model.

#### `src/vestigial/monte_carlo.py` (235 lines)
**Purpose:** Metropolis Monte Carlo for the lattice model. Measures tetrad VEV and metric correlator.

#### `src/vestigial/phase_diagram.py` (199 lines)
**Purpose:** Phase diagram construction from mean-field and MC data. Uses corrected phase classification from `mean_field.py`.

#### `src/vestigial/finite_size.py` (461 lines)
**Purpose:** Finite-size scaling analysis for the vestigial-to-full-tetrad transition.

---

## 2. LEAN FORMAL VERIFICATION (16 modules, 216 theorems + 1 axiom)

### Lean 4.28.0, Mathlib pinned to commit `8f9d9cff`

| Module | Lines | Theorems | Axioms | Phase | Key Results |
|--------|-------|----------|--------|-------|-------------|
| Basic | 202 | 0 | 0 | 1 | Type definitions (ScalarField, Spacetime1D) |
| AcousticMetric | 310 | 8 | 0 | 1 | det(g)=-ρ², Lorentzian signature, T_H formula |
| SKDoubling | 661 | 9 | 0 | 1 | Uniqueness (γ₁,γ₂), FDR, KMS optimality, zeroTemp_nontrivial |
| HawkingUniversality | 555 | 9 | 0 | 1 | Dispersive bound, dissipative existence, universality |
| SecondOrderSK | 882 | 19 | 0 | 2 | Counting formula, positivity constraint, full uniqueness |
| WKBAnalysis | 561 | 15 | 0 | 2 | Damping nonneg, turning point, biconditionals |
| CGLTransform | 352 | 7 | 0 | 2 | CGL FDR, Einstein relation, CGL→KMS chain |
| ThirdOrderSK | 329 | 14 | 0 | 3 | Parity alternation (general N), spectral parity |
| GaugeErasure | 262 | 11 | 1 | 3 | Gauge erasure theorem, U(1) survival, SM dichotomy |
| WKBConnection | 414 | 17 | 0 | 3 | Decoherence nonneg, noise floor, unitarity deficit |
| ADWMechanism | 288 | 21 | 0 | 3 | Critical coupling pos, curvature_zero_at_Gc, NG modes |
| ChiralityWall | 301 | 17 | 0 | 4 | GS no-go requires all, TPF evasion count, wall status |
| VestigialGravity | 272 | 18 | 0 | 4 | Phase hierarchy, EP violation, metric DOF |
| FractonHydro | 264 | 17 | 0 | 4 | Binomial monotonicity, charge counting, erasure universal |
| FractonGravity | 248 | 20 | 0 | 4 | Bootstrap divergence, DOF gap, route achievements |
| FractonNonAbelian | 203 | 14 | 0 | 4 | YM incompatibility, obstruction count, param gap |

**Axiom:** `non_abelian_center_discrete` (GaugeErasure.lean) — Encodes Lie theory: center of non-Abelian compact Lie group is discrete.

---

## 3. ARISTOTLE THEOREM PROVER (56 proved across 18 runs)

| Run ID | Date | Theorems | Scope |
|--------|------|----------|-------|
| 082e6776 | 2026-03-23 | 4 | Phase 1 core (det, inv, Lorentzian, positivity) |
| a87f425a | 2026-03-23 | 1 | Phonon EOM |
| 88cf2000 | 2026-03-23 | 1 | Acoustic metric candidate |
| 638c5ff3 | 2026-03-23 | 1 | FDR complete |
| 657fcd6a | 2026-03-23 | 1 | Dissipative existence |
| d65e3bba | 2026-03-23 | 1 | Dispersive bound |
| 416fb432 | 2026-03-23 | 1 | Hawking universality |
| 270e77a0 | 2026-03-23 | 1 | firstOrder_uniqueness (most complex proof) |
| 20556034 | 2026-03-23 | 2 | FDR per-sector (γ₁, γ₂) |
| d61290fd | 2026-03-24 | 4 | Counting formula + instances |
| c4d73ca8 | 2026-03-24 | 4 | Full uniqueness, positivity constraint, turning point |
| 3eedcabb | 2026-03-24 | 10 | Stress tests batch (KMS optimal, limit checks) |
| 518636d7 | 2026-03-24 | 3 | Round 5: total-division strengthening |
| dab8cfc1 | 2026-03-24 | 2 | CGL: Einstein relation, secondOrder_cgl_fdr |
| 2ca3e7e6 | 2026-03-24 | 3 | CGL: general FDR, spatial, cgl→KMS |
| f8de66d1 | 2026-03-25 | 1 | ADW: curvature_zero_at_Gc |
| b1ea2eb7 | 2026-03-26 | 13 | Phase 4 batch (fracton, vestigial, chirality) |
| f35ca767 | 2026-03-27 | 2 | Wave 5: gs_nogo_requires_all, zeroTemp_nontrivial |

---

## 4. JUPYTER NOTEBOOKS (16 total: 8 Technical + 8 Stakeholder)

| Notebook | Phase | Topic |
|----------|-------|-------|
| Phase1_Technical | 1 | Transonic flow, Beliaev damping, δ_diss for 3 platforms |
| Phase1_Stakeholder | 1 | BEC analog gravity motivation, key results |
| Phase2_Technical | 2 | Enumeration, KMS, WKB, frequency-dependent correction |
| Phase2_Stakeholder | 2 | Parity breaking, ω³ spectrum distortion |
| Phase3a_ThirdOrder_Technical | 3 | Parity alternation, third-order enumeration |
| Phase3a_ThirdOrder_Stakeholder | 3 | Parity as experimental probe |
| Phase3b_GaugeErasure_Technical | 3 | Non-Abelian erasure, SM scorecard |
| Phase3b_GaugeErasure_Stakeholder | 3 | Gauge hierarchy implications |
| Phase3c_WKBConnection_Technical | 3 | Complex turning point, exact Bogoliubov, noise floor |
| Phase3c_WKBConnection_Stakeholder | 3 | Modified unitarity, decoherence |
| Phase3d_ADW_Technical | 3 | Gap equation, NG modes, obstacles, He-3 analogy |
| Phase3d_ADW_Stakeholder | 3 | Emergent gravity concept, phase diagram |
| Phase4a_ExperimentalPredictions_Technical | 4 | Prediction tables, κ-scaling test, shot requirements |
| Phase4a_ExperimentalPredictions_Stakeholder | 4 | What experimentalists need to measure |
| Phase4b_Vestigial_Technical | 4 | Mean-field + MC, 3-phase structure, EP violation |
| Phase4b_Vestigial_Stakeholder | 4 | Pre-geometric→vestigial→full tetrad narrative |

**Convention:** Technical mirrors paper structure. Stakeholder teaches the physics. All import from `src/` modules (no inline formula redefinition).

---

## 5. PAPER DRAFTS (6 papers + prediction tables)

| Paper | Format | Lines | Topic |
|-------|--------|-------|-------|
| paper1_first_order | PRL | 397 | First-order SK-EFT: δ_diss = Γ_H/κ |
| paper2_second_order | PRD | 453 | Second-order + CGL + counting formula |
| paper3_gauge_erasure | PRL | 310 | Non-Abelian gauge erasure theorem |
| paper4_wkb_connection | PRD | 298 | Exact WKB connection formula |
| paper5_adw_gap | PRD | 397 | ADW mean-field gap equation |
| paper6_vestigial | PRD | 530 | Vestigial metric phase (3-phase structure) |
| experimental_predictions | Tables | 156 | Platform spectral predictions |

**Key numerical claims (all traced to formulas.py via CHECK 14):**
- δ_diss ~ 10⁻⁵-10⁻³ (Paper 1)
- δ^(2)(ω) ∝ ω³ (Paper 2)
- U(1) only SM survivor (Paper 3)
- Noise floor = δ_diss/(1-δ_diss) (Paper 4)
- G_c = 8π²/(N_f·Λ²) (Paper 5)
- Vestigial window: G/G_c ≈ 0.8-1.0 in mean-field (Paper 6)

---

## 6. TEST FILES (16 files, 822 tests)

| Test File | Tests | Covers |
|-----------|-------|--------|
| test_transonic_background | 12 | BEC parameters, background solver, corrections |
| test_second_order | 12 | Enumeration, coefficients, WKB |
| test_cgl_derivation | 26 | CGL FDR, kernel decomposition, boundary terms |
| test_cross_validation | 7 | Wraps validate.py 14 checks |
| test_lean_integrity | 9 | Module presence, toolchain, zero sorry |
| test_third_order | 36 | Third-order enumeration, parity structure |
| test_gauge_erasure | 25 | Erasure theorem, SM analysis |
| test_wkb_connection | 65 | Connection formula, Bogoliubov, spectrum |
| test_adw | 78 | Gap equation, NG modes, fluctuations |
| test_ginzburg_landau | 75 | GL expansion, He-3 analogy |
| test_experimental | 34 | Prediction tables, shot counts |
| test_chirality | 55 | GS conditions, TPF evasion |
| test_fracton | 110 | SK-EFT, information retention |
| test_fracton_gravity | 146 | Bootstrap, DOF gap, non-Abelian |
| test_vestigial | 56 | Mean-field, MC, 3-phase structure |
| test_backreaction | 76 | Cooling, extremality, timescales |

---

## 7. SCRIPTS

| Script | Lines | Purpose |
|--------|-------|---------|
| validate.py | 1158 | 14 cross-layer validation checks |
| review_figures.py | 959 | Generate 45 PNGs + structural checks + manifest |
| submit_to_aristotle.py | 466 | Aristotle submission/retrieval/integration |

---

## 8. CONFIGURATION FILES

| File | Purpose |
|------|---------|
| pyproject.toml | Project metadata, dependencies (numpy, scipy, plotly, pandas, sympy, kaleido, aristotlelib) |
| uv.lock | uv package manager lock file |
| .python-version | Python >=3.11 |
| lean/lakefile.toml | Lean Lake build config (depends on Mathlib) |
| lean/lean-toolchain | v4.28.0 |
| lean/lake-manifest.json | Lean package manifest |
| .env | ARISTOTLE_API_KEY (not committed) |
| .gitignore | Excludes __pycache__, .venv, .env, figures/*.html, data/ |

---

## 9. DOCUMENTATION

### Reference Documents
| Document | Location | Purpose |
|----------|----------|---------|
| WAVE_EXECUTION_PIPELINE.md | docs/ | **Mandatory** 12-stage execution process |
| Theorm_Proving_Aristotle_Lean.md | docs/references/ | Aristotle API reference (read before every session) |
| Feasibility Study | docs/ | Top-level feasibility assessment |
| Critical Review v3 | docs/ | Consolidated evidence evaluation |

### Roadmaps
| Document | Location | Status |
|----------|----------|--------|
| Phase1_Roadmap.md | docs/roadmaps/ | Complete |
| Phase2_Roadmap.md | docs/roadmaps/ | Complete |
| Phase3_Roadmap.md | docs/roadmaps/ | Complete |
| Phase4_Roadmap.md | docs/roadmaps/ | Complete (includes Wave 5) |
| Phase5_Roadmap.md | docs/roadmaps/ | Planning |

### Stakeholder Documents
| Document | Location |
|----------|----------|
| companion_guide.md | docs/stakeholder/ |
| Phase1_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase2_Implications.md + Strategic_Positioning.md + companion_guide | docs/stakeholder/ |
| Phase3_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase4_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |

### Analysis Documents
| Document | Location | Topic |
|----------|----------|-------|
| gravity_hierarchy_synthesis.md | docs/analysis/ | Three-phase vestigial structure |
| fracton_layer2_assessment.md | docs/analysis/ | Fracton vs standard hydro comparison |
| chirality_wall_analysis.md | docs/analysis/ | GS no-go condition analysis |

### Validation
| Document | Location | Status |
|----------|----------|--------|
| lean_quality_audit.md | docs/validation/ | Wave 5 theorem quality audit |
| VALIDATION_REPORT.md | docs/validation/ | Phase 2 validation snapshot (archived) |
| reports/*.json, *.txt | docs/validation/reports/ | Timestamped validation run archives |

---

## 10. KEY FORMULAS (all in `src/core/formulas.py` with Lean refs)

### Acoustic Metric & Hawking Temperature
- ds² = (n/c_s)[-(c_s²-v²)dt² - 2v·dt·dx + dx²]
- κ = |dv/dx - dc_s/dx| at horizon
- T_H = ℏκ/(2πk_B) — Lean: `hawking_temp_from_surface_gravity`

### First-Order SK-EFT
- δ_diss = Γ_H/κ — Lean: `firstOrder_positivity`
- Γ_H = (γ₁+γ₂)·(κ/c_s)² — Lean: `dampingRate_firstOrder_nonneg`

### Second-Order SK-EFT
- count(N) = floor((N+1)/2) + 1 — Lean: `transport_coefficient_count`
- γ_{2,1} + γ_{2,2} = 0 — Lean: `combined_positivity_constraint`
- δ^(2)(ω) ∝ (ω/Λ)³ — Lean: `secondOrder_vanishes_on_shell_with_positivity`

### Dispersive Correction
- δ_disp = -(π/6)·D² — Lean: `dispersive_correction_bound`
- D = κξ/c_s (adiabaticity)

### Exact WKB
- Decoherence parameter = 2Γ_H/(κ(1-Γ_H/κ)) — Lean: `decoherence_nonneg`
- Noise floor = δ_diss/(2(1-δ_diss)) — Lean: `noise_floor_nonneg`

### ADW Gravity
- G_c = 8π²/(N_f·Λ²) — Lean: `critical_coupling_pos`
- d²V_eff/dC²|_{C=0} = 1/G - N_f·Λ²/(8π²) — Lean: `curvature_zero_at_Gc`
- Broken generators: d²-1 — Lean: `broken_generators_4d`
- Graviton polarizations: d(d-3)/2 — Lean: `graviton_pol_4d`

### Vestigial Phase Classification
- Pre-geometric: curvature > 0.3 × curvature_max (weak coupling)
- Vestigial: curvature < 0.3 × curvature_max, C = 0 (near G_c)
- Full tetrad: C > 0 (above G_c) — Lean: `pos_C_gives_full_tetrad`

### Fracton Hydro
- Fracton charges: C(d+N-1, N) — Lean: `fracton_charges_monotone`
- Standard charges: C(d+N-1, N) for N=1 — Lean: `fracton_exceeds_standard_general`

---

## SUMMARY TABLE

| Category | Count | Status |
|----------|-------|--------|
| **Python Source Modules** | 30 | Complete (Phases 1-4) |
| **Python __init__.py** | 11 | Complete |
| **Test Files** | 16 | 822 tests, all passing |
| **Notebooks** | 16 | Phases 1-4 (Technical + Stakeholder) |
| **Lean Modules** | 16 | All build clean (zero sorry) |
| **Lean Theorems** | 216 + 1 axiom | Zero sorry |
| **Aristotle-proved** | 56 | 18 runs |
| **Manual proofs** | 160 | |
| **Paper Drafts** | 6 + prediction tables | Full LaTeX |
| **Pipeline Figures** | 45 | All PNGs generated |
| **Validation Checks** | 14 | All passing |
| **Scripts** | 3 | validate, review_figures, submit_to_aristotle |
| **Stakeholder Docs** | 11 | Phases 1-4 |
| **Analysis Docs** | 3 | Vestigial, fracton, chirality |
| **Roadmaps** | 5 | Phases 1-5 |

---

**Project Status:** Phase 4 COMPLETE. Wave 5 quality hardening COMPLETE.
