# SK-EFT Hawking Project: Comprehensive Inventory

**Repository Root:** `SK_EFT_Hawking/`

**Project Summary:** Formal verification of dissipative effective field theory corrections to analog Hawking radiation in BEC sonic black holes. Ten papers (Phases 1-5b) + Phase 5 analytical completion, chirality wall formalization, Layer 1 categorical infrastructure, Weingarten/fracton/NJL formalization, vestigial susceptibility, and Waves 7A-7C (gauge-link MC + RHMC). Lean 4 formalization: 951 theorems, 0 axioms across 64 modules — ZERO sorry. 273 Aristotle-proved (270 machine + 3 manual). 1506 tests, 72 pipeline figures, 26 notebooks, 49 Python source modules.

**Last verified:** April 4, 2026 (axiom integrity sweep — 4 axioms discharged/removed, W7C RHMC complete, L=4 done, L=8 in flight)

---

## 1. PYTHON SOURCE FILES (49 modules + 11 __init__.py)

### 1.1 Core Module: `src/core/`

#### `src/core/constants.py` (242 lines)
**Purpose:** Single source of truth for all physical constants, experimental parameters, and the Aristotle theorem registry. **No other file may hardcode physical constants or experimental values.**

**Contents:**
- `HBAR`, `K_B` — SI physical constants
- `ATOMS` dict — Atomic properties (mass, scattering length) for Rb87, K39, Na23
- `EXPERIMENTS` dict — Experimental parameters (density, velocity, omega_perp) for Steinhauer, Heidelberg, Trento
- `ARISTOTLE_THEOREMS` dict — 254 theorem→run_id mappings across 32+ runs
- `ARISTOTLE_PROVED_COUNT = 99`
- `COLORS` dict — Plotly color palette for consistent visualization
- `CATEGORY_HIERARCHY` — 3-layer categorical infrastructure
- `FUSION_EXAMPLES` — 5 fusion categories with rules + F-matrices
- `DRINFELD_DOUBLE` — D(G) data for Z/2, Z/3, S₃
- `LAYER1_CONNECTIONS` — Layer 1→2→3 bridge connections
- `GS_CONDITIONS`, `TPF_VIOLATIONS`, `LATTICE_FRAMEWORK` — Chirality wall data
- `POLARITON_PLATFORMS` — 3 cavity qualities for polariton predictions
- `ADW_2D_MODEL`, `ADW_4D_MODEL`, `SU2_HAAR`, `SO4_HAAR` — MC parameters

---

#### `src/core/formulas.py` (~1200 lines)
**Purpose:** Canonical Python implementations of every physics formula verified by Lean/Aristotle. **No other file may reimplement these formulas.** Each function documents its Lean theorem name and Aristotle run ID.

**Functions (39):** (19 Phase 1-4 + 20 Phase 5)
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

#### `src/core/visualizations.py` (~4230 lines)
**Purpose:** All Plotly figures (60 functions) + full COLORS palette. **Only place figure functions live.**

**Color Palette:** Steel blue (Steinhauer), berry (Heidelberg), amber (Trento), sage (dispersive), carmine (dissipative), warm tan (noise), cool grey (cross-terms)

**Figure Functions by Phase (60 total):**
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
- Phase 5 Wave 1 (2): kappa_scaling_physical, polariton_regime_map
- Phase 5 Wave 2 (4): grassmann_trg_2d_phase, fermion_bag_4d_binder, fermion_bag_4d_phase_diagram, vestigial_binder_crossing
- Phase 5 Wave 3/5 (5): gs_condition_formalization, tpf_evasion_architecture, fock_exterior_algebra, lean_theorem_summary, vestigial_susceptibility_split
- Phase 5 Wave 4 (5): category_hierarchy, fusion_rules_comparison, fibonacci_f_matrix, drinfeld_anyon_spectrum, layer123_bridge
- Phase 5 Wave 5 (1): vestigial_phase_diagram_mc (MF + MC overlay)

**Stakeholder variants** use `stakeholder=True` parameter for simplified versions.

---

#### `src/core/aristotle_interface.py` (~1200 lines)
**Purpose:** Interface to Aristotle automated theorem prover. Registry of sorry gaps (all filled).

**Key Types:** `SorryGap` (dataclass), `AristotleResult` (dataclass), `AristotleRunner` (class)

**Sorry Gap Registry (254 registry entries, all gaps filled):**
- Phase 1: 14 gaps (AcousticMetric, SKDoubling, HawkingUniversality)
- Phase 2: 9 gaps (SecondOrderSK, WKBAnalysis)
- Phase 2 Stress Tests: 9 gaps (KMS optimality, FDR sign tests, limit checks)
- Phase 2 Round 5: 3 gaps (total-division strengthening)
- Direction D CGL: 5 gaps (einstein_relation, cgl_fdr, cgl_implies_KMS)
- Phase 3: 1 gap (curvature_zero_at_Gc)
- Phase 4: 13 gaps (fracton, vestigial, chirality batch b1ea2eb7)
- Wave 1C/3A-C: 22 gaps (kappa-scaling, LatticeHamiltonian, GoltermanShamir, TPFEvasion, ExteriorAlgebra)
- Wave 4A: 11 gaps (KLinearCategory, SphericalCategory)
- Wave 4B: 7 gaps (FusionExamples)
- Wave 4C: 5 gaps (VecG, DrinfeldDouble)
- Wave 9C: 77 gaps (SO4Weingarten 14, FractonFormulas 45, WetterichNJL 18)
- Wave 6B: 16 gaps (VestigialSusceptibility)
- Wave 7A-B: 21 gaps (QuaternionGauge 10, GaugeFermionBag 9, Binder 2)
- Wave 7B-C: 47 manual proofs (HubbardStratonovichRHMC 22, MajoranaKramers 25)

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

#### `src/vestigial/su2_integration.py` (Phase 5 Wave 2A)
**Purpose:** Analytical SU(2) Haar measure integration. Peter-Weyl decomposition of the one-link integral. Pseudo-reality verification for sign-problem absence.

#### `src/vestigial/grassmann_trg.py` (Phase 5 Wave 2A)
**Purpose:** 2D Grassmann TRG implementation. Iterative tensor coarse-graining for the reduced ADW model. Free energy, specific heat, coupling scan, D_cut convergence.

#### `src/vestigial/lattice_4d.py` (Phase 5 Wave 2B)
**Purpose:** 4D hypercubic lattice model with SO(4) ≅ SU(2)_L × SU(2)_R gauge integration. Site/bond/total action, tetrad/metric order parameters, neighbor/bond indexing.

#### `src/vestigial/fermion_bag.py` (Phase 5 Wave 2B)
**Purpose:** Fermion-bag Metropolis MC for 8-fermion vertices (Chandrasekharan algorithm). Avoids sign problem via SU(2) pseudo-reality.

#### `src/vestigial/phase_scan.py` (Phase 5 Wave 2B)
**Purpose:** 4D coupling scan with Binder cumulant analysis. Identifies vestigial phase via split Binder crossings for tetrad vs metric order parameters.

### 1.5 Phase 5 Modules

#### `src/experimental/kappa_scaling.py` (Phase 5 Wave 1A)
**Purpose:** Physical kappa-scaling sweeps for all BEC platforms. Computes dispersive (∝κ²) and dissipative (∝κ) corrections as functions of surface gravity. Identifies crossover κ_cross where |δ_disp| = δ_diss.

#### `src/experimental/polariton_predictions.py` (Phase 5 Wave 1B)
**Purpose:** Tier 1 polariton platform predictions. Spatial attenuation correction, validity parameter Γ_pol/κ, regime classification (ultra-long/long/standard cavities).

#### `src/vestigial/quaternion.py` (Phase 5 Wave 7A)
**Purpose:** SU(2) quaternion algebra for SO(4) gauge theory. Vectorized operations, Haar random sampling.

#### `src/vestigial/so4_gauge.py` (Phase 5 Wave 7A)
**Purpose:** SO(4) gauge theory via quaternion pair decomposition. Plaquette, staple, Kennedy-Pendleton heatbath, overrelaxation.

#### `src/vestigial/gauge_fermion_bag.py` (Phase 5 Wave 7B)
**Purpose:** Hybrid fermion-bag + gauge-link Monte Carlo. 4×4 complex fermion matrix, Sherman-Morrison-Woodbury updates.

#### `src/vestigial/gauge_fermion_bag_majorana.py` (Phase 5 Wave 7B)
**Purpose:** 8×8 Majorana sign-free fermion-bag. Kramers degeneracy (PRL 116), Givens Spin(4), Woodbury gauge updates. Hits percolation wall at L≥6.

#### `src/vestigial/hs_rhmc.py` (Phase 5 Wave 7C)
**Purpose:** Hubbard-Stratonovich + RHMC algorithm. Reference numpy/scipy implementation. Complex pseudofermion, Zolotarev rational approximation, multi-shift CG.

#### `src/vestigial/hs_rhmc_jax.py` (Phase 5 Wave 7C)
**Purpose:** JAX CPU backend for RHMC. Batched CG solver.

#### `src/vestigial/hs_rhmc_torch.py` (Phase 5 Wave 7C)
**Purpose:** PyTorch CPU backend for RHMC. Production default. Batched LU (L=4) and batched CG (L≥6), FSAL Omelyan integrator.

#### `src/core/provenance.py` (Phase 5 Wave 9D)
**Purpose:** Parameter provenance registry. PARAMETER_PROVENANCE dict with tiers, sources, verification dates.

#### `src/core/citations.py` (Phase 5 Wave 9D)
**Purpose:** Citation registry. CITATION_REGISTRY with DOIs, usage mapping.

---

## 2. LEAN FORMAL VERIFICATION (58 modules, 900 theorems + 2 axioms)

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
| KappaScaling | ~200 | 11 | 0 | 5 | Crossover balance, regime classification, scaling laws |
| PolaritonTier1 | ~150 | 6 | 0 | 5 | Spatial attenuation ≥ 1, monotonicity, BEC recovery |
| SU2PseudoReality | ~200 | 10 | 0 | 5 | One-link normalization, effective coupling, Binder limits |
| FermionBag4D | ~250 | 16 | 0 | 5 | SO(4) integration, 8-fermion bounds, bag positivity, vestigial splitting |
| LatticeHamiltonian | ~400 | 28 | 0 | 5 | BZ compact, GS 9 conditions, TPF 3 violations, ℓ²(ℤ) ∞-dim, round discontinuous, Hermitian trace |
| GoltermanShamir | ~330 | 14 | 1 | 5 | 9 GS conditions as substantive Props, no-go bundle, TPF evasion, Fock space finite-dim, Pauli exclusion |
| TPFEvasion | ~200 | 12 | 0 | 5 | Master synthesis: 5 violations assembled, tpf_outside_gs_scope_main, two_violations_proved |
| KLinearCategory | ~300 | 16 | 0 | 5 | SemisimpleCategory, FinitelyManySimples, Schur orthogonality, FusionRules, Vec_G D²=\|G\|, Rep(S₃) D²=6 |
| SphericalCategory | ~350 | 18 | 0 | 5 | PivotalCategory (FIRST-EVER), CategoricalTrace, SphericalCategory, quantumDim, Fibonacci φ²=φ+1 |
| FusionCategory | ~250 | 14 | 0 | 5 | FusionCategoryData axioms, FSymbolData, PentagonSatisfied, globalDimSq_pos, Frobenius-Perron |
| FusionExamples | ~400 | 30 | 0 | 5 | Vec_{Z/2,Z/3}, Rep(S₃), Fibonacci: fusion rules, commutativity, τ⊗τ=1⊕τ, F-matrix, chirality |
| VecG | ~200 | 9 | 0 | 5 | GradedVectorSpace, Day convolution, unit/assoc/simple tensor, dim multiplicativity |
| DrinfeldDouble | ~300 | 15 | 0 | 5 | DrinfeldDoubleElement, twisted multiplication, conjugation action, D(G) unit laws, anyon counting |
| GaugeEmergence | ~250 | 14 | 0 | 5 | Half-braiding, gauge emergence Z(Vec_G)≅Rep(D(G)), chirality limitation c≡0(8), Layer 1→2→3 bridge |
| SO4Weingarten | ~250 | 14 | 0 | 5 | Weingarten 2nd/4th moment, channel positivity, bond weight, Planck occupation (**ALL PROVED**, Aristotle `117a7115`) |
| FractonFormulas | ~400 | 45 | 0 | 5 | Charge counting, dispersion, retention, DOF gap, YM obstructions (**ALL PROVED**, Aristotle `4528aa2b`) |
| WetterichNJL | ~250 | 18 | 0 | 5 | Fierz completeness, scalar/pseudoscalar/vector channels, NJL-ADW correspondence (**ALL PROVED**, Aristotle `4528aa2b`) |
| VestigialSusceptibility | ~250 | 16 | 0 | 5 | Gamma trace, u_g positivity, bubble integral, RPA susceptibility, vestigial_before_tetrad (**ALL PROVED**, Aristotle `9e2251cd`) |
| QuaternionGauge | ~200 | 10 | 0 | 5 | Unit quaternion norm, identity, SO(4) dim, plaquette bounds, heatbath detailed balance (**ALL PROVED**, Aristotle `fb657b4d`) |
| GaugeFermionBag | ~200 | 9 | 0 | 5 | Tetrad gauge covariance, metric invariance, bag weight real, SMW update, Binder limits (**ALL PROVED**, Aristotle `fb657b4d`) |
| HubbardStratonovichRHMC | ~400 | 22 | 0 | 5 | HS identity, Kramers, multi-shift CG, complex pseudofermion Pfaffian identity |
| MajoranaKramers | ~400 | 25 | 0 | 5 | Majorana Kramers degeneracy, sign-free determinant, 8×8 block structure |

**Axioms:**
- `non_abelian_center_discrete` (GaugeErasure.lean) — Encodes Lie theory: center of non-Abelian compact Lie group is discrete.
- `gs_nogo_axiom` (GoltermanShamir.lean) — Statement-level axiomatization of GS no-go theorem. Proof requires spectral theory infrastructure not yet in Mathlib (target: future wave).

---

## 3. ARISTOTLE THEOREM PROVER (254 registry entries across 32+ runs)

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
| run_20260328_051547 | 2026-03-28 | 3 | Wave 1A: kappa-scaling |
| run_20260328_132925 | 2026-03-28 | 7 | Wave 3A: LatticeHamiltonian |
| run_20260328_142342 | 2026-03-28 | 3 | Wave 3B: GoltermanShamir |
| run_20260328_151228 | 2026-03-28 | 3 | Wave 3B+: GoltermanShamir strengthening |
| run_20260328_170451 | 2026-03-29 | 4 | Wave 3C: ExteriorAlgebra finite-dim (fock_space_finite_dim + helpers) |
| run_20260329_094416 | 2026-03-29 | 11 | Wave 4A: KLinearCategory + SphericalCategory (tensor_preserves_nonzero, simple_indecomposable, golden_ratio_eq, etc.) |
| run_20260329_133200 | 2026-03-29 | 7 | Wave 4B: FusionExamples (associativity, fib_tau_squared, fib_F_involutory, fib_is_chiral) |
| run_20260329_162811 | 2026-03-29 | 3 | Wave 4C-1: VecG (day_unit_left/right, day_assoc) |
| run_20260329_173500 | 2026-03-29 | 5 | Wave 4C-2: VecG+DrinfeldDouble (simple_tensor, day_dim_multiplicative, ddMul_one_left/right, dd_abelian_simples) |
| 117a7115 | 2026-03-31 | 14 | 9C-2: SO4Weingarten (all 14 theorems) |
| 4528aa2b | 2026-03-31 | 63 | 9C-1+3: FractonFormulas (45) + WetterichNJL (18) |
| 9e2251cd | 2026-04-01 | 16 | Wave 6B: VestigialSusceptibility (all 16 theorems) |
| fb657b4d | 2026-04-02 | 19 | Wave 7A+7B: QuaternionGauge (10) + GaugeFermionBag (9) |
| cc257137 | 2026-04-02 | 2 | W7B-fix: Binder cumulant theorems |
| *manual* | 2026-04-02 | 47 | HubbardStratonovichRHMC (22) + MajoranaKramers (25) — manual proofs |

---

## 4. JUPYTER NOTEBOOKS (24 total: 12 Technical + 12 Stakeholder)

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
| Phase5a_ChiralityWall_Technical | 5 | GS 9 conditions, TPF evasion, formal verification |
| Phase5a_ChiralityWall_Stakeholder | 5 | Lattice chirality problem, what the wall means |
| Phase5b_Synthesis_Technical | 5 | κ-scaling, polariton, categorical infrastructure, Drinfeld double |
| Phase5b_Synthesis_Stakeholder | 5 | Phase 5 results for non-specialists |

**Convention:** Technical mirrors paper structure. Stakeholder teaches the physics. All import from `src/` modules (no inline formula redefinition). All figure cells tagged `# viz-ref: fig_<name>`.

---

## 5. PAPER DRAFTS (9 papers + prediction tables)

| Paper | Format | Lines | Topic |
|-------|--------|-------|-------|
| paper1_first_order | PRL | 397 | First-order SK-EFT: δ_diss = Γ_H/κ |
| paper2_second_order | PRD | 453 | Second-order + CGL + counting formula |
| paper3_gauge_erasure | PRL | 310 | Non-Abelian gauge erasure theorem |
| paper4_wkb_connection | PRD | 298 | Exact WKB connection formula |
| paper5_adw_gap | PRD | 397 | ADW mean-field gap equation |
| paper6_vestigial | PRD | ~620 | Vestigial metric phase + analytical susceptibility + RHMC production (L=4 done, L=8 in flight) |
| paper7_chirality_formal | PRD/CPC | ~330 | GS no-go formal verification + TPF evasion in Lean 4 |
| experimental_predictions | Tables | 156 | Platform spectral predictions |

**Key numerical claims (all traced to formulas.py via CHECK 14):**
- δ_diss ~ 10⁻⁵-10⁻³ (Paper 1)
- δ^(2)(ω) ∝ ω³ (Paper 2)
- U(1) only SM survivor (Paper 3)
- Noise floor = δ_diss/(1-δ_diss) (Paper 4)
- G_c = 8π²/(N_f·Λ²) (Paper 5)
- Vestigial window: G/G_c ≈ 0.8-1.0 in mean-field (Paper 6)

---

## 6. TEST FILES (29 files, 1456 tests)

| Test File | Tests | Covers |
|-----------|-------|--------|
| test_transonic_background | 12 | BEC parameters, background solver, corrections |
| test_second_order | 12 | Enumeration, coefficients, WKB |
| test_cgl_derivation | 26 | CGL FDR, kernel decomposition, boundary terms |
| test_cross_validation | 7 | Wraps validate.py 15 checks |
| test_lean_integrity | 9 | Module presence, toolchain, zero sorry |
| test_third_order | 36 | Third-order enumeration, parity structure |
| test_gauge_erasure | 25 | Erasure theorem, SM analysis |
| test_wkb_connection | 65 | Connection formula, Bogoliubov, spectrum |
| test_adw | 78 | Gap equation, NG modes, fluctuations |
| test_ginzburg_landau | 75 | GL expansion, He-3 analogy |
| test_experimental | 54 | Prediction tables, shot counts, kappa-scaling, polariton |
| test_chirality | 93 | GS 9 conditions, TPF evasion, lattice framework, no-go structure |
| test_fracton | 110 | SK-EFT, information retention |
| test_fracton_gravity | 146 | Bootstrap, DOF gap, non-Abelian |
| test_vestigial | 159 | Mean-field, MC, 3-phase structure, SU(2), TRG, 4D fermion-bag, NJL, susceptibility |
| test_backreaction | 76 | Cooling, extremality, timescales |
| test_layer1 | 84 | Categorical infrastructure, fusion rules, Drinfeld double, quantum dimensions |
| test_gauge | 146 | SO(4) gauge, quaternion algebra, fermion-bag, Majorana, RHMC infrastructure |
| test_hs_rhmc | 32 | HS+RHMC: Zolotarev, multi-shift CG, forces, heatbath, torch backend |

---

## 7. SCRIPTS

| Script | Lines | Purpose |
|--------|-------|---------|
| validate.py | 1343 | 15 cross-layer validation checks (incl. parameter_provenance) |
| review_figures.py | 1205 | Generate 64 PNGs + structural checks + manifest |
| submit_to_aristotle.py | 466 | Aristotle submission/retrieval/integration |
| run_vestigial_production.py | 709 | Multiprocessing production MC runner (fermion-bag, L=4,6,8) |
| run_rhmc_production.py | 239 | RHMC production runner (Rust backend, checkpoint/resume) |
| run_majorana_production.py | 281 | Majorana fermion-bag production runner (W7B) |
| provenance_dashboard.py | 627 | Flask+HTMX parameter provenance command center |
| view_vestigial_mc.py | 639 | MC results viewer and analysis dashboard |
| analyze_majorana_results.py | 241 | Majorana MC results analysis |
| benchmark_rust_parallel.py | 133 | Rust RHMC backend benchmarking |
| test_pseudofermion_convention.py | 262 | Empirical pseudofermion convention test (W7C-fix) |

---

## 8. CONFIGURATION FILES

| File | Purpose |
|------|---------|
| pyproject.toml | Project metadata, dependencies (numpy, scipy, plotly, pandas, sympy, kaleido, aristotlelib) |
| uv.lock | uv package manager lock file |
| .python-version | Python >=3.14 |
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
| Phase5_Roadmap.md | docs/roadmaps/ | Active (W7C RHMC, L=8 in flight) |
| Phase5a_Roadmap.md | docs/roadmaps/ | New — Onsager algebra + GT + Z₁₆ chirality wall |

### Stakeholder Documents (12 total)
| Document | Location |
|----------|----------|
| companion_guide.md | docs/stakeholder/ |
| Phase1_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase2_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase3_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase4_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase5_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |

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

### Kappa-Scaling (Phase 5)
- δ_disp(κ) = -(π/6)(ξκ/c_s)² — Lean: `kappa_scaling_dispersive_quadratic`
- δ_diss(κ) = (γ₁+γ₂)κ/c_s² — Lean: `kappa_scaling_dissipative_linear`
- κ_cross = 6(γ₁+γ₂)/(πξ²) — Lean: `crossover_balance`

### Categorical Infrastructure (Phase 5)
- Quantum dimension: d_i = tr(id_{V_i}) — Lean: `quantumDim`
- Global dimension: D² = Σ_i d_i² — Lean: `globalDimSq_pos`
- Fusion multiplicity: (i⊗j) = Σ_k N^k_{ij} · k — Lean: `totalMult_unit`
- dim D(G) = |G|² — Lean: `dd_abelian_simples`
- Z(Vec_G) ≅ Rep(D(G)) — Lean: `gauge_emergence_statement`
- Chirality limitation: c ≡ 0 (mod 8) — Lean: `chirality_limitation_vecG`

---

## SUMMARY TABLE

| Category | Count | Status |
|----------|-------|--------|
| **Python Source Modules** | 49 | Complete (Phases 1-5b) |
| **Python __init__.py** | 11 | Complete |
| **Test Files** | 31 | 1506 tests, all passing |
| **Notebooks** | 26 | Phases 1-5b (Technical + Stakeholder) |
| **Lean Modules** | 64 | All build clean |
| **Lean Theorems** | 951 (0 axioms) | Zero sorry |
| **Aristotle-proved** | 273 (270 machine + 3 manual in registry) | 33+ runs |
| **Manual proofs** | 678 | |
| **Paper Drafts** | 10 + prediction tables | Full LaTeX |
| **Pipeline Figures** | 72 | All PNGs generated |
| **Validation Checks** | 16 | All passing |
| **Scripts** | 11 | validate, review_figures, submit_to_aristotle, 3 production runners, provenance_dashboard, 4 utilities |
| **Stakeholder Docs** | 12 | Phases 1-5b |
| **Analysis Docs** | 3 | Vestigial, fracton, chirality |
| **Roadmaps** | 7 | Phases 1-5b + Phase 6 deferred |

---

**Project Status (2026-04-04):** Phase 5b COMPLETE. 951 theorems, 0 axioms (ZERO sorry), 273 Aristotle-registry entries (270 machine-proved, 3 manual), 1506 tests (all pass), 72 figures, 64 Lean modules, 49 Python modules, 10 papers, 26 notebooks. Phase 5b: SM anomaly in Z16, generation constraint, Drinfeld center (monoidal Vec_G, toric code, S3 non-abelian, CenterEquivalenceZ2, DrinfeldDoubleAlgebra, DrinfeldDoubleRing, DrinfeldEquivalence), Wang bridge (c₋=8N_f derived from fermion content). All axioms removed (Wave 6): non_abelian_center_discrete and gs_nogo_axiom proved as theorems. L=8 RHMC results pending for Paper 6.
