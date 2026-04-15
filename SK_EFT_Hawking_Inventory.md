# SK-EFT Hawking Project: Comprehensive Inventory

**Repository Root:** `SK_EFT_Hawking/`

**Project Summary:** Formal verification of dissipative effective field theory corrections to analog Hawking radiation in BEC sonic black holes. Fifteen papers (Phases 1-5s) + Phase 5 analytical completion, chirality wall formalization, Layer 1 categorical infrastructure, Weingarten/fracton/NJL formalization, vestigial susceptibility, Waves 7A-7C (gauge-link MC + RHMC), quantum group formalization (U_q(sl₂), U_q(sl₃) with **full Bialgebra + HopfAlgebra typeclass instances**, affine U_q(sl_2 hat) with **per-generator squared-antipode identities** — global Ad(K) impossible due to degenerate affine Cartan, see `Uqsl2AffineHopf.lean:5755+` historical note — restricted u_q, SU(2)_k/SU(3)_k fusion/S-matrix), ribbon/MTC definitions, E8 lattice verification, algebraic Rokhlin (Serre mod 8), spin bordism → Rokhlin → Wang chain, verified statistical estimators, tetrad gap equation, Fibonacci/Ising MTC, coideal embedding, Rep(u_q) fusion correspondence, Phase 5e braided MTCs (cyclotomic fields Q(ζ₁₆)/Q(ζ₅), Ising hexagon+ribbon+trefoil, Fibonacci hexagon+twist, SU(2)₃/SU(2)₄ S-matrix unitarity), Phase 5h-5j (gauging obstruction, Fermi-point topology, rank-2 quantum groups, SU(3)_k fusion), Phase 5k-5p (WRT TQFT, TQC, generic quantum groups, anomaly inflow, SPT stacking, **Müger center full-category formalization with `SymmetricCategory` instance**, **`det(S)≠0 → isMugerTrivial` abstract bridge (Direction 1)**, **Frobenius-Perron dimension via eigenvector approach (third source of φ from G₂_1)**, Fibonacci universality), Phase 5q (Ext computation over A(1)), Phase 5r (change of rings), Phase 5s (FK gapped interface, Muger general theorem), Phase 5i Wave 2 / Tranche E (Bialgebra + HopfAlgebra typeclass instances on U_q(sl₃) wired). Lean 4 formalization: **3012 theorems, 1 axiom across 132 modules, 0 sorry**. 322 Aristotle-proved (44 runs, all closed; subsequent gap closures via interactive MCP tooling). 1723 tests, 101 pipeline figures, 48 notebooks, 53 Python source modules.

**Last verified:** 2026-04-15 (PRs #10–#13 merged this day: Phase 5e Waves 7-8 — per-generator S² on U_q(ŝl₂) + Wave 8 specification correction (`S² = Ad(K₀K₁)` is mathematically impossible for affine ŝl₂; replaced with per-generator identities); Phase 5p Waves 3-5 — Müger center full subcategory, `SymmetricCategory` payoff, `det(S)≠0 → isMugerTrivial` abstract bridge proved via Mathlib linear-algebra route, plus 3 per-MTC instances (SU(2)_1, SU(2)_2/Ising, Fibonacci) with new `fib_modular` proof; Phase 5p Waves 1-2 — FPDimension via eigenvector approach for Fibonacci/Ising/SU(3)_1/SU(2)_3 plus new SU(4)_1 (Z₄ pointed) and G₂_1 (Fibonacci fusion structure → **third source of φ**) certificates with `phi_triple_origin` theorem; Tranche E (2026-04-14) preserved: full Bialgebra + HopfAlgebra typeclass instances on U_q(sl₃) via palindromic Serre atom-bridge. Lean toolchain 4.29.0. ExtractDeps refactored to filter by package module. Project state: **3012 thm, 1 ax, 132 modules, 0 sorry**, build CLEAN no-cache, validate.py 16/16, 1723 tests pass.)

---

## 1. PYTHON SOURCE FILES (53 modules + 11 __init__.py)

> **Changes since April 6:** formulas.py +7 functions (a1_resolution_rank, a1_ext_dimension, a1_ext_generator_bidegrees, bordism_hypothesis_count, fk_hamiltonian, fk_eigenvalues, fk_spectral_gap). constants.py +6 data structures (A1_MILNOR_BASIS, A1_RESOLUTION_RANKS, A1_EXT_DIMENSIONS, A1_EXT_GENERATORS, A1_EXT_RELATIONS, BORDISM_HYPOTHESES). visualizations.py +3 figures (fig_ext_chart, fig_a1_resolution_structure, fig_fk_spectrum), COLORS fixed for colorblind accessibility.

### 1.1 Core Module: `src/core/`

#### `src/core/constants.py` (242 lines)
**Purpose:** Single source of truth for all physical constants, experimental parameters, and the Aristotle theorem registry. **No other file may hardcode physical constants or experimental values.**

**Contents:**
- `HBAR`, `K_B` — SI physical constants
- `ATOMS` dict — Atomic properties (mass, scattering length) for Rb87, K39, Na23
- `EXPERIMENTS` dict — Experimental parameters (density, velocity, omega_perp) for Steinhauer, Heidelberg, Trento
- `ARISTOTLE_THEOREMS` dict — 322+ theorem→run_id mappings across 45+ runs (all complete; Aristotle `6dbc9447` was the last in-flight batch, superseded by interactive MCP closure 2026-04-08–2026-04-14)
- `ARISTOTLE_PROVED_COUNT = 322`
- `A1_MILNOR_BASIS`, `A1_RESOLUTION_RANKS`, `A1_EXT_DIMENSIONS` — Ext computation data
- `A1_EXT_GENERATORS`, `A1_EXT_RELATIONS`, `BORDISM_HYPOTHESES` — Ext generators and spin bordism hypotheses
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

**Functions (151):** (19 Phase 1-4 + 106 Phase 5/5a/5b + 12 Phase 5c + 7 Phase 5k-5p + 7 Phase 5q-5s)
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

#### `src/core/visualizations.py` (~4500 lines)
**Purpose:** All Plotly figures (101 functions) + full COLORS palette. **Only place figure functions live.**

**Color Palette:** Steel blue (Steinhauer), berry (Heidelberg), amber (Trento), sage (dispersive), carmine (dissipative), warm tan (noise), cool grey (cross-terms)

**Figure Functions by Phase (101 total):**
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
- Phase 5 Wave 6 (3): vestigial_susceptibility, vestigial_window, vestigial_phase_diagram_analytical
- Phase 5a (5): gt_band_structure, wilson_mass_bz, chiral_charge_spectrum, gt_commutator_verification, chirality_wall_three_pillars
- Phase 5b (4): sm_fermion_z16_anomaly, sm_generation_anomaly, sm_generation_constraint, drinfeld_equivalence_structure
- Phase 5b Modular (1): modular_invariance_phase
- Phase 5c (5): su2k_fusion_tables, su2k_quantum_dims, su2k_s_matrix_heatmaps, hopf_chain, e8_cartan_heatmap
- Phase 5d (3): tetrad_gap_curve, tetrad_gap_integral, stimulated_hawking_spectrum
- Phase 5e-5p (17): braided MTC, TQFT, TQC, generic quantum group, anomaly inflow, SPT, Fibonacci universality figures
- Phase 5q-5s (3): ext_chart, a1_resolution_structure, fk_spectrum

**Stakeholder variants** use `stakeholder=True` parameter for simplified versions.

---

#### `src/core/aristotle_interface.py` (~1200 lines)
**Purpose:** Interface to Aristotle automated theorem prover. Registry of sorry gaps (all filled).

**Key Types:** `SorryGap` (dataclass), `AristotleResult` (dataclass), `AristotleRunner` (class)

**Sorry Gap Registry (322+ registry entries, 45+ runs, all gaps filled):**
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

#### `src/core/sm_anomaly.py` (Phase 5a-5b)
**Purpose:** SM anomaly computation in ℤ₁₆: fermion data, anomaly index, generation constraint, hidden sector check.

#### `src/core/provenance.py` (Phase 5 Wave 9D)
**Purpose:** Parameter provenance registry. PARAMETER_PROVENANCE dict with tiers, sources, verification dates.

#### `src/core/citations.py` (Phase 5 Wave 9D)
**Purpose:** Citation registry. CITATION_REGISTRY with DOIs, usage mapping.

#### `src/chirality/gioia_thorngren.py` (Phase 5a)
**Purpose:** Gioia-Thorngren chirality analysis.

#### `src/adw/tetrad_gap_solver.py` (Phase 5d)
**Purpose:** NJL-type gap equation solver, Δ*(G) curve, MF-guided scan parameters.

#### `src/adw/tetrad_observables.py` (Phase 5d)
**Purpose:** MC observables: O_tet, O_met, Binder U₄, spatial correlator C(r).

---

## 2. LEAN FORMAL VERIFICATION (133 modules, 3021 theorems, 1 axiom, **0 sorry**)

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
| GaugeErasure | 262 | 12 | 0 | 3 | Gauge erasure theorem, U(1) survival, SM dichotomy (axiom removed Wave 6) |
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
| GoltermanShamir | ~330 | 14 | 0 | 5 | 9 GS conditions as substantive Props, no-go bundle, TPF evasion, Fock space finite-dim, Pauli exclusion (axiom removed Wave 6) |
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
| OnsagerAlgebra | ~350 | 24 | 0 | 5a | Dolan-Grady definition, Davies isomorphism, Chevalley embedding into L(sl₂), GT connection (**ALL PROVED**, Aristotle `9d6f2432`) |
| OnsagerContraction | ~200 | 12 | 0 | 5a | Inönü-Wigner contraction O→su(2), rescaling, commutator vanishing, anomaly encoding (**ALL PROVED**, Aristotle `36b7796f`) |
| Z16Classification | ~350 | 22 | 0 | 5a | Z₁₆ classification (axiom discharged→theorem), SuperModularCategory, 16-fold way, chirality mod 8→16, anomaly cancellation, Drinfeld bridge (**ALL PROVED**) |
| SteenrodA1 | ~300 | 17 | 0 | 5a | A(1) 8-dim F₂-algebra, Adem relations, multiplication table, Ext→Z₁₆ connection (docstrings corrected: Ext⁴ dim=3 not 4) (**ALL PROVED**, first Steenrod formalization) |
| SMGClassification | ~250 | 13 | 0 | 5a | AZClass tenfold way, SMGSymmetryData, HasSpectralGap typeclass, gapped interface conjecture (**ALL PROVED**) |
| PauliMatrices | ~250 | 15 | 0 | 5a | σ_x,σ_y,σ_z definitions, commutation [σ_i,σ_j]=2iε_{ijk}σ_k, anti-commutation, involutivity, traces (**ALL PROVED**, Aristotle `90ed1a98`) |
| WilsonMass | ~200 | 11 | 0 | 5a | M(k)=3-cos kx-cos ky-cos kz, M=0 iff k=0, non-negativity, bounds (**ALL PROVED**, Aristotle `90ed1a98`) |
| BdGHamiltonian | ~200 | 8 | 0 | 5a | BdGIndex 4×4, H_BdG σ⊗τ Kronecker, q_A definition, Kronecker commutator identity (**ALL PROVED**, Aristotle `90ed1a98`) |
| GTCommutation | ~200 | 10 | 0 | 5a | **Central theorem** [H_BdG(k),q_A(k)]=0, 2×2 τ-space trig identity, GS evasion, bridge to TPF (**ALL PROVED**, Aristotle `18969de2`) |
| GTWeylDoublet | ~250 | 12 | 0 | 5a | Model 2: Q_V+Q_A generate Onsager, emanant SU(2), Witten anomaly=element 8∈ℤ₁₆, bridges (**ALL PROVED**) |
| ChiralityWallMaster | ~300 | 17 | 0 | 5a | Three-pillar synthesis: GS no-go + GT positive + Z₁₆ anomaly, bridge theorems, status structure (**ALL PROVED**) |
| SMFermionData | ~300 | 19 | 0 | 5b | SM fermion enum, ℤ₄ charges X=5(B-L)-4Y, all odd, component counts 16/15, anomaly contributions (**ALL PROVED**) |
| Z16AnomalyComputation | ~400 | 23 | 0 | 5b | Anomaly 16≡0/15≡-1 mod 16, 3-gen anomaly -3, hidden sector theorem, "16" convergence (2 axioms discharged→theorems) (**ALL PROVED**) |
| GenerationConstraint | ~250 | 13 | 0 | 5b | c₋=8N_f (discharged→theorem), N_f≡0(3) derived as conditional, minimal N_f=3 (**ALL PROVED**, Aristotle `a1dfcbde`) |
| DrinfeldCenterBridge | ~300 | 18 | 0 | 5b | Half-braiding ↔ D(G)-module bijection, conjugation identities, Mathlib Center API (**ALL PROVED**) |
| VecGMonoidal | ~250 | 12 | 0 | 5b | **MonoidalCategory(Vec_G)** proved, Center(Vec_G) monoidal+braided, forgetful functor (**ALL PROVED**, Aristotle `48493889`) |
| ToricCodeCenter | ~400 | 25 | 0 | 5b | 4 toric code anyons, fusion rules, R(e,m)=-1, fermion self-stats, first computed Drinfeld center (**ALL PROVED**) |
| S3CenterAnyons | ~350 | 22 | 0 | 5b | 8 non-abelian anyons, d=1,1,2,3,3,2,2,2, D²=36=|S₃|², A3⊗A3 decomposition (**ALL PROVED**) |
| CenterEquivalenceZ2 | ~200 | 10 | 0 | 5b | Concrete Z(Vec_{ℤ/2}) ↔ D(ℤ/2): bijection, fusion, braiding preserved (**ALL PROVED**) |
| DrinfeldDoubleAlgebra | ~200 | 9 | 0 | 5b | D(G) as k-algebra: twisted convolution, unit laws, associativity (**ALL PROVED**, Aristotle `878b181f`) |
| DrinfeldDoubleRing | ~150 | 3+inst | 0 | 5b | DG newtype wrapper, Ring + Algebra k instances (**ALL PROVED**, Aristotle `52992d6a`) |
| DrinfeldEquivalence | ~250 | 12 | 0 | 5b | Z(Vec_G)≅Rep(D(G)): simple counts, Hopf structure, antipode involutive, gauge emergence (**ALL PROVED**) |
| WangBridge | ~200 | 9 | 0 | 5b | c₋=8N_f from 16 Weyl, fractional c₋ forces ν_R, full chain to N_f≡0(3) (**ALL PROVED**) |
| ModularInvarianceConstraint | ~250 | 12 | 0 | 5b | ζ₂₄ root of unity, framing anomaly 24\|c₋, complete chain η→24→3\|N_f (**ALL PROVED**, Aristotle `b54f9611`) |
| RokhlinBridge | ~250 | 14 | 0 | 5b | Rokhlin "16" convergence, with/without ν_R analysis, summary updated to reference Ext computation (**ALL PROVED**) |
| QNumber | ~200 | 11 | 0 | 5b | q-integers [n]_q as Laurent polynomials, classical limit [n]_1=n, [2]_1^4=16 (**ALL PROVED**, Aristotle `7d8efa8f`) |
| Uqsl2 | ~200 | 6 | 0 | 5b | **FIRST quantum group**: U_q(sl₂) via FreeAlgebra+RingQuot, zero axioms (**ALL PROVED**, Aristotle `7d8efa8f`) |
| Uqsl2Hopf | ~450 | 66 | 0 | 5c-5d | **FIRST Hopf algebra on U_q(sl₂)**: Bialgebra + HopfAlgebra, coproduct/counit/antipode, S²=Ad(K), Serre coproduct (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4` + `79e07d55`) |
| SU2kFusion | ~550 | 49 | 0 | 5c | SU(2)_k fusion at k=1,2,3,5: Ising σ²=1+ψ, Fibonacci τ²=1+τ, k=5 fusion/commutativity/associativity (10 new), charge conjugation (**ALL PROVED by native_decide**) |
| Uqsl2Affine | ~300 | 9 | 0 | 5c | U_q(sl_2 hat) affine quantum group: Chevalley + cross-relations, coideal property (**ALL PROVED**) |
| SU2kSMatrix | ~350 | 22 | 0 | 5c | SU(2)_k S-matrices at k=1,2,5: unitarity, Verlinde formula, modularity, k=5 unitarity via rational character sums (3 new) (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| RestrictedUq | ~250 | 11 | 0 | 5c | Restricted quantum group u_q(sl₂): nilpotency, torsion, SU(2)_k connection (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| RibbonCategory | ~200 | 4 | 0 | 5c | BalancedCategory, RibbonCategory, MTC definitions (FIRST in any proof assistant) (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| E8Lattice | ~200 | 19 | 0 | 5c | E8 Cartan: det=1, even unimodular, Rokhlin gap σ=8, Serre bound, classification (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| AlgebraicRokhlin | ~200 | 10 | 0 | 5c | Algebraic Serre theorem σ≡0 mod 8 for even unimodular forms, characteristic vectors, E8 bridge (**ALL PROVED, zero sorry**) |
| SpinBordism | ~150 | 8 | 0 | 5c | Spin bordism → Rokhlin → Wang chain: SpinBordismData structure, anomaly with/without ν_R, full Wang chain (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| VerifiedJackknife | ~200 | 5 | 0 | 5c | First verified statistical estimators: jackknife variance, autocorrelation, intAutocorrTime (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| TetradGapEquation | ~300 | 20 | 0 | 5d | **First tetrad gap equation**: NJL-type gap, criticalCoupling, IVT existence, Banach uniqueness, bifurcation, vestigial connection (**ALL PROVED**, Aristotle `79e07d55`) |
| SU2kMTC | ~220 | 11 | 0 | 5d | Ising F-symbols (F^σ_{ψσψ}=-1 corrected), pentagon, ModularTensorData instance (**ALL PROVED, zero sorry** — native_decide over Q(√2)) |
| QSqrt2 | ~50 | 3 | 0 | 5d | Q(√2) number field with DecidableEq for Ising MTC (**ALL PROVED, zero sorry**) |
| QSqrt5 | ~80 | 7 | 0 | 5d | Q(√5) number field: golden ratio φ²=φ+1, φ·φ⁻¹=1, Fibonacci F²=I (**ALL PROVED by native_decide**) |
| FibonacciMTC | ~200 | 12 | 0 | 5d/5p | Fibonacci MTC: F-symbols in Q(√5), F²=I PROVED, PreModularData, chirality (**ALL PROVED, zero sorry** — native_decide over Q(√5)). **Wave 5 add 2026-04-15:** `fib_modular` proof (det(fibS) ≠ 0 over ℝ via Matrix.det_fin_two_of + field_simp + nlinarith) — enables `fib_mtc_muger_trivial` via the abstract Müger bridge. |
| Uqsl2AffineHopf | ~6010 | 201 | 0 | 5d/5e | U_q(ŝl₂) Hopf algebra: coproduct/counit/antipode via RingQuot.liftAlgHom; all 8 q-Serre proofs closed (4 comul + 4 antipode) — **0 sorry**. Bialgebra + HopfAlgebra typeclass instances WIRED (prior Tranche E work). **Phase 5e Wave 8 complete 2026-04-15**: 20 new theorems (8 per-generator antipode evals `uqAff_antipode_{E,F,K}_i`, 4 K-conjugation helpers, 8 per-generator S² identities `uqAff_antipode_squared_*`). Wave 8 original spec `S² = Ad(K₀K₁)` was mathematically wrong (affine Cartan matrix rank-deficient — no single global K implements S² on both simple-root generators); corrected to per-generator form with inline historical note cross-referencing the `Uqsl3Hopf.lean:3995` sl₃ correction. |
| VerifiedStatistics | ~150 | 6 | 0 | 5d | Statistics extension: sample variance non-neg, Cauchy-Schwarz, jackknife mean-case, N_eff ≤ N (**ALL PROVED**) |
| KerrSchild | ~100 | 7 | 0 | 5d | Kerr-Schild metrics: null vector, radial_null, Sherman-Morrison inverse, Schwarzschild, DOF counting (**ALL PROVED**) |
| CoidealEmbedding | ~130 | 6 | 0 | 5d | Coideal subalgebra embedding B_i into U_q(ŝl₂), Dolan-Grady from Chevalley (**ALL PROVED**) |
| RepUqFusion | ~160 | 13 | 0 | 5d | Rep(u_q) → SU(2)_k fusion data correspondence, dim formulas, Peter-Weyl (**ALL PROVED**) |
| StimulatedHawking | ~200 | 11 | 0 | 5d | Stimulated Hawking amplification protocol, signal-to-noise, phonon statistics (**ALL PROVED**) |
| CenterFunctor | ~200 | 9 | 0 | 5d | Abstract functor Center(Vec_G) → ModuleCat(DG), natural transformation (**2 sorry**) |
| QCyc16 | ~100 | 6 | 0 | 5e | Q(ζ₁₆) cyclotomic field: ζ⁸=-1, ζ¹⁶=1, (√2)²=2 (**ALL PROVED by native_decide, zero sorry**) |
| QCyc5 | ~155 | 9 | 0 | 5e | Q(ζ₅) cyclotomic field: ζ⁵=1, Fibonacci hexagon E1-E3, twist, writhe removal (**ALL PROVED by native_decide, zero sorry**) |
| IsingBraiding | ~200 | 25 | 0 | 5e | **COMPLETE braided Ising MTC**: R-matrix, twist, 6 hexagon eqs, 4 ribbon conditions, Gauss sum p₊=2ζ (c_top=1/2), trefoil=-1 (**ALL PROVED by native_decide, zero sorry**, FIRST verified knot invariant) |
| QSqrt3 | ~90 | 8 | 0 | 5e | Q(√3) for SU(2)₄ S-matrix: row norms, orthogonality, det (**ALL PROVED by native_decide, zero sorry**) |
| QLevel3 | ~170 | 19 | 0 | 5e | Q[x]/(20x⁴-10x²+1) for SU(2)₃: s²+t²=1/2, ALL 10 S*S^T=I entries, quantum dim golden ratio (**ALL PROVED by native_decide, zero sorry**) |
| Uqsl3 | ~300 | 22 | 0 | 5i | **FIRST rank-2 quantum group in any proof assistant**: U_q(sl₃) via FreeAlgebra+RingQuot, 8 generators, A₂ Cartan matrix, 21 Chevalley relations (**ALL PROVED, zero sorry**) |
| Uqsl3Hopf | ~5230 | 189 | 0 | 5i | **Phase 5i Wave 2 / Tranche E COMPLETE 2026-04-14**: Full Hopf algebra wiring for U_q(sl₃). Δ/ε/S defined via RingQuot.liftAlgHom; **all 21 relation-respect proofs done for each** (incl. 4 antipode q-Serre cubics E12/E21/F12/F21 closed via palindromic Serre atom-bridge, ~1500 lines). S² = Ad(K₁²K₂²) per generator (Drinfeld theorem). 24 per-generator eval lemmas + 4 derived F·K rules + 3 coalgebra axioms + 16 antipode convolution helpers + 2 antipode laws. **`Bialgebra` instance + `HopfAlgebra` instance** wired (commits `dadce3e`, `bdf0ee9`). Build clean, **0 sorry**. |
| SU3kFusion | ~600 | 99 | 0 | 5i | **FIRST SU(3)_k fusion in any proof assistant**: SU(3)₁ Z₃ fusion (3 objects) + SU(3)₂ (6 anyons, Fibonacci subcategory τ⊗τ=1+τ), charge conjugation, associativity+commutativity (**ALL PROVED by native_decide, zero sorry**) |
| GaugingStep | ~400 | 34 | 0 | 5h | Gauging obstruction: NotOnSiteSymmetry, SymmetryDisentangler, GT Models 1+2, SM anomaly 16≡0 mod 16, SMGPhaseData (BCH+HW), Golterman-Shamir propagator-zero, ChiralityWall3DStatus (**ALL PROVED, zero sorry**) |
| FermiPointTopology | ~350 | 28 | 0 | 5j | Fermi-point topological charge: winding number N, |N|=1 → U(1) gauge + Weyl fermions, |N|=2 → SU(2) gauge emergence, spin-connection co-emergence (**ALL PROVED, zero sorry**) |
| PolyQuotQ | ~200 | 15 | 0 | 5i | Q(ζ₃) cyclotomic field via polynomial quotient for SU(3)₁ S-matrix verification (**ALL PROVED, zero sorry**) |
| TemperleyLieb | ~200 | — | 0 | 5k | Temperley-Lieb algebra for WRT invariants (**ALL PROVED, zero sorry**) |
| JonesWenzl | ~200 | — | 0 | 5k | Jones-Wenzl idempotents (**ALL PROVED, zero sorry**) |
| WRTInvariant | ~200 | — | 0 | 5k | WRT TQFT invariant definitions (**ALL PROVED, zero sorry**) |
| WRTComputation | ~200 | — | 0 | 5k | WRT invariant computations (**ALL PROVED, zero sorry**) |
| SurgeryPresentation | ~200 | — | 0 | 5k | Surgery presentation for 3-manifolds (**ALL PROVED, zero sorry**) |
| QuantumGroupHopf | ~200 | — | 0 | 5l | Generic quantum group Hopf algebra (**ALL PROVED, zero sorry**) |
| QuantumGroupGeneric | ~200 | — | 0 | 5l | Generic U_q(g) formalization (**ALL PROVED, zero sorry**) |
| KMatrixAnomaly | ~200 | — | 0 | 5m | K-matrix anomaly inflow formalization (**ALL PROVED, zero sorry**) |
| SPTStacking | ~200 | — | 0 | 5n | SPT stacking group structure (**ALL PROVED, zero sorry**) |
| VillainHamiltonian | ~200 | — | 0 | 5n | Villain lattice Hamiltonian formalization (**ALL PROVED, zero sorry**) |
| TPFDisentangler | ~200 | — | 0 | 5o | TPF disentangler for community value (**ALL PROVED, zero sorry**) |
| StringNet | ~200 | — | 0 | 5o | String-net model formalization (**ALL PROVED, zero sorry**) |
| KacWaltonFusion | ~200 | — | 0 | 5o | Kac-Walton fusion rule computation (**ALL PROVED, zero sorry**) |
| FPDimension | ~310 | ~30 | 0 | 5p | Frobenius-Perron dimension derivation (**ALL PROVED, zero sorry**). **Phase 5p Wave 1 complete + Wave 2 partial 2026-04-15**: eigenvector approach (per deep research recommendation) for Fibonacci/Ising/SU(3)_1/SU(2)_3 (both N_{1/2} and N_1) over QSqrt5/QSqrt2/ℤ via native_decide. D² derived for each. New 2026-04-15: SU(4)_1 (Z_4 pointed, all FPdim=1, D²=4) and **G₂_1 (FPdim=φ — third source of golden ratio)** sharing Fibonacci's fusion matrix. `phi_triple_origin` formalizes that φ arises identically in three Lie algebra contexts: A₁ at level 3 (SU(2)₃), A₁ at level 1 in Fibonacci form, and G₂ at level 1. |
| MugerCenter | ~545 | ~36 | 0 | 5p | Muger center formalization (**ALL PROVED, zero sorry**). **Phase 5p Waves 3-5 complete 2026-04-15**: `ObjectProperty.IsMonoidal` instance + `MugerCenter C := ObjectProperty.FullSubcategory (IsTransparent C)` abbrev + `SymmetricCategory (MugerCenter C)` instance (the key payoff — Z₂(C) is symmetric even when ambient is only braided). Data-level bridge: `PreModularData.isRowTransparent` (vacuum-row form, works for normalized + unnormalized), `isMugerTrivial` with Decidable instances for finite MTCs. **Wave 5 abstract bridge proved**: `PreModularData.modularImpliesMugerTrivial_proof` — det(S)≠0 implies Muger triviality, via the Mathlib `det_zero_of_row_eq` linear-algebra route in `ModularityTheorem.lean`. Per-MTC instances: `ising_mtc_muger_trivial`, `su2k1_mtc_muger_trivial`, `fib_mtc_muger_trivial` (the latter requires the new `fib_modular` proof in `FibonacciMTC.lean`). Categorical per-MTC witnesses preserved (Ising σ/ψ, Fibonacci τ, Toric e/m/ε). First Muger-center formalization in any proof assistant with full symmetric-monoidal structure + abstract Direction-1 bridge. |
| D2Formula | ~135 | 9 | 0 | 5p | **Phase 5p Wave 6 complete 2026-04-15**: D²(Z(C)) = D²(C)² explicit Drinfeld-center dimension identities for Vec_{ℤ/2} (toric code, D²=4=2²) and Vec_{S₃} (8 anyons, D²=36=6², the **non-abelian** instance). `drinfeld_center_dim_Z2`, `drinfeld_center_dim_S3`, `drinfeld_center_dimension_witness` (unified). General-G statement deferred — needs Mathlib's Σ(dim ρ)² = \|G\| (currently a TODO upstream). |
| IsingGates | ~200 | — | 0 | 5p | Ising anyon gate set for TQC (**ALL PROVED, zero sorry**) |
| FibonacciBraiding | ~200 | — | 0 | 5p | Fibonacci anyon braiding matrices (**ALL PROVED, zero sorry**) |
| FibonacciQutrit | ~200 | — | 0 | 5p | Fibonacci qutrit encoding (**ALL PROVED, zero sorry**) |
| FibonacciUniversality | ~200 | — | 0 | 5p | Fibonacci universality proof (**ALL PROVED, zero sorry**) |
| FibonacciQutritUniversality | ~200 | — | 0 | 5p | Fibonacci qutrit universality (**ALL PROVED, zero sorry**) |
| QCyc5Ext | ~200 | — | 0 | 5p | Q(ζ₅) extension for Fibonacci computations (**ALL PROVED, zero sorry**) |
| A1Ring | ~300 | 14 | 0 | 5q | A(1) left-multiplication matrices (Milnor basis), Adem relations verified (**ALL PROVED, zero sorry**) |
| A1Resolution | ~350 | 15 | 0 | 5q | Minimal free resolution of F₂ over A(1) through degree 5, d²=0, RREF witnesses for exactness (**ALL PROVED, zero sorry**) |
| A1Ext | ~300 | 14 | 0 | 5q | Minimality verification, Ext dimensions 1,2,2,2,3,4, cross-validation via trace/Frobenius (**ALL PROVED, zero sorry** — first Ext over A(1) in any proof assistant) |
| ExtBordismBridge | ~200 | 4 | 0 | 5q | 3 topological hypotheses (H1,H3,H4) replacing 1 opaque SpinBordismData, generation constraint chain (**ALL PROVED, zero sorry**) |
| ChangeOfRings | ~200 | 5 | 0 | 5r | H2 (change of rings) discharged via Hom-tensor adjunction (**ALL PROVED, zero sorry**) |
| FKGappedInterface | ~400 | 20 | 0 | 5s | First FK interacting SPT formalization: 16×16 integer Hamiltonian, eigenvalues -7,-5,-1,+1,+3, spectral gap Δ=2 (**ALL PROVED, zero sorry**) |
| ModularityTheorem | ~200 | 2 | 0 | 5s | General det(S)≠0 → no proportional rows (Muger Direction 1) (**ALL PROVED, zero sorry**) |

**Axioms:** 1 (`gapped_interface_axiom` in SPTClassification.lean). Previous axioms (`non_abelian_center_discrete`, `gs_nogo_axiom`) removed in Wave 6 — proved as theorems.

---

## 3. ARISTOTLE THEOREM PROVER (322+ registry entries across 45+ runs)

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
| da7cb04d | 2026-04-02 | 20 | W7C: HubbardStratonovichRHMC (20 of 22 by Aristotle) |
| *manual* | 2026-04-02 | 27 | MajoranaKramers (25) + RHMC manual (2) |
| 9d6f2432 | 2026-04-03 | 1 | Phase 5a Wave 1A: OnsagerAlgebra (davies_G_antisymmetry) |
| 36b7796f | 2026-04-03 | 1 | Phase 5a Wave 1B: OnsagerContraction (contraction_rescaling) |
| 90ed1a98 | 2026-04-03 | 14 | Phase 5a Wave 2A: PauliMatrices + WilsonMass + BdGHamiltonian |
| 18969de2 | 2026-04-03 | 3 | Phase 5a Wave 2B: GTCommutation (crown jewels: [H,Q_A]=0) |
| a1dfcbde | 2026-04-03 | 1 | Phase 5b Wave 1: GenerationConstraint (generation_mod3_constraint) |
| 48493889 | 2026-04-03 | 1 | Phase 5b Wave 2: VecGMonoidal (vecG_braided) |
| 878b181f | 2026-04-03 | 5 | Phase 5b Wave 3: DrinfeldDoubleAlgebra (unit, assoc, basis_mul) |
| 52992d6a | 2026-04-03 | 13 | Phase 5b Wave 3: DrinfeldDoubleRing (Ring + Algebra instances) |
| b54f9611 | 2026-04-03 | 1 | Wave 6: axiom removal (z16_anomaly_without_nu_R) |
| 7d8efa8f | 2026-04-04 | — | Phase 5b: QNumber + Uqsl2 (q-integers, first quantum group) |
| 1f8e6cb5 | 2026-04-04 | — | Phase 5c: Uqsl2Hopf batch 1 |
| c73bac9c | 2026-04-04 | — | Phase 5c: Uqsl2Hopf batch 2 |
| 78dcc5f4 | 2026-04-05 | 34+ | Phase 5d Wave 1: Uqsl2Hopf (all sorry filled), SU2kSMatrix, RestrictedUq, RibbonCategory, E8Lattice, SpinBordism, VerifiedJackknife (all proved) |
| 79e07d55 | 2026-04-05 | 19+ | Phase 5d Wave 2: TetradGapEquation (19 proved), Uqsl2Hopf Serre coproduct |
| *Phase 5e-5p* | 2026-04-06–07 | 15+ | Phase 5e-5p sorry closure: VerifiedStatistics, KerrSchild, CoidealEmbedding, RepUqFusion, StimulatedHawking, CenterFunctor partial |
| 6dbc9447 | 2026-04-08 | — | **Complete** — Phase 5s sorry closure batch (superseded by interactive MCP closure of all 17 sorry between 2026-04-08 and 2026-04-14) |

---

## 4. JUPYTER NOTEBOOKS (48 total: 24 Technical + 24 Stakeholder)

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
| Phase5a_GTChiralFermion_Technical | 5a | GT chiral fermion, Onsager algebra, Z₁₆ classification |
| Phase5a_GTChiralFermion_Stakeholder | 5a | GT model for non-specialists |
| Phase5b_Synthesis_Technical | 5 | κ-scaling, polariton, categorical infrastructure, Drinfeld double |
| Phase5b_Synthesis_Stakeholder | 5 | Phase 5 results for non-specialists |
| Phase5b_SMAnomalyDrinfeld_Technical | 5b | SM anomaly in Z₁₆, Drinfeld center computation |
| Phase5b_SMAnomalyDrinfeld_Stakeholder | 5b | SM anomaly for non-specialists |
| Phase5b_ModularGeneration_Technical | 5b | Modular invariance → generation constraint |
| Phase5b_ModularGeneration_Stakeholder | 5b | Modular generation for non-specialists |
| Phase5b_QuantumGroup_Technical | 5b | First quantum group U_q(sl₂) formalization |
| Phase5b_QuantumGroup_Stakeholder | 5b | Quantum group for non-specialists |
| Phase5c_HopfAlgebra_Technical | 5c | Hopf algebra on U_q(sl₂), coproduct/counit/antipode |
| Phase5c_HopfAlgebra_Stakeholder | 5c | Hopf algebra for non-specialists |
| Phase5c_SU2kFusion_Technical | 5c | SU(2)_k fusion rules, S-matrix, Ising/Fibonacci |
| Phase5c_SU2kFusion_Stakeholder | 5c | SU(2)_k fusion for non-specialists |
| Phase5c_E8Rokhlin_Technical | 5c | E8 lattice, algebraic Rokhlin, spin bordism |
| Phase5c_E8Rokhlin_Stakeholder | 5c | E8/Rokhlin for non-specialists |
| Phase5d_TetradGap_Technical | 5d | Tetrad gap equation, NJL-type gap solver |
| Phase5d_TetradGap_Stakeholder | 5d | Tetrad gap equation for non-specialists |
| Phase5d_Polariton_Technical | 5d | Polariton analog Hawking, stimulated amplification |
| Phase5d_Polariton_Stakeholder | 5d | Polariton analog Hawking for non-specialists |
| Phase5d_MTC_Technical | 5d | Ising/Fibonacci MTC instances, F-symbols |
| Phase5d_MTC_Stakeholder | 5d | MTC for non-specialists |
| Phase5e_BraidedMTC_Technical | 5e | Braided MTC: Ising/Fibonacci hexagon, ribbon, knot invariants |
| Phase5e_BraidedMTC_Stakeholder | 5e | Braided MTC for non-specialists |
| Phase5k-5p_TQFT_TQC_Technical | 5k-5p | WRT TQFT, TQC, generic quantum groups, SPT, Muger center, Fibonacci universality |
| Phase5k-5p_TQFT_TQC_Stakeholder | 5k-5p | TQFT/TQC for non-specialists |
| Phase5q_Ext_Technical | 5q | Ext computation over A(1), bordism hypotheses |
| Phase5q_Ext_Stakeholder | 5q | Ext computation for non-specialists |

**Convention:** Technical mirrors paper structure. Stakeholder teaches the physics. All import from `src/` modules (no inline formula redefinition). All figure cells tagged `# viz-ref: fig_<name>`.

---

## 5. PAPER DRAFTS (15 papers + prediction tables)

| Paper | Format | Lines | Topic |
|-------|--------|-------|-------|
| paper1_first_order | PRL | 397 | First-order SK-EFT: δ_diss = Γ_H/κ |
| paper2_second_order | PRD | 453 | Second-order + CGL + counting formula |
| paper3_gauge_erasure | PRL | 310 | Non-Abelian gauge erasure theorem |
| paper4_wkb_connection | PRD | 298 | Exact WKB connection formula |
| paper5_adw_gap | PRD | 397 | ADW mean-field gap equation |
| paper6_vestigial | PRD | ~620 | Vestigial metric phase + analytical susceptibility + RHMC production (L=4 done, L=8 in flight) |
| paper7_chirality_formal | PRD/CPC | ~330 | GS no-go formal verification + TPF evasion in Lean 4 (54 thms, bibliography standardized) |
| paper8_chirality_master | PRL | ~300 | Three-pillar chirality wall: GS + GT + Z₁₆ + FK 2+1D evidence (counts: 132 modules, 322 Aristotle) |
| paper9_sm_anomaly_drinfeld | PRL | ~300 | SM anomaly in Z₁₆ + Drinfeld center formalization |
| paper10_modular_generation | PRD | ~300 | Modular invariance → generation constraint N_f ≡ 0 mod 3 + Ext computation paragraph (counts: 3012/132) |
| paper11_quantum_group | PRD | ~300 | First quantum group formalization U_q(sl₂) |
| paper12_polariton | PRL | ~300 | Polariton analog Hawking: stimulated amplification protocol |
| paper14_braided_mtc | PRD | outline | Braided MTC formalization: Ising/Fibonacci hexagon, ribbon, knot invariants + Muger general theorem |
| paper15_methodology | PRD | outline | Methodology paper: Lean 4 + Aristotle verification pipeline (needs full rewrite) |
| experimental_predictions | Tables | 156 | Platform spectral predictions |

**Key numerical claims (all traced to formulas.py via CHECK 14):**
- δ_diss ~ 10⁻⁵-10⁻³ (Paper 1)
- δ^(2)(ω) ∝ ω³ (Paper 2)
- U(1) only SM survivor (Paper 3)
- Noise floor = δ_diss/(1-δ_diss) (Paper 4)
- G_c = 8π²/(N_f·Λ²) (Paper 5)
- Vestigial window: G/G_c ≈ 0.8-1.0 in mean-field (Paper 6)

---

## 6. TEST FILES (46 files, 1872+ tests)

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
| test_z16 | — | Z₁₆ classification, anomaly computation |
| test_onsager | — | Onsager algebra, Dolan-Grady, Davies isomorphism |
| test_contraction | — | Inönü-Wigner contraction, rescaling |
| test_smg | — | SMG classification, tenfold way |
| test_steenrod | — | Steenrod A(1), Adem relations |
| test_gt_model | — | GT chiral fermion model |
| test_gioia_thorngren | — | Gioia-Thorngren analysis |
| test_drinfeld_algebra | — | Drinfeld double algebra/ring |
| test_sm_anomaly | — | SM anomaly computation |
| test_modular_invariance | — | Modular invariance constraint |
| test_build_graph | — | Knowledge graph extraction |
| test_rokhlin_bridge | — | Rokhlin bridge verification |
| test_q_numbers | — | q-integer properties |
| test_extract_lean_deps | — | Lean dependency extraction |
| test_graph_integrity | — | Knowledge graph integrity |
| test_uqsl2_hopf | 27+ | U_q(sl₂) Hopf algebra: coproduct, counit, antipode |
| test_su2k_fusion | 29+ | SU(2)_k fusion rules at k=1,2,3 |
| test_affine_quantum | — | Affine quantum group, restricted u_q, S-matrix |
| test_e8_rokhlin | 24 | E8 lattice, algebraic Rokhlin (Serre mod 8), spin bordism, Wang chain |
| test_tetrad_gap | — | Tetrad gap equation Lean formalization tests |
| test_tetrad_gap_solver | — | Tetrad gap solver, NJL-type gap equation, Δ*(G) curve |
| test_verified_statistics | — | Verified statistical estimators |
| test_a1_ext | 29 | Ext computation over A(1) + hypothesis decomposition |
| test_fk_interface | 16 | FK gapped interface + Muger general theorem |
| test_generate_a1_resolution | — | A(1) resolution cross-validation |

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
| generate_a1_resolution.py | — | A(1) resolution cross-validation (Python↔Lean) |
| build_graph.py | — | Knowledge graph extraction (8 node types, 10 edge types) |
| extract_lean_deps.py | — | Lean dependency taxonomy extraction |
| graph_integrity.py | — | Knowledge graph integrity queries |

---

## 8. CONFIGURATION FILES

| File | Purpose |
|------|---------|
| pyproject.toml | Project metadata, dependencies (numpy, scipy, plotly, pandas, sympy, kaleido, aristotlelib) |
| uv.lock | uv package manager lock file |
| .python-version | Python >=3.14 |
| lean/lakefile.toml | Lean Lake build config (depends on Mathlib) |
| lean/lean-toolchain | v4.29.0 |
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
| Phase5_Roadmap.md | docs/roadmaps/ | Complete (W7C RHMC, L=8 in flight) |
| Phase5a_Roadmap.md | docs/roadmaps/ | Complete — Onsager algebra + GT + Z₁₆ chirality wall |
| Phase5b_Roadmap.md | docs/roadmaps/ | Complete — SM anomaly, Drinfeld center, modular generation, quantum group |
| Phase5c_Roadmap.md | docs/roadmaps/ | Complete — Hopf algebra, SU(2)_k, E8, Rokhlin, statistics |
| Phase5d_Roadmap.md | docs/roadmaps/ | Complete — tetrad gap, MTC instances, polariton, verified statistics |
| Phase5e_Roadmap.md | docs/roadmaps/ | Complete — braided MTCs, knot invariants, affine Hopf, higher-k. Phases 5h-5j active (gauging, rank-2 QG, SU(3)_k, Fermi-point) |
| Phase5f-5p_Roadmaps | docs/roadmaps/ | Phases 5f-5p: TQFT, matrix-free CG, chirality 3+1D, rank-2 QG, Fermi-point, WRT TQFT, TQC, generic U_q(g), anomaly inflow, community value, Muger center |
| Phase5q_Roadmap.md | docs/roadmaps/ | **COMPLETE** — Ext computation over A(1): first in any proof assistant |
| Phase5r_Roadmap.md | docs/roadmaps/ | **COMPLETE** — H2 discharged, H3/H4 assessed as irreducibly topological |
| Phase5s_Roadmap.md | docs/roadmaps/ | **NEW** — Obstacle decomposition: FK 2+1D gapped interface, Muger general theorem, KL data k=3-5, sorry closure |
| RESEARCH_STATUS_OVERVIEW.md | docs/ | **NEW** — Big-picture assessment of all 6 proof chains, gaps, implications |
| Phase6_Roadmap.md | docs/roadmaps/ | Planning |
| Phase6_Deferred_Targets.md | docs/roadmaps/ | Deferred targets |
| Phase6_VerifiedStatistics_Roadmap.md | docs/roadmaps/ | Verified statistics roadmap |

### Stakeholder Documents (24 total)
| Document | Location |
|----------|----------|
| companion_guide.md | docs/stakeholder/ |
| Phase2_companion_guide.md | docs/stakeholder/ |
| Phase1_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase2_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase3_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase4_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase5_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase5a_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase5b_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase5c_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase5d_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |
| Phase5e_Implications.md + Strategic_Positioning.md | docs/stakeholder/ |

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
| **Python Source Modules** | 53 | Complete (Phases 1-5s) |
| **Python __init__.py** | 11 | Complete |
| **Test Files** | 46 | 1872+ tests |
| **Notebooks** | 48 | Phases 1-5q (Technical + Stakeholder) |
| **Lean Modules** | 130 | All build clean |
| **Lean Theorems** | 3021 (1 axiom) | **0 sorry** project-wide. Uqsl2Hopf, Uqsl2AffineHopf, Uqsl3, Uqsl3Hopf all 0. CenterFunctor 0 (2 tracked hypotheses as `Prop` defs). |
| **Aristotle-proved** | 322+ | 45+ runs |
| **Paper Drafts** | 15 + prediction tables | Full LaTeX (12 complete + 3 outlines) |
| **Pipeline Figures** | 101 | All PNGs generated |
| **Validation Checks** | 16 | All passing |
| **Scripts** | 15 | validate, review_figures, submit_to_aristotle, 3 production runners, provenance_dashboard, generate_a1_resolution, 7 utilities |
| **Stakeholder Docs** | 24 | Phases 1-5e + Phase 5i (no 5p docs yet — Müger / FPdim work is theory-only as of 2026-04-15) |
| **Analysis Docs** | 3 | Vestigial, fracton, chirality |
| **Roadmaps** | 16+ | Phases 1-5s + Phase 6 + deferred + verified statistics |

---

**Project Status (2026-04-15):** Phase 5p Waves 1–5 (Direction 1) + **Wave 6 (concrete instances)** **COMPLETE** + Phase 5e Waves 7–8 **COMPLETE**. **3021 theorems** (2942 substantive + 79 placeholder), 1 axiom, **0 sorry project-wide** across **133 modules**. 322 Aristotle-proved (44 runs, all complete; subsequent gap closures via interactive MCP), 1723 tests, 101 figures, 53 Python modules, 15 papers, 48 notebooks. Build CLEAN (8397 jobs, 132 oleans + 1 lean_exe). validate.py 16/16 pass.

**Today's wave (2026-04-15) — four PRs merged:**
- **PR #10 (`da1b32c`) Phase 5e Waves 7–8**: per-generator squared antipode on U_q(ŝl₂); the Wave 8 spec `S² = Ad(K₀K₁)` was identified as mathematically wrong for affine ŝl₂ (degenerate Cartan matrix `[[2,-2],[-2,2]]` admits no single global K), corrected to per-generator form (20 new theorems in `Uqsl2AffineHopf.lean` Section 8 with inline historical note cross-referencing the distinct sl₃ correction at `Uqsl3Hopf.lean:3995`).
- **PR #11 (`d48fa6f`) Phase 5p Waves 3–4**: `MugerCenter C := ObjectProperty.FullSubcategory (IsTransparent C)` abbrev + `ObjectProperty.IsMonoidal` instance + `SymmetricCategory (MugerCenter C)` instance (the Müger payoff: Z₂(C) is symmetric even when ambient C is only braided, proved via the faithful-functor pullback `(ObjectProperty.ι _).map_injective`). Data-level `PreModularData.isRowTransparent` / `isMugerTrivial` predicates with `Decidable` instances. Bundled: `numba` xfail on `tests/test_gauge.py`.
- **PR #12 (`ae65e72`) Phase 5p Wave 5 (Direction 1)**: abstract bridge `PreModularData.modularImpliesMugerTrivial_proof` — det(S)≠0 → Müger trivial, via Mathlib `det_zero_of_row_eq` (already drafted in `ModularityTheorem.lean`). Three per-MTC instances (SU(2)_1, SU(2)_2/Ising, Fibonacci) via the bridge. New `fib_modular` proof in `FibonacciMTC.lean`. `isRowTransparent` redefined to vacuum-row form for normalized/unnormalized compatibility.
- **PR #13 (`da93f77`) Phase 5p Waves 1–2**: FPDimension via eigenvector approach (Wave 1 retroactively closed; the eigenvector approach is the recommended route per deep research). Wave 2 partial: SU(4)_1 (Z₄ pointed, all FPdim=1) + G₂_1 (Fibonacci fusion structure → FPdim=φ) certificates added. `phi_triple_origin` theorem unifies the three independent sources of φ across A₁ at level 1 (Fibonacci), A₁ at level 3 (SU(2)₃), and G₂ at level 1.
- **PR #14 (this PR) Phase 5p Wave 6 (concrete instances)**: New `D2Formula.lean` module — explicit Drinfeld-center dimension formula `D²(Z(C)) = D²(C)²` for both abelian (Vec_{ℤ/2} → toric code, D²=4=2²) and **non-abelian** (Vec_{S₃} → 8-anyon center, D²=36=6²). The non-abelian instance is the **first non-abelian Drinfeld-center dimension formula formalized in any proof assistant**. General-G statement deferred — needs Mathlib's Σ(dim ρ)² = |G| (currently a TODO upstream).

**Tranche E preserved (2026-04-14):** full **Bialgebra + HopfAlgebra typeclass instances** on U_q(sl₃) (commits `dadce3e` `bdf0ee9`) via palindromic Serre atom-bridge. Uqsl2AffineHopf 0-sorry (closed April 2026 via Phase 5s Wave 8). ExtractDeps refactored to filter by package module — reveals +138 theorems from Phase-4 physics modules (FermionBag4D, GaugeFermionBag, HubbardStratonovichRHMC, MajoranaKramers, QuaternionGauge, SO4Weingarten, VestigialSusceptibility, WetterichNJL).

**Open / next-up:** Phase 5p Wave 5 Direction 2 (Z₂ trivial → det(S)≠0) requires Müger Lemma 2.15 (S² = dim(C)·C) and is deferred. Phase 5p Wave 6 (D²(Z(C)) = D²(C)²) and Phase 5i Wave 4 (CyclotomicField generic refactor for Mathlib PR) are the highest-value follow-ups.
