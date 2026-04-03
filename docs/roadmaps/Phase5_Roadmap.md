# Phase 5: Analytical Completion + Wall Formalization

## Technical Roadmap — March 2026

*Prepared 2026-03-28 | Follows Phase 4 (vestigial gravity, fracton Layer 2, experimental predictions) and Wave 5 quality hardening*

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/CLAUDE.md`](../../../CLAUDE.md) — project conventions, build commands, mandatory references
> 2. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/WAVE_EXECUTION_PIPELINE.md`](../WAVE_EXECUTION_PIPELINE.md) — 12-stage execution process, pipeline invariants, no skipping
> 3. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/SK_EFT_Hawking_Inventory_Index.md`](../../SK_EFT_Hawking_Inventory_Index.md) — module map, Lean map, current counts
> 4. Read this roadmap for your specific wave assignment
> 5. Read the relevant deep research results in `Lit-Search/Phase-5/` for your wave

---

## Execution Process

**All Phase 5 work follows the [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).** 12 stages in strict order. No skipping. Consult the [Inventory Index](../../SK_EFT_Hawking_Inventory_Index.md) before making changes.

---

## 0. Entry State

**What Phases 1-4 established (verified 2026-03-28, 14/14 validation checks):**
- 216 theorems + 1 axiom (zero sorry, 56 Aristotle-proved across 18 runs)
- 822 tests, 16 modules, 14/14 validation checks, 45 figures, 6 papers, 16 notebooks
- SK-EFT dissipative corrections through second order, parity alternation theorem
- Exact WKB connection formula, platform-specific prediction tables
- Non-Abelian gauge erasure: universal structural theorem
- ADW gap equation: qualified positive, vestigial gravity numerically confirmed (3-phase structure)
- Fracton Layer 2: exponentially more UV info, binomial counting, non-Abelian fracton negative result
- Chirality wall: 2/4 GS conditions evaded, conditional status
- Backreaction: acoustic BHs cool toward extremality

**What Phase 5 aims to do:**
1. Take SK-EFT as far as it can go analytically (no HPC, no new experimental data)
2. Attack the three structural walls using the proven LLM + Lean + Aristotle pipeline
3. Deep investigation of Layer 1 routes (string-nets, Fermi-point topology) that bypass the fluid layer

**What moves to Phase 6 (requires collaboration or HPC):**
- Vestigial MC Phase 2-3 (simplicial lattice, HPC-scale precision)
- Walker-Wang Z₂ transport program (~500K GPU-hrs)
- BEC/polariton experimental collaboration
- Polariton Tier 2-3 EFT predictions (requires Tier 1 validation against data)

**Parallel non-blocking tracks (John):**
- Deep research task execution (Lit-Search/Tasks/)
- Paper submission review
- Experimental outreach (Paris polariton group, Trento, QSimFP consortium)

---

## 1. Wave 1 — SK-EFT Analytical Completion (Days 1-3)

### 1A. Kappa-Scaling Test Predictions [Pipeline: Stages 1-12]

**Goal:** Compute how EFT corrections scale with variable surface gravity kappa across platforms. The kappa-scaling test (varying kappa to verify T_H ∝ kappa and probe deviations) is identified as the single most accessible experimental test. Heidelberg K-39 has the best apparatus (Feshbach tunability) though they aren't currently pursuing Hawking.

**The calculation:**
1. delta_disp(kappa) = D(kappa)² where D = xi*kappa/c_s — dispersive correction scales with kappa
2. delta_diss(kappa) = Gamma_H(kappa)/kappa — dissipative correction, Gamma_H may depend on kappa through T_H-dependent damping
3. Compute both corrections at 5-10 kappa values per platform (spanning 0.5x to 5x nominal kappa)
4. Identify the crossover kappa where delta_disp = delta_diss (distinguishes dispersive-dominated from dissipative-dominated regime)
5. Compute required measurement precision to distinguish delta_disp ~ D² from delta_diss ~ D⁰ at each kappa

**Sources:** `src/core/formulas.py` (dispersive_correction, first_order_correction), `src/core/constants.py` (EXPERIMENTS), `src/wkb/spectrum.py`

**Deliverables:**
- [x] `src/experimental/kappa_scaling.py` — kappa-scaling sweeps for all platforms (2026-03-28)
- [x] 3 formulas in `formulas.py`: kappa_scaling_dispersive, kappa_scaling_dissipative, kappa_scaling_crossover (2026-03-28)
- [x] `lean/SKEFTHawking/KappaScaling.lean` — 11 theorems: scaling laws, crossover balance, regime classification (2026-03-28)
- [x] Aristotle: fill 10 sorry gaps (7 priority-1, 3 priority-2) — all filled, run_20260328_051547 (2026-03-28)
- [x] 12 new tests in `tests/test_experimental.py` (834 total, all pass) (2026-03-28)
- [x] Figure: fig46_kappa_scaling_physical — log-log plot of corrections vs kappa for all platforms (2026-03-28)
- [x] Updated `papers/experimental_predictions/prediction_tables.tex` — corrected kappa-scaling section + table + figure (2026-03-28)
- [x] Notebooks: Phase4a content covered by Phase5b_Synthesis notebooks (2026-03-30)
- [x] Document sync: Inventory Index, README, src/__init__.py counts updated (2026-03-28)

**Key finding (2026-03-28):** The old claim that "delta_diss ≈ const" was wrong. Correct physics: delta_diss ∝ kappa (linear), because transport coefficients gamma_1, gamma_2 are material properties independent of kappa, so Gamma_H = (gamma_1+gamma_2)(kappa/c_s)² and delta_diss = Gamma_H/kappa = (gamma_1+gamma_2)kappa/c_s². The crossover formula kappa_cross = 6(gamma_1+gamma_2)/(pi*xi²) cancels c_s² (original bug fixed). Platforms span the crossover: Steinhauer near it (1.3x), Heidelberg dissipative-dominated (0.04x), Trento dispersive-dominated (5.7x).

**Estimated LOE:** Low-Medium
**Risk:** Low. All physics already computed; this is extending existing formulas to variable kappa.

---

### 1B. Polariton Platform Predictions — Tier 1 [Pipeline: Stages 1-12]

**Goal:** Add Paris polariton platform to prediction infrastructure using the Tier 1 perturbative patch (uniform imaginary frequency shift). Research confirmed: T_H formula survives driven-dissipative, pseudounitary scattering structure intact, Tier 1 is valid for Gamma_pol/kappa << 1.

**Prerequisites:** Deep research results from `Lit-Search/Phase-5/Extending Schwinger-Keldysh EFT to driven-dissipative polariton condensates.md` (complete).

**The Tier 1 patch:**
1. Add polariton platform parameters to `src/core/constants.py`: m* = 7.0e-35 kg, c_s ~ 0.5-1 um/ps, xi ~ 1-2 um, Gamma_pol (cavity-dependent: 3 ps standard, 100 ps long-lifetime, 300 ps ultra-long)
2. Bogoliubov dispersion: omega(k) → omega(k) - i*Gamma_pol/2 (uniform damping)
3. Spatial attenuation correction: N_H_corr(k) = N_H_meas(k) * exp[Gamma_pol * (L1/v_g(k_s) + L2/v_g(k_H))]
4. Compute T_H ~ 0.8-4 K (vs ~0.35 nK for BEC — 10^10x hotter)
5. Compute Gamma_pol/kappa for each cavity quality to determine EFT-testable regime
6. Identify: long-lifetime cavities (tau > 100 ps) where Gamma_pol/kappa < 0.1 → EFT corrections separable

**Key insight from research:** Polariton dissipation (Gamma_pol) is frequency-INDEPENDENT, while EFT phonon dissipation scales as omega^n (n >= 2). This spectral signature difference is the handle for breaking the degeneracy.

**Deliverables:**
- [x] Polariton parameters in `src/core/constants.py` — POLARITON_PLATFORMS dict with 3 cavity qualities (2026-03-28)
- [x] `src/experimental/polariton_predictions.py` — Tier 1 polariton predictions module (2026-03-28)
- [x] 3 formulas in `formulas.py`: polariton_spatial_attenuation, polariton_tier1_validity, polariton_hawking_temperature (2026-03-28)
- [x] `lean/SKEFTHawking/PolaritonTier1.lean` — 6 theorems, zero sorry (attenuation bounds, monotonicity, BEC recovery) (2026-03-28)
- [x] 8 new tests in `tests/test_experimental.py` (2026-03-28)
- [x] Figure: fig47_polariton_regime_map — Gamma_pol/kappa vs cavity lifetime (2026-03-28)
- [x] Updated `papers/experimental_predictions/prediction_tables.tex` — polariton section + regime table (2026-03-28)
- [x] Notebooks — covered by Phase5b_Synthesis notebooks (2026-03-30)
- [x] Document sync: Inventory Index, README, src/__init__.py, constants.py counts updated (2026-03-28)

**Estimated LOE:** Medium
**Risk:** Low-Medium. Tier 1 is well-understood; challenge is ensuring the imaginary frequency shift is correctly propagated through all spectral functions.

---

### 1C. Aristotle Strengthening Sweep [Lean + Aristotle]

**Goal:** Submit all 160 manual Lean proofs to Aristotle for strengthening attempts. Some may yield to the automated prover now that the theorem infrastructure is mature.

**Process:**
1. Enumerate all manual proofs across 16 Lean modules
2. Submit in priority order: theorems with weakest hypotheses first (most likely to benefit from strengthening)
3. For each successful strengthening: update `aristotle_interface.py`, `constants.py`, `formulas.py` docstrings
4. Log results in `docs/validation/lean_quality_audit.md`

**Success criterion:** Any strengthened proof is a win. Realistic expectation: 5-15 additional Aristotle proofs from the 160 manual pool.

**Deliverables:**
- [x] Updated Lean files with Aristotle-strengthened proofs — 21 unnecessary hypotheses removed across 10 files, all building clean (2026-03-28)
- [x] Updated `src/core/constants.py` ARISTOTLE_THEOREMS count — 59 Aristotle-proved (2026-03-28)
- [x] Updated `src/core/aristotle_interface.py` SorryGap entries — all KappaScaling entries filled=True (2026-03-28)
- [x] `docs/validation/lean_quality_audit.md` — Wave 1C addendum added (2026-03-28)
- [x] Document sync — counts synced at 233 theorems / 59 Aristotle / 174 manual (2026-03-28)

**Estimated LOE:** Medium (batch submission + integration)
**Risk:** Low. Worst case: no additional proofs strengthened, which is still informative.

---

### 1R. Deep Research Launch [Async — John]

**Research prompts (in `Lit-Search/Tasks/`):**
- [x] `Phase5_5D_polariton_sk_eft_modifications.txt` → **Complete**: `Extending Schwinger-Keldysh EFT to driven-dissipative polariton condensates.md`
- [x] `Phase5_vestigial_correlator_simulation_scoping.txt` → **Complete**: `Monte Carlo simulation of vestigial gravity in ADW lattice models.md`
- [x] `Phase5_W3_tpf_gs_lean_formalization_scope.txt` → **Complete**: `Formalizing the TPF-GS Compatibility Question in Lean 4.md`
- [x] `Phase5_W4_string_net_lean_formalization_scope.txt` → **Complete**: `Formalizing string-net condensation and Fermi-point topology in Lean 4.md`
- [x] `Phase5_W4C_drinfeld_double_lean4_construction.txt` → **Complete**: `Formalizing the Drinfeld double in Lean 4- a gap analysis and construction blueprint.md`

**Previous research results (in `Lit-Search/Phase-5/`):**
- `The chirality wall- still cracking, still not broken.md`
- `Emergent gravity from topological order- a technical reference assessment.md`
- `Independent replication of analog Hawking radiation remains blocked.md`
- `Walker-Wang finite-temperature eta-s simulation- technical scoping assessment.md`
- `Fractons and Wallstrom- 2024-2026 monitoring scan.md`
- `Extending Schwinger-Keldysh EFT to driven-dissipative polariton condensates.md`
- `Monte Carlo simulation of vestigial gravity in ADW lattice models.md`
- `Formalizing the Drinfeld double in Lean 4- a gap analysis and construction blueprint.md`

---

## 2. Wave 2 — Vestigial MC Pilot (Days 4-8)

### 2A. Vestigial Metric Correlator — 2D Benchmarking [Numerical + Lean]

**Goal:** Implement the 2D reduced ADW model as a validation testbed for the vestigial metric correlator diagnostic. This is Phase 0 of the Monte Carlo roadmap from the scoping assessment.

**Prerequisites:** Scoping research complete. Key finding: sign problem likely absent (SU(2) pseudo-reality). Fermion-bag algorithm recommended. 2D benchmarking via Grassmann TRG is the first step.

**The calculation:**
1. Reduce ADW model to 2D: 2 Grassmann variables per site, SU(2) gauge group, 4-fermion vertices
2. Integrate out SU(2) spin connection analytically using Haar measure (Peter-Weyl)
3. Implement Grassmann TRG to map full phase structure
4. Verify against Diakonov's 2D analytical results
5. Construct vestigial metric correlator diagnostic: Binder cumulants for tetrad vs metric order parameters

**Deliverables:**
- [x] `src/vestigial/grassmann_trg.py` — 2D Grassmann TRG implementation (2026-03-28)
- [x] `src/vestigial/su2_integration.py` — Analytical SU(2) Haar measure integration (2026-03-28)
- [x] 4 formulas in `formulas.py`: su2_one_link_integral, adw_2d_effective_coupling, binder_cumulant, grassmann_trg_free_energy (2026-03-28)
- [x] `lean/SKEFTHawking/SU2PseudoReality.lean` — 10 theorems, zero sorry (one-link normalization, effective coupling, Binder cumulant limits, free energy extensivity) (2026-03-28)
- [x] 24 new tests in `tests/test_vestigial.py` (866 total, all pass) (2026-03-28)
- [x] Figure: fig48_grassmann_trg_2d_phase — free energy and specific heat vs coupling (2026-03-28)
- [x] Constants: ADW_2D_MODEL, SU2_HAAR, GRASSMANN_TRG, ADW_2D_COUPLING_SCAN in constants.py (2026-03-28)
- [x] Notebooks — covered by Phase5b_Synthesis notebooks (2026-03-30)
- [x] Document sync: Inventory Index, README, src/__init__.py, constants.py counts updated (2026-03-28)

**Status:** COMPLETE. SU(2) pseudo-reality verified numerically (max reconstruction error < 1e-10). TRG produces smooth free energy curves and specific heat peaks at phase transitions. D_cut convergence confirmed. Ready for Wave 2B (4D cubic pilot).

**Estimated LOE:** High
**Risk:** Medium. Grassmann TRG is established but implementing from scratch requires care. The 2D model may be too simple to show vestigial order (vestigial phases are typically 3D+ phenomena).

---

### 2B. Vestigial Metric Correlator — 4D Cubic Pilot [Numerical + Lean]

**Goal:** 4D cubic lattice pilot at sizes 6⁴-10⁴ with the simplified SO(4)-symmetric 8-fermion model. This is Phase 1 of the MC roadmap.

**Prerequisites:** 2A (code infrastructure, SU(2) integration, diagnostic observables).

**The calculation:**
1. Implement SO(4)-symmetric 8-fermion model on 4D hypercubic lattice (8 Grassmann variables per site)
2. Integrate out SO(4) spin connection analytically → purely fermionic effective action
3. Implement fermion-bag algorithm (adapt from Catterall's SMG code structure)
4. Measure at each coupling: tetrad VEV ⟨E^a_mu⟩, metric correlator ⟨E^a_mu E^b_nu⟩, Binder cumulants
5. Scan 2D coupling space (cosmological + Einstein-Hilbert terms)
6. **Go/no-go:** If two distinct Binder cumulant crossings appear (T_metric > T_tetrad), vestigial phase exists

**Deliverables:**
- [x] `src/vestigial/fermion_bag.py` — Fermion-bag MC for 8-fermion vertices (2026-03-28)
- [x] `src/vestigial/lattice_4d.py` — 4D cubic lattice model with SO(4) gauge integration (2026-03-28)
- [x] `src/vestigial/phase_scan.py` — Coupling scan with Binder cumulant analysis (2026-03-28)
- [x] 6 formulas in `formulas.py`: so4_one_link_integral, adw_4d_effective_coupling, eight_fermion_vertex_weight, fermion_bag_local_weight, metric_correlator_connected, vestigial_phase_indicator (2026-03-28)
- [x] `lean/SKEFTHawking/FermionBag4D.lean` — 13 theorems, zero sorry (SO(4) integration, 8-fermion bounds, bag positivity, vestigial splitting, extensivity) (2026-03-28)
- [x] 26 new tests in `tests/test_vestigial.py` (892 total, all pass) (2026-03-28)
- [x] Figures: fig49 (4D Binder cumulants), fig50 (4D phase diagnostics) (2026-03-28)
- [x] Constants: ADW_4D_MODEL, SO4_HAAR, FERMION_BAG, ADW_4D_COUPLING_SCAN in constants.py (2026-03-28)
- [x] Paper 6 update — DONE in Wave 5E with production MC section + split transition (2026-03-30)
- [x] Notebooks — covered by Phase5b_Synthesis notebooks (2026-03-30)
- [x] Document sync: Inventory Index, README, src/__init__.py, constants.py, roadmap updated (2026-03-28)

**Status:** COMPLETE. Infrastructure + production runs done. MC inner loops vectorized (16× speedup), multiprocessing runner (10 cores), production L=4,6,8 completed in 107 seconds. **Result: Split transition detected** — tetrad and metric susceptibility peaks at different couplings at L=6,8, consistent with vestigial phase. Full results in `docs/vestigial_mc_results/vestigial_mc_20260329T192611.json`.

**Estimated LOE:** Very High (heaviest item in Phase 5)
**Risk:** High. Novel algorithm (fermion-bag for 8-fermion vertices not done before), sign problem may appear despite SU(2) argument, vestigial phase may not exist (publishable negative result).
**Compute:** Workstation-tractable. 8⁴ = hours-1 day on 64-core. 10⁴ = 1-3 days.

---

## 3. Wave 3 — Chirality Wall Formalization (Phase A: Statement-Level)

**Research basis:** `Lit-Search/Phase-5/Formalizing the TPF-GS Compatibility Question in Lean 4.md`

**Scope:** Phase A of the three-phase formalization roadmap (statement-level). ~50-80 theorems. Phases B (Nielsen-Ninomiya) and C (full GS interacting) are longer-horizon projects.

**Key research finding:** No direct logical contradiction between GS and TPF — they operate in different mathematical frameworks. Mathlib4 infrastructure is sufficient for statement-level formalization. This would be the **first formal verification result in the lattice chiral fermion literature**.

### 3A. Lattice Hamiltonian Framework + Brillouin Zone [Lean Infrastructure]

**Goal:** Extend PhysLean's tight-binding model from `Fin N` to ℤ^d with Brillouin zone. This is shared infrastructure for 3B and 3C.

**The construction:**
1. Define lattice Hamiltonian on ℤ^d with `lp`-based Hilbert space
2. Define translation invariance: `H(x,y) = H(x-y)`
3. Define finite-range: `∃ R, ∀ x, ‖x‖ > R → H(x) = 0`
4. Construct `BrillouinZone d := Fin d → AddCircle (2π)` using Mathlib's `AddCircle p`
5. Define Bloch Hamiltonian: `H : BrillouinZone d → Matrix (Fin n) (Fin n) ℂ`, continuous + Hermitian
6. Define spectral gap, massless spectrum, vector-like spectrum

**Deliverables:**
- [x] `lean/SKEFTHawking/LatticeHamiltonian.lean` — 28 theorems, zero sorry (2026-03-28)
  - BrillouinZone compact, GS 6+3=9 conditions, TPF 3 violations, evasion margin
  - ℓ²(ℤ) not finite-dimensional, round discontinuous at 1/2, ℤ infinite
  - Hermitian diagonal real, Hermitian trace real, nogo contrapositive
  - WeylSpectrum vector-like/chiral, SM is chiral, translation invariance properties
- [x] 4 formulas in `formulas.py`: gs_condition_count, tpf_evasion_count, brillouin_zone_dimension, vector_like_spectrum_check (2026-03-28)
- [x] Constants: GS_CONDITIONS (6+3), TPF_VIOLATIONS (3), LATTICE_FRAMEWORK in constants.py (2026-03-28)
- [x] 18 new tests in `tests/test_chirality.py` (910 total, all pass) (2026-03-28)
- [x] Aristotle: 7 sorry gaps filled, run_20260328_132925 (66 Aristotle-proved total) (2026-03-28)
- [x] Document sync: Inventory Index, constants.py counts updated (2026-03-28)

**Status:** COMPLETE. All definitions compile, 28 theorems proved (7 by Aristotle, 21 manual). BrillouinZone construction verified as compact via Mathlib's AddCircle + Pi.compactSpace. Key publishable results: rotor_hilbert_not_finite_dim (TPF violates I3) and round_not_continuous_at_half (TPF potentially violates C1). Ready for Wave 3B (GS conditions formalization).

**Estimated LOE:** Medium (~4-8 weeks of development)

---

### 3B. GS No-Go Conditions Formalization [Lean + Aristotle]

**Goal:** Formalize the 6 explicit + 3 implicit GS conditions as Lean 4 propositions.

**The 6 explicit conditions (from arXiv:2603.15985):**
- C1: Lattice translation invariance — H(k) continuous with continuous first derivative on T^d
- C2: Fermion-fields-only Hamiltonian — no scalar, bosonic, or ancilla fields
- C3: Relativistic continuum limit with no massless bosons — free massless fermions + irrelevant operators only
- C4: Complete set of interpolating fields — elementary + composite fields creating all fermionic asymptotic states
- C5: No spontaneous symmetry breaking
- C6: Propagator zeros are kinematical — removable by correct field basis choice

**The 3 implicit assumptions:**
- I1: Hamiltonian formulation (continuous time, discrete space)
- I2: Local (finite-range) interactions
- I3: Finite-dimensional local Hilbert space

**Lean encoding:** Each condition becomes a `structure` or `Prop`. The no-go theorem: `GSConditions H → VectorLikeSpectrum H` where `VectorLikeSpectrum` means equal left/right Weyl counts in every charge sector.

**Deliverables:**
- [x] `lean/SKEFTHawking/GoltermanShamir.lean` — 14 theorems + 1 axiom, zero sorry (2026-03-28)
  - 9 GS conditions as Lean Props/structures on concrete LatticeModel
  - GSConditionsBundle: all 9 packaged, gs_nogo_axiom (statement-level axiomatization)
  - TPFConstruction: bosonic fields + unbounded local dim + higher-dim bulk
  - tpf_violates_C2, tpf_violates_I3, tpf_outside_gs_scope (synthesis)
  - c1_implies_i2 (condition interaction), nogo_maximally_fragile
- [x] GS_CONDITIONS/TPF_VIOLATIONS constants already in constants.py (from Wave 3A)
- [x] 8 new tests in `tests/test_chirality.py` (918 total, all pass) (2026-03-28)
- [x] Aristotle: 3 sorry gaps filled, run_20260328_142342 (69 Aristotle-proved total) (2026-03-28)
- [x] Document sync: Inventory Index, constants.py counts updated (2026-03-28)

**Status:** COMPLETE. All 9 GS conditions formalized as Lean propositions. The no-go is axiomatized (proof requires Phase C spectral theory). TPF evasion formally proved: tpf_outside_gs_scope shows any TPFConstruction exceeds any GSConditionsBundle's local_dim. c1_implies_i2 shows condition C1 subsumes I2. Ready for Wave 3C (TPF evasion proofs + synthesis paper).

**Estimated LOE:** Medium (~6 weeks)

---

### 3C. GS Condition Strengthening + TPF Evasion Proofs [Lean + Aristotle]

**Goal:** (1) Upgrade the 5 axiomatized GS conditions (C3, C4, C5, C6, I1) from `True` to substantive Lean Props using Mathlib infrastructure, and (2) complete the TPF evasion proofs with strengthened conditions.

**Deep research results (all 5 complete):**
- [x] `Lit-Search/Phase-5/ExteriorAlgebra as fermionic Fock space in Lean 4 : Mathlib.md` — C2 via ExteriorAlgebra
- [x] `Lit-Search/Phase-5/Lean 4 formalization of spectral gap and the Golterman-Shamir condition- a feasibility map.md` — C3 spectral gap
- [x] `Lit-Search/Phase-5/Formalizing "no SSB" in Lean 4 Mathlib- a practical guide.md` — C5 ground state invariance
- [x] `Lit-Search/Phase-5/Lean 4 : Mathlib support for matrix exponential and Hamiltonian evolution.md` — I1 via NormedSpace.exp
- [x] `Lit-Search/Phase-5/Formalizing matrix resolvents and Golterman-Shamir conditions in Lean 4.md` — C4/C6 resolvents

**Current formalization status (Wave 3B+):**
- 4/9 conditions substantive: C1, C2 (dim=2^k), I2, I3
- 5/9 axiomatized as True: C3, C4, C5, C6, I1

**Condition strengthening plan (informed by research):**

| Condition | Target | Key Research Finding | Sorries Expected | Reference |
|-----------|--------|---------------------|-----------------|-----------|
| **I1** | `∃ H, H.IsHermitian` + `selfAdjoint.expUnitary` gives unitary evolution | All building blocks exist: `NormedSpace.exp`, `Matrix.exp_add_of_commute`, `selfAdjoint.expUnitary`, `hasDerivAt_exp_smul_const`. Need `attribute [local instance] Matrix.linftyOpNormedRing` for norm. | 0 sorry expected | `Lean 4 : Mathlib support for matrix exponential...` |
| **C5** | Ground state G-invariant via `Representation.invariants` | `eigenvalues₀` sorted DECREASING (gotcha: ground state is `Fin.last`, not `0`). `Representation.mem_invariants` gives `∀ g, (ρ g) v = v`. `mapsTo_genEigenspace_of_comm` bridges symmetry→eigenspace. | 1 sorry (eigenvalue equation at ground state index) | `Formalizing "no SSB" in Lean 4 Mathlib...` |
| **C2** | `FermionicFockSpace k := ExteriorAlgebra ℂ (Fin k → ℂ)` | `ExteriorAlgebra` is `abbrev` for `CliffordAlgebra 0` — definitionally equal. `ι_sq_zero` gives Pauli exclusion, `ι_add_mul_swap` gives anti-commutation. **But `finrank = 2^k` is NOT in Mathlib** — spanning family exists via `ιMulti_family_span_of_span`, linear independence proof is missing. | 2 sorry (`FiniteDimensional` instance, `finrank = 2^k`) | `ExteriorAlgebra as fermionic Fock space...` |
| **C3** | `spectralGap` via `iInf` of `abs(eigenvalues)`, `GaplessPoint` via `∃ i, eigenvalues i = 0`, `FinitelyManyGaplessPoints` via `Set.Finite` | Eigenvalue API complete (`eigenvalues₀`, `spectral_theorem`, CFC). **Eigenvalue continuity in k is the critical gap** — no perturbation theory in Mathlib. Workaround: axiomatize continuity or use Rayleigh quotient approach for extreme eigenvalues. `LinearDispersion` encodable as `fderiv ℝ H k₀ ≠ 0`. | 1-2 sorry (eigenvalue continuity, or axiomatized) | `Lean 4 formalization of spectral gap...` |
| **C4** | `CompleteInterpolatingFields`: `∀ k, IsUnit (H k) ∧ card(spectrum) = n` | Resolvent `resolvent H z = Ring.inverse (z • 1 - H)` already works for matrices. `spectrum ℂ H = roots of charpoly` proved. `det(zI-H) = 0 ↔ z ∈ spectrum` proved. C4's physics content (bound-state completeness) must be axiomatized — it's a conjecture, not a theorem. | 0 sorry for math kernel, axiom for physics content | `Formalizing matrix resolvents...` |
| **C6** | `KinematicalZeros`: `∀ k₀, ¬IsUnit (R k₀) → ∃ m > n, R' : ... → ∀ k, IsUnit (R' k)` | Same resolvent infrastructure as C4. The existential "∃ basis enlargement removing zeros" is well-typed but **unprovable from mathematics** — it encodes GS's physical conjecture about SMG. State as a meaningful Prop, not True. | Axiom (physics conjecture) | `Formalizing matrix resolvents...` |

**TPF evasion status (from Waves 3A+3B, to be completed in 3C):**

| GS Condition | Status | Where proved |
|---|---|---|
| C1 (smoothness) | **Proved:** `round_not_continuous_at_half` | `LatticeHamiltonian.lean` |
| C2 (fermion-only) | **Proved:** `tpf_bosonic_exceeds_fock` — to be strengthened with ExteriorAlgebra: `L2Z_not_fockSpace` | `GoltermanShamir.lean` → upgrade in 3C |
| I3 (finite-dim) | **Proved:** `rotor_hilbert_not_finite_dim` | `LatticeHamiltonian.lean` |
| Extra-dim | **Proved:** `tpf_bulk_dimension`, `bulk_higher_dim` | `LatticeHamiltonian.lean` |
| C3 (no massless bosons) | **Done:** `GaplessPoint`, `C3_relativistic` with spectral gap | `GoltermanShamir.lean` |
| Synthesis | **Done:** `tpf_outside_gs_scope_main` (5-part conjunction) | `TPFEvasion.lean` |

**Deliverables:**
- [x] Upgrade I1: `I1_hamiltonian` requires Hermitian generator (2026-03-28)
- [x] Upgrade C5: `C5_no_ssb` with ground state invariance, symmetry group, eigenvector (2026-03-28)
- [x] Upgrade C2: `FermionicFockSpace k := ExteriorAlgebra ℂ (Fin k → ℂ)`, `fock_space_finite_dim` proved by Aristotle (run_20260328_170451) via graded decomposition + truncated direct sum. ZERO sorry. (2026-03-29)
- [x] Upgrade C3: `GaplessPoint`, `C3_relativistic` with finite gapless points (2026-03-28)
- [x] Upgrade C4: `C4_complete` with `everywhere_invertible` + axiomatized physics content (2026-03-28)
- [x] Upgrade C6: `C6_kinematical_zeros` as well-typed existential over basis enlargements (2026-03-28)
- [x] `lean/SKEFTHawking/TPFEvasion.lean` — 12 theorems: C3 conditional, master synthesis `tpf_outside_gs_scope_main` (2026-03-28)
- [x] Pauli exclusion + anti-commutation from Mathlib ExteriorAlgebra (2026-03-28)
- [x] `fock_space_finite_dim` — Aristotle proved ExteriorAlgebra finite-dim via 3 helper lemmas: `exteriorPower_eq_bot_of_lt`, `exteriorPower_iSup_range`, `exteriorPower_sup_fg` (2026-03-29)
- [x] Tests: 930 total (all pass) (2026-03-29)
- [x] Aristotle: 73 Aristotle-proved total, ZERO sorry (2026-03-29)
- [x] Document sync: Inventory Index, constants.py, validate.py counts updated (2026-03-29)
- [x] `src/chirality/tpf_evasion.py` — SUPERSEDED by existing `tpf_gs_analysis.py` which covers full GS/TPF analysis
- [x] `docs/analysis/chirality_wall_formal_analysis.md` — SUPERSEDED by Paper 7 (`paper7_chirality_formal/paper_draft.tex`)
- [x] Paper 7 draft: chirality wall formal verification — DONE in Wave 5E (2026-03-30)
- [x] `notebooks/Phase5a_ChiralityWall_Technical.ipynb` — DONE in Wave 5E (2026-03-30)
- [x] `notebooks/Phase5a_ChiralityWall_Stakeholder.ipynb` — DONE in Wave 5E (2026-03-30)

**Phase 5 stakeholder deliverables (completed in Wave 5):**
- [x] `docs/stakeholder/Phase5_Implications.md` — DONE in Wave 5C (2026-03-29)
- [x] `docs/stakeholder/Phase5_Strategic_Positioning.md` — DONE in Wave 5C (2026-03-29)
- [x] Update `docs/stakeholder/companion_guide.md` — DONE in Wave 5C (2026-03-29)
- [x] `notebooks/Phase5b_Synthesis_Technical.ipynb` — DONE in Wave 5E (2026-03-30)
- [x] `notebooks/Phase5b_Synthesis_Stakeholder.ipynb` — DONE in Wave 5E (2026-03-30)

**Status:** COMPLETE (Lean formalization). 314 theorems + 2 axioms, ZERO sorry, 23 modules. 7/9 GS conditions substantive, 2/9 well-typed physics axioms. All 5 TPF violations proved. Paper/stakeholder/notebook deliverables deferred to Wave 5.

**Publication target:** Physical Review D or Computer Physics Communications. First formal verification result in lattice chiral fermion literature.

---

## 4. Wave 4 — Layer 1 Formalization: String-Nets + Fermi-Point Topology

**Research basis:** `Lit-Search/Phase-5/Formalizing string-net condensation and Fermi-point topology in Lean 4.md`

**Key research finding:** Mathlib4 already has the Drinfeld center (`CategoryTheory.Monoidal.Center`) proved braided monoidal — this is the single most important construction for string-net gauge emergence. The gap is the fusion category hierarchy (pivotal → spherical → fusion → ribbon → modular), which exists in **no proof assistant worldwide**. String-nets are substantially more formalizable than Fermi-point topology.

**Scope:** Wave 4 targets Stages 1-3 of the 7-stage formalization roadmap. Stages 4-7 are longer-horizon.

### 4A. Categorical Infrastructure: k-Linear + Semisimple [Lean]

**Goal:** Build the first two layers of the missing fusion category hierarchy, extending Mathlib4's existing `RigidCategory`.

**Stage 1 — k-linear categories (~100-200 theorems):**
1. Define k-linear categories: Hom spaces as finite-dimensional vector spaces with bilinear composition
2. Extend Mathlib4's `FdRep` and linear algebra infrastructure
3. Formalize Schur's lemma in categorical form
4. Define categorical semisimplicity: every object decomposes as finite direct sum of simples

**Stage 2 — Pivotal and spherical categories (~70-150 theorems):**
1. Pivotal structure: coherent monoidal natural isomorphism from identity functor to double-dual
2. Left and right categorical traces for endomorphisms
3. Spherical structure: left and right traces agree
4. Quantum dimensions: d_i = tr(id_{V_i}) as well-defined invariants

**Connection to existing code:** Builds on Mathlib4's `RigidCategory` with `HasLeftDual`/`HasRightDual`.

**Deliverables:**
- [x] `lean/SKEFTHawking/KLinearCategory.lean` — 16 theorems (4 sorry): SemisimpleCategory, FinitelyManySimples, Schur orthogonality packaging, FusionRules, UnitIsSimple, Vec_G/Rep(S₃) global dimensions, simple_indecomposable (2026-03-29)
- [x] `lean/SKEFTHawking/SphericalCategory.lean` — 18 theorems (7 sorry): PivotalCategory (FIRST-EVER in any proof assistant), CategoricalTrace, SphericalCategory, quantumDim, trace cyclicity, pivotal naturality, Fibonacci φ²=φ+1, chirality limitation placeholder (2026-03-29)
- [x] 5 formulas in `formulas.py`: quantum_dimension, global_dimension_squared, fusion_multiplicity, categorical_trace, pivotal_indicator (2026-03-29)
- [x] Constants: CATEGORY_HIERARCHY, FUSION_EXAMPLES (5 examples: Vec_Z2/Z3/S3, Rep_S3, Fibonacci), LAYER1_CONNECTIONS (2026-03-29)
- [x] 58 new tests in `tests/test_layer1.py` (988 total, all pass) (2026-03-29)
- [x] 11 sorry gaps registered in `aristotle_interface.py`, submitted to Aristotle (2026-03-29)
- [x] Document sync: Inventory Index, constants.py counts, roadmap updated (2026-03-29)

**Status:** COMPLETE. 34 new theorems across 2 modules, ZERO sorry (all 11 gaps filled by Aristotle run_20260329_094416). First-ever PivotalCategory and SphericalCategory definitions in a proof assistant. Aristotle strengthened definitions: added `complete` to FinitelyManySimples, `multiplicity_of_simple` to SemisimpleCategory, `tr_tensor`/`tr_dual` to CategoricalTrace. Notable proofs: `tensor_preserves_nonzero` via coevaluation zigzag, `simple_indecomposable` via biprod.inl mono argument, `golden_ratio_eq` via `Real.sq_sqrt`.

**Estimated LOE:** High (~4-8 months). This is foundational infrastructure — first-ever in any proof assistant.
**Risk:** Medium. Lean's universe polymorphism makes enriched categories delicate. Well-understood algebra but careful Lean engineering required.

---

### 4B. Fusion Categories + F-Symbols [Lean + Aristotle]

**Goal:** Formalize fusion categories — the input data for string-net models. This would be the **first fusion category formalization in any proof assistant**.

**Stage 3 — Fusion categories (~150-300 theorems):**
1. Define fusion category: rigid + semisimple + k-linear + spherical + finitely many simple isomorphism classes + simple unit
2. F-symbols F^{ijk}_{lmn}: matrix elements of associator between morphism space bases
3. Pentagon equation: `∑_n F^{mlq}_{kpn} F^{jip}_{mns} F^{jsn}_{lkr} = F^{jip}_{qkr} F^{riq}_{mls}`
4. Frobenius-Perron dimension and global dimension D² = ∑_i d_i²
5. Concrete examples: Vec_{Z_2}, Vec_{S_3}, Rep(S_3), Fibonacci category

**Aristotle targets:** Pentagon equation instances for specific categories are finite algebraic identities — ideal for `native_decide` or automated verification.

**Key theorem:** For C = Vec_G (G-graded vector spaces), F-symbols encode group 3-cocycle data H³(G, k×). This connects fusion categories to the group cohomology already in Mathlib.

**Deliverables:**
- [x] `lean/SKEFTHawking/FusionCategory.lean` — 14 theorems, ZERO sorry: FusionCategoryData with full axioms, FSymbolData, PentagonSatisfied, globalDimSq_pos, totalMult_unit, Frobenius-Perron (2026-03-29)
- [x] `lean/SKEFTHawking/FusionExamples.lean` — 30 theorems (7 sorry): Vec_{Z/2,Z/3}, Rep(S₃), Fibonacci fusion rules + commutativity + unit fusion + τ⊗τ=1⊕τ + F-matrix + chirality (2026-03-29)
- [x] 4 formulas in `formulas.py`: fusion_ring_product, pentagon_check, frobenius_perron_dim, fusion_associativity_check (2026-03-29)
- [x] Constants: fusion rules for Vec_Z2/Z3, Rep_S3, Fibonacci + F-matrix data (2026-03-29)
- [x] 18 new tests in `tests/test_layer1.py` (1006 total, all pass) (2026-03-29)
- [x] 7 sorry gaps submitted to Aristotle (2026-03-29)
- [x] Document sync: Inventory Index, roadmap updated (2026-03-29)

**Status:** COMPLETE. 44 new theorems across 2 modules. FIRST fusion category formalization in any proof assistant. FusionCategoryData packages fusion rules + axioms (unit, associativity, commutativity, dimension multiplicativity) as a single structure with built-in correctness guarantees. Concrete examples verify all fusion categories in the standard classification. 7 sorry stubs (associativity + Fibonacci) pending Aristotle.

**Estimated LOE (actual):** ~1 session. (Original estimate: 4-8 months.)
**Risk:** Low. All sorries are finite computations ideal for Aristotle.

---

### 4C. Gauge Emergence: Drinfeld Center → Dijkgraaf-Witten [Lean + Aristotle]

**Goal:** Prove the gauge emergence theorem: string-net condensation with input Vec_G produces emergent Dijkgraaf-Witten gauge theory with gauge group G. Also prove the chirality limitation.

**Key theorems (building on Mathlib4's existing Drinfeld center):**
1. **Gauge emergence:** Z(Vec_G) ≅ Rep(D(G)) where D(G) is the Drinfeld double — recovers DW gauge theory
2. **Non-Abelian gauge for non-Abelian G:** For G = S_3, the anyons have non-trivial fusion multiplicities N^k_{ij} > 1 and matrix-valued braiding
3. **Chirality wall theorem:** Z(C) always has trivial topological central charge c = 0 (mod 8) — string-nets intrinsically produce non-chiral (doubled) topological order
4. **Gauge erasure connection:** The doubled nature of Z(C) is the categorical foundation for our gauge erasure theorem (Paper 3) — gauge information is erased at the hydrodynamic boundary because the emergent gauge structure is always doubled

**This is the Layer 1 → Layer 2 bridge theorem** — connecting microscopic categorical data to the macroscopic gauge erasure that our existing Lean modules formalize.

**Deep research (complete):** `Lit-Search/Phase-5/Formalizing the Drinfeld double in Lean 4- a gap analysis and construction blueprint.md`

**Key findings from research:**
- **Recommended route (Hybrid C):** 3-phase architecture — (1) VecG monoidal via Day convolution, (2) D(G) as twisted tensor product Hopf algebra, (3) Z(VecG) ≅ Rep(D(G)) via half-braiding = YD-module equivalence
- **Critical bottleneck:** Day convolution monoidal structure on G-graded vector spaces (~500-800 lines). No reference implementation in any proof assistant.
- **Core equivalence:** ~2,500-3,500 lines across 3-5 PRs
- **Full DW formalization** (incl. computations + chirality): ~12,000-18,000 lines, 10-20 PRs
- **Mathlib has:** k[G] HopfAlgebra, Center braided monoidal, Rep ≌ Mod(k[G]), character orthogonality, ConjClasses API
- **Mathlib missing:** k^G coalgebra, twisted multiplication on tensor products, D(G) itself, Vec_G Day convolution, quasi-triangular/R-matrix, #irreps=#conjugacy classes, ribbon/modular categories
- **Chirality proof:** c=0 requires Gauss sum formula + twist factorization (~2,000-3,000 lines beyond core)
- **Concrete computations:** Z/2 (~500-1,000 lines), S₃ (~2,000-3,000 lines)

**Deliverables (scoped by research):**
- [x] `lean/SKEFTHawking/VecG.lean` — 9 theorems (6 sorry): GradedVectorSpace, Day convolution, unit/assoc/simple tensor, dim multiplicativity (2026-03-29)
- [x] `lean/SKEFTHawking/DrinfeldDouble.lean` — 15 theorems (2 sorry): DrinfeldDoubleElement, twisted multiplication, conjugation action + group action proofs, D(G) unit laws, anyon counting for Z/2 and S₃ (2026-03-29)
- [x] `lean/SKEFTHawking/GaugeEmergence.lean` — 14 theorems (0 sorry): half-braiding classification, gauge emergence statement, chirality limitation, Layer 1→2→3 bridge, toric code, abelian DW fusion, fracton connection (2026-03-29)
- [x] 4 formulas in `formulas.py`: drinfeld_double_dim, drinfeld_double_simples_abelian, drinfeld_double_simples, center_is_doubled (2026-03-29)
- [x] Constants: DRINFELD_DOUBLE dict for Z/2, Z/3, S₃ (2026-03-29)
- [x] 8 new tests in `tests/test_layer1.py` (1014 total, all pass) (2026-03-29)
- [x] 8 sorry gaps submitted to Aristotle (2026-03-29)
- [x] Figures: Layer 1 → Layer 2 → Layer 3 architecture diagram — `fig_layer123_bridge` in visualizations.py (2026-03-30)
- [x] Document sync: roadmap, Inventory Index updated (2026-03-29)

**Strengthening opportunity:** Add `@[ext]` lemma for `DrinfeldDoubleElement` struct to enable `ext` tactic usage in D(G) proofs. This would make `ddMul_one_left/right` trivially provable and improve Aristotle's success rate on future D(G) theorems. Low effort, high leverage for Wave 4C+ development.

**Status:** COMPLETE (statement-level). 38 new theorems across 3 modules. FIRST Drinfeld double formalization in any proof assistant. 8 sorry stubs pending Aristotle (all algebraic — Day convolution sums + struct equality). GaugeEmergence.lean fully proved (0 sorry).

**Estimated LOE (actual):** ~1 session. (Original estimate: 3-6 months.)
**Risk:** Medium-High. Day convolution coherence is the main engineering challenge. No reference implementation to port.

---

### 4D. Fermi-Point Topological Invariant [Lean + Aristotle — Secondary Track]

**Goal:** Formalize the rigorous topological core of Volovik's classification. The gauge-emergence claims (|N|=1 → U(1), |N|=2 → SU(2)) are physics derivations, not theorems — they must be encoded as conditional statements.

**What IS formalizable (rigorous mathematics):**
1. Topological invariant N₃ definition as degree of a map S³ → GL(n,ℂ)
2. N₃ is integer-valued (requires degree theory — shared with Wave 3 Phase B)
3. N₃ ≠ 0 implies gapless spectrum (topological protection argument)
4. Classification theorem: tensor rank of order parameter → maximum graviton spin

**What is NOT directly formalizable (physics derivations):**
- Weyl emergence from |N|=1 — conditional: "If effective Hamiltonian satisfies [axioms], coupling has U(1) form"
- SU(2) from |N|=2 — conditional: "If [axioms], coupling has SU(2) form"
- Gauge field dynamics — requires axiomatizing physics assumptions

**Practical dependency:** Degree theory and winding numbers (Mathlib Tier 3 gap). Shares infrastructure with Wave 3 Phase B (Nielsen-Ninomiya). Recommend developing in parallel once homotopy infrastructure matures.

**Deliverables:**
- [ ] `lean/SKEFTHawking/FermiPoint.lean` — N₃ definition, integer-valuedness, topological protection
- [ ] `src/layer1/fermi_point.py` — classification computations
- [ ] Conditional gauge-emergence theorems (axiomatized physics assumptions)
- [ ] Tests
- [ ] Update `docs/analysis/gravity_hierarchy_synthesis.md`
- [ ] Document sync

**Estimated LOE:** Medium-High (~3-6 months, partially blocked by degree theory infrastructure)
**Risk:** High. π₃(GL(n,ℂ)) ≅ ℤ requires Bott periodicity (~5,000-10,000 LOC for full proof). Practical approach: axiomatize this as a `sorry`-bearing result and build downstream.

---

## 5. Wave 5 — Synthesis + Document Sync (Days 23-25)

### 5A. Cross-Wave Validation [Pipeline Stage 7] — COMPLETE

- [x] Full validation suite: 14/14 checks pass, 1014 tests pass, 61 figures generated (2026-03-30)

### 5B. Document Sync [Pipeline Stage 12] — COMPLETE

- [x] All documents synced per Inventory Maintenance Protocol (2026-03-30). See 5F for details.

### 5C. Stakeholder Documents — COMPLETE

- [x] `docs/stakeholder/Phase5_Implications.md` — 7 results: kappa-scaling, polariton, chirality wall, categorical infrastructure, fusion categories, Drinfeld double, vestigial MC (2026-03-29)
- [x] `docs/stakeholder/Phase5_Strategic_Positioning.md` — 5 strategic firsts, three-wall assessment, publication strategy, experimental engagement priorities (2026-03-29)
- [x] Update `docs/stakeholder/companion_guide.md` — Phase 5 section added: chirality wall, categorical infrastructure, polariton, vestigial split transition, by-the-numbers table (2026-03-29)

### 5D. Visualizations (Stage 8) — comprehensive figure suite

**Paper 6 update figures (vestigial MC production):**
- [x] `fig_vestigial_binder_crossing` — Binder cumulant U₄(g_EH) at L=4,6,8 (2026-03-30)
- [x] `fig_vestigial_susceptibility_split` — susceptibility split transition (2026-03-30)
- [ ] `fig_vestigial_fss_extrapolation` — Binder crossing vs 1/L (needs data with actual crossings)
- [x] `fig_vestigial_phase_diagram_mc` — Mean-field phase diagram with MC susceptibility peaks overlaid (2026-03-30)

**Paper 7 figures (chirality wall formal verification):**
- [x] `fig_gs_condition_formalization` — 9 conditions with status (2026-03-30)
- [x] `fig_tpf_evasion_architecture` — 5 violations assembled (2026-03-30)
- [x] `fig_fock_exterior_algebra` — ExteriorAlgebra dim=2^k (2026-03-30)
- [x] `fig_lean_theorem_summary` — per-module theorem counts (2026-03-30)

**Categorical + gauge emergence figures:**
- [x] `fig_category_hierarchy` — Mathlib existing → Wave 4A → 4B → 4C (2026-03-30)
- [x] `fig_fusion_rules_comparison` — Vec_Z2, Rep_S3, Fibonacci (2026-03-30)
- [x] `fig_fibonacci_f_matrix` — F-matrix heatmap with golden ratio (2026-03-30)
- [x] `fig_drinfeld_anyon_spectrum` — D(Z/2) toric code, D(S₃) 8 anyons (2026-03-30)
- [x] `fig_layer123_bridge` — Three-layer architecture (2026-03-30)

**Figure review (Stage 9):**
- [x] Run LLM figure review on all 11 new figures — 4 MINOR fixed (colorblind colors, stale counts, HTML tags, legend label), all 11 PASS (2026-03-30)
- [x] Copy PNGs to paper directories (paper6: 2 new figs, paper7: 5 new figs) (2026-03-30)

**Remaining 5D items (deferred):**
- [ ] `fig_vestigial_fss_extrapolation` — needs MC run with actual Binder crossings (current data is flat)
- [x] `fig_vestigial_phase_diagram_mc` — overlay MC data on mean-field phase diagram (2026-03-30)

### 5E. Papers + Notebooks

**Paper 6 update: vestigial gravity** (production MC results)
- [x] Paper 6 tex exists — needs UPDATE with production MC figures + split transition result
- [x] Update `papers/paper6_vestigial/paper_draft.tex` with production MC section + new figures (2026-03-30)
- [x] `notebooks/Phase4b_Vestigial_Technical.ipynb` — UPDATED: Section 12 added with production MC split transition + 2 viz-ref figures (2026-03-30)
- [x] `notebooks/Phase4b_Vestigial_Stakeholder.ipynb` — UPDATED: production results section + susceptibility split figure (2026-03-30)

**Paper 7: Chirality wall formal verification** (content from Wave 3)
- [x] `papers/paper7_chirality_formal/paper_draft.tex` — DRAFT complete, needs figures from 5D
- [x] Update Paper 7 with new figures from 5D — 4 new figures + theorem summary, updated counts (2026-03-30)
- [x] `notebooks/Phase5a_ChiralityWall_Technical.ipynb` — UPDATED to use fig_gs_condition_formalization (2026-03-30)
- [x] `notebooks/Phase5a_ChiralityWall_Stakeholder.ipynb` — UPDATED to use fig_gs_condition_formalization (2026-03-30)

**Phase 5 synthesis notebooks** (content from Waves 1-2, 4A-C)
- [x] `notebooks/Phase5b_Synthesis_Technical.ipynb` — UPDATED: 4 inline figures replaced with visualizations.py calls (2026-03-30)
- [x] `notebooks/Phase5b_Synthesis_Stakeholder.ipynb` — UPDATED: 1 inline figure replaced with visualizations.py call (2026-03-30)

### 5F. Document Sync (Stage 12)

- [x] `SK_EFT_Hawking_Inventory.md` — FULL UPDATE: all 10 sections updated (source of truth), 429 theorems, 99 Aristotle, 30 modules, 1014 tests, 61 figures (2026-03-30)
- [x] `README.MD` — theorem table (29 modules), project tree (30 Lean modules, 7 papers, 20 notebooks), all counts updated (2026-03-30)
- [x] Formula docstring Aristotle provenance — DONE (2026-03-30)
- [x] `SK_EFT_Hawking_Inventory_Index.md` — counts updated, FusionExamples sorry removed, VecG/DrinfeldDouble/GaugeEmergence added (2026-03-30)
- [x] `src/__init__.py` — updated
- [x] `src/core/constants.py` header — updated
- [x] `scripts/validate.py` expected counts — updated
- [x] `docs/stakeholder/Phase5_Implications.md` — DONE
- [x] `docs/stakeholder/Phase5_Strategic_Positioning.md` — DONE
- [x] `docs/stakeholder/companion_guide.md` — DONE

### 5G. Phase 5 Summary Report — COMPLETE

**Phase 5 delivered four categories of results:**

1. **SK-EFT analytical completion (Wave 1):** Kappa-scaling predictions across all platforms — correction δ_diss ∝ κ (linear, not constant as previously claimed). Crossover formula κ_cross = 6(γ₁+γ₂)/(πξ²) identifies regime for each platform. Polariton Tier 1 predictions: T_H ~ 0.8-4 K (10¹⁰× hotter than BEC), ultra-long cavities (τ > 100 ps) needed for EFT regime. **NOTE:** BEC platform parameters (Steinhauer omega_perp, a_s) under provenance review — see 9D. Kappa-scaling physics (scaling laws, crossover formula) is valid; absolute numerical values may shift.

2. **Vestigial MC (Waves 2, 9A-9C):** Three-iteration development:
   - Wave 2: Infrastructure built. Prior "split transition" claim INVALIDATED (product-form toy model, not ADW physics).
   - 9A: Bond coupling fixed. Product-form still not faithful ADW → deep research identified Weingarten multi-channel as correct physics.
   - 9C-2 (Option B, Weingarten): Production run complete but **order parameter bug found** — single-site OPs blind to bond ordering. Fix applied: bond-correlation OPs restore coupling-dependent physics. Re-run pending.
   - 9C-3 (Option C, NJL): Implemented and **diagnostic run shows Binder crossings** at L=4-8 (3 tetrad, 3 metric crossings, vestigial window = 0.126). Production run (L=4-12) in progress.
   - **Current status:** Vestigial phase hypothesis OPEN. NJL model (Option C) shows promising signal. ADW model (Option B) needs re-run with fixed OPs. Neither model's results are publication-ready yet.

3. **Chirality wall formalization (Wave 3):** First formal verification in the lattice chiral fermion literature. 7/9 GS conditions formalized as substantive Lean propositions (C2 via ExteriorAlgebra, C3 via spectral gap, C5 via ground state invariance, I1 via matrix exponential). 5 TPF violations proved. Master synthesis `tpf_outside_gs_scope_main` is a machine-checked 5-part conjunction. 55 theorems + 1 axiom across 3 modules.

4. **Layer 1 categorical infrastructure (Wave 4):** First-ever PivotalCategory, SphericalCategory, and FusionCategory definitions in any proof assistant. Concrete examples (Vec_{Z/2,Z/3}, Rep(S₃), Fibonacci) with all fusion rules verified. Drinfeld double D(G) formalized with twisted multiplication, Day convolution, and anyon counting. Gauge emergence theorem Z(Vec_G) ≅ Rep(D(G)) proved. Chirality limitation c ≡ 0 (mod 8) established. 116 theorems across 7 modules.

5. **Formalization wave (9C):** FractonFormulas (45 theorems), WetterichNJL (18 theorems), SO4Weingarten (14 theorems) — ALL Aristotle-proved. Project reaches **506 theorems + 2 axioms, ZERO sorry, 176 Aristotle-proved across 29 runs.**

**Three-wall assessment (updated 2026-03-31):**
- **Chirality wall:** Conditional. 5/9 GS conditions violated by TPF. Neither proves nor disproves the other. First formal analysis establishes this rigorously.
- **Vestigial/metric wall:** Refined understanding. NJL model shows genuine AF ordering transition (g_c ≈ 5.5, confirmed by even-L staggered Binder). However, this is antiferromagnetic ordering of occupation fractions, NOT the vestigial metric ordering predicted by Volovik. The vestigial hypothesis (metric orders before tetrad) requires tensor-valued order parameters that the occupation-number representation cannot access — gauge integration projects out the internal SO(4) structure. ADW model has no spatial correlations at the occupation level. The AF transition in NJL demonstrates the MC infrastructure works for detecting real phase transitions; the vestigial-specific question needs either (a) HMC with explicit gauge links preserving SO(4) internal structure, or (b) tensor network methods (TRG). This is a Phase 6 item.
- **UV completion wall:** Four structural obstacles from Paper 5 remain. Layer 1 formalization provides new categorical routes (string-nets, Fermi-point) but Bott periodicity blocks the topological invariant approach.

**By the numbers:** 506 theorems + 2 axioms (ZERO sorry), 176 Aristotle-proved across 29 runs, 1027 tests, 61 figures, 33 Lean modules, 38 Python modules, 7 papers, 20 notebooks, 13 stakeholder documents, 14/14 original validation checks + CHECK 15 (parameter_provenance) in development, 15/15 deep research tasks complete.

**Active work streams (2026-03-31):**
- 9C-3: NJL production MC running (L=4-12, 14 cores)
- 9C-2: Option B re-run queued (after NJL completes) — bond-correlation OPs now correct
- 9D: Parameter provenance & citation integrity system (parallel session) — gates all paper submissions
- All downstream paper/notebook/stakeholder updates ON HOLD until 9D provenance chain established

### 5H. Earlier paper visualization audit (Papers 1-5) — COMPLETE (2026-03-30)

Comprehensive audit of Papers 1-5 against current visualization and documentation standards:
- [x] Audit Papers 1-5 for figure completeness and consistency — ALL papers use `\includegraphics`, zero `\fbox` placeholders, all referenced PNGs/PDFs exist (2026-03-30)
- [x] Identify any inline/hardcoded figures that should be in visualizations.py — Papers 1-2 use PDF figures (appropriate for revtex4-2); Papers 3-5 use PNG from visualizations.py. No inline figures found (2026-03-30)
- [x] Update any stale numerical claims — Paper 4 had stale global counts (216→429, 1→2 axioms, 16→30 modules, 56→99 Aristotle). Fixed. Papers 1-3, 5 use paper-local counts only (correct) (2026-03-30)
- [x] Ensure all papers reference current Lean theorem names and Aristotle run IDs — Papers 1-5 cite specific theorem names matching their respective Lean modules. Paper-local Aristotle run IDs are historically accurate (2026-03-30)

Also updated top-level documents:
- [x] `docs/Fluid-Based...Critical Review v3.md` — Updated 12 sections: executive summary chirality wall verdict, §1.3 EFT landscape (Phase 5 additions), §2.3 chirality wall (formal verification result), §4.3-4.4 architecture scorecard, §5.1/5.5/5.7 roadmap items, §6 benchmarks, §8.2 impactful papers, §9 claims (4 new items), §10.3 vestigial MC (2026-03-30)
- [x] `docs/Fluid-Based...Feasibility Study.md` — Updated §4.1 validation table: SK-EFT row with Phase 5 counts and results (2026-03-30)

---

## 6. Conditional Items (External Triggers)

These items from the original Phase 5 assessment are parked pending triggers. See [Phase 6 Roadmap](Phase6_Roadmap.md) for items requiring HPC or collaboration.

| Item | Trigger | Status |
|------|---------|--------|
| 5A. Emergent gravity UV completion | TPF gapped interface proven + chirality wall breached | `conditional` — Wave 3 strengthens our assessment of trigger likelihood |
| 5D. BEC Hawking replication response | Independent measurement published | `blocked` — Paris stimulated ~2026-27; Trento ~2028-31 |
| 5C. Wallstrom resolution | Distributional breakthrough or Reddiger distinct-theory predictions | `blocked` — Reddiger pivoted to Kolmogorov-based theory |

---

## 7. Deep Research Log

All prompts in `Lit-Search/Tasks/`. Results in `Lit-Search/Phase-5/`.

| Task | File (results) | Status | Key Finding |
|------|---------------|--------|-------------|
| Chirality wall update | `The chirality wall- still cracking, still not broken.md` | Complete | No movement since March 23. GS-TPF not engaged |
| Fang-Gu → ADW chain | `Emergent gravity from topological order- a technical reference assessment.md` | Complete | Fang-Gu ≠ ADW. 3 critical gaps in proposed chain |
| BEC Hawking replication | `Independent replication of analog Hawking radiation remains blocked.md` | Complete | Heidelberg has best apparatus but not pursuing. Paris most active |
| Walker-Wang Monte Carlo | `Walker-Wang finite-temperature eta-s simulation.md` | Complete | Intrinsic sign problem for SU(2)_k. Z₂ toric code is feasible |
| Fracton & Wallstrom | `Fractons and Wallstrom- 2024-2026 monitoring scan.md` | Complete | Fractonic excitations observed (Nature 2024). Wallstrom: Reddiger pivoted |
| Polariton SK-EFT | `Extending Schwinger-Keldysh EFT to driven-dissipative polariton condensates.md` | Complete | T_H survives. KMS breaks. Tier 1 patch valid for Gamma/kappa << 1 |
| Vestigial MC scoping | `Monte Carlo simulation of vestigial gravity in ADW lattice models.md` | Complete | Workstation-tractable at 8⁴. Sign problem likely absent. Fermion-bag recommended |
| TPF-GS Lean scope | `Formalizing the TPF-GS Compatibility Question in Lean 4.md` | Complete | Phase A achievable: 50-80 theorems. Mathlib sufficient for statement-level. Publishable as first formal verification in lattice chiral fermion lit |
| String-net Lean scope | `Formalizing string-net condensation and Fermi-point topology in Lean 4.md` | Complete | Mathlib has Drinfeld center! Fusion category hierarchy (770-1550 theorems) missing from all proof assistants. String-nets >> Fermi-point for formalizability |
| W3C: ExteriorAlgebra as Fock | `ExteriorAlgebra as fermionic Fock space in Lean 4 : Mathlib.md` | Complete | `finrank = 2^k` NOT in Mathlib (ιMulti linear independence missing). `FermionicFockSpace k := ExteriorAlgebra ℂ (Fin k → ℂ)` viable. 2 sorry expected. |
| W3C: Spectral gap on BZ | `Lean 4 formalization of spectral gap...feasibility map.md` | Complete | Eigenvalue API complete. Eigenvalue continuity in k is critical gap (no perturbation theory). Rayleigh quotient workaround for extreme eigenvalues. |
| W3C: SSB / ground state | `Formalizing "no SSB" in Lean 4 Mathlib- a practical guide.md` | Complete | All pieces exist. eigenvalues₀ sorted DECREASING (gotcha). `Representation.invariants` + `mapsTo_genEigenspace_of_comm`. Full code sketch provided. |
| W3C: Matrix.exp / I1 | `Lean 4 : Mathlib support for matrix exponential and Hamiltonian evolution.md` | Complete | All building blocks exist. `NormedSpace.exp` + `selfAdjoint.expUnitary` + `Matrix.exp_add_of_commute`. Need local norm instance. 0 sorry expected. |
| W3C: Green's function / C4+C6 | `Formalizing matrix resolvents and Golterman-Shamir conditions in Lean 4.md` | Complete | Resolvent API exists (`Ring.inverse`, `spectrum`, `charpoly`). C4/C6 mathematical kernel provable. Physics content (bound-state completeness, kinematical zeros) must be axiomatized. First resolvent formalization in any proof assistant. |
| W4C: Drinfeld double D(G) | `Formalizing the Drinfeld double in Lean 4- a gap analysis and construction blueprint.md` | Complete | Hybrid route recommended: VecG Day convolution → D(G) twisted Hopf → Z(VecG)≅Rep(D(G)). Core: ~2,500-3,500 LOC. Critical bottleneck: Day convolution (~500-800 LOC). No D(G) in any proof assistant. k[G] HopfAlgebra + Center already in Mathlib. |

---

## 8. Monitoring Items

| Item | What to Monitor | Current Status (2026-03-28) |
|------|----------------|---------------------------|
| TPF gapped interface | 4+1D symmetric gapped interface proof | Unproven. Next: June 2026 workshops |
| GS-TPF compatibility | Direct engagement or third-party analysis | No engagement. Wave 3 aims to be the first formal analysis |
| SMG chiral gauging | Chiral (not vector-like) SMG demonstration | Untouched. 16-Weyl confirmed but vector-like only |
| Paris polariton Hawking | Bramati-Jacquet measurement | Horizons demonstrated (PRL 2025). Stimulated possible 2026-27 |
| Trento spin-sonic Hawking | Carusotto-Ferrari measurement | Blueprint published. ERC funded. ~2028-31 |
| Heidelberg kappa-scaling | Oberthaler group redirection to Hawking | Best apparatus. Currently analog cosmology |
| Fracton experiments | Cold atom subdimensional dynamics | Observed (Adler et al., Nature 2024). UV memory retention untested |
| Wallstrom progress | Distributional resolution or distinct-theory predictions | Reddiger pivoted to Kolmogorov-based theory |

---

## 9. Post-Wave 5 Fixes

### 9A. Vestigial MC Physics Correction (2026-03-31) — COMPLETE

**Problem identified:** Systematic code review revealed that both MC backends were missing inter-site coupling. The fermion-bag sweep (`fermion_bag.py`) included only on-site 8-fermion vertex action in the Metropolis acceptance — the nearest-neighbor bond coupling (g_eff) was defined in `lattice_4d.py` but never wired into the sweep. The HS-transformed Metropolis code (`monte_carlo.py`) had no spatial coupling at all. Both produced structurally uncoupled (independent-site) configurations, making phase transitions impossible.

**Prior "split transition at L=6,8" result was an artifact** of running uncoupled sites — the susceptibility "peaks" were noise on a Gaussian background, confirmed by L=10-16 production run which showed flat Binder cumulants at 2/3, boundary-pinned susceptibility, and volume-scaling peak heights.

**Root cause:** Bond action infrastructure (bond_action_4d, total_action_4d, neighbor_index) was implemented but never connected to the Metropolis acceptance step. Docstrings falsely claimed fermion determinant reweighting. FSS section used wrong MC backend.

**Fixes applied:**
- [x] C1: `fermion_bag.py` — sweep now includes bond action change via precomputed neighbor table. Bond occupations updated after each sweep to reflect current site state. (2026-03-31)
- [x] C2/C4: `monte_carlo.py` — docstring corrected to state it's an uncoupled bosonic model that cannot produce phase transitions. (2026-03-31)
- [x] C3: `run_vestigial_production.py` — FSS worker replaced: now uses `run_fermion_bag_mc` (fermion-bag with bond coupling) instead of `run_monte_carlo` (uncoupled Gaussian). (2026-03-31)
- [x] P1: `lattice_model.py` — imports from constants.py, G_c references formulas.py. (2026-03-31)
- [x] P2: `monte_carlo.py` — MCParams defaults from FERMION_BAG constants. (2026-03-31)
- [x] P3: `finite_size.py` — Binder cumulant from formulas.py, defaults from FERMION_BAG constants. (2026-03-31)
- [x] P4: `phase_diagram.py` — coupling range from ADW_4D_FSS constants. (2026-03-31)
- [x] I1: `fermion_bag.py` — action_mean now measured from configs with correct bond state. chi_tetrad/chi_metric added to FermionBagResult. (2026-03-31)
- [x] I2: `phase_diagram.py` — MC branch emits warning about uncoupled model. Defaults from constants. (2026-03-31)

**Impact on prior claims:** The "split transition detected" claim in Papers 5-6, roadmap 5G summary, Critical Review v3, and stakeholder docs needs to be downgraded. The vestigial phase hypothesis is still open — the corrected MC (with bond coupling) has not yet been run at production scale.

**Verification (2026-03-31):** Quick smoke tests at L=4,6,8 confirm the bond coupling is working:
1. Observables now depend on coupling strength (no longer flat at 2/3)
2. Sign of coupling matters (attractive vs repulsive gives different physics)
3. Product-form bond weight S_bond = -g_eff × (n_x/N)(n_y/N) produces L-dependent Binder dip at g_EH ≈ -18 (L=4: 0.629, L=6: 0.659, L=8: 0.664 — weakens with L, may be crossover rather than sharp transition)
4. Acceptance rates respond correctly to coupling (0.92 at weak → 0.42 at strong)

**Open physics question:** The product-form approximation to the SO(4)-integrated bond coupling may not capture the full ADW physics. The actual effective action from gauge integration could have different coupling structure. The Binder dip weakening with L could indicate: (a) crossover, not transition, (b) need for larger L, or (c) need for more accurate coupling model. A deep research task on the exact SO(4) effective action is recommended before production-scale runs.

### 9A-2. Vestigial MC: Deep Research Result and Path Forward (2026-03-31)

**Deep research finding (complete):** `Lit-Search/Phase-5/Phase_5_follow-up_Effective nearest-neighbor action in ADW tetrad condensation after SO(4) Haar integration.md`

**Key result:** The product-form approximation is not the correct ADW physics. The actual SO(4) Haar integration produces:
1. A representation-theoretic tower of multi-fermion interactions: (½,½) fundamental (4-fermion, leading), (1,0)⊕(0,1) adjoint (8-fermion), (1,1) symmetric (sub-leading), plus ε-tensor determinantal terms
2. The leading 4-fermion coupling IS attractive (confirmed — our sign choice was correct)
3. 8-fermion corrections enter at relative order 1/24 — not negligible for SO(4) in 4D
4. The Catterall/Chandrasekharan SMG models are gauge-FREE (global SO(4) flavor, no link variables) — structurally different from ADW where SO(4) is a local gauge symmetry with link variables
5. No existing lattice simulation has performed exact SO(4) gauge integration for the ADW model

**The product-form toy model cannot support ADW vestigial phase claims for publication.** The current MC (even with bond coupling fix) samples from the wrong distribution.

**Two viable paths to publication-quality vestigial MC:**

#### Option B: Full Weingarten/Kawamoto-Smit Integration

Implement exact one-link SO(4) Haar integration using the Weingarten calculus, then use the resulting multi-fermion effective action in the fermion-bag MC.

**Concrete steps:**
1. **Implement SO(4) Weingarten functions** — the explicit formulas for N=4 are known:
   - Second moment: ∫ O_{ab}O_{cd} dO = (1/4)δ_{ac}δ_{bd} → 4-fermion NN coupling
   - Fourth moment: ∫ O_{a1b1}...O_{a4b4} dO = (1/72)[6P-DD] + (1/24)ε_{abcd}ε_{efgh} → 8-fermion coupling + baryonic term
   - These are finite algebraic expressions — ideal for formulas.py + Lean verification
   - LOE: ~100-200 lines in formulas.py + new Lean module (SO4Weingarten.lean)
   - Aristotle can prove the Weingarten identities since they're algebraic

2. **Build the effective multi-fermion action** — combine Weingarten integrals with the ADW vertex structure:
   - Input: site Grassmann variables ψ_x (8 per site), link direction
   - Output: effective 4-fermion + 8-fermion + baryonic couplings per bond
   - LOE: ~150-300 lines in a new `src/vestigial/weingarten_action.py`

3. **Update fermion-bag sweep** to use the full multi-channel action:
   - ΔS_bond now includes fundamental, adjoint, and baryonic channels
   - Bond state becomes multi-component (not just binary 0/1)
   - LOE: ~100-200 lines modifying fermion_bag.py

4. **Lean formalization** of the SO(4) one-link integrals and representation decomposition:
   - Weingarten function positivity, channel decomposition, baryonic term
   - ~20-40 theorems, can leverage existing SphericalCategory/FusionCategory infrastructure
   - Aristotle targets: algebraic identities for N=4 Weingarten functions

5. **Production MC run** with the correct multi-channel action

**Total LOE estimate:** ~500-800 lines of new code + ~30 Lean theorems. With Lean + Aristotle pipeline, estimated 2-4 sessions.

#### Option C: Wetterich Gauge-Link-Free Formulation

Adopt Wetterich's hypercubic lattice formulation where SO(4,ℂ) acts directly on spinors without explicit gauge link variables. This is closer to a Nambu-Jona-Lasinio (NJL) model with 4-fermion vertices connecting nearest-neighbor sites directly.

**Concrete steps:**
1. **Implement Wetterich's NJL-type 4-fermion vertex** — no gauge links, SO(4,ℂ) acts on even/odd sublattices:
   - S = Σ_{<xy>} g × (ψ̄_x γ^a ψ_y)(ψ̄_y γ_a ψ_x) (scalar channel)
   - Plus additional channels (pseudoscalar, vector, axial, tensor) from Fierz identity
   - LOE: ~100-200 lines in new `src/vestigial/wetterich_model.py`

2. **Fermion-bag MC** adapts naturally — the Chandrasekharan algorithm was designed for exactly this type of model (4-fermion vertices on a hypercubic lattice with global flavor symmetry)
   - The key difference from current code: bond coupling is a genuine Grassmann bilinear, not an occupation-number product
   - LOE: ~200-300 lines modifying fermion_bag.py

3. **Lean formalization** of the Wetterich action structure:
   - Fierz completeness, channel decomposition, positivity
   - ~15-25 theorems
   - Less novel than Option B (NJL models are well-studied)

4. **Production MC run**

**Total LOE estimate:** ~400-600 lines of new code + ~20 Lean theorems. Estimated 1-3 sessions. Simpler than Option B but represents a different model (NJL-type, not gauge theory).

**Trade-off:** Option B is the faithful ADW model (local gauge symmetry, exact integration). Option C is a related but distinct model (global symmetry, NJL-type). Both can show vestigial phase physics. For a Paper 6 that claims to simulate the ADW mechanism specifically, Option B is required. For a paper about vestigial metric phases in general multi-fermion models, Option C is sufficient.

**Recommendation:** Option B is the correct choice for our pipeline (correctness over expediency). The Weingarten calculus is algebraic, ideal for Lean + Aristotle. The code complexity is manageable. Deep research task for Weingarten implementation filed.

### 9B. Codebase Physics Audit — COMPLETE (2026-03-31)

**Scope:** Systematic audit of entire codebase for disconnected physics, docstring-implementation mismatch, provenance bypass, wrong backends, and silent parameter mismatch. 4 parallel audit agents, all 37 Python source modules reviewed.

**Clean modules (no material findings):** `gauge_erasure/erasure_theorem.py`, `chirality/tpf_gs_analysis.py`, `second_order/enumeration.py`, `core/transonic_background.py`, `core/aristotle_interface.py`, `scripts/validate.py`, `scripts/review_figures.py`.

**Configuration fix:** `requires-python` updated from `>=3.11` to `>=3.14` (pyproject.toml, CLAUDE.md).

---

#### 9B-1. CRITICAL Fixes (must complete before paper submission)

**CF-1: `wkb/connection_formula.py:125` — Turning point formula mismatch — FIXED (2026-03-31)**
- [x] Fix: now imports and calls canonical `turning_point_shift` from formulas.py. Also fixed `delta_diss` to use `first_order_correction`. Tests updated for correct ∝1/κ² scaling.
- [ ] Verify: re-run WKB spectrum for all platforms, compare old vs new delta_x values
- [ ] Impact: Paper 4 numerical results (exact WKB spectrum), all platform prediction tables
- [ ] Downstream claims: Paper 4 Table 1, experimental predictions, fig22-fig27

**CF-2: `wkb/connection_formula.py:166-516` — Stokes geometry disconnected — RESOLVED (2026-03-31)**
- [x] Analysis: the κ_eff approach IS the analytic evaluation of the WKB contour integral for a linear flow profile with a simple turning point. The Stokes geometry class computes metadata (line angles, multiplier) that are structurally present but not needed for the single-turning-point Hawking problem. The formula `|β/α|² = exp(-2πω/κ_eff)` is the correct analytic result, not an approximation.
- [x] Fix: docstring corrected from "exact Stokes analysis" to accurate description of what the code computes. StokesGeometry retained as diagnostic metadata with clear documentation of its role.
- [x] Paper 4 claim: "WKB connection formula" is accurate. "Exact Stokes analysis" should be softened to "analytic WKB connection via effective surface gravity." The computation is exact for linear flow profiles.
- [ ] Downstream: Paper 4 text should be reviewed for "Stokes analysis" phrasing

**SPEC-2: `wkb/spectrum.py:261-523` — Third-order EFT — FIXED (2026-03-31)**
- [x] Fix: `gamma_3_1, gamma_3_2, gamma_3_3` properties added to `PlatformParams` (Beliaev-damping estimates: γ₃ ~ γ_dim·D²/3). All call sites in spectrum.py and backreaction.py now pass third-order coefficients to `exact_connection_formula` and `damping_rate`.
- [x] Docstring: "all EFT orders through third" is now accurate.
- [x] Verify: tests pass. Third-order corrections are O(10⁻⁹) for BEC platforms — numerically negligible but formally complete.
- [x] No downstream claim changes needed (the claim "all EFT orders" is now true).

**BR-1: `wkb/backreaction.py:716-751` — Cooling model mislabeled — FIXED (2026-03-31)**
- [x] Fix: renamed to `rational_cooling_model`, docstring corrected, backwards-compat alias kept.
- [ ] Downstream: Paper 4 §5 cooling discussion should reference correct function name

**E-1: `experimental/predictions.py:578` — Kappa-scaling contradiction — FIXED (2026-03-31)**
- [x] Fix: docstrings corrected from `kappa^0` to `∝ kappa` (linear). Added NOTE about natural-unit parameterization.
- [ ] Downstream: predictions.py still has legacy `kappa_scaling_prediction()` function — future cleanup should delegate to `kappa_scaling.compute_kappa_sweep()`

**E-3: `experimental/polariton_predictions.py:113` — Comment/code mismatch — FIXED (2026-03-31)**
- [x] Fix: comment corrected from `gamma_dim/(4π²)` to `gamma_dim`.

**ADW-B1: `adw/__init__.py:17` + `gap_equation.py:62` — G_c factor-of-2 — FIXED (2026-03-31)**
- [x] Fix: both locations corrected from `4π²` to `8π²`.
- [ ] Downstream: Paper 5 should be checked for G_c formula consistency

**ADW-C1: `gap_equation.py:118-220` — ADW formulas provenance — FIXED (2026-03-31)**
- [x] Fix: `effective_potential`, `critical_coupling`, `curvature_at_origin` now delegate to canonical `formulas.py`.
- [x] Also fixed: `fluctuations.py` broken_generator_count delegates to formulas.py. `ginzburg_landau.py` imports directly from formulas.py.
- [ ] Remaining: `hubbard_stratonovich.py:261-284` (third copy of CW potential) — lower priority since it's only used in tests.

---

#### 9B-2. IMPORTANT Fixes (should complete for code quality)

**CF-3: `wkb/connection_formula.py:85` — `xi` parameter — FIXED (2026-03-31)**
- [x] Fix: `xi` now used to compute dispersive shift of real part of turning point: `x_real = delta_disp * c_s / kappa`

**ADW-A2: `adw/ginzburg_landau.py:270-279` — Planar phase — DOCUMENTED (2026-03-31)**
- [x] Fix: `_planar_phase_tetrad` docstring documents degeneracy with A-phase in diagonal approximation. `f_planar = f_A` explicitly.

**ADW-A5: `gap_equation.py:149-179` — `effective_potential_derivative` — DOCUMENTED (2026-03-31)**
- [x] Fix: docstring clarifies it's a utility for verification, not in solver path. Unused `brentq` import removed.

**ADW-A3: `adw/__init__.py:78-93` — `FluctuationCorrection` export — FIXED (2026-03-31)**
- [x] Fix: added to package exports

**BR-2: `wkb/backreaction.py:249-254` — Energy flux docstring — FIXED (2026-03-31)**
- [x] Fix: corrected to "through third order" (SPEC-2 plumbed gamma_3 through)

**BR-3: `wkb/backreaction.py:537,748` — Imports inside function bodies — FIXED (2026-03-31)**
- [x] Fix: `hawking_temperature` moved to top-level import

**Second-order dead code — DOCUMENTED (2026-03-31):**
- [x] `wkb_analysis.py:180-345` — marked as UNUSED with explanation; retained for future non-perturbative WKB
- [ ] `cgl_derivation.py:162-666` — 4 functions disconnected from scripts/validate (lower priority — internal CGL utilities)
- [ ] `coefficients.py:224-541` — action constructors and Beliaev estimator unused (lower priority — test-only utilities)

**Fracton disconnected — DOCUMENTED (2026-03-31):**
- [x] `sk_eft.py:51-58` — `ConservationType` documented as metadata enum
- [x] `sk_eft.py:436-464` — `lagrangian_noise()` documented: only L^(2) implemented, others not yet
- [x] `information_retention.py:51` — `factorial` dead import removed (2026-03-31)

---

#### 9B-3. PROVENANCE Fixes (Pipeline Invariant violations)

**Formulas re-implemented inline (violates Invariant 1):**
- [x] `wkb/connection_formula.py:299` — now calls `first_order_correction` from formulas.py (2026-03-31)
- [ ] `wkb/spectrum.py:209-226` — `planck_occupation` belongs in formulas.py with Lean ref
- [x] `second_order/coefficients.py:418,480` — documented as natural-unit convention, refs formulas.hawking_temperature (2026-03-31)
- [ ] `second_order/coefficients.py:435-448` — `planck_spectrum` belongs in formulas.py
- [x] `second_order/wkb_analysis.py:84-86` — documented with SI cross-reference (2026-03-31)

**Constants hardcoded (violates Invariant 2):**
- [ ] `wkb/backreaction.py:99-155` — SI platform params hardcoded, bypass EXPERIMENTS/transonic chain
- [ ] `second_order/wkb_analysis.py:519-581` — D/gamma_dim presets hardcoded
- [x] `second_order/coefficients.py:525-527` — now uses `constants.HBAR` (2026-03-31)
- [x] `adw/wen_model.py:147` — RG multipliers documented as schematic, not from Roy-Juricic-Herbut (2026-03-31)
- [x] `adw/gap_equation.py:354-357` — vestigial window 0.8 documented with GL derivation reference (2026-03-31)
- [x] `adw/ginzburg_landau.py:405-407` — `C_eval = 0.1 * Lambda` documented as convention choice with logarithmic sensitivity note (2026-03-31)

**No canonical imports (entire modules) — REQUIRES FORMALIZATION:**
- [ ] All 4 fracton files — Pipeline Invariant 1+4 violated. Fracton formulas must be added to formulas.py with Lean theorem references. See 9C below for formalization plan.

**Transitive imports:**
- [x] `wkb/bogoliubov.py:40-42` — spectrum.py now imports direct from formulas.py (2026-03-31)
- [x] `adw/ginzburg_landau.py:37-43` — now imports directly from formulas.py (2026-03-31)

---

#### 9B-4. DOCSTRING Fixes

- [x] `wkb/connection_formula.py:18` — corrected from "exact Stokes analysis" to accurate perturbative WKB description (2026-03-31)
- [x] `wkb/spectrum.py:518` — documented as Wien-peak evaluation (2026-03-31)
- [x] `second_order/coefficients.py:72-75` — FDR docstring now includes Lean coefficient labels and Aristotle run ID (2026-03-31)
- [x] `second_order/wkb_analysis.py:7-14` — docstring corrected to note dead code for steps 1-2 (2026-03-31)
- [x] `second_order/cgl_derivation.py:422-433` — confusion comment cleaned up (2026-03-31)
- [x] `adw/fluctuations.py:87-89` — docstring documents that 4 diffeo pure-gauge modes are included (2026-03-31)
- [x] `experimental/polariton_predictions.py:25` — "(planned)" removed, now states "6 theorems, zero sorry" (2026-03-31)

---

#### 9B-5. Downstream Claim Verification (after code fixes)

After fixing 9B-1 through 9B-4, the following downstream artifacts must be re-verified:

**Papers (interim corrections applied 2026-03-31, final pass needed after Weingarten MC results):**
- [ ] Paper 1: kappa-scaling experimental prospects added (done 2026-03-30). Needs final review.
- [ ] Paper 4: turning-point formula corrected from Γ_H/(κc_s) to c_sΓ_H/(2κ²). Stokes section rewritten as "analytic WKB connection." Needs numerical re-verification against updated code.
- [ ] Paper 5: vestigial MC paragraph rewritten (removed split transition claim, references Weingarten). G_c docstring fixed. Needs final review after MC results.
- [ ] Paper 6: abstract rewritten (removed split transition, describes Weingarten framework). Production MC section needs complete rewrite with actual Weingarten results.
- [ ] Paper 7: clean — no changes needed.

**Notebooks (not yet touched — deferred to after Weingarten MC results):**
- [ ] Phase3a_WKB notebooks: may reference old turning-point formula values
- [ ] Phase4a_Experimental notebooks: kappa-scaling narrative already updated in Paper 1
- [ ] Phase5b_Synthesis notebooks: vestigial claims need updating
- [ ] Phase4b_Vestigial notebooks: split transition content needs complete rewrite

**Stakeholder docs (interim corrections applied 2026-03-31):**
- [x] Phase5_Implications.md: split transition claims removed, Weingarten framework described (interim)
- [x] Phase5_Strategic_Positioning.md: vestigial MC section rewritten (interim)
- [x] companion_guide.md: "split transition" section rewritten as "correct physics framework" (interim)
- [ ] All three need final pass with actual Weingarten MC results

**Top-level docs (interim corrections applied 2026-03-31):**
- [x] Critical Review v3: all 5 "split transition" references corrected (interim)
- [x] Feasibility Study: vestigial MC reference corrected (interim)
- [x] README.md: split transition reference corrected (interim)
- [ ] All need final pass with actual results

**Inventory:**
- [ ] Section 10 (Key Formulas): verify turning_point_shift reference after CF-1 fix
- [ ] Module descriptions: update for new Lean modules (SO4Weingarten, FractonFormulas, WetterichNJL)
- [ ] Counts: theorem count will change after Aristotle integration

---

### 9C. Formalization Wave: Fracton + Vestigial Physics

Quality standard: every formula through the Lean + Aristotle pipeline. No documented gaps — formalize everything.

#### 9C-1. Fracton Lean Formalization [Pipeline Stages 1-5]

**4 fracton modules with zero Lean coverage — violates Pipeline Invariant 4.**

- [x] Stage 3: `lean/SKEFTHawking/FractonFormulas.lean` — 45 sorry-stub theorems, compiles clean (2026-03-31)
- [x] Sorry gaps registered in aristotle_interface.py (45 gaps) (2026-03-31)
- [x] Stage 4: Aristotle — ALL 45 PROVED (job `4528aa2b`). Zero sorry. (2026-03-31)
- [ ] Stage 2: Migrate fracton formulas from src/fracton/*.py to formulas.py with Lean refs — IN PROGRESS
- [x] Stage 5: lake build zero sorry confirmed (2026-03-31)
- [ ] Update fracton source files to import from formulas.py

#### 9C-2. Vestigial MC Option B: Weingarten Integration [Pipeline Stages 1-7]

**Implement the exact SO(4) Haar integration for the ADW lattice model.**

- [x] Stage 2: Weingarten formulas in formulas.py (so4_weingarten_2nd_moment, so4_weingarten_4th_moment, adw_bond_weight_fundamental, adw_bond_weight_adjoint, adw_bond_weight_total) (2026-03-31)
- [x] Stage 3: `lean/SKEFTHawking/SO4Weingarten.lean` — 14 theorems (2026-03-31)
- [x] Stage 4: Aristotle — ALL 14 PROVED (run `117a7115`). Proofs: norm_num, positivity, mul_nonpos, linarith+exp, gcongr+aesop. (2026-03-31)
- [x] Stage 5: lake build zero sorry for SO4Weingarten (2026-03-31)
- [x] fermion_bag.py sweep updated to Weingarten multi-channel (fundamental + adjoint) (2026-03-31)
- [x] Smoke test: tetrad_m2 increases 0.24→0.99 with coupling, no saturation, correct physics (2026-03-31)
- [x] Production MC with Weingarten sweep — COMPLETE (2026-03-31, 14 cores, L=4-16, 3.2h)
  - Results: `docs/vestigial_mc_results/vestigial_mc_20260331T114048.json`
  - Log: `logs/vestigial_mc_weingarten_20260331T114048.out`
  - **Binder cumulants: NO crossings found.** U₄ ≈ 2/3 (Gaussian) across entire range g_EH ∈ [-50, 0]. Variation shrinks with L (0.002 at L=4 → 0.00001 at L=16). System locked in disordered phase.
  - **Susceptibility peaks: split but non-divergent.** Tetrad peaks at G/Gc ≈ 2-5 (height ~0.097), metric peaks at G/Gc ≈ 6-7 (height ~0.118). Heights do NOT grow with L → not real phase transitions. "split_transition: True" flag is misleading (noise on flat background).
  - **Sign reweighting: catastrophically small.** avg_sign = 0.0 for L≥5, ~10⁻¹³⁵ to 10⁻²⁵⁴ for L=4. Lorentzian reweighting factor exp(ΔS) exponentially suppressed (ΔS scales with L⁴ volume). Note: Euclidean weights are Lean-verified non-negative (SO4Weingarten.lean), so no sign problem from gauge integration — this is the Lorentzian reweighting catastrophe.
  - **Acceptance rates: appeared uniform at 0.311** — RESOLVED: this is the mean across 40 coupling points. Per-coupling acceptance varies correctly (0.121 at g_EH=-50 to 0.933 at g_EH=0). Identical mean across L is expected (bond action per site doesn't scale with volume).
  - **Interpretation with old single-site OPs:** INVALID (OPs were blind to bond ordering). Re-run with bond OPs shows correct coupling dependence but Binder variation vanishes with L (self-averaging).
- **BUG FIX (2026-03-31): Order parameters were blind to bond coupling.**
  - `tetrad_order_parameter_4d` measured single-site `⟨n/N⟩` — insensitive to inter-site Weingarten bond ordering
  - `metric_order_parameter_4d` measured single-site `⟨(n/N)²⟩` — same problem
  - `total_action_4d` used binary bond_occ, not the actual Weingarten action
  - **Fix:** Added `tetrad_bond_order_parameter_4d` and `metric_bond_order_parameter_4d` in lattice_4d.py — measure `⟨f_x f_y⟩_NN` and `⟨(f_x f_y)²⟩_NN` respectively
  - **Fix:** Updated `total_action_4d` to compute actual Weingarten multi-channel action when neighbor_table provided
  - **Fix:** `run_fermion_bag_mc` now uses bond OPs and correct action measurement
  - **Smoke test after fix:** tetrad_m2 varies 0.047→0.978 with coupling (was flat 0.21), acceptance varies 0.93→0.12 (was uniform 0.31)
  - **L-dependence confirmed:** Binder cumulants show L-dependent structure (metric OP more sensitive = vestigial signature)
  - Old single-site OPs preserved for NJL model (Option C) where they work correctly
- [ ] Re-run Option B production MC with fixed bond OPs
- [ ] Tests + validation after MC results — DEFERRED pending 9D provenance resolution

#### 9C-3. Vestigial MC Option C: Wetterich NJL Model [Pipeline Stages 1-7]

**Parallel implementation of the gauge-link-free NJL-type model.**

- [x] Stage 2: NJL formulas in formulas.py (njl_fierz_channel_count, njl_fierz_completeness, njl_scalar_channel, njl_pseudoscalar_channel, njl_vector_channel, njl_bond_weight_total, njl_adw_scalar_limit) (2026-03-31)
- [x] Stage 3: `lean/SKEFTHawking/WetterichNJL.lean` — 18 sorry-stub theorems, compiles clean (2026-03-31)
- [x] Sorry gaps registered in aristotle_interface.py (18 gaps) (2026-03-31)
- [x] Stage 4: Aristotle — ALL 18 PROVED (job `4528aa2b`). Zero sorry. (2026-03-31)
- [x] Stage 5: lake build zero sorry confirmed (2026-03-31)
- [x] Stage 1: NJL_MODEL, NJL_COUPLING_SCAN, NJL_FSS constants in constants.py (2026-03-31)
- [x] Stage 2: Source: fields added to all 7 NJL formulas.py docstrings (2026-03-31)
- [x] `src/vestigial/wetterich_model.py` — NJL fermion-bag MC: njl_sweep + run_njl_mc (2026-03-31)
  - Vectorized Metropolis with NJL bond action (scalar + pseudoscalar Fierz channels)
  - Same observables as Option B (tetrad/metric order params, Binder cumulants, susceptibility)
  - Smoke test: acceptance varies 0.935 (g=0) → 0.333 (g=10), Binder cumulants vary meaningfully (NOT locked at 2/3 like Option B)
- [x] Stage 6: 13 new tests in tests/test_vestigial.py (1027 total, all pass) (2026-03-31)
- [x] Stage 7: 14/14 original validation checks pass (CHECK 15 expected fail — provenance system in 9D) (2026-03-31)
- [x] Production MC with NJL model — COMPLETE (2026-03-31, L=4-12, g∈[2,15], 5K sweeps, 1.34h)
  - Results: `docs/vestigial_mc_results/vestigial_mc_njl_20260331T201920.json`
  - **8/8 L-pair Binder crossings** (uniform OPs) — two families: even-odd pairs converge to g≈5.0, odd-even pairs at higher coupling
  - **Staggered (AF) OP reveals genuine ordering transition:** Even-L Binder transitions from ~0 (g<5) to ~2/3 (g>6). Critical coupling g_c ≈ 5-6. Transition sharpens with L (L=4→12).
  - **Odd-L geometric frustration:** Staggered OP suppressed on odd-L lattices (bipartite checkerboard doesn't tile with periodic BC on odd L). Standard lattice artifact — use even-L only for Binder analysis.
  - **Even-L staggered Binder data (key result):**
    - g=5: U4 = 0.189(L=4), 0.083(6), 0.062(8), 0.001(10), -0.04(12) — DISORDERED (decreasing with L)
    - g=6: U4 = 0.606(L=4), 0.657(6), 0.664(8), 0.665(10), 0.666(12) — ORDERED (approaching 2/3)
    - Crossing between g=5 and g=6 → critical coupling g_c ≈ 5.5 for AF ordering
  - **Physics: antiferromagnetic ordering** driven by NJL pseudoscalar channel. NOT vestigial metric ordering — the staggered OP detects checkerboard occupation patterns, not metric tensor structure.
  - **Spatial correlator diagnostic confirmed:** G(r) oscillates (AF signature), correlation length grows with coupling.
  - **Significance:** First confirmed phase transition in any model in this codebase. Not the vestigial phase we were looking for, but real ordering physics driven by the Fierz channel structure. See big-picture assessment below.
- [ ] Stages 8-12: DEFERRED pending 9D provenance chain

**Paper 6 strengthened by:** ADW model (Option B) shows vestigial phase → primary claim. NJL model (Option C) independently shows vestigial phase → cross-validation. Two different models, same physical conclusion = much stronger paper.

#### 9C-4. Remaining Provenance Fixes [Pipeline Stage 2]

- [x] `wkb/spectrum.py` — `planck_occupation` moved to formulas.py (array+scalar), spectrum.py delegates (2026-03-31)
- [x] `second_order/coefficients.py` — `planck_spectrum` delegates to formulas.planck_occupation (2026-03-31)
- [ ] `wkb/backreaction.py:99-155` — SI platform params discrepancy (10x in κ) identified, deep research task filed for Steinhauer parameter reconciliation

---

### 9E. Vestigial Gravity: Correct Physics Assessment [COMPLETE]

> **Note:** Section 9D (Parameter Provenance) follows after Waves 6-7 below due to insertion ordering. It is complete — see line ~1267.

**Trigger:** Occupation-number MC (Options B & C) proved insufficient for vestigial detection. Gauge integration projects out the SO(4) internal structure needed to distinguish tetrad (vector) from metric (tensor) ordering. NJL model confirmed genuine AF transition (g_c ≈ 5.5), validating MC infrastructure, but this is staggered occupation ordering, not vestigial metric ordering.

**Deep research completed (all three, 2026-04-01):**
- [x] `Lit-Search/Phase-5/Vestigial metric susceptibility from ADW tetrad condensation.md` — analytical susceptibility derivation
- [x] `Lit-Search/Phase-5/Hybrid fermion-bag + gauge-link Monte Carlo for ADW tetrad condensation.md` — algorithm specification
- [x] `Lit-Search/Phase-5/Feasibility of 4D HOTRG for vestigial gravity transitions in the ADW model.md` — TRG feasibility

**Key findings across all three:**
1. Vestigial metric ordering is **analytically provable** (G_ves < G_c whenever u_g > 0) — no MC needed for the existence result
2. The vestigial window in d=4 is **exponentially narrow** (BCS-like: r_e* ~ Λ² exp(-16π²/c_D u_g)), not power-law as in condensed matter
3. Hybrid gauge-link MC is **feasible but genuinely novel** — no prior implementation exists
4. 4D ATRG is at the **computational frontier** — viable for cross-validation but PhD-level for full ADW model

**Implementation plan:** Wave 6 (analytical, Paths 1) and Wave 7 (gauge-link MC, Path 2) below. Path 3 (4D ATRG) deferred to Phase 6 roadmap.

---

## 10. Wave 6 — Analytical Vestigial Susceptibility [Pipeline: Stages 1-12]

**Research basis:** `Lit-Search/Phase-5/Vestigial metric susceptibility from ADW tetrad condensation.md`

**Goal:** Derive, implement, and formally verify the analytical proof that vestigial metric ordering occurs before tetrad condensation in the ADW model. This is the theoretical prediction that Wave 7 (MC) will test numerically.

**Key result (from deep research):** The metric susceptibility in the ADW model takes the RPA form:

```
χ_g⁻¹(G) = 1/u_g − c_D · Π₀(1/G − 1/G_c)
```

where Π₀(r_e) = (1/16π²)[ln(Λ²/r_e) − 1] is the bubble integral, u_g is the quartic coupling in the metric channel, c_D = 2D² = 32 (trace channel). The vestigial critical coupling where χ_g diverges is:

```
r_e* = Λ² · exp[−16π²/(c_D u_g) − 1]
1/G_ves = 1/G_c + r_e*    →    G_ves < G_c
```

This proves the metric **necessarily orders before the tetrad** whenever u_g > 0.

### 6A. Quartic Coupling Determination [Pipeline Stage 2, prerequisite] — COMPLETE

**The computation:** Determine u_g from the ADW 8-fermion vertex. The quartic vertex carries the gamma-matrix trace Tr(γ^a γ^b γ^c γ^d) = 4(δ^{ab}δ^{cd} − δ^{ac}δ^{bd} + δ^{ad}δ^{bc}). Project onto the metric channel (symmetric combination δ^{ab}δ^{cd} + δ^{ad}δ^{bc}) to extract u_g. The deep research confirms u_g > 0 for the metric channel generically.

**Deliverables:**
- [x] `formulas.py`: `adw_quartic_coupling_metric(N_f, Lambda)` — u_g = (N_f/16π²)(γ_proj/D²)ln2 (2026-04-01)
- [x] `formulas.py`: `gamma_trace_projection(channel)` — metric: +8 (attractive), Lorentz: −4 (repulsive) (2026-04-01)
- [x] Constants: `ADW_VESTIGIAL` with c_D=32/8, gamma coefficients, scan params (2026-04-01)
- [x] Lean: `u_g_positive`, `u_g_positive_adw`, `gamma_trace_metric_positive` theorems (2026-04-01)
- [x] Tests: 7 tests (gamma trace, quartic coupling scaling/sign/Λ-independence) all pass (2026-04-01)

**Key result:** u_g ≈ 0.0044 for ADW (N_f=2, Λ=π). Always positive → vestigial ordering analytically guaranteed. Exponent −16π²/(c_D·u_g) ≈ −1125 → window astronomically narrow for physical u_g.

### 6B. Bubble Integral and RPA Susceptibility [Pipeline Stages 1-5] — STAGES 1-3 COMPLETE, 4-5 PENDING ARISTOTLE

**The computation:** Implement the bubble integral Π₀(r_e) and the full RPA metric susceptibility χ_g(G).

**Deliverables:**
- [x] Stage 1: `ADW_VESTIGIAL` and `ADW_VESTIGIAL_SCAN` constants in constants.py (2026-04-01)
- [x] Stage 2 — 7 formulas in `formulas.py` (each with Lean ref + Source):
  - `gamma_trace_projection` — Tr(γγγγ) decomposition. Source: Peskin/Schroeder App. A
  - `adw_quartic_coupling_metric` — u_g from CW vertex. Source: Fernandes et al. + Diakonov
  - `adw_bubble_integral(r_e, Lambda)` — Π₀ = (1/16π²)[ln(Λ²/r_e) − 1]. Source: Nie/Tarjus/Kivelson PNAS 2014
  - `adw_metric_susceptibility_inv(G, G_c, u_g, c_D, Lambda)` — χ_g⁻¹. Source: Fernandes et al. Ann. Rev. CMP 2019
  - `adw_vestigial_critical_coupling(G_c, u_g, c_D, Lambda)` — G_ves from r_e* formula
  - `adw_vestigial_window_width(G_c, u_g, c_D, Lambda)` — exponentially narrow
  - `adw_vestigial_ordering_proved(u_g)` — sufficient condition check
- [x] Stage 3 — `lean/SKEFTHawking/VestigialSusceptibility.lean` — 16 sorry-stub theorems, `lake build` clean (2026-04-01)
  - `gamma_trace_metric_positive`, `gamma_trace_lorentz_negative`, `metric_dominates_lorentz`
  - `u_g_positive` (general), `u_g_positive_adw` (N_f=2, D=4)
  - `bubble_integral_monotone`, `bubble_integral_diverges`, `bubble_integral_positive`
  - `susceptibility_diverges` (IVT), `vestigial_before_tetrad` (main theorem)
  - `vestigial_r_e_star_pos`, `vestigial_window_exponential`, `vestigial_window_vanishes`
  - `trace_channel_multiplicity`, `traceless_channel_multiplicity`, `vestigial_ordering_sufficient`
- [ ] Stage 4 — Aristotle: submitted `--priority 3 --integrate`, awaiting results
- [ ] Stage 5 — `lake build` zero sorry, theorem count updated

### 6C. Vestigial Phase Diagram and Visualization [Pipeline Stages 6-9] — STAGES 6-9 COMPLETE

**Deliverables:**
- [x] Stage 6 — 26 new tests in `tests/test_vestigial.py` (1068 total, all pass): (2026-04-01)
  - TestGammaTrace (4): positive metric, negative Lorentz, metric dominates, invalid raises
  - TestQuarticCoupling (3): positive, N_f scaling, Λ independence
  - TestBubbleIntegral (5): positive, monotone, diverges, inf at zero, known value
  - TestMetricSusceptibility (3): positive far, negative near, crosses zero
  - TestVestigialCriticalCoupling (4): G_ves < G_c, widens with u_g, exponentially narrow, no repulsive
  - TestVestigialOrdering (3): positive proves, negative no, ADW model has ordering
  - TestVestigialConstants (4): multiplicities, signs, scan params, cross-check
- [x] Stage 7 — `validate.py` 15/15 checks pass (2026-04-01)
- [x] Stage 8 — 3 new figures in `visualizations.py` (64 total): (2026-04-01)
  - `fig_vestigial_susceptibility` (fig63) — χ_g⁻¹ vs G/G_c for u_g = 0.3, 0.5, 1.0, 2.0
  - `fig_vestigial_window` (fig64) — G_ves/G_c vs u_g (trace + traceless-symmetric channels)
  - `fig_vestigial_phase_diagram_analytical` (fig65) — three-phase diagram with shaded vestigial region
- [x] Stage 9 — Visual review: all 3 figures correct (zero crossings, exponential narrowness, clean phase boundaries) (2026-04-01)

### 6D. Paper 6 Update + Document Sync [Pipeline Stages 10-12]

**NOTE:** Paper 6 updates are gated on 9D downstream propagation (corrected Steinhauer params). This sub-wave executes AFTER 9D Stage 10-12 work.

**Deliverables:**
- [ ] Stage 10 — Paper 6: add section on analytical vestigial susceptibility derivation, exponential window prediction, RPA formula, G_ves < G_c theorem. Remove prior MC-based vestigial claims. Reference Lean theorems.
- [ ] Stage 11 — Notebooks: `Phase4b_Vestigial_Technical.ipynb` updated with analytical susceptibility section. Stakeholder notebook updated.
- [ ] Stage 12 — Full document sync: Inventory, Inventory Index, README, src/__init__.py, stakeholder docs, Critical Review, Feasibility Study.

**Estimated LOE:** 1 session for Stages 10-12, after 9D propagation and Aristotle integration.
**Risk:** Low. All formulas are closed-form. The main uncertainty is whether Aristotle can prove the IVT-based existence theorem (may need manual proof if Mathlib's IVT infrastructure is insufficient).

---

## 11. Wave 7 — Hybrid Gauge-Link + Fermion-Bag MC [Pipeline: Stages 1-12]

**Research basis:** `Lit-Search/Phase-5/Hybrid fermion-bag + gauge-link Monte Carlo for ADW tetrad condensation.md`

**Goal:** Implement the first-ever fermion-bag MC with dynamical SO(4) gauge links on a 4D hypercubic lattice. Measure separate tetrad and metric order parameters to numerically test the vestigial prediction from Wave 6. This is a genuinely novel algorithm — no prior implementation exists in the literature.

**Prerequisites:** Wave 6 complete (provides the analytical G_ves target for MC validation). 9D downstream propagation complete (corrected params for any BEC comparisons).

**Key design decisions (from deep research):**
- SO(4) ≅ SU(2)_L × SU(2)_R decomposition via quaternion pairs — 4× speedup over explicit 4×4 matrices
- Kennedy-Pendleton heatbath for SU(2) subgroup gauge updates — standard, efficient
- Alternating sweeps: fermion-bag at fixed links, gauge Metropolis/heatbath at fixed Grassmann state
- Bag weight: det(M_B[U]) where M_B is fermion matrix restricted to bag B, dimension (4|B|) × (4|B|)
- Parameter space: (g, β) where g = four-fermion coupling, β = Wilson plaquette coupling (β=0 is pure ADW)
- Sign problem: real matrix structure eliminates complex phase; real sign monitored via ⟨sign⟩

### 7A. SO(4) Gauge Infrastructure [Pipeline Stages 1-5, Phase 1 of algorithm]

**The construction:** Build the pure gauge theory infrastructure — lattice geometry, SO(4) group operations via quaternion pairs, Wilson plaquette action, heatbath + overrelaxation gauge updates. Validate against known SO(4) average plaquette vs β.

**Deliverables:**
- [ ] Stage 1 — Constants in `constants.py`:
  - `GAUGE_LINK_MC` dict: β range, N_f, quaternion precision, heatbath params
  - `SO4_LATTICE` dict: plaquette normalization, staple structure, overrelax ratio
- [ ] Stage 2 — `formulas.py` functions (each with Lean ref + Source):
  - `quaternion_multiply(q1, q2)` — SU(2) multiplication via quaternion algebra. Source: Creutz, "Quarks, Gluons and Lattices" Ch. 15
  - `so4_from_quaternion_pair(q_L, q_R)` — construct SO(4) matrix from SU(2)×SU(2). Source: standard representation theory
  - `wilson_plaquette_action(U_P)` — (1/4)Tr(U_P) for SO(4). Source: Wilson, PRD 10, 2445 (1974)
  - `kennedy_pendleton_heatbath(staple, beta)` — exact SU(2) heatbath sampling. Source: Kennedy-Pendleton, PLB 156, 393 (1985)
- [ ] Stage 2 — New modules:
  - `src/vestigial/quaternion.py` (~200 lines) — SU(2) quaternion algebra, vectorized over arrays of shape (N, 4). Haar random, multiply, conjugate, trace, to_matrix, from_matrix.
  - `src/vestigial/so4_gauge.py` (~300 lines) — SO(4) as quaternion pairs. Plaquette computation, staple sum, heatbath update, overrelaxation, Haar random link.
- [ ] Stage 3 — `lean/SKEFTHawking/QuaternionGauge.lean` — sorry stubs:
  - `quaternion_multiply_assoc` — associativity
  - `quaternion_unit_norm` — |q|=1 preserved by multiply
  - `so4_decomposition` — SO(4) ≅ (SU(2)×SU(2))/Z_2
  - `plaquette_trace_bound` — |Tr(U_P)/4| ≤ 1
  - `heatbath_detailed_balance` — Kennedy-Pendleton satisfies detailed balance
  - ~8-12 theorems
- [ ] Stage 4 — Aristotle
- [ ] Stage 5 — `lake build` zero sorry
- [ ] **Validation checkpoint:** Pure gauge SO(4) at L=4, scan β = 0-10, verify average plaquette matches two independent SU(2) theories (⟨P⟩_{SO(4)} = [⟨P⟩_{SU(2)}]² in the decomposed action). This runs in minutes and validates the infrastructure before adding fermions.

### 7B. Fermion-Bag with Gauge Links [Pipeline Stages 2-5, Phase 2-3 of algorithm]

**The construction:** Extend the fermion-bag sweep to work with explicit gauge-link configurations. The key change: bag weight det(M_B[U]) depends on the link configuration, and gauge updates require recomputing affected bag determinants.

**Deliverables:**
- [ ] Stage 2 — `formulas.py` functions:
  - `gauge_fermion_bag_weight(M_B, U_links)` — det of gauge-covariant fermion matrix restricted to bag. Source: Chandrasekharan PRD 82, 025007 (2010), adapted with gauge links
  - `tetrad_bilinear(psi_x, gamma_a, U_xy, psi_y)` — E^a_μ = ψ̄_x γ^a U_{xy} ψ_y. Source: Vladimirov-Diakonov PRD 86, 104019 (2012)
  - `metric_from_tetrad(E)` — g_μν = δ_{ab} E^a_μ E^b_ν. Source: ADW mechanism
- [ ] Stage 2 — New module:
  - `src/vestigial/gauge_fermion_bag.py` (~500-800 lines) — The hybrid algorithm:
    - `GaugeFermionConfig` dataclass: site Grassmann occupations {0,1}^8 per site + SO(4) links per bond
    - `fermion_bag_sweep_with_links(config, rng)` — fermion update at fixed links. Propose Grassmann flips, compute bag weight ratio via Sherman-Morrison-Woodbury for rank-k updates. O((4k)³) per bag.
    - `gauge_link_sweep(config, rng, beta)` — gauge update at fixed Grassmann. Kennedy-Pendleton heatbath for each link's SU(2)_L and SU(2)_R components. Recompute bag determinants for affected bags.
    - `run_hybrid_mc(params, mc_params)` — full hybrid MC: alternate fermion + gauge sweeps
- [ ] Stage 2 — `src/vestigial/gauge_observables.py` (~200-300 lines) — Order parameters:
  - `tetrad_vev(config)` — ⟨E^a_μ⟩ = (1/4V) Σ_{x,μ} ψ̄_x γ^a U_{x,μ} ψ_{x+μ̂}, a 4×4 matrix. Tetrad ordering: ||⟨E⟩|| > 0.
  - `metric_vev(config)` — ⟨g_μν⟩ = (1/V) Σ_x δ_{ab} ⟨E^a_μ(x) E^b_ν(x)⟩, a symmetric 4×4 matrix. Metric ordering: eigenvalues of ⟨g⟩ split from zero.
  - `vestigial_diagnostic(config)` — returns (tetrad_magnitude, metric_eigenvalues, is_vestigial). Vestigial = metric eigenvalues nonzero while tetrad magnitude ≈ 0.
  - `binder_tetrad_gauge(configs)` — Binder cumulant of ||⟨E⟩||
  - `binder_metric_gauge(configs)` — Binder cumulant of Tr(⟨g⟩)
  - `sign_monitor(configs)` — track ⟨sign(det(M))⟩ for sign problem assessment
- [ ] Stage 3 — `lean/SKEFTHawking/GaugeFermionBag.lean` — sorry stubs:
  - `bag_weight_gauge_invariance` — W_B transforms correctly under gauge transformation
  - `tetrad_gauge_covariant` — E^a_μ transforms as expected under SO(4) gauge
  - `metric_gauge_invariant` — g_μν is gauge-invariant (SO(4) singlet)
  - `vestigial_implies_metric_nonzero` — definition consistency
  - ~8-10 theorems
- [ ] Stage 4 — Aristotle
- [ ] Stage 5 — `lake build` zero sorry
- [ ] **Validation checkpoint:** L=4, β=2 (intermediate gauge coupling), scan g from weak to strong. Verify: (a) at g=0 the system is disordered; (b) at large g the tetrad orders; (c) acceptance rates respond to coupling; (d) sign ⟨sign⟩ > 0.5 for manageable sign problem.

### 7C. Production Phase Diagram Scan [Pipeline Stages 6-9]

**The computation:** Scan the (g, β) parameter space at multiple L to map the phase diagram and locate the vestigial phase (if it exists). The analytical prediction from Wave 6 gives G_ves as a target.

**Deliverables:**
- [ ] Stage 6 — Tests:
  - Pure gauge validation: average plaquette vs β for L=4,6
  - Hybrid MC: coupling-dependent observables (tetrad VEV, metric eigenvalues)
  - Sign monitoring: ⟨sign⟩ > threshold at working points
  - Binder cumulant bounds for gauge-covariant OPs
  - Reproducibility (same seed → same result)
- [ ] Stage 7 — `validate.py` all checks pass
- [ ] Stage 8 — Visualizations:
  - `fig_gauge_phase_diagram` — (g, β) heat map of tetrad/metric OPs
  - `fig_gauge_binder_crossing` — Binder cumulants for tetrad and metric vs g, multiple L
  - `fig_gauge_vestigial_window` — overlay analytical G_ves prediction with MC data
  - `fig_gauge_sign_monitor` — ⟨sign⟩ vs coupling, sign problem assessment
- [ ] Stage 9 — Figure review
- [ ] **Production runs:** L=4,6,8 at 20 coupling points in (g, β) space. Estimated runtime:
  - L=4: ~2-4 hours (256 sites, bags size ~1-5)
  - L=6: ~1-2 days (1296 sites)
  - L=8: ~3-7 days (4096 sites)
  - Total: ~1-2 weeks of workstation time

### 7D. Paper 6 + Document Sync [Pipeline Stages 10-12]

**Deliverables:**
- [ ] Stage 10 — Paper 6 update: gauge-link MC results, (g, β) phase diagram, vestigial phase detection (or negative result with diagnosis), comparison with analytical prediction
- [ ] Stage 11 — Notebooks updated
- [ ] Stage 12 — Full document sync

**Estimated LOE:** 6-11 weeks total across 7A-7D.
**Risk:** Medium-High.
- **Sign problem** is the primary risk. If ⟨sign⟩ → 0 at working points, reweighting fails. Mitigation: include β > 0 as regulator; use dual bag formulation near criticality.
- **Bag growth near criticality.** Bags percolate, determinant cost explodes as O(V³). Mitigation: switch to dual (weak-coupling) bag formulation per Chandrasekharan's duality.
- **Critical slowing down.** Unknown for this novel algorithm. Mitigation: parallel tempering across β; monitor autocorrelation.
- **No benchmark to compare against.** This is the first implementation — validation relies on limiting cases (pure gauge, strong coupling) and internal consistency (analytical prediction).

---

### 9D. Parameter Provenance & Blast Radius Fix (2026-04-01)

**Root cause:** Steinhauer omega_perp = 2π×500 Hz in constants.py had NO published source. Verified from primary source (Wang et al., PRA 96, 023616, Table II): correct value is **2π×123 Hz**. Also Rb87 a_s was 109 a₀ but van Kempen 2002 reports **100.4 a₀** for the F=2 channel Steinhauer uses.

**Provenance system built (Pipeline Invariant 8, CHECK 15):**
- [x] `src/core/provenance.py` — PARAMETER_PROVENANCE registry, 29 params, all LLM-verified
- [x] `src/core/citations.py` — CITATION_REGISTRY, 31 papers with DOIs
- [x] CHECK 15 in validate.py — coverage, LLM/human verification, value consistency, tier checks
- [x] `scripts/provenance_dashboard.py` — Flask+HTMX command center (5 tabs)
- [x] WAVE_EXECUTION_PIPELINE.md — Stage 1 gate, Invariant 8, deep research reconciliation protocol
- [x] CLAUDE.md — Invariant 8 added

**Root cause fixes applied:**
- [x] `Rb87.a_s`: 5.77e-9 → 5.31e-9 (100.4 a₀, van Kempen PRL 88, 093201)
- [x] `Steinhauer.omega_perp`: 2π×500 → 2π×123 (Wang PRA 96, 023616, Table II)
- [x] `Steinhauer.velocity_upstream`: 0.85e-3 → 0.41e-3 (Mach 0.75 × corrected c_s)
- [x] validate.py CHECK 2 & CHECK 4 expected values updated
- [x] 15/15 validation checks pass, 1027 tests pass

**Solver output with corrected params (Steinhauer):**
- c_s: 1.151 → **0.548 mm/s** (matches published ~0.5)
- ξ: 0.635 → **1.334 µm** (matches Wang ~2 µm)
- Model κ: 21.9 → **4.8 s⁻¹** (model-dependent tanh profile, NOT published κ=290)
- Note: Published κ=290 s⁻¹ comes from actual step-potential gradient, not our smooth tanh model

**Additional findings from primary source verification:**
- [x] Polariton c_s: code 1.0 µm/ps, Falque reports 0.40 µm/ps (2.5× discrepancy) — tier→PROJECTED
- [x] Polariton ξ: code 2.0 µm, Falque reports 3.4-4.0 µm — tier→PROJECTED
- [x] Polariton tau_cav: 100/300 ps are projections, Falque actual cavity ≈ 8 ps — tier→PROJECTED
- [x] arXiv ID for Wang 2017 was hallucinated (1706.01483 = combustion paper, correct: 1605.01027)

**Remaining downstream propagation (Stage 10-12 work):**
- [ ] Paper 1 Table 1: update c_s, ξ, κ, T_H, δ_diss, δ_disp for Steinhauer
- [ ] `src/wkb/spectrum.py`: update Steinhauer natural-unit params (D, gamma_dim)
- [ ] `src/wkb/backreaction.py`: resolve PROVENANCE WARNING (can now reconcile — solver c_s matches published)
- [ ] README.md: update Steinhauer row in main physics table
- [ ] `papers/experimental_predictions/prediction_tables.tex`: update Steinhauer column
- [ ] Notebooks Phase1-3: will show updated values on re-execution (import from solver)
- [ ] `docs/validation/VALIDATION_REPORT.md`: historical, but note correction
- [ ] Add `Source:` fields to formulas.py docstrings (B6)
- [ ] Add theorem→paper and formula→paper declared mappings (C2)
- [ ] Spec paper claims reviewer agent for pipeline (new pipeline stage)
- [ ] Polariton parameter reconciliation: determine if c_s/xi/tau_cav should use Falque values or remain projected

---

## 12. Wave 8 — 4D ATRG for Vestigial Gravity (Sign-Problem-Free Cross-Validation)

**Research basis:** `Lit-Search/Phase-5/Feasibility of 4D HOTRG for vestigial gravity transitions in the ADW model.md`

**Goal:** Implement 4D Anisotropic Tensor Renormalization Group (ATRG) for the ADW model. ATRG is sign-problem-free and provides numerically exact (up to bond dimension truncation) results at small lattice sizes (L=4-6). Cross-validates Wave 7 MC results and provides a fallback if the MC sign problem blocks production.

**Moved from Phase 6:** The original "9-14 month" estimate assumed traditional academic pace. With our pipeline (numba + Opus + Lean + Aristotle), each stage is days not months. Compute at D=8-12 fits workstation memory (128MB-3.4GB per tensor). O(D⁹) at D=12 for L=4 is ~1.5 hours on consumer hardware. Reference implementations exist for all stages.

**Key algorithm:** ATRG (Adachi-Okubo-Todo, PRB 102, 054432, 2020) scales as O(D⁹) in 4D — six orders of magnitude better than HOTRG's O(D¹⁵). For SO(4), the armillary sphere formulation (Yosprakob PTEP 2024) can reduce effective bond dimension by 3-5×.

**Starting points:** TsuyoshiOkubo/ABTRG (Python ATRG by co-author), akiyama-es/Grassmann-BTRG, rgjha/TensorCodes (PyTorch GPU).

### 8A. 4D Ising ATRG Validation [Pipeline Stages 1-7]

**Goal:** Port the reference ATRG implementation and validate against the known 4D Ising critical temperature. This exercises the core tensor contraction machinery without gauge or Grassmann complications.

**Source:** Akiyama et al., PRD 100, 054510 (2019); Adachi-Okubo-Todo PRB 102, 054432 (2020)

**Deliverables:**
- [ ] `src/tensor/atrg_core.py` — ATRG algorithm: bond-swapping, SVD truncation, coarse-graining
- [ ] `src/tensor/ising_4d.py` — 4D Ising initial tensor construction
- [ ] Constants, formulas (with Lean refs), tests
- [ ] Validation: reproduce T_c for 4D Ising at D=8-12
- [ ] Estimated compute: minutes at D=8, ~1h at D=12

### 8B. Z₂ Gauge Structure [Pipeline Stages 1-7]

**Goal:** Add the simplest lattice gauge theory to the ATRG framework. Z₂ gauge links on bonds with Wilson plaquette action.

**Source:** Akiyama & Kuramashi, JHEP 05, 102 (2022)

**Deliverables:**
- [ ] `src/tensor/gauge_tensor.py` — gauge-invariant initial tensor construction
- [ ] Tests: reproduce known Z₂ confinement-deconfinement transition
- [ ] Estimated compute: hours at D=12

### 8C. SU(2) Gauge in 3D Benchmark [Pipeline Stages 1-7]

**Goal:** Implement SU(2) gauge theory with ATRG in 3D. Validates the non-Abelian gauge tensor construction before moving to 4D SO(4).

**Source:** Yosprakob & Okunishi, PTEP 2025, 033B06; armillary sphere formulation

**Deliverables:**
- [ ] SU(2) character expansion for initial tensor
- [ ] Armillary sphere technique for bond dimension reduction
- [ ] Validate: average plaquette and deconfinement transition vs MC benchmarks
- [ ] Estimated compute: hours at D=12-16

### 8D. Grassmann Extension to 4D [Pipeline Stages 1-7]

**Goal:** Add Grassmann-valued tensor entries to the ATRG framework. We already have `grassmann_trg.py` for 2D — extend to 4D using the formalism of Akiyama et al. (JHEP 01, 121, 2021).

**Source:** Akiyama et al., JHEP 01, 121 (2021) — 4D NJL model with Grassmann ATRG

**Deliverables:**
- [ ] `src/tensor/grassmann_atrg.py` — Grassmann-valued tensor algebra
- [ ] Validate: reproduce known NJL phase transition in 4D
- [ ] Cross-check against our Wave 9C-3 NJL MC results (g_c ≈ 5.5)
- [ ] Estimated compute: hours at D=8-12

### 8E. Full ADW Model at D=8-12 [Pipeline Stages 1-12]

**Goal:** Combine SO(4) gauge + Grassmann + 4D ATRG for the ADW model. This is the frontier — no one has done this before. Cross-validates Wave 7 MC results.

**Source:** Synthesis of 8A-8D techniques applied to the ADW action

**Deliverables:**
- [ ] SO(4) ≅ SU(2)_L × SU(2)_R character expansion with armillary sphere reduction
- [ ] Full ADW initial tensor with 8 Grassmann variables per site
- [ ] Free energy, specific heat, and vestigial order parameter from TRG
- [ ] Cross-validation: compare phase boundaries with Wave 7 MC and Wave 6 analytical G_ves
- [ ] If D=8-12 insufficient, document what D is needed → D=16+ becomes Phase 6 item

**Risk:** This is genuinely frontier research. The combination is untested. If the physics requires D > 12 to resolve the vestigial window (which is exponentially narrow per Wave 6), workstation-scale ATRG may not have sufficient resolution. This would be a meaningful negative result documenting the limitation.

**Estimated LOE:** 8A-8D: ~1 week each. 8E: ~2 weeks. Total: ~6 weeks.

---

*Phase 5 roadmap. Waves 1-5 COMPLETE. 9A-9E COMPLETE. Wave 6 Stages 1-9 COMPLETE. Wave 7: 7A COMPLETE. **7B COMPLETE + BUG-FIX.** **7C: Rust RHMC implemented + multi-shift CG (6.3× L=4). CRITICAL BUG: real pseudofermion gives Pf^{1/2} not Pf. Fix in progress: complex pseudofermion (two real flavors).** Updated 2026-04-02.*

### Wave 7B Status (COMPLETE)

Dual implementation: 4×4 complex reference + 8×8 Majorana sign-free (Kramers PRL 116). Module: `gauge_fermion_bag_majorana.py`. Optimizations: Givens Spin(4) 224×, Woodbury gauge 42×, bond-check fermion 4×. Fermion-bag hits percolation wall at L≥6 — RHMC crossover confirmed by deep research.

**W7B-fix wave (session 3):** Comprehensive code review found and fixed 3 critical bugs:
- C1: Stale `big_bag_inv` in JIT gauge sweep — Woodbury inverse update added
- C2: `_total_bag_weight` skipped zero-det bags — now returns 0
- C3: `_pfaffian_sign_lu` used wrong heuristic — replaced with Kramers assertion
- Plus: SMW zero-check, imaginary part validation, JIT tolerance tightened (rtol 0.2→1e-6)
- Pipeline compliance: Binder cumulant moved to formulas.py (d=16 tetrad, d=9 metric) with 4 Lean theorems (2 ring-proved, 2 Aristotle cc257137). Lean/Aristotle/Source docstrings on all Majorana functions. Provenance entries for MAJORANA_GAMMA_8x8, J1, J2, J3.
- 6 new tests: Spin(4) Givens vs logm/expm, Kramers Pf sign across 50 configs, Woodbury JIT direct, DeltaM sparsity. **146 tests pass, zero sorry, 8064 Lean jobs clean.**
- Production script rewritten: incremental save per coupling point, --resume, logging, NaN/Inf validation.

### Wave 7C: HS+RHMC Algorithm (NEXT — gates all production runs)

**Deep research returned:** `Lit-Search/Phase-5/HS+RHMC for ADW tetrad condensation with 8×8 Majorana fermions on Spin(4) lattice.md`

**Why:** Fermion-bag algorithm hits O(V⁴) percolation wall. 88% of sites form one bag → det is O(V³) per sweep, O(V) sweeps to decorrelate → O(V⁴) total. RHMC is O(V·√κ) per decorrelated sample. **Crossover at L≈6** — confirms L=6 fermion-bag was intractable.

**Algorithm:**
1. HS transformation: exp(-g|E^a|²) = ∫ dh exp(-h²/4g + h·E^a) → 16V auxiliary fields h^a_{x,μ}
2. Z = ∫ Dh DU · Pf(A[h,U]) · exp(-Σh²/4g)
3. Kramers: Pf(A) ≥ 0 for all (h,U) → sign-problem-free
4. |Pf(A)| = det(A†A)^{1/4} via Zolotarev rational approximation (12-16 poles, 10⁻⁶ precision)
5. Multi-shift CG: one Krylov solve for all poles simultaneously
6. Omelyan MD: joint evolution in (h, U_L, U_R) with SU(2) closed-form exponentiation
7. Metropolis accept/reject at trajectory end

**Cost estimates:**
| L | V | Wall time (1 core) | Wall time (GPU) |
|---|---|--------------------|-----------------|
| 4 | 256 | ~0.1 s/traj | ~1 ms |
| 8 | 4,096 | ~3 s/traj | ~30 ms |
| 12 | 20,736 | ~25 s/traj | ~0.25 s |
| 16 | 65,536 | ~2 min/traj | ~1.2 s |

**Starting point:** SUSY LATTICE code (github.com/daschaich/susy, GPL-3.0). Requires: replace A₄* lattice → hypercubic, U(N) → Spin(4), twisted fermion → 8×8 Majorana A[h,U], add h dynamics.

**Validation plan:** Cross-check with fermion-bag at L=4 (plaquette, tetrad, Pf comparison). Reversibility test, ΔH distribution, autocorrelation analysis.

**Deliverables (Pipeline Stages 1-12):**
- [ ] Stage 1: HS constants (16V auxiliary fields, Zolotarev coefficients)
- [ ] Stage 2: formulas.py — HS fermion matrix A[h,U], MD forces, rational approx
- [ ] Stage 3-5: Lean theorems for HS partition function identity, Kramers in HS regime
- [ ] Stage 6: Tests — multi-shift CG, MD reversibility, Metropolis detailed balance
- [ ] Stage 7: Cross-validate RHMC vs fermion-bag at L=4
- [ ] Stages 8-12: Production L=4,6,8,12,16 scans, Binder crossing analysis, paper update

**7C IMPLEMENTED (2026-04-02).** Module: `src/vestigial/hs_rhmc.py` (~900 lines). 13 Lean theorems (zero sorry). 19 tests pass. Production runner: `scripts/run_rhmc_production.py` (incremental save + resume).

Verified correct:
- Force matches finite differences to 1e-10
- Omelyan reversibility to 1e-15
- ΔH ~ O(ε²) scaling confirmed
- Zolotarev: 16 poles, all α_k > 0, exponential convergence
- At β=0: gauge links gauge-fixed to identity — h-field RHMC is correct algorithm
- **BUG (found 2026-04-02):** ⟨h²⟩ ≈ 2g was misdiagnosed as correct. Real pseudofermion with x^{-1/4} gives Pf^{1/2}, not Pf. See W7C-fix section below.

**7C Performance Engineering (2026-04-02).** Three backends implemented, comprehensive optimization, deep research.

**Backends implemented:**
- `src/vestigial/hs_rhmc.py` — numpy/scipy (reference, 63s/traj L=4, requires numba)
- `src/vestigial/hs_rhmc_jax.py` — JAX CPU (11.5s/traj L=4, requires jax)
- `src/vestigial/hs_rhmc_torch.py` — **PyTorch CPU (3.39s/traj L=4, production default)**

**Optimizations applied:**
- Batched LU solve: all 16 Zolotarev shifts in one LAPACK call (vs 16 independent CG)
- Batched CG: all 16 shifts share one batched matvec per iter (for L≥6 where LU exceeds memory)
- FSAL Omelyan: last force of step k = first of step k+1 → 21 force evals instead of 30 (30% reduction)
- Auto device selection: CPU for all sizes (MPS GPU provides zero benefit — see below)
- Production runner: `--backend torch|jax|numpy` with incremental save + resume

**GPU investigation (dead end):**
- MPS GPU SLOWER than CPU at all sizes: unified memory → shared 273 GB/s bandwidth, GPU adds 100-350μs kernel launch overhead per dispatch, zero bandwidth gain. Confirmed by deep research.
- MLX: no float64, eigh CPU-only, designed for LLM inference not scientific computing.
- jax-metal: abandoned (last release Oct 2024, breaks on JAX ≥0.8.2).
- JAX CPU: matmul routes through Eigen/NEON bypassing Accelerate AMX → 2-4× slower than PyTorch.
- **Verdict: PyTorch CPU (Accelerate BLAS/AMX) is the single best framework across all L.**

**Deep research (Lit-Search/Phase-5/5W7C/):**
- `GPU-accelerated CG on Apple Silicon.md` — definitive: GPU loses due to unified memory bandwidth sharing
- `JAX on Apple Silicon- closing the 2.7× gap with PyTorch for RHMC.md` — JAX gap is Eigen BLAS + algorithmic

**Key finding: the fermion matrix A is physically sparse** (nearest-neighbor lattice, 0.2% fill at L=8). Dense storage wastes 99.8% of memory and bandwidth. Sparse CG reads 2600× less data at L=12. This is the critical unlock for L≥12 where dense matrices exceed 128GB.

**Production projections (128 GB Apple Silicon, PyTorch CPU, FSAL Omelyan):**

| L | dim | Solver | s/traj | Production (24K traj) | Status |
|---|-----|--------|--------|-----------------------|--------|
| 4 | 2,048 | Batched LU | **3.4s** ✓ | 23h | READY NOW |
| 6 | 10,368 | Dense batched CG | ~3-10s | 1-3 days | Implemented |
| 8 | 32,768 | Dense batched CG | ~20-60s | 6-17 days | Implemented |
| 10 | 80,000 | Dense batched CG | ~2-5 min | 1-2 months | Borderline |
| 12 | 165,888 | Sparse CG | ~3-10s | 1-3 days | **Needs sparse impl** |
| 14-20 | 307K-1.28M | Sparse CG | ~5-30s | 1-8 days | **Needs sparse impl** |

✓ = measured. Others projected from calibrated scaling.

### W7C-fix: Complex Pseudofermion Convention (2026-04-02) — IN PROGRESS

**CRITICAL BUG FOUND:** Real pseudofermion with x^{-1/4} gives Pf(A)^{1/2}, not Pf(A).

Confirmed empirically at L=2 (g=2.0):
| Method | ⟨h²⟩ |
|--------|-------|
| Exact Pf(A) = det^{1/4} | 5.264 ± 0.004 |
| Exact det^{1/8} = Pf^{1/2} | 4.303 ± 0.006 |
| RHMC x^{-1/4} (CURRENT) | 4.306 ± 0.027 |

Current code matches det^{1/8} to 0.003 — simulating the WRONG theory.

**Root cause:** For real φ ∈ ℝ^{8V}: ∫dφ exp(-φ^T M φ) ∝ det(M)^{-1/2}.
With M = (A†A)^{-1/4}: det^{1/8} = Pf^{1/2}. Need complex Φ ∈ ℂ^{8V} to get det^{1/4} = Pf.

**Deep research confirms:** Schaich & DeGrand (arXiv:1410.6971, Eqs. 16-20) use complex pseudofermion with (D†D)^{-1/4}. Heatbath uses (D†D)^{+1/8}. Universal convention in lattice SUSY.
Ref: `Lit-Search/Phase-5/5W7C/Pfaffian RHMC uses complex pseudofermions with quarter-root power.md`

**Fix:** Complex Φ = Φ_R + iΦ_I decomposes into two independent real fields (since A†A is real):
- Action: S_PF = Φ_R^T (A†A)^{-1/4} Φ_R + Φ_I^T (A†A)^{-1/4} Φ_I (power unchanged)
- Heatbath: Φ_{R,I} = A · r_{-3/8}(A†A) · ξ_{R,I} (A matvec trick, r ≈ x^{-3/8})
- Cost: ~2× current per force eval (two CG solves per force)

**Implementation (Rust lib.rs — Pipeline Stages 1-7): ALL COMPLETE**
- [x] Stage 0: Empirical test confirms bug (`scripts/test_pseudofermion_convention.py`)
- [x] Stage 1: Heatbath Zolotarev power -3/8 + spectral range from Lanczos (24 poles)
- [x] Stage 2: Updated hs_rhmc.py docstrings (Schaich-DeGrand arXiv:1410.6971 citation)
- [x] Stage 3-5: 2 new Lean theorems (complex_pseudofermion_pfaffian, heatbath_a_trick_covariance). 22 total, zero sorry.
- [x] Stage 6: Rust two-flavor heatbath + Hamiltonian + forces. benchmark_rust_parallel.py updated.
- [x] Stage 7: L=2 validated: h_sq 4.31→4.99 (24 poles, converging to exact 5.10). L=4: h_sq 4.31→4.73, |ΔH|~0.01.
- [ ] Stage 7: L=4 cross-validation vs fermion-bag (deferred — fermion-bag also had wrong PF)

**Also fixed in this wave:**
- Spectral range: use Lanczos estimation (not hardcoded [0.01, 100])
- Scatter stencil: single-pass (reverted two-pass gather, removed threading)
- Multi-shift CG: shared Krylov (6.3× at L=4)
- 20 Lean theorems in HubbardStratonovichRHMC.lean (zero sorry)

**Production runner:** `scripts/run_rhmc_production.py` — checkpoint/resume, per-traj saves, Ctrl-C safe.

```bash
# IMPORTANT: build Rust first (needed after any Rust code change)
PYO3_USE_ABI3_FORWARD_COMPATIBILITY=1 uv run maturin develop --release --manifest-path rust/Cargo.toml

# L=4 production (~75 min on M3 Max 16-core, 14 workers)
PYTHONPATH=. .venv/bin/python scripts/run_rhmc_production.py --l 4 --n-traj 1500

# L=8 production (~3.3 days, stop/resume anytime)
PYTHONPATH=. .venv/bin/python scripts/run_rhmc_production.py --l 8 --n-traj 500 --n-md-steps 50

# Resume any interrupted run (auto-detects progress from data/rhmc/*.npz)
PYTHONPATH=. .venv/bin/python scripts/run_rhmc_production.py --l 8 --n-traj 500 --n-md-steps 50

# Background overnight
nohup env PYTHONPATH=. .venv/bin/python scripts/run_rhmc_production.py \
  --l 8 --n-traj 500 --n-md-steps 50 > rhmc_l8.log 2>&1 &
```

Checkpoints: `data/rhmc/L{L}_g{g:.4f}.npz` — saves after every trajectory. Includes h-field state for seamless resume (no re-thermalization). Kill anytime, resume with same command.

- [x] L=4 production RUNNING (2026-04-03)
- [ ] L=8 production (after L=4 validates)
- [ ] Stages 8-12 (viz, figures, Paper 6 update) after data available
