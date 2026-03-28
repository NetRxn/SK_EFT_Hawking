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
- [ ] `src/experimental/kappa_scaling.py` — kappa-scaling prediction functions
- [ ] `lean/SKEFTHawking/KappaScaling.lean` — Lean theorems: scaling laws, crossover condition
- [ ] Aristotle: fill sorry gaps
- [ ] Tests in `tests/test_experimental.py`
- [ ] Figure: kappa-scaling comparison across platforms (delta_disp vs delta_diss vs kappa)
- [ ] Update Paper 1 or Paper 4 appendix with kappa-scaling predictions
- [ ] Notebooks: update Phase4a Technical + Stakeholder
- [ ] Document sync (Inventory, README, etc.)

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
- [ ] Polariton parameters in `src/core/constants.py` (ATOMS, EXPERIMENTS dicts)
- [ ] `src/experimental/polariton_predictions.py` — Tier 1 polariton spectral predictions
- [ ] Lean theorems: pseudounitary scattering, Tier 1 validity conditions
- [ ] Tests
- [ ] Figures: polariton vs BEC comparison, Gamma_pol/kappa regime map
- [ ] Update prediction tables in Paper 4
- [ ] Notebooks
- [ ] Document sync

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
- [ ] Updated Lean files with Aristotle-strengthened proofs
- [ ] Updated `src/core/constants.py` ARISTOTLE_THEOREMS count
- [ ] Updated `src/core/aristotle_interface.py` SorryGap entries
- [ ] `docs/validation/lean_quality_audit.md` — audit report
- [ ] Document sync

**Estimated LOE:** Medium (batch submission + integration)
**Risk:** Low. Worst case: no additional proofs strengthened, which is still informative.

---

### 1R. Deep Research Launch [Async — John]

**Research prompts (in `Lit-Search/Tasks/submitted/`):**
- [x] `Phase5_5D_polariton_sk_eft_modifications.txt` → **Complete**: `Extending Schwinger-Keldysh EFT to driven-dissipative polariton condensates.md`
- [x] `Phase5_vestigial_correlator_simulation_scoping.txt` → **Complete**: `Monte Carlo simulation of vestigial gravity in ADW lattice models.md`
- [ ] `Phase5_W3_tpf_gs_lean_formalization_scope.txt` — Scope for chirality wall formalization in Lean
- [ ] `Phase5_W4_string_net_lean_formalization_scope.txt` — Scope for string-net / Fermi-point formalization in Lean

**Previous research results (in `Lit-Search/Phase-5/`):**
- `The chirality wall- still cracking, still not broken.md`
- `Emergent gravity from topological order- a technical reference assessment.md`
- `Independent replication of analog Hawking radiation remains blocked.md`
- `Walker-Wang finite-temperature eta-s simulation- technical scoping assessment.md`
- `Fractons and Wallstrom- 2024-2026 monitoring scan.md`
- `Extending Schwinger-Keldysh EFT to driven-dissipative polariton condensates.md`
- `Monte Carlo simulation of vestigial gravity in ADW lattice models.md`

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
- [ ] `src/vestigial/grassmann_trg.py` — 2D Grassmann TRG implementation
- [ ] `src/vestigial/su2_integration.py` — Analytical SU(2) Haar measure integration
- [ ] Tests: verify against known 2D results
- [ ] Figures: 2D phase diagram with vestigial diagnostic
- [ ] Lean theorems: SU(2) pseudo-reality → real effective action, Binder cumulant ordering

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
- [ ] `src/vestigial/fermion_bag.py` — Fermion-bag MC for 8-fermion vertices
- [ ] `src/vestigial/lattice_4d.py` — 4D cubic lattice model with SO(4) gauge integration
- [ ] `src/vestigial/phase_scan.py` — Coupling scan with Binder cumulant analysis
- [ ] Tests: sign problem check, convergence tests, known-limit validation
- [ ] Figures: 4D phase diagram, Binder cumulant crossings, metric correlator vs coupling
- [ ] Lean theorems: vestigial phase existence/non-existence conditions
- [ ] Paper 6 update (or new Paper 7 if results are substantial)
- [ ] Notebooks (Technical + Stakeholder)
- [ ] Document sync

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
- [ ] `lean/SKEFTHawking/LatticeHamiltonian.lean` — framework definitions
- [ ] Tests verifying definitions compile and basic properties hold
- [ ] Aristotle: prove basic lattice Hamiltonian properties

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
- [ ] `lean/SKEFTHawking/GoltermanShamir.lean` — all 9 conditions + no-go structure
- [ ] `src/chirality/gs_conditions.py` — Python representations for analysis
- [ ] Tests
- [ ] Aristotle submissions

**Estimated LOE:** Medium (~6 weeks)

---

### 3C. TPF Evasion Proofs [Lean + Aristotle]

**Goal:** Formalize TPF properties and machine-verify which GS conditions are violated.

**The violations (from deep research — 3 clean, 1 potential, 1 implicit):**

| GS Condition | TPF Status | Lean Proof Strategy |
|---|---|---|
| C1 (smoothness) | **Potentially violated** — nearest-integer `round` is discontinuous | Prove `¬ Continuous round` (elementary) |
| C2 (fermion-only) | **Violated** — rotor ancillas are bosonic | Prove rotor Hilbert space L²(S¹) is not a fermionic Fock space |
| C3 (no massless bosons) | **Potentially violated** — rotor modes may be gapless | State as conditional: `¬ GappedRotorModes → ¬ C3` |
| I3 (finite-dim local) | **Violated** — L²(S¹) is infinite-dimensional | Prove `¬ FiniteDimensional ℂ (Lp 2 (AddCircle (2π)))` |
| D-dimensional | **Violated** — 4+1D SPT slab | Structural: construction uses `ℤ^(d+1)`, not `ℤ^d` |

**The 4 publishable key theorems:**
1. `tpf_local_hilbert_not_finite_dim` — TPF local Hilbert space is not finite-dimensional
2. `tpf_has_bosonic_fields` — TPF Hamiltonian contains non-fermionic (rotor) fields
3. `round_not_continuous` — the nearest-integer disentangler map is discontinuous
4. `tpf_not_purely_d_dimensional` — TPF construction uses (D+1)-dimensional bulk

**Synthesis theorem:** `TPFConstruction → ¬ (C2 ∧ I3)` — TPF provably violates at least C2 and I3, placing it outside the GS theorem's scope.

**Deliverables:**
- [ ] `lean/SKEFTHawking/TPFEvasion.lean` — TPF properties + evasion proofs
- [ ] `src/chirality/tpf_evasion.py` — updated analysis with formal backing
- [ ] `docs/analysis/chirality_wall_formal_analysis.md` — full writeup (publishable)
- [ ] Aristotle: fill all sorry gaps
- [ ] Tests
- [ ] Paper draft: "Formal verification that the TPF disentangler lies outside the GS no-go scope"
- [ ] Document sync

**Estimated LOE:** High (~8 weeks)
**Risk:** Medium. C4 (complete interpolating fields) involves Green's function existence — may need to be axiomatized rather than proved. C3 (massless bosons) depends on an open physics question about rotor gapping.

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
- [ ] `lean/SKEFTHawking/KLinearCategory.lean` — k-linear, semisimple definitions + Schur's lemma
- [ ] `lean/SKEFTHawking/SphericalCategory.lean` — pivotal, spherical, quantum dimensions
- [ ] Tests verifying all definitions compile with concrete examples
- [ ] Aristotle: algebraic identity proofs

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
- [ ] `lean/SKEFTHawking/FusionCategory.lean` — definitions + pentagon equation
- [ ] `lean/SKEFTHawking/FusionExamples.lean` — Vec_G, Rep(G) for small groups
- [ ] `src/layer1/fusion_category.py` — Python computations for F-symbols
- [ ] Tests: pentagon equation verification for concrete examples
- [ ] Aristotle: algebraic identities, pentagon instances

**Estimated LOE:** Very High (~4-8 months). Central milestone of the Layer 1 program.
**Risk:** Medium-High. Pentagon equation verification for non-trivial categories requires careful tensor algebra.

---

### 4C. Gauge Emergence: Drinfeld Center → Dijkgraaf-Witten [Lean + Aristotle]

**Goal:** Prove the gauge emergence theorem: string-net condensation with input Vec_G produces emergent Dijkgraaf-Witten gauge theory with gauge group G. Also prove the chirality limitation.

**Key theorems (building on Mathlib4's existing Drinfeld center):**
1. **Gauge emergence:** Z(Vec_G) ≅ Rep(D(G)) where D(G) is the Drinfeld double — recovers DW gauge theory
2. **Non-Abelian gauge for non-Abelian G:** For G = S_3, the anyons have non-trivial fusion multiplicities N^k_{ij} > 1 and matrix-valued braiding
3. **Chirality wall theorem:** Z(C) always has trivial topological central charge c = 0 (mod 8) — string-nets intrinsically produce non-chiral (doubled) topological order
4. **Gauge erasure connection:** The doubled nature of Z(C) is the categorical foundation for our gauge erasure theorem (Paper 3) — gauge information is erased at the hydrodynamic boundary because the emergent gauge structure is always doubled

**This is the Layer 1 → Layer 2 bridge theorem** — connecting microscopic categorical data to the macroscopic gauge erasure that our existing Lean modules formalize.

**Deliverables:**
- [ ] `lean/SKEFTHawking/GaugeEmergence.lean` — DW gauge emergence + chirality limitation
- [ ] `src/layer1/drinfeld_double.py` — D(G) computations for small groups
- [ ] Tests
- [ ] Figures: Layer 1 → Layer 2 → Layer 3 architecture diagram with formal verification checkpoints
- [ ] Paper draft or extended Paper 3 appendix
- [ ] Document sync

**Estimated LOE:** High (~3-6 months)
**Risk:** Medium. Mathlib4 already has Z(C) proved braided monoidal. The new work is proving fusion structure and the gauge-theory identification.

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

### 5A. Cross-Wave Validation [Pipeline Stage 7]

Full validation suite after all waves. Verify all new theorems, tests, figures are consistent across layers.

### 5B. Document Sync [Pipeline Stage 12]

Update all documents per the Inventory Maintenance Protocol. This is a heavy sync given 4 waves of new content.

### 5C. Phase 5 Summary Paper or Report

Synthesize Phase 5 results into a coherent narrative:
- What SK-EFT delivers analytically (kappa-scaling, polariton predictions)
- What the vestigial MC pilot found (positive or negative)
- What the chirality wall formalization proved
- What the Layer 1 formalization established
- Updated assessment of all three walls

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

*Phase 5 roadmap. Waves 1-2 complete SK-EFT analytically. Waves 3-4 attack the structural walls via LLM + Lean + Aristotle formalization (first-ever in lattice chiral fermion and fusion category literature). Wave 5 synthesizes. Items requiring HPC or collaboration deferred to Phase 6. All deep research complete (9/9 tasks). Prepared 2026-03-28.*
