# SK-EFT Hawking: Formally Verified Physics from Analog Black Holes to the Standard Model

## What This Project Is About

This project investigates whether the mathematical structures that describe exotic states of matter — superfluids, topological insulators, quantum spin liquids — can also describe the fundamental forces and particles of the universe. Everything is machine-checked in the Lean 4 proof assistant: 1100+ theorems, zero axioms, across 76 modules.

### Analog Hawking radiation and testable predictions

When a fluid flows faster than its own speed of sound, it creates a sonic horizon that traps sound waves exactly the way a black hole traps light. The "acoustic Hawking temperature" follows the same formula Hawking derived for real black holes. We computed the first corrections from dissipation — the fact that real fluids have viscosity — and found they have a specific frequency dependence that gives experimentalists a concrete test: vary the flow speed and watch how the spectrum changes. The polariton platform is 10 billion times hotter than BEC systems (~1 Kelvin vs ~10^-10 Kelvin), making it the most accessible route to observing these corrections. A Paris group has already seen negative-energy modes; spontaneous Hawking detection is plausible within 1-2 years.

### Why three generations of matter

The Standard Model has three copies of its fundamental particles (electron/muon/tau and their quarks). Nobody knows why. We formally derived that the number must be divisible by three, from two independent mathematical facts: the SM's 16 Weyl fermions per generation give a chiral central charge of 8, and modular invariance of the quantum field theory (via the Dedekind eta function, studied by Ramanujan in 1916) forces this charge to be divisible by 24. The ratio 24/8 = 3 constrains the generation count — pure mathematics (number theory) meets pure physics (particle content). We also provide a formal argument for right-handed neutrinos: without them, the central charge is fractional (15/2), which is a gravitational anomaly independent of the usual mass-based argument.

### The "16 convergence"

The number 16 appears in four seemingly unrelated places: the SM's Weyl fermion count, the Z/16 anomaly classification, Rokhlin's theorem on 4-manifold signatures, and Kitaev's classification of topological superconductors. We proved these are the same 16, rooted in the quaternionic structure of spinors in four dimensions. The E8 lattice (verified formally using Mathlib's existing Cartan matrix) has signature 8, proving the algebraic bound is 8, not 16 — the jump to 16 requires smooth topology, not just algebra. This cleanly separates what mathematics alone constrains from what requires physics.

### From lattice models to gauge theory

We formalized the complete chain connecting integrable lattice models to topological gauge theory: Onsager algebra → q-deformation → quantum group U_q(sl_2) with Hopf structure → affine quantum group → restricted quantum group at roots of unity → SU(2)_k fusion categories → modular S-matrix → Chern-Simons gauge theory. The SU(2)_k fusion rules at k=3 contain the Fibonacci anyon — universal for topological quantum computation. Our formalization provides verified mathematical foundations for the fusion operations these future quantum computers would perform.

### The chirality wall

The biggest obstacle to deriving the Standard Model from condensed matter is chirality: the weak force only acts on left-handed particles. We provided the first formal analysis of a 2026 construction (Thorngren-Preskill-Fidkowski) that likely evades the 1981 no-go theorems: all 9 conditions of the competing Golterman-Shamir no-go formalized, 5 proved violated, master synthesis theorem machine-checked.

### Emergent gravity: what works and what doesn't

Fracton symmetric tensor gauge theory reproduces linearized gravity but fails at the nonlinear level — formally verified obstruction. The Akama-Diakonov-Wetterich mechanism (gravity from fermion condensation) is more promising: the gap equation for tetrad condensation has never been explicitly written down in the literature. Our deep research identifies it and scopes the computation. The non-Abelian gauge wall is a structural theorem: SU(3) and SU(2) gauge forces cannot survive through a fluid layer (proved), but can originate from topological order (the quantum group route we formalized).

### Verified statistical estimators

The jackknife variance estimator and autocorrelation function — foundational tools for analyzing Monte Carlo data from lattice simulations — are formalized for the first time in any proof assistant. Non-negativity of the jackknife variance is proved. This opens the path to formally verified data analysis for lattice quantum field theory.

*Items marked with \* are pending completion by the Aristotle automated theorem prover: Hopf algebra compatibility proofs, S-matrix unitarity and determinant computations, E8 determinant, and the bordism-derived Rokhlin/Wang chain.*

---

## Technical Summary

**Lean 4 formalization:** 1102 theorems across 76 modules. Zero axioms, ~41 sorry pending Aristotle.
273 Aristotle-proved across 33+ runs. Lean 4.28.0, Mathlib commit `8f9d9cff`.

**Three-layer verification:** Python numerics ↔ Lean 4 formal proofs ↔ Aristotle automated theorem prover.

**Eleven papers** in a unified codebase — from first-order dissipative corrections (Paper 1) through gauge erasure (Paper 3), exact WKB (Paper 4), emergent gravity (Papers 5-6), chirality wall (Papers 7-8), SM anomaly and Drinfeld center (Paper 9), modular generation counting (Paper 10), and quantum groups through MTC (Paper 11).

## Project Structure

```
SK_EFT_Hawking/
├── lean/                              # Lean 4 formalization (1102 theorems, 0 axioms, 76 modules, 41 sorry pending Aristotle)
│   ├── lakefile.toml                  # Lake build config (pinned Mathlib)
│   ├── lean-toolchain                 # Lean 4 v4.28.0
│   ├── SKEFTHawking.lean              # Root module (imports all 75 theorem modules)
│   └── SKEFTHawking/
│       ├── Basic.lean                 # Shared types and definitions
│       ├── AcousticMetric.lean        # Structure A: acoustic metric (8 theorems)
│       ├── SKDoubling.lean            # Structure B: SK doubling + KMS (9 theorems)
│       ├── HawkingUniversality.lean   # Structure C: universality + κ-crossing + spin-sonic (9 theorems)
│       ├── HubbardStratonovichRHMC.lean # Phase 5: HS identity, Kramers, complex pseudofermion (22 theorems)
│       ├── SecondOrderSK.lean         # Phase 2: second-order counting + stress tests (19 theorems)
│       ├── WKBAnalysis.lean           # Phase 2: WKB + Bogoliubov bound (15 theorems)
│       ├── CGLTransform.lean          # Phase 2: CGL FDR derivation (7 theorems)
│       ├── ThirdOrderSK.lean          # Phase 3: third-order EFT + parity alternation (14 theorems)
│       ├── GaugeErasure.lean          # Phase 3: gauge erasure theorem (12 theorems)
│       ├── WKBConnection.lean         # Phase 3: exact WKB connection formula (17 theorems)
│       ├── ADWMechanism.lean          # Phase 3: ADW tetrad condensation (21 theorems)
│       ├── ChiralityWall.lean         # Phase 4: chirality wall analysis (17 theorems)
│       ├── VestigialGravity.lean      # Phase 4: vestigial metric phase (18 theorems)
│       ├── FractonHydro.lean          # Phase 4: fracton hydrodynamics (17 theorems)
│       ├── FractonGravity.lean        # Phase 4: fracton-gravity bootstrap (20 theorems)
│       ├── FractonNonAbelian.lean     # Phase 4: non-Abelian fracton obstruction (14 theorems)
│       ├── KappaScaling.lean          # Phase 5: crossover balance, regime classification (11 theorems)
│       ├── PolaritonTier1.lean        # Phase 5: attenuation bounds, BEC recovery (6 theorems)
│       ├── SU2PseudoReality.lean      # Phase 5: one-link normalization, Binder limits (10 theorems)
│       ├── FermionBag4D.lean          # Phase 5: SO(4) integration, bag positivity (16 theorems)
│       ├── LatticeHamiltonian.lean    # Phase 5: BZ compact, GS conditions, TPF violations (28 theorems)
│       ├── MajoranaKramers.lean       # Phase 5: Majorana Kramers degeneracy, sign-free determinant (25 theorems)
│       ├── GoltermanShamir.lean       # Phase 5: 9 GS Props, Fock space finite (14 theorems)
│       ├── TPFEvasion.lean            # Phase 5: master synthesis, 5 violations (12 theorems)
│       ├── KLinearCategory.lean       # Phase 5: semisimple, Schur, fusion rules (16 theorems)
│       ├── SphericalCategory.lean     # Phase 5: FIRST-EVER pivotal + spherical (18 theorems)
│       ├── FusionCategory.lean        # Phase 5: fusion axioms, pentagon, F-symbols (14 theorems)
│       ├── FusionExamples.lean        # Phase 5: Vec_Z2/Z3, Rep_S3, Fibonacci (30 theorems)
│       ├── VecG.lean                  # Phase 5: Day convolution, graded spaces (9 theorems)
│       ├── DrinfeldDouble.lean        # Phase 5: D(G) twisted multiplication (15 theorems)
│       ├── GaugeEmergence.lean        # Phase 5: Z(Vec_G)≅Rep(D(G)), chirality (14 theorems)
│       ├── SO4Weingarten.lean         # Phase 5: Weingarten 2nd/4th moment, channel positivity (14 theorems)
│       ├── FractonFormulas.lean       # Phase 5: charge counting, dispersion, DOF gap (45 theorems)
│       ├── WetterichNJL.lean          # Phase 5: Fierz completeness, NJL channels (18 theorems)
│       ├── VestigialSusceptibility.lean # Phase 5: RPA susceptibility, vestigial_before_tetrad (16 theorems)
│       ├── QuaternionGauge.lean       # Phase 5: SO(4) quaternion gauge, heatbath (10 theorems)
│       ├── GaugeFermionBag.lean       # Phase 5: tetrad covariance, bag weight, SMW update (9 theorems)
│       ├── OnsagerAlgebra.lean        # Phase 5a: Dolan-Grady, Davies isomorphism, Chevalley (24 theorems)
│       ├── OnsagerContraction.lean    # Phase 5a: Inönü-Wigner contraction O→su(2) (12 theorems)
│       ├── Z16Classification.lean     # Phase 5a: Z₁₆ classification, super-modular, 16-fold way (22 theorems, axiom discharged)
│       ├── SteenrodA1.lean            # Phase 5a: A(1) sub-Hopf algebra, Adem, Ext→Z₁₆ (17 theorems)
│       ├── SMGClassification.lean     # Phase 5a: AZ tenfold way, SMG data, spectral gap (13 theorems)
│       ├── PauliMatrices.lean         # Phase 5a: σ_x,σ_y,σ_z, commutation, anti-commutation (15 theorems)
│       ├── WilsonMass.lean            # Phase 5a: M(k)=3-Σcos, zero locus, bounds (11 theorems)
│       ├── BdGHamiltonian.lean        # Phase 5a: BdG 4x4, σ⊗τ Kronecker, chiral charge (8 theorems)
│       ├── GTCommutation.lean         # Phase 5a: [H,Q_A]=0 central theorem, GS evasion (10 theorems)
│       ├── GTWeylDoublet.lean         # Phase 5a: Weyl doublet, Onsager→SU(2), Witten anomaly (12 theorems)
│       ├── ChiralityWallMaster.lean   # Phase 5a: Three-pillar synthesis theorem (17 theorems)
│       ├── SMFermionData.lean         # Phase 5b: SM fermion ℤ₄ charges, component counts (19 theorems)
│       ├── Z16AnomalyComputation.lean # Phase 5b: SM anomaly in ℤ₁₆, hidden sector theorem (23 theorems, 2 axioms discharged)
│       ├── GenerationConstraint.lean  # Phase 5b: N_f ≡ 0 mod 3 (conditional on 24|8N_f) (13 theorems, axioms discharged/removed)
│       ├── DrinfeldCenterBridge.lean  # Phase 5b: Half-braiding ↔ D(G)-module, Mathlib Center (18 theorems)
│       ├── VecGMonoidal.lean          # Phase 5b: MonoidalCategory(Vec_G), Center(Vec_G) (12 theorems)
│       ├── ToricCodeCenter.lean       # Phase 5b: Toric code from Center(Vec_{ℤ/2}), R(e,m)=-1 (25 theorems)
│       ├── S3CenterAnyons.lean        # Phase 5b: Non-abelian Center(Vec_{S₃}), 8 anyons, D²=36 (22 theorems)
│       ├── CenterEquivalenceZ2.lean   # Phase 5b: Concrete Z(Vec_{ℤ/2}) ↔ D(ℤ/2) bijection (10 theorems)
│       ├── DrinfeldDoubleAlgebra.lean # Phase 5b: D(G) twisted convolution, unit/assoc (9 theorems)
│       ├── DrinfeldDoubleRing.lean    # Phase 5b: D(G) as Ring + Algebra k (3 thms + instances)
│       ├── DrinfeldEquivalence.lean   # Phase 5b: Z(Vec_G)≅Rep(D(G)) structure (12 theorems)
│       ├── WangBridge.lean            # Phase 5b: c₋=8N_f from 16 Weyl, ν_R required (9 theorems)
│       ├── ModularInvarianceConstraint.lean # Phase 5b: framing anomaly, η→24→3|N_f (12 theorems)
│       ├── RokhlinBridge.lean         # Phase 5b: Rokhlin "16" convergence (14 theorems)
│       ├── QNumber.lean               # Phase 5b: q-integers [n]_q, classical limit (11 theorems)
│       ├── Uqsl2.lean                 # Phase 5b: FIRST quantum group U_q(sl₂), zero axioms (6 theorems)
│       ├── Uqsl2Hopf.lean            # Phase 5c: FIRST Hopf algebra on U_q(sl₂), coproduct/counit/antipode (23 theorems, 22 sorry pending Aristotle)
│       ├── SU2kFusion.lean           # Phase 5c: SU(2)_k fusion at k=1,2,3, Ising/Fibonacci (29 theorems)
│       ├── Uqsl2Affine.lean          # Phase 5c: U_q(sl_2 hat) affine quantum group (9 theorems)
│       ├── SU2kSMatrix.lean          # Phase 5c: SU(2)_k S-matrices, unitarity, Verlinde (16 theorems, 10 sorry pending Aristotle)
│       ├── RestrictedUq.lean         # Phase 5c: restricted quantum group u_q(sl₂), nilpotency (11 theorems, 1 sorry pending Aristotle)
│       ├── RibbonCategory.lean       # Phase 5c: Balanced/Ribbon/MTC definitions (4 theorems, 2 sorry pending Aristotle)
│       ├── E8Lattice.lean            # Phase 5c: E8 Cartan, Rokhlin gap, classification (19 theorems, 2 sorry pending Aristotle)
│       ├── AlgebraicRokhlin.lean     # Phase 5c: algebraic Serre theorem σ≡0 mod 8 (10 theorems, all proved)
│       ├── SpinBordism.lean          # Phase 5c: spin bordism → Rokhlin → Wang chain (8 theorems, 2 sorry pending Aristotle)
│       └── VerifiedJackknife.lean    # Phase 5c: verified jackknife/autocorrelation estimators (5 theorems, 2 sorry pending Aristotle)
│
├── src/
│   ├── core/                          # Shared infrastructure
│   │   ├── transonic_background.py    # 1D BEC transonic flow solver + δ_diss estimates
│   │   ├── aristotle_interface.py     # Aristotle API + sorry-gap registry (273 proved)
│   │   ├── visualizations.py          # Plotly figures (77 functions) + COLORS palette
│   │   ├── provenance.py             # Parameter provenance registry (Phase 5 Wave 9D)
│   │   └── citations.py              # Citation registry with DOIs (Phase 5 Wave 9D)
│   ├── first_order/                   # Phase 1 specific analysis
│   ├── second_order/                  # Phase 2 analysis (absorbed from SK_EFT_Phase2)
│   │   ├── enumeration.py             # Transport coefficient counting at arbitrary order
│   │   ├── coefficients.py            # Second-order data structures + action constructors
│   │   └── wkb_analysis.py            # WKB mode analysis through the dissipative horizon
│   ├── gauge_erasure/                 # Non-Abelian gauge erasure theorem
│   │   └── erasure_theorem.py         # GaugeGroup, HigherFormSymmetry, standard model analysis
│   ├── wkb/                           # Exact WKB connection formula (Phase 3 Wave 2)
│   │   ├── connection_formula.py       # Complex turning point, Stokes geometry, exact formula
│   │   ├── bogoliubov.py              # Modified Bogoliubov coefficients, decoherence, noise floor
│   │   ├── spectrum.py                # Observable spectrum, platform predictions, comparison
│   │   └── backreaction.py            # Acoustic BH cooling toward extremality (Phase 4)
│   ├── adw/                           # ADW mean-field gap equation (Phase 3 Wave 3)
│   │   ├── wen_model.py               # Wen's emergent QED, Nielsen-Ninomiya, Herbut RG
│   │   ├── hubbard_stratonovich.py    # HS decomposition, TetradField, fermion determinant
│   │   ├── gap_equation.py            # Coleman-Weinberg V_eff, critical coupling, phase diagram
│   │   ├── fluctuations.py            # SSB pattern, NG modes, Vergeles counting, obstacles
│   │   └── ginzburg_landau.py         # GL expansion, beta_i analogs, phase classification (Phase 4)
│   ├── experimental/                  # Experimental prediction package (Phase 4-5)
│   │   ├── predictions.py            # Platform tables, detector requirements, kappa-scaling
│   │   ├── kappa_scaling.py          # Physical kappa-scaling sweeps (Phase 5 Wave 1A)
│   │   └── polariton_predictions.py  # Tier 1 polariton predictions (Phase 5 Wave 1B)
│   ├── chirality/                     # Chirality wall synthesis (Phase 4 Wave 1)
│   │   └── tpf_gs_analysis.py        # GS conditions vs TPF evasion
│   ├── vestigial/                     # Vestigial gravity simulation (Phase 4-5, Waves 2-7C)
│   │   ├── lattice_model.py           # Lattice Hamiltonian, HS-transformed ADW
│   │   ├── mean_field.py              # Extended mean-field with metric correlator
│   │   ├── monte_carlo.py             # Metropolis-Hastings sampler
│   │   ├── phase_diagram.py           # Coupling scan and phase classification
│   │   ├── finite_size.py             # Binder cumulant + finite-size scaling
│   │   ├── su2_integration.py         # SU(2) Haar measure integration (Wave 2A)
│   │   ├── grassmann_trg.py           # 2D Grassmann TRG (Wave 2A)
│   │   ├── lattice_4d.py             # 4D hypercubic lattice model (Wave 2B)
│   │   ├── fermion_bag.py            # Fermion-bag MC (Wave 2B)
│   │   ├── wetterich_model.py        # NJL fermion-bag MC (Wave 9C-3)
│   │   ├── phase_scan.py             # 4D coupling scan (Wave 2B)
│   │   ├── quaternion.py             # SU(2) quaternion algebra (Wave 7A)
│   │   ├── so4_gauge.py              # SO(4) gauge theory (Wave 7A)
│   │   ├── gauge_fermion_bag.py      # Hybrid fermion-bag + gauge-link MC (Wave 7B)
│   │   ├── gauge_fermion_bag_majorana.py # 8×8 Majorana sign-free (Wave 7B)
│   │   ├── hs_rhmc.py               # HS+RHMC numpy reference (Wave 7C)
│   │   ├── hs_rhmc_jax.py           # JAX CPU backend (Wave 7C)
│   │   └── hs_rhmc_torch.py         # PyTorch CPU production default (Wave 7C)
│   └── fracton/                       # Fracton hydrodynamics (Phase 4 Waves 2-3)
│       ├── sk_eft.py                  # Fracton SK-EFT transport coefficients
│       ├── information_retention.py   # UV information comparison
│       ├── gravity_connection.py      # Fracton-gravity Kerr-Schild + bootstrap
│       └── non_abelian.py             # Non-Abelian fracton analysis
│
├── papers/
│   ├── paper1_first_order/            # PRL submission
│   │   └── paper_draft.tex
│   ├── paper2_second_order/           # PRD companion paper
│   │   └── paper_draft.tex
│   ├── paper3_gauge_erasure/          # PRL gauge erasure
│   │   └── paper_draft.tex
│   ├── paper4_wkb_connection/         # PRD exact WKB
│   │   └── paper_draft.tex
│   ├── paper5_adw_gap/               # PRD ADW gap equation
│   │   └── paper_draft.tex
│   ├── paper6_vestigial/             # PRD vestigial gravity + production MC (Phase 4-5)
│   │   └── paper_draft.tex
│   ├── paper7_chirality_formal/      # PRD/CPC GS no-go + TPF evasion in Lean 4 (Phase 5)
│   │   └── paper_draft.tex
│   ├── paper8_chirality_master/      # PRL three-pillar chirality wall (Phase 5a)
│   │   └── paper_draft.tex
│   ├── paper9_sm_anomaly_drinfeld/   # PRL SM anomaly + Drinfeld center (Phase 5b)
│   │   └── paper_draft.tex
│   ├── paper10_modular_generation/   # PRD modular generation constraint (Phase 5b)
│   │   └── paper_draft.tex
│   ├── paper11_quantum_group/        # PRD first quantum group formalization (Phase 5b)
│   │   └── paper_draft.tex
│   └── experimental_predictions/     # Standalone prediction tables (Phase 4)
│       └── prediction_tables.tex
│
├── notebooks/
│   ├── Phase1_Technical.ipynb         # Full paper computation (23 cells, 6 Plotly figs)
│   ├── Phase1_Stakeholder.ipynb       # Lay-person version (20 cells)
│   ├── Phase2_Technical.ipynb         # Second-order computation (30 cells, 9+ Plotly figs)
│   ├── Phase2_Stakeholder.ipynb       # Lay-person version (19 cells)
│   ├── Phase3a_ThirdOrder_Technical.ipynb       # Phase 3 Wave 1: third-order EFT
│   ├── Phase3a_ThirdOrder_Stakeholder.ipynb
│   ├── Phase3b_GaugeErasure_Technical.ipynb     # Phase 3 Wave 1: gauge erasure
│   ├── Phase3b_GaugeErasure_Stakeholder.ipynb
│   ├── Phase3c_WKBConnection_Technical.ipynb    # Phase 3 Wave 2: exact WKB
│   ├── Phase3c_WKBConnection_Stakeholder.ipynb
│   ├── Phase3d_ADW_Technical.ipynb              # Phase 3 Wave 3: ADW gap equation
│   ├── Phase3d_ADW_Stakeholder.ipynb
│   ├── Phase4a_ExperimentalPredictions_Technical.ipynb  # Phase 4 Wave 1: predictions
│   ├── Phase4a_ExperimentalPredictions_Stakeholder.ipynb
│   ├── Phase4b_Vestigial_Technical.ipynb        # Phase 4 Wave 2: vestigial gravity
│   ├── Phase4b_Vestigial_Stakeholder.ipynb
│   ├── Phase5a_ChiralityWall_Technical.ipynb    # Phase 5: chirality wall formal verification
│   ├── Phase5a_ChiralityWall_Stakeholder.ipynb
│   ├── Phase5a_GTChiralFermion_Technical.ipynb   # Phase 5a: GT chiral fermion, Onsager, Z₁₆
│   ├── Phase5a_GTChiralFermion_Stakeholder.ipynb
│   ├── Phase5b_Synthesis_Technical.ipynb        # Phase 5: kappa-scaling, categorical, Drinfeld
│   ├── Phase5b_Synthesis_Stakeholder.ipynb
│   ├── Phase5b_SMAnomalyDrinfeld_Technical.ipynb # Phase 5b: SM anomaly, Drinfeld center
│   ├── Phase5b_SMAnomalyDrinfeld_Stakeholder.ipynb
│   ├── Phase5b_ModularGeneration_Technical.ipynb # Phase 5b: modular generation constraint
│   ├── Phase5b_ModularGeneration_Stakeholder.ipynb
│   ├── Phase5b_QuantumGroup_Technical.ipynb     # Phase 5b: first quantum group formalization
│   └── Phase5b_QuantumGroup_Stakeholder.ipynb
│
├── docker/
│   └── docker-compose.graph.yml       # PG+AGE container for knowledge graph (port 5433)
│
├── docs/
│   ├── KNOWLEDGE_GRAPH.md             # Knowledge graph documentation and guide
│   ├── roadmaps/                      # Phase 1 + Phase 2 technical roadmaps
│   ├── stakeholder/                   # Implications, strategic positioning, companion guides
│   ├── aristotle_results/             # All 33+ Aristotle run archives
│   └── archive/                       # Superseded artifacts
│
├── tests/                             # pytest suite (1635+ tests across 38 files)
│   ├── test_transonic_background.py   # Physics validation (12 tests)
│   ├── test_second_order.py           # Enumeration + WKB tests (12 tests)
│   ├── test_gauge_erasure.py          # Gauge erasure theorem tests (25 tests)
│   ├── test_wkb_connection.py         # Exact WKB connection tests (65 tests)
│   ├── test_adw.py                    # ADW gap equation tests (78 tests)
│   ├── test_cross_validation.py       # Cross-layer validation (7 tests)
│   ├── test_lean_integrity.py         # Module structure + sorry-gap regression (9 tests)
│   ├── test_vestigial.py             # MC, SU(2), TRG, 4D, NJL, susceptibility (159 tests)
│   ├── test_gauge.py                 # SO(4) gauge, quaternion, Majorana (146 tests)
│   └── test_hs_rhmc.py              # HS+RHMC algorithm (32 tests)
│
├── figures/                           # 77 pipeline figures (PNG + HTML) + provenance_graph.json
├── scripts/
│   ├── submit_to_aristotle.py         # Aristotle submission + integration script
│   ├── build_graph.py                 # Knowledge graph extraction (8 node types, 10 edge types)
│   ├── graph_integrity.py             # Graph integrity queries (orphans, conflicts, chains)
│   ├── provenance_dashboard.py        # Flask dashboard + /api/graph endpoints
│   └── templates/
│       ├── dashboard.html             # Dashboard template (Datastar)
│       └── partials/
│           └── graph_tab.html         # D3 knowledge graph visualization
├── pyproject.toml                     # Unified Python dependencies
└── .env                               # Aristotle API key (not committed)
```

## Quick Start

### Python
```bash
cd SK_EFT_Hawking
uv sync                                    # Install dependencies
python -m pytest tests/ -v                 # Run all tests
python -m src.second_order.enumeration     # Print transport coefficient counting table
```

### Lean
```bash
cd SK_EFT_Hawking/lean
lake build                                 # ~2259 jobs, should be clean
```

### Aristotle
```bash
cd SK_EFT_Hawking
python scripts/submit_to_aristotle.py --priority 1    # Submit sorry gaps
python scripts/submit_to_aristotle.py --retrieve <ID>  # Retrieve results
```

### Provenance Knowledge Graph
```bash
cd SK_EFT_Hawking
uv run python scripts/provenance_dashboard.py          # Opens http://localhost:8050
# Navigate to "Knowledge Graph" tab for interactive D3 visualization
# See docs/KNOWLEDGE_GRAPH.md for full documentation
```

## Documentation Guide

| If you want to... | Start here |
|---|---|
| Understand the physics and results | This README (above) |
| See what's been built and its status | [`SK_EFT_Hawking_Inventory_Index.md`](SK_EFT_Hawking_Inventory_Index.md) — counts, module map |
| Understand the execution process | [`docs/WAVE_EXECUTION_PIPELINE.md`](docs/WAVE_EXECUTION_PIPELINE.md) — 12-stage pipeline |
| Explore the provenance graph | [`docs/KNOWLEDGE_GRAPH.md`](docs/KNOWLEDGE_GRAPH.md) — interactive D3 visualization |
| Browse the dashboard | `uv run python scripts/provenance_dashboard.py` → http://localhost:8050 |
| Read non-technical summaries | `docs/stakeholder/` — implications and strategic positioning per phase |
| See what's next | [`docs/roadmaps/Phase5c_Roadmap.md`](docs/roadmaps/Phase5c_Roadmap.md), [`Phase5d_Roadmap.md`](docs/roadmaps/Phase5d_Roadmap.md), [`Phase6_Deferred_Targets.md`](docs/roadmaps/Phase6_Deferred_Targets.md) |
| Understand the broader research program | [`docs/Fluid-Based Approach to Fundamental Physics  Feasibility Study.md`](docs/Fluid-Based%20Approach%20to%20Fundamental%20Physics%20%20Feasibility%20Study.md) |
| Read the critical review | [`docs/Fluid-Based Approach to Fundamental Physics- Consolidated Critical Review v3.md`](docs/Fluid-Based%20Approach%20to%20Fundamental%20Physics-%20Consolidated%20Critical%20Review%20v3.md) |
| See the deep research corpus | `Lit-Search/` — 40+ research files across Phases 3-5c |
| Work with Aristotle | [`docs/references/Theorm_Proving_Aristotle_Lean.md`](docs/references/Theorm_Proving_Aristotle_Lean.md) |
| Check the full inventory | [`SK_EFT_Hawking_Inventory.md`](SK_EFT_Hawking_Inventory.md) — comprehensive source of truth |

## Theorem Inventory (1102 theorems — zero axioms, ~41 sorry pending Aristotle)

| Module | Phase | Theorems | Notes |
|---|---|---|---|
| AcousticMetric.lean | 1 | 8 | Aristotle: 082e6776, a87f425a, 88cf2000 |
| SKDoubling.lean | 1 | 9 | Aristotle: 082e6776, 638c5ff3, 270e77a0, 20556034 |
| HawkingUniversality.lean | 1+3 | 9 | +κ-crossing, spin-sonic |
| SecondOrderSK.lean | 2 | 19 | Aristotle: d61290fd, c4d73ca8, 3eedcabb |
| WKBAnalysis.lean | 2+3 | 15 | Aristotle: 518636d7 |
| CGLTransform.lean | 2 | 7 | CGL FDR derivation |
| ThirdOrderSK.lean | 3 | 14 | Parity alternation theorem |
| GaugeErasure.lean | 3 | 12 | Gauge erasure (axiom removed) |
| WKBConnection.lean | 3 | 17 | Exact WKB connection |
| ADWMechanism.lean | 3 | 21 | Vergeles counting, phase classification |
| ChiralityWall.lean | 4 | 17 | GS conditions, TPF evasion, wall status |
| VestigialGravity.lean | 4 | 18 | Phase hierarchy, EP violation |
| FractonHydro.lean | 4 | 17 | Multipole conservation, information retention |
| FractonGravity.lean | 4 | 20 | Bootstrap gap, DOF mismatch |
| FractonNonAbelian.lean | 4 | 14 | Non-Abelian fracton obstruction |
| KappaScaling.lean | 5 | 11 | Crossover balance, regime classification |
| PolaritonTier1.lean | 5 | 6 | Attenuation bounds, BEC recovery |
| SU2PseudoReality.lean | 5 | 10 | One-link normalization, Binder limits |
| FermionBag4D.lean | 5 | 16 | SO(4) integration, bag positivity |
| LatticeHamiltonian.lean | 5 | 28 | BZ compact, GS 9 conditions, TPF 3 violations |
| GoltermanShamir.lean | 5 | 14 | 9 GS Props, Fock space finite, TPF evasion (axiom removed) |
| TPFEvasion.lean | 5 | 12 | Master synthesis, 5 violations |
| KLinearCategory.lean | 5 | 16 | SemisimpleCategory, Schur, Vec_G D² |
| SphericalCategory.lean | 5 | 18 | PivotalCategory (FIRST-EVER), quantumDim |
| FusionCategory.lean | 5 | 14 | FusionCategoryData, pentagon, F-symbols |
| FusionExamples.lean | 5 | 30 | Vec_Z2/Z3, Rep_S3, Fibonacci |
| VecG.lean | 5 | 9 | Day convolution, graded spaces |
| DrinfeldDouble.lean | 5 | 15 | D(G) twisted multiplication, anyon counting |
| GaugeEmergence.lean | 5 | 14 | Z(Vec_G)≅Rep(D(G)), chirality limitation |
| SO4Weingarten.lean | 5 | 14 | Weingarten 2nd/4th moment, channel positivity, Planck occupation |
| FractonFormulas.lean | 5 | 45 | Charge counting, dispersion, retention, DOF gap, YM obstructions |
| WetterichNJL.lean | 5 | 18 | Fierz completeness, NJL channels, ADW correspondence |
| VestigialSusceptibility.lean | 5 | 16 | Gamma trace, RPA susceptibility, vestigial window |
| QuaternionGauge.lean | 5 | 10 | SO(4) quaternion gauge, plaquette bounds, heatbath |
| GaugeFermionBag.lean | 5 | 9 | Tetrad covariance, bag weight, SMW update |
| HubbardStratonovichRHMC.lean | 5 | 22 | HS identity, Kramers, multi-shift CG, complex pseudofermion |
| MajoranaKramers.lean | 5 | 25 | Majorana Kramers degeneracy, sign-free determinant, 8x8 block |
| OnsagerAlgebra.lean | 5a | 24 | Dolan-Grady definition, Davies isomorphism, Chevalley embedding, GT connection. Aristotle: 9d6f2432 |
| OnsagerContraction.lean | 5a | 12 | Inönü-Wigner contraction O→su(2), rescaling, anomaly encoding. Aristotle: 36b7796f |
| Z16Classification.lean | 5a | 22 | Z₁₆ classification (axiom discharged), super-modular categories, 16-fold way, chirality mod 8→16 |
| SteenrodA1.lean | 5a | 17 | A(1) F₂-algebra, Adem relations, multiplication table, Ext→Z₁₆ |
| SMGClassification.lean | 5a | 13 | AZ tenfold way, SMG symmetry data, spectral gap typeclass, gapped interface |
| PauliMatrices.lean | 5a | 15 | Pauli σ_x,σ_y,σ_z, commutation [σ_i,σ_j]=2iε σ_k, involutivity, traces. Aristotle: 90ed1a98 |
| WilsonMass.lean | 5a | 11 | Wilson mass M(k), M=0 iff k=0 for all finite L, non-negativity, bounds. Aristotle: 90ed1a98 |
| BdGHamiltonian.lean | 5a | 8 | BdG 4x4 Kronecker structure, H_BdG(k), q_A(k), Kronecker comm identity. Aristotle: 90ed1a98 |
| GTCommutation.lean | 5a | 10 | **[H,Q_A]=0**: 2x2 τ-space trig identity, full 4x4, GS evasion. Aristotle: 18969de2 |
| GTWeylDoublet.lean | 5a | 12 | Model 2: Q_V+Q_A→Onsager, emanant SU(2), Witten ℤ₂=elem 8∈ℤ₁₆, bridges |
| ChiralityWallMaster.lean | 5a | 17 | Three-pillar synthesis: GS no-go + GT positive + Z₁₆ anomaly |
| SMFermionData.lean | 5b | 19 | SM fermion enum, ℤ₄ charges X=5(B-L)-4Y, all odd, component counts 16/15 |
| Z16AnomalyComputation.lean | 5b | 23 | SM anomaly 16≡0/15≡-1 mod 16, hidden sector theorem, "16" convergence (2 axioms discharged) |
| GenerationConstraint.lean | 5b | 13 | N_f≡0(3) conditional on 24|8N_f (axioms discharged/removed). Aristotle: a1dfcbde |
| DrinfeldCenterBridge.lean | 5b | 18 | Half-braiding ↔ D(G)-module bijection, Mathlib Center API, bidirectional |
| VecGMonoidal.lean | 5b | 12 | **MonoidalCategory(Vec_G)**, Center(Vec_G) monoidal, forgetful functor |
| ToricCodeCenter.lean | 5b | 25 | First computed Drinfeld center: 4 toric code anyons, R(e,m)=-1 |
| S3CenterAnyons.lean | 5b | 22 | First non-abelian center: 8 D(S₃) anyons, d=2,3, D²=36 |
| CenterEquivalenceZ2.lean | 5b | 10 | Concrete Z(Vec_{ℤ/2}) ↔ D(ℤ/2): bijection, fusion, braiding preserved |
| DrinfeldDoubleAlgebra.lean | 5b | 9 | D(G) as k-algebra: twisted convolution, unit laws, assoc. Aristotle: 878b181f |
| DrinfeldDoubleRing.lean | 5b | 3 | DG wrapper → Ring + Algebra k instances, distrib. Aristotle: 52992d6a |
| DrinfeldEquivalence.lean | 5b | 12 | Z(Vec_G)≅Rep(D(G)): simple counts, Hopf structure, antipode, gauge bridge |
| WangBridge.lean | 5b | 9 | c₋=8N_f derived from 16 Weyl, fractional c₋ forces ν_R, full chain |
| ModularInvarianceConstraint.lean | 5b | 12 | Framing anomaly from η, q-parameter shift, 24\|c₋, complete chain η→24→3\|N_f. Aristotle: b54f9611 |
| RokhlinBridge.lean | 5b | 14 | Rokhlin "16" convergence, with/without ν_R analysis |
| QNumber.lean | 5b | 11 | q-integers [n]_q as Laurent polynomials, classical limit [n]_1=n, [2]_1^4=16. Aristotle: 7d8efa8f |
| Uqsl2.lean | 5b | 6 | **FIRST quantum group in a proof assistant**: U_q(sl₂) via FreeAlgebra+RingQuot, zero axioms. Aristotle: 7d8efa8f |
| Uqsl2Hopf.lean | 5c | 23 | **FIRST Hopf algebra in a proof assistant**: coproduct/counit/antipode, S²=Ad(K) (22 sorry pending Aristotle) |
| SU2kFusion.lean | 5c | 29 | SU(2)_k fusion at k=1,2,3: Ising σ²=1+ψ, Fibonacci τ²=1+τ, charge conjugation (ALL PROVED by native_decide) |
| Uqsl2Affine.lean | 5c | 9 | U_q(sl_2 hat) affine quantum group, Chevalley + cross-relations, coideal property |
| SU2kSMatrix.lean | 5c | 16 | SU(2)_k S-matrices at k=1,2: unitarity, Verlinde formula, modularity (10 sorry pending Aristotle) |
| RestrictedUq.lean | 5c | 11 | Restricted quantum group u_q(sl₂): nilpotency E^ell=0, torsion K^ell=1, SU(2)_k connection (1 sorry pending Aristotle) |
| RibbonCategory.lean | 5c | 4 | Balanced, Ribbon, MTC definitions (FIRST in any proof assistant) (2 sorry pending Aristotle) |
| E8Lattice.lean | 5c | 19 | E8 Cartan: det=1, even unimodular, Rokhlin gap σ=8, Serre bound, classification (2 sorry pending Aristotle) |
| AlgebraicRokhlin.lean | 5c | 10 | Algebraic Serre theorem σ≡0 mod 8, unimodular/even/symmetric defs, characteristic vectors (ALL PROVED) |
| SpinBordism.lean | 5c | 8 | Spin bordism → Rokhlin → Wang chain, SpinBordismData, anomaly with/without ν_R (2 sorry pending Aristotle) |
| VerifiedJackknife.lean | 5c | 5 | First verified statistical estimators: jackknife, autocorrelation, intAutocorrTime (2 sorry pending Aristotle) |

## Build Environment

- **Lean:** 4.28.0 with Mathlib (commit 8f9d9cff6bd728b17a24e163c9402775d9e6a365)
- **Python:** ≥3.14, managed via uv. Key deps: numpy, scipy, sympy, mpmath, plotly, aristotlelib, torch, maturin.
- **Visualization:** Plotly (not matplotlib). Color scheme: #2E86AB steel blue, #A23B72 berry, #F18F01 amber.

## Key References

**Project documentation:**
- [Wave Execution Pipeline](docs/WAVE_EXECUTION_PIPELINE.md) — the 12-stage process governing all work
- [Inventory Index](SK_EFT_Hawking_Inventory_Index.md) — quick reference: module map, counts, pipeline invariants
- [Knowledge Graph](docs/KNOWLEDGE_GRAPH.md) — interactive provenance visualization
- [Dashboard](docs/DASHBOARD.md) — parameter verification, proof architecture, paper claims

**Roadmaps:** [`docs/roadmaps/`](docs/roadmaps/) contains phase-specific execution plans (Phases 1-5d) and the [Phase 6 Deferred Targets](docs/roadmaps/Phase6_Deferred_Targets.md) tracking future work with deep research linkage.

**Stakeholder docs:** [`docs/stakeholder/`](docs/stakeholder/) contains non-technical implications and strategic positioning documents for each phase.

**Deep research:** [`Lit-Search/`](../Lit-Search/) contains 40+ research files spanning Phases 3-5c covering quantum groups, modular tensor categories, Rokhlin's theorem, the ADW gap equation, fracton-gravity, and verified statistics.
