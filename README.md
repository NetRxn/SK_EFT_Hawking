# Dissipative EFT Corrections to Analog Hawking Radiation

Computation and formal verification connecting Schwinger-Keldysh dissipative EFT
to acoustic Hawking radiation in BEC analog gravity. Ten papers in a unified codebase:

- **Paper 1 (first-order):** Two transport coefficients (γ₁, γ₂), frequency-independent
  δ_diss = Γ_H/κ correction. PRL format, submission-ready.
- **Paper 2 (second-order):** Two additional coefficients (γ_{2,1}, γ_{2,2}),
  frequency-dependent ω³ spectral distortion, WKB mode analysis, CGL FDR derivation.
- **Paper 3 (gauge erasure):** Universal structural theorem — non-Abelian gauge DOF
  erased by hydrodynamization, U(1) survives (photonization). PRL format.
- **Paper 4 (exact WKB):** Non-perturbative connection formula: modified unitarity
  |α|²-|β|²=1-δ_k, FDR noise floor, spectral floor at ω≳6T_H. PRD format.
- **Paper 5 (ADW gap equation):** Mean-field tetrad condensation via the
  Akama-Diakonov-Wetterich mechanism. Qualified positive result: nontrivial
  Lorentzian solution for G > G_c, 2 massless graviton modes as Higgs bosons.
  Four structural obstacles for emergent fermion bootstrap. PRD format.
- **Paper 6 (vestigial gravity):** Lattice evidence for vestigial metric phase
  in the ADW model. Three-phase structure: pre-geometric, vestigial, full tetrad.
  EP violation prediction. Monte Carlo + mean-field. PRD format.

- **Paper 7 (chirality wall):** First formal verification of the Golterman-Shamir
  no-go conditions and TPF evasion in Lean 4. PRD/CPC format.

- **Paper 8 (chirality master):** Three-pillar chirality wall: GS no-go + GT positive
  construction + Z₁₆ anomaly classification. PRL format.

- **Paper 9 (SM anomaly + Drinfeld center):** First formally verified anomaly
  constraint in particle physics. SM anomaly in Z16, generation constraint,
  toric code center, D(S3) non-abelian center. PRL format.

- **Paper 10 (modular generation):** From modular forms to generation counting.
  First formal derivation connecting number-theoretic modular invariance to
  SM generation constraint N_f = 0 mod 3. PRD format.

**Lean 4 formalization:** 951 theorems across 64 Lean modules. Zero axioms, zero sorry.
273 Aristotle-proved across 33+ runs.
Lean 4.28.0, Mathlib commit `8f9d9cff`.

**Phase 5 additions:** Kappa-scaling predictions, polariton Tier 1, Weingarten multi-channel
MC framework (Lean-verified), chirality wall formalization (GS 9 conditions,
TPF evasion machine-verified), Layer 1 categorical infrastructure (first-ever
PivotalCategory, FusionCategory, DrinfeldDouble in any proof assistant),
gauge emergence theorem Z(Vec_G) ≅ Rep(D(G)), analytical vestigial susceptibility,
hybrid gauge-link + fermion-bag MC, HS+RHMC with 8×8 Majorana sign-free fermions (L=4 complete, L=8 in flight).

## Project Structure

```
SK_EFT_Hawking/
├── lean/                              # Lean 4 formalization (951 theorems, 0 axioms, 64 modules, zero sorry)
│   ├── lakefile.toml                  # Lake build config (pinned Mathlib)
│   ├── lean-toolchain                 # Lean 4 v4.28.0
│   ├── SKEFTHawking.lean              # Root module (imports all 64)
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
│       ├── GoltermanShamir.lean       # Phase 5: 9 GS Props, Fock space finite (15 theorems)
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
│       └── RokhlinBridge.lean         # Phase 5b: Rokhlin "16" convergence (14 theorems)
│
├── src/
│   ├── core/                          # Shared infrastructure
│   │   ├── transonic_background.py    # 1D BEC transonic flow solver + δ_diss estimates
│   │   ├── aristotle_interface.py     # Aristotle API + sorry-gap registry (273 proved)
│   │   ├── visualizations.py          # Plotly figures (72 functions) + COLORS palette
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
│   ├── Phase5b_Synthesis_Technical.ipynb        # Phase 5: kappa-scaling, categorical, Drinfeld
│   └── Phase5b_Synthesis_Stakeholder.ipynb
│
├── docker/
│   └── docker-compose.graph.yml       # PG+AGE container for knowledge graph (port 5433)
│
├── docs/
│   ├── KNOWLEDGE_GRAPH.md             # Knowledge graph documentation and guide
│   ├── roadmaps/                      # Phase 1 + Phase 2 technical roadmaps
│   ├── stakeholder/                   # Implications, strategic positioning, companion guides
│   ├── aristotle_results/             # All 13 Aristotle run archives
│   └── archive/                       # Superseded artifacts
│
├── tests/                             # pytest suite (1245 tests across 19 files)
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
├── figures/                           # 64 pipeline figures (PNG + HTML) + provenance_graph.json
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

## Main Physics Results

### Phase 1: First-Order Correction (Frequency-Independent)

T_eff = T_H(1 + δ_disp + δ_diss + δ_cross)

- δ_disp = (κξ/c_s)² — dispersive, known (Corley-Jacobson)
- δ_diss = Γ_H/κ — **dissipative, our result**
- Γ_H = 1.1 · γ_Bel where γ_Bel = √(na_s³) · κ²/c_s
- Spin-sonic enhancement: ×(c_density/c_spin)² ≈ 100
- FirstOrderKMS: Aristotle discovered the correct KMS structure constraining all 9 coefficients → 2 free parameters

| Experiment | ξ [μm] | c_s [mm/s] | T_H [nK] | D | δ_disp | δ_diss |
|---|---|---|---|---|---|---|
| Steinhauer ⁸⁷Rb | 1.57 | 0.46 | 0.006 | 0.013 | 8.5e-5 | 4.2e-4 |
| Heidelberg ³⁹K | 0.48 | 3.37 | 0.12 | 0.012 | 7.3e-5 | 2.0e-5 |
| Trento ²³Na (spin) | 1.51 | 1.83 | 0.03 | 0.014 | 9.9e-5 | 9.3e-5 |

### Phase 2: Second-Order Correction (Frequency-Dependent)

- Counting formula: count(N) = ⌊(N+1)/2⌋ + 1 at EFT order N
- Two new coefficients at second order, both requiring broken spatial parity
- δ^(2)(ω) ∝ ω³ — spectral distortion absent at first order
- Positivity constraint: (γ_{2,1} + γ_{2,2})² ≤ 4·γ₂·γ_x·β
- Formally verified logical chain: firstOrderCorrection = 0 ↔ dampingRate = 0 ↔ all γᵢ = 0

## Theorem Inventory (951 theorems — zero axioms, zero sorry)

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
| GoltermanShamir.lean | 5 | 15 | 9 GS Props, Fock space finite, TPF evasion (axiom removed) |
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

## Build Environment

- **Lean:** 4.28.0 with Mathlib (commit 8f9d9cff6bd728b17a24e163c9402775d9e6a365)
- **Python:** ≥3.14, managed via uv. Key deps: numpy, scipy, sympy, mpmath, plotly, aristotlelib, torch, maturin.
- **Visualization:** Plotly (not matplotlib). Color scheme: #2E86AB steel blue, #A23B72 berry, #F18F01 amber.

## References

See `docs/roadmaps/Phase1_Roadmap.md` through `docs/roadmaps/Phase4_Roadmap.md` for full technical context and reference lists.
