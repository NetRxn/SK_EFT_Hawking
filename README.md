# Dissipative EFT Corrections to Analog Hawking Radiation

Computation and formal verification connecting Schwinger-Keldysh dissipative EFT
to acoustic Hawking radiation in BEC analog gravity. Six papers in a unified codebase:

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

**Lean 4 formalization:** 429 theorems + 2 axioms, zero sorry.
30 Lean modules. 99 Aristotle-proved across 27 runs. Lean 4.28.0, Mathlib commit `8f9d9cff`.

**Phase 5 additions:** Kappa-scaling predictions, polariton Tier 1, 4D fermion-bag MC pilot
(split transition detected at L=6,8), chirality wall formalization (GS 9 conditions,
TPF evasion machine-verified), Layer 1 categorical infrastructure (first-ever
PivotalCategory, FusionCategory, DrinfeldDouble in any proof assistant),
gauge emergence theorem Z(Vec_G) ≅ Rep(D(G)).

## Project Structure

```
SK_EFT_Hawking/
├── lean/                              # Lean 4 formalization (429 theorems + 2 axioms, zero sorry)
│   ├── lakefile.toml                  # Lake build config (pinned Mathlib)
│   ├── lean-toolchain                 # Lean 4 v4.28.0
│   ├── SKEFTHawking.lean              # Root module (imports all 30)
│   └── SKEFTHawking/
│       ├── Basic.lean                 # Shared types and definitions
│       ├── AcousticMetric.lean        # Structure A: acoustic metric (8 theorems)
│       ├── SKDoubling.lean            # Structure B: SK doubling + KMS (9 theorems)
│       ├── HawkingUniversality.lean   # Structure C: universality + κ-crossing + spin-sonic (9 theorems)
│       ├── SecondOrderSK.lean         # Phase 2: second-order counting + stress tests (19 theorems)
│       ├── WKBAnalysis.lean           # Phase 2: WKB + Bogoliubov bound (15 theorems)
│       ├── CGLTransform.lean          # Phase 2: CGL FDR derivation (7 theorems)
│       ├── ThirdOrderSK.lean          # Phase 3: third-order EFT + parity alternation (14 theorems)
│       ├── GaugeErasure.lean          # Phase 3: gauge erasure theorem (11 theorems + 1 axiom)
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
│       ├── GoltermanShamir.lean       # Phase 5: 9 GS Props, Fock space finite (15 theorems + 1 axiom)
│       ├── TPFEvasion.lean            # Phase 5: master synthesis, 5 violations (12 theorems)
│       ├── KLinearCategory.lean       # Phase 5: semisimple, Schur, fusion rules (16 theorems)
│       ├── SphericalCategory.lean     # Phase 5: FIRST-EVER pivotal + spherical (18 theorems)
│       ├── FusionCategory.lean        # Phase 5: fusion axioms, pentagon, F-symbols (14 theorems)
│       ├── FusionExamples.lean        # Phase 5: Vec_Z2/Z3, Rep_S3, Fibonacci (30 theorems)
│       ├── VecG.lean                  # Phase 5: Day convolution, graded spaces (9 theorems)
│       ├── DrinfeldDouble.lean        # Phase 5: D(G) twisted multiplication (15 theorems)
│       └── GaugeEmergence.lean        # Phase 5: Z(Vec_G)≅Rep(D(G)), chirality (14 theorems)
│
├── src/
│   ├── core/                          # Shared infrastructure
│   │   ├── transonic_background.py    # 1D BEC transonic flow solver + δ_diss estimates
│   │   ├── aristotle_interface.py     # Aristotle API + sorry-gap registry (56 proved)
│   │   └── visualizations.py          # Plotly figures + interactive dashboard
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
│   ├── experimental/                  # Experimental prediction package (Phase 4 Wave 1)
│   │   └── predictions.py            # Platform tables, detector requirements, kappa-scaling
│   ├── chirality/                     # Chirality wall synthesis (Phase 4 Wave 1)
│   │   └── tpf_gs_analysis.py        # GS conditions vs TPF evasion
│   ├── vestigial/                     # Vestigial gravity simulation (Phase 4 Wave 2)
│   │   ├── lattice_model.py           # Lattice Hamiltonian, HS-transformed ADW
│   │   ├── mean_field.py              # Extended mean-field with metric correlator
│   │   ├── monte_carlo.py             # Metropolis-Hastings sampler
│   │   ├── phase_diagram.py           # Coupling scan and phase classification
│   │   └── finite_size.py             # Binder cumulant + finite-size scaling
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
├── docs/
│   ├── roadmaps/                      # Phase 1 + Phase 2 technical roadmaps
│   ├── stakeholder/                   # Implications, strategic positioning, companion guides
│   ├── aristotle_results/             # All 13 Aristotle run archives
│   └── archive/                       # Superseded artifacts
│
├── tests/                             # pytest suite (1014 tests)
│   ├── test_transonic_background.py   # Physics validation
│   ├── test_second_order.py           # Enumeration + WKB tests
│   ├── test_gauge_erasure.py          # Gauge erasure theorem tests
│   ├── test_wkb_connection.py         # Exact WKB connection tests (65 tests)
│   ├── test_adw.py                    # ADW gap equation tests (78 tests)
│   ├── test_cross_validation.py       # Cross-layer validation
│   └── test_lean_integrity.py         # Module structure + sorry-gap regression
│
├── figures/                           # 61 pipeline figures (PNG + HTML)
├── scripts/
│   └── submit_to_aristotle.py         # Aristotle submission + integration script
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
| Steinhauer ⁸⁷Rb | 0.64 | 1.15 | 0.03 | 0.013 | 1.8e-4 | 6.5e-5 |
| Heidelberg ³⁹K | 0.42 | 3.92 | 0.12 | 0.012 | 1.4e-4 | 1.8e-3 |
| Trento ²³Na (spin) | 1.26 | 2.19 | 0.03 | 0.014 | 1.9e-4 | 1.6e-5 |

### Phase 2: Second-Order Correction (Frequency-Dependent)

- Counting formula: count(N) = ⌊(N+1)/2⌋ + 1 at EFT order N
- Two new coefficients at second order, both requiring broken spatial parity
- δ^(2)(ω) ∝ ω³ — spectral distortion absent at first order
- Positivity constraint: (γ_{2,1} + γ_{2,2})² ≤ 4·γ₂·γ_x·β
- Formally verified logical chain: firstOrderCorrection = 0 ↔ dampingRate = 0 ↔ all γᵢ = 0

## Theorem Inventory (429 + 2 axioms — ZERO sorry)

| Module | Phase | Theorems | Notes |
|---|---|---|---|
| AcousticMetric.lean | 1 | 8 | Aristotle: 082e6776, a87f425a, 88cf2000 |
| SKDoubling.lean | 1 | 9 | Aristotle: 082e6776, 638c5ff3, 270e77a0, 20556034 |
| HawkingUniversality.lean | 1+3 | 9 | +κ-crossing, spin-sonic |
| SecondOrderSK.lean | 2 | 19 | Aristotle: d61290fd, c4d73ca8, 3eedcabb |
| WKBAnalysis.lean | 2+3 | 15 | Aristotle: 518636d7 |
| CGLTransform.lean | 2 | 7 | CGL FDR derivation |
| ThirdOrderSK.lean | 3 | 14 | Parity alternation theorem |
| GaugeErasure.lean | 3 | 11 + 1 axiom | Gauge erasure |
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
| GoltermanShamir.lean | 5 | 15 + 1 axiom | 9 GS Props, Fock space finite, TPF evasion |
| TPFEvasion.lean | 5 | 12 | Master synthesis, 5 violations |
| KLinearCategory.lean | 5 | 16 | SemisimpleCategory, Schur, Vec_G D² |
| SphericalCategory.lean | 5 | 18 | PivotalCategory (FIRST-EVER), quantumDim |
| FusionCategory.lean | 5 | 14 | FusionCategoryData, pentagon, F-symbols |
| FusionExamples.lean | 5 | 30 | Vec_Z2/Z3, Rep_S3, Fibonacci |
| VecG.lean | 5 | 9 | Day convolution, graded spaces |
| DrinfeldDouble.lean | 5 | 15 | D(G) twisted multiplication, anyon counting |
| GaugeEmergence.lean | 5 | 14 | Z(Vec_G)≅Rep(D(G)), chirality limitation |

## Build Environment

- **Lean:** 4.28.0 with Mathlib (commit 8f9d9cff6bd728b17a24e163c9402775d9e6a365)
- **Python:** ≥3.11, managed via uv. Key deps: numpy, scipy, sympy, mpmath, plotly, aristotlelib.
- **Visualization:** Plotly (not matplotlib). Color scheme: #2E86AB steel blue, #A23B72 berry, #F18F01 amber.

## References

See `docs/roadmaps/Phase1_Roadmap.md` through `docs/roadmaps/Phase4_Roadmap.md` for full technical context and reference lists.
