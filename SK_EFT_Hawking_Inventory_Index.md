# SK-EFT Hawking Inventory Index

**Purpose:** LLM-friendly quick reference for the full inventory (`SK_EFT_Hawking_Inventory.md`). Read this first; consult the full inventory for details.

**Last synced:** April 3, 2026 (Phase 5a Waves 1A+3A: OnsagerAlgebra + Z16Classification added)

---

## Counts (ground truth — update atomically)

| Item | Count | Source of truth |
|------|-------|-----------------|
| Lean theorems | 675 + 3 axioms | `grep -c "^theorem" lean/SKEFTHawking/*.lean` |
| Aristotle-proved | 234 | ARISTOTLE_THEOREMS in constants.py (211 prior + 22 RHMC manual + 1 Onsager) |
| Manual proofs | 439 | 675 - 234 - 2 sorry |
| **Sorry gaps** | **2** | OnsagerContraction (2, Aristotle in flight — 13%) |
| Lean modules | 43 | `ls lean/SKEFTHawking/*.lean` |
| Proved (zero sorry) | 672 + 3ax | 3 sorry pending Aristotle |
| Python source modules | 47 | `find src/ -name "*.py" ! -name "__init__.py"` |
| Test files | 24 | `find tests/ -name "test_*.py"` |
| Test count | 1339 | `pytest tests/ -q` |
| Figures | 64 | `grep -c FigureSpec review_figures.py` |
| Notebooks | 20 | `ls notebooks/*.ipynb` |
| Papers | 7 + tables | `ls papers/*/paper_draft.tex` |
| Validation checks | 15 | `python scripts/validate.py --list` (all 15 pass) |
| Stakeholder docs | 12 | See Section 9 of inventory |
| Aristotle runs | 30+ | See Aristotle run table in full inventory |
| Deep research tasks | 18 + 6 Phase-5a | 18 Phase-5 complete + 6 Phase-5a complete |

---

## Inventory Sections → What to update

| Section | Covers | When to update |
|---------|--------|----------------|
| 1. Python Source | All `src/` modules with purpose + line counts | New module added or module purpose changes |
| 2. Lean Verification | 16-module table: lines, theorem count, key results | Theorem added/removed, module added |
| 3. Aristotle | Run table with dates + theorem counts | New Aristotle submission |
| 4. Notebooks | 16-notebook table: phase, topic | Notebook added or topic changes |
| 5. Papers | 7-paper table: format, lines, topic, key claims | Paper content changes |
| 6. Tests | 16-file table: test counts, coverage | Test file added or count changes |
| 7. Scripts | 11-script table | Script added or purpose changes |
| 8. Configuration | Dependency table | Dependency added |
| 9. Documentation | Reference, roadmap, stakeholder, analysis tables | Doc added/moved/content changes |
| 10. Key Formulas | Physics formulas with Lean refs | Formula added to formulas.py |
| Summary Table | All counts | Any count changes (run verification commands above) |

---

## Source module map (module → purpose, one line each)

### Core (`src/core/`)
- `constants.py` — Physical constants, experimental params, Aristotle registry, NJL/ADW model params
- `formulas.py` — Canonical physics formulas with Lean refs (~55 functions including Weingarten, NJL, fracton, Planck)
- `transonic_background.py` — 1D BEC transonic flow solver
- `visualizations.py` — All 43 Plotly figure functions + COLORS palette
- `aristotle_interface.py` — Aristotle API + sorry gap registry (all filled)
- `provenance.py` — Parameter provenance registry (PARAMETER_PROVENANCE, tiers, verification dates)
- `citations.py` — Citation registry (CITATION_REGISTRY, DOI tracking, usage mapping)

### Phase 1-2 (`src/second_order/`)
- `enumeration.py` — Transport coefficient counting: count(N) = floor((N+1)/2)+1
- `coefficients.py` — Second-order data structures + action constructors
- `wkb_analysis.py` — WKB mode analysis, frequency-dependent Bogoliubov
- `cgl_derivation.py` — CGL dynamical KMS → FDR at arbitrary order

### Phase 3 (`src/gauge_erasure/`, `src/wkb/`, `src/adw/`)
- `gauge_erasure/erasure_theorem.py` — Non-Abelian gauge erasure → U(1) survives
- `wkb/connection_formula.py` — Exact WKB through complex turning point
- `wkb/bogoliubov.py` — Modified unitarity, decoherence
- `wkb/spectrum.py` — Full Hawking spectrum with corrections + noise
- `wkb/backreaction.py` — Acoustic BH cooling toward extremality
- `adw/wen_model.py` — Wen's lattice QED (UV completion)
- `adw/hubbard_stratonovich.py` — HS decomposition → composite tetrad
- `adw/gap_equation.py` — Coleman-Weinberg V_eff, G_c
- `adw/fluctuations.py` — SSB, NG modes (2 gravitons in 4D), Vergeles check
- `adw/ginzburg_landau.py` — GL expansion, He-3 analogy

### Phase 4 (`src/experimental/`, `src/chirality/`, `src/fracton/`, `src/vestigial/`)
- `experimental/predictions.py` — Platform prediction tables, shot counts
- `experimental/kappa_scaling.py` — Physical kappa-scaling sweeps for all platforms
- `chirality/tpf_gs_analysis.py` — TPF vs GS no-go: 2/4 conditions evaded
- `fracton/sk_eft.py` — Fracton SK-EFT, binomial charge counting
- `fracton/information_retention.py` — Fracton retains exponentially more UV info
- `fracton/gravity_connection.py` — Kerr-Schild bootstrap, DOF gap
- `fracton/non_abelian.py` — Non-Abelian fracton obstruction (negative result)
- `vestigial/mean_field.py` — Curvature-based 3-phase classification
- `vestigial/lattice_model.py` — Euclidean lattice formulation
- `vestigial/monte_carlo.py` — Metropolis MC for lattice model
- `vestigial/phase_diagram.py` — Phase diagram from MF + MC
- `vestigial/finite_size.py` — Finite-size scaling analysis
- `vestigial/su2_integration.py` — Analytical SU(2) Haar measure integration
- `vestigial/grassmann_trg.py` — 2D Grassmann TRG implementation
- `vestigial/lattice_4d.py` — 4D hypercubic lattice model with SO(4) gauge integration
- `vestigial/fermion_bag.py` — Fermion-bag MC algorithm for 8-fermion vertices (ADW Option B)
- `vestigial/wetterich_model.py` — NJL fermion-bag MC (Option C, gauge-link-free, staggered OPs)
- `vestigial/phase_scan.py` — 4D coupling scan with Binder cumulant analysis (ADW + NJL)
- `vestigial/quaternion.py` — SU(2) quaternion algebra for SO(4) gauge (Wave 7A)
- `vestigial/so4_gauge.py` — SO(4) gauge theory via quaternion pairs, heatbath (Wave 7A)
- `vestigial/gauge_fermion_bag.py` — Hybrid fermion-bag + gauge-link MC (Wave 7B)
- `vestigial/gauge_fermion_bag_majorana.py` — 8×8 Majorana sign-free fermion-bag (Wave 7B)
- `vestigial/hs_rhmc.py` — HS+RHMC algorithm, numpy/scipy reference (Wave 7C)
- `vestigial/hs_rhmc_jax.py` — JAX CPU backend for RHMC (Wave 7C)
- `vestigial/hs_rhmc_torch.py` — PyTorch CPU backend for RHMC (production default) (Wave 7C)
- `experimental/polariton_predictions.py` — Tier 1 polariton platform predictions (Wave 1B)

---

## Lean module map (module → theorem count, key result)

| Module | Thms | Key Result |
|--------|------|------------|
| Basic | 0 | Type definitions |
| AcousticMetric | 8 | det(g)=-ρ², T_H formula |
| SKDoubling | 9 | Uniqueness, FDR, zeroTemp_nontrivial |
| HawkingUniversality | 9 | Universality theorem |
| SecondOrderSK | 19 | Counting formula, positivity constraint |
| WKBAnalysis | 15 | Damping biconditionals, turning point |
| CGLTransform | 7 | CGL FDR, Einstein relation |
| ThirdOrderSK | 14 | Parity alternation (general N) |
| GaugeErasure | 11+1ax | Erasure theorem, U(1) survival |
| WKBConnection | 17 | Decoherence, noise floor, unitarity |
| ADWMechanism | 21 | Critical coupling, NG modes |
| ChiralityWall | 17 | GS no-go requires all, TPF evasion |
| VestigialGravity | 18 | Phase hierarchy, EP violation |
| FractonHydro | 17 | Binomial monotonicity, erasure universal |
| FractonGravity | 20 | Bootstrap divergence, DOF gap |
| FractonNonAbelian | 14 | YM incompatibility |
| KappaScaling | 11 | Crossover balance, regime classification |
| PolaritonTier1 | 6 | Spatial attenuation ≥ 1, monotonicity, BEC recovery |
| SU2PseudoReality | 10 | One-link normalization, effective coupling, Binder cumulant limits |
| FermionBag4D | 16 | SO(4) integration, 8-fermion bounds, bag positivity+boundedness, Binder range, vestigial splitting |
| LatticeHamiltonian | 28 | BZ compact, GS 9 conditions, TPF 3 violations, ℓ²(ℤ) ∞-dim, round discontinuous, Hermitian trace real |
| GoltermanShamir | 14+1ax | 9 conditions as substantive Props (C2 via ExteriorAlgebra, C3 via spectralGap, C5 via ground state, I1 via Hermitian, C4/C6 via resolvent), TPF evasion, Pauli exclusion, anti-commutation |
| TPFEvasion | 12 | Master synthesis: 5 violations assembled, tpf_outside_gs_scope_main, two_violations_proved |
| KLinearCategory | 16 | SemisimpleCategory, FinitelyManySimples, Schur orthogonality, FusionRules, Vec_G D²=\|G\|, Rep(S₃) D²=6 |
| SphericalCategory | 18 | PivotalCategory (FIRST-EVER), CategoricalTrace, SphericalCategory, quantumDim, fibonacci φ²=φ+1, chirality limitation |
| FusionCategory | 14 | FusionCategoryData with axioms, FSymbolData, PentagonSatisfied, globalDimSq_pos, totalMult_unit, Frobenius-Perron |
| FusionExamples | 30 | Vec_{Z/2}, Vec_{Z/3}, Rep(S₃), Fibonacci: fusion rules, commutativity, unit fusion, τ⊗τ=1⊕τ, F-matrix, chirality |
| VecG | 9 | GradedVectorSpace, Day convolution, unit/assoc/simple tensor, dim multiplicativity |
| DrinfeldDouble | 15 | DrinfeldDoubleElement, twisted multiplication, conjugation action, D(G) unit laws, anyon counting |
| GaugeEmergence | 14 | Half-braiding, gauge emergence Z(Vec_G)≅Rep(D(G)), chirality limitation c≡0(8), Layer 1→2→3 bridge |
| SO4Weingarten | 14 | Weingarten 2nd/4th moment, channel positivity, bond weight, Planck occupation (**ALL PROVED, zero sorry**) |
| FractonFormulas | 45 | Charge counting, dispersion, retention, DOF gap, YM obstructions (**ALL PROVED**, Aristotle `4528aa2b`) |
| WetterichNJL | 18 | Fierz completeness, scalar/pseudoscalar/vector channels, NJL-ADW correspondence (**ALL PROVED**, Aristotle `4528aa2b`) |
| VestigialSusceptibility | 16 | Gamma trace, u_g positivity, bubble integral Π₀, RPA susceptibility, vestigial_before_tetrad, exponential window (**ALL PROVED**, Aristotle `9e2251cd`) |
| QuaternionGauge | 10 | Unit quaternion norm, identity, conjugate inverse, SO(4) dim, plaquette bounds, heatbath detailed balance (**ALL PROVED**, Aristotle `fb657b4d`) |
| GaugeFermionBag | 9 | Tetrad gauge covariance, metric invariance, bag weight real, SMW update, vestigial diagnostic, Binder limits (**ALL PROVED**, Aristotle `fb657b4d`) |
| HubbardStratonovichRHMC | 22 | HS identity, Kramers, multi-shift CG, complex pseudofermion Pfaffian identity |
| MajoranaKramers | 25 | Majorana Kramers degeneracy, sign-free determinant, 8x8 block structure |
| OnsagerAlgebra | 24 | Dolan-Grady definition, Davies isomorphism, Chevalley embedding into L(sl₂), GT connection (**ALL PROVED**, Aristotle `9d6f2432`) |
| OnsagerContraction | 12 | Inönü-Wigner contraction O→su(2), rescaling, commutator vanishing, anomaly encoding (**2 sorry pending Aristotle**) |
| Z16Classification | 21+1ax | Z₁₆ axiom, SuperModularCategory, 16-fold way, chirality strengthening mod 8→16, anomaly cancellation, Drinfeld bridge (**ALL PROVED**) |
| SteenrodA1 | 17 | A(1) 8-dim F₂-algebra, explicit multiplication table, Adem relations, Ext→Z₁₆ connection (**ALL PROVED**, first Steenrod formalization) |
| SMGClassification | 13 | AZClass tenfold way, SMGSymmetryData, HasSpectralGap typeclass, gapped interface conjecture, conditional theorems (**ALL PROVED**) |

---

## Pipeline invariants (from WAVE_EXECUTION_PIPELINE.md)

1. `formulas.py` is canonical — only place physics formulas live
2. `constants.py` is canonical — only place constants + Aristotle registry live
3. `visualizations.py` is canonical — only place figure functions live
4. Every formula has a Lean theorem (zero sorry)
5. Every computed quantity has bounds (CHECK 12)
6. Every paper claim traces to computation (CHECK 14)
7. Narrative derives from data (feasibility claims need computed support)
