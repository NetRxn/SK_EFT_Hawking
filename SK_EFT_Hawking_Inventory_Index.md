# SK-EFT Hawking Inventory Index

**Purpose:** LLM-friendly quick reference for the full inventory (`SK_EFT_Hawking_Inventory.md`). Read this first; consult the full inventory for details.

**Last synced:** April 4, 2026 (Post Wave 7: 968 thm, 0 ax, 66 modules, 11 sorry pending Aristotle)

---

## Counts (ground truth — update atomically)

| Item | Count | Source of truth |
|------|-------|-----------------|
| Lean theorems | 968 (0 axioms) | `grep -c "^theorem" lean/SKEFTHawking/*.lean` |
| Aristotle-proved | 273 (270 machine + 3 manual) | ARISTOTLE_THEOREMS in constants.py |
| Manual proofs | 695 | 968 - 273 |
| **Sorry gaps** | **11** | 5 in QNumber.lean, 6 in Uqsl2.lean (Aristotle pending) |
| **Axioms** | **0** | All removed (Wave 6) |
| Lean modules | 66 | `ls lean/SKEFTHawking/*.lean` |
| Proved (zero sorry) | 957 | 968 - 11 |
| Python source modules | 49 | `find src/ -name "*.py" ! -name "__init__.py"` |
| Test files | 34 | `find tests/ -name "test_*.py"` |
| Test count | 1506+ | `pytest tests/ -q` |
| Figures | 72 | `grep -c "^def fig_" src/core/visualizations.py` |
| Notebooks | 28 | `ls notebooks/*.ipynb` |
| Papers | 11 | `ls papers/*/paper_draft.tex` |
| Validation checks | 16 | `python scripts/validate.py --list` |
| Stakeholder docs | 12 | See Section 9 of inventory |
| Aristotle runs | 33+ | See Aristotle run table in full inventory |
| Deep research tasks | 18 + 8 + 6 | 18 Phase-5 + 8 Phase-5a + 6 Phase-5b (incl. 4 q-Onsager)

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
- `formulas.py` — Canonical physics formulas with Lean refs (~59 functions including SM anomaly, Weingarten, NJL, fracton, Planck)
- `transonic_background.py` — 1D BEC transonic flow solver
- `visualizations.py` — All 72 Plotly figure functions + COLORS palette
- `aristotle_interface.py` — Aristotle API + sorry gap registry (all filled, zero unfilled)
- `sm_anomaly.py` — SM anomaly computation in ℤ₁₆: fermion data, anomaly index, generation constraint, hidden sector check
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
| GaugeErasure | 12 | Erasure theorem, U(1) survival (axiom removed) |
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
| GoltermanShamir | 15 | 9 conditions as substantive Props (C2 via ExteriorAlgebra, C3 via spectralGap, C5 via ground state, I1 via Hermitian, C4/C6 via resolvent), TPF evasion, Pauli exclusion, anti-commutation (axiom removed) |
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
| OnsagerContraction | 12 | Inönü-Wigner contraction O→su(2), rescaling, commutator vanishing, anomaly encoding (**ALL PROVED**, Aristotle `36b7796f` + manual) |
| Z16Classification | 22 | Z₁₆ classification (axiom discharged→theorem), SuperModularCategory, 16-fold way, chirality strengthening mod 8→16, anomaly cancellation, Drinfeld bridge (**ALL PROVED**) |
| SteenrodA1 | 17 | A(1) 8-dim F₂-algebra, explicit multiplication table, Adem relations, Ext→Z₁₆ connection (**ALL PROVED**, first Steenrod formalization) |
| SMGClassification | 13 | AZClass tenfold way, SMGSymmetryData, HasSpectralGap typeclass, gapped interface conjecture, conditional theorems (**ALL PROVED**) |
| PauliMatrices | 15 | σ_x,σ_y,σ_z definitions, commutation [σ_i,σ_j]=2iε_{ijk}σ_k, anti-commutation, involutivity, traces (**ALL PROVED**, Aristotle `90ed1a98`) |
| WilsonMass | 11 | M(k)=3-cos kx-cos ky-cos kz, M=0 iff k=0 (all finite L), non-negativity, bounds (**ALL PROVED**, Aristotle `90ed1a98`) |
| BdGHamiltonian | 8 | BdGIndex 4×4, H_BdG σ⊗τ Kronecker structure, q_A definition, Kronecker commutator identity (**ALL PROVED**, Aristotle `90ed1a98`) |
| GTCommutation | 10 | **Central theorem** [H_BdG(k),q_A(k)]=0, 2×2 τ-space trig identity, GS evasion, bridge to TPF (**ALL PROVED**, Aristotle `18969de2`) |
| GTWeylDoublet | 12 | Model 2: Q_V+Q_A generate Onsager, emanant SU(2), Witten anomaly=element 8∈ℤ₁₆, bridges to GS/TPF/Z₁₆ (**ALL PROVED**) |
| ChiralityWallMaster | 17 | Three-pillar synthesis: GS no-go + GT positive + Z₁₆ anomaly, bridge theorems, status structure (**ALL PROVED**) |
| SMFermionData | 19 | SM fermion enum, ℤ₄ charges X=5(B-L)-4Y, all odd, component counts 16/15, anomaly contributions (**ALL PROVED**) |
| Z16AnomalyComputation | 23 | Anomaly 16≡0 / 15≡-1 mod 16, 3-gen anomaly -3, hidden sector theorem, "16" convergence (2 axioms discharged→theorems) (**ALL PROVED**) |
| GenerationConstraint | 13 | c₋=8N_f (discharged→theorem) + modular_invariance_constraint (REMOVED, was false). N_f≡0(3) **derived** as conditional, minimal N_f=3 (**ALL PROVED**, Aristotle `a1dfcbde`) |
| DrinfeldCenterBridge | 18 | Half-braiding ↔ D(G)-module bijection, conjugation identities, Mathlib Center API, bidirectional encoding (**ALL PROVED**) |
| VecGMonoidal | 12 | **MonoidalCategory(Vec_G)** proved, Center(Vec_G) category+monoidal+braided, forgetful functor (**ALL PROVED**, Aristotle `48493889`) |
| ToricCodeCenter | 25 | 4 toric code anyons, fusion rules, R(e,m)=-1, fermion self-stats, first computed Drinfeld center (**ALL PROVED**) |
| S3CenterAnyons | 22 | 8 non-abelian anyons, d=1,1,2,3,3,2,2,2, D²=36=|S₃|², A3⊗A3 decomposition, first non-abelian center (**ALL PROVED**) |
| CenterEquivalenceZ2 | 10 | Concrete Z(Vec_{ℤ/2}) ↔ D(ℤ/2): bijection, fusion, braiding preserved (**ALL PROVED**) |
| DrinfeldDoubleAlgebra | 9 | D(G) as k-algebra: twisted convolution, unit laws, associativity, basis mul, abelian specialization (**ALL PROVED**, Aristotle `878b181f`) |
| DrinfeldDoubleRing | 3+4inst | DG newtype wrapper, Ring + Algebra k instances, distrib, basis_mul (**ALL PROVED**, Aristotle `52992d6a`) |
| DrinfeldEquivalence | 12 | Z(Vec_G)≅Rep(D(G)): simple counts, Hopf structure, antipode involutive, gauge emergence bridge (**ALL PROVED**) |
| WangBridge | 9 | Derives c₋=8N_f from SM fermion content (16 Weyl → c₋=8), fractional c₋ without ν_R, full chain to N_f≡0(3), "16 convergence" (**ALL PROVED**) |
| ModularInvarianceConstraint | 12 | ζ₂₄ root of unity, q-parameter shift (proved), framing anomaly 24\|c₋ ↔ phase=1, complete chain η→24→3\|N_f, Rokhlin "16" (**ALL PROVED**, Aristotle `b54f9611`) |
| RokhlinBridge | 14 | Rokhlin "16" convergence, with/without ν_R analysis (**ALL PROVED**) |
| QNumber | 11 | q-integers [n]_q as Laurent polynomials, classical limit [n]_1=n, [2]_1^4=16=DG_COEFF (**5 sorry pending Aristotle**) |
| Uqsl2 | 6 | **FIRST quantum group in a proof assistant**: U_q(sl_2) via FreeAlgebra+RingQuot, zero axioms, Chevalley relations (**6 sorry pending Aristotle**) |

---

## Pipeline invariants (from WAVE_EXECUTION_PIPELINE.md)

1. `formulas.py` is canonical — only place physics formulas live
2. `constants.py` is canonical — only place constants + Aristotle registry live
3. `visualizations.py` is canonical — only place figure functions live
4. Every formula has a Lean theorem (zero sorry)
5. Every computed quantity has bounds (CHECK 12)
6. Every paper claim traces to computation (CHECK 14)
7. Narrative derives from data (feasibility claims need computed support)
