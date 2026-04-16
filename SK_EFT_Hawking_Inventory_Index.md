# SK-EFT Hawking Inventory Index

**Purpose:** LLM-friendly quick reference for the full inventory (`SK_EFT_Hawking_Inventory.md`). Read this first; consult the full inventory for details.

**Last synced:** 2026-04-15 (**Phase 5i COMPLETE** via Wave 4: generic `PolyQuotQ n` + `PolyQuotOver K m` tower primitives consolidate all 7 number fields in the project; new modules `QCyc3`, `QCyc15`, `QCyc15SqrtPhi`, `SU3k2SMatrix`, `SU3k2FSymbols`; first non-cyclotomic number field (Q(ζ₁₅, √φ)) via tower; first rank-6 MTC modular data (SU(3)₂); first SU(3)₂ F-symbols; Mathlib-upstream-ready architecture unblocking Phase 5g Track B. Wave 4 commits: `bd92d3b` 4a / `b576fe8` 4b / `5064c4c` 4b.ext / `e7e111a` 4c-part1 (mulReduce bug fix: lazy-closure-reeval → Array-based + eager materialization) / `112f562` 4c-part2 / `43872e6` 4c-part3 / `bf5efce` 4d. Full package 8403 jobs clean. Earlier same day: Phase 5p Waves 1-6 (D2Formula, FPdim, Müger bridge, SymmetricCategory); Phase 5e W7-8.)

---

## Counts (ground truth — update atomically)

**Source of truth:** `docs/counts.json`, regenerated via `scripts/update_counts.py` (which re-runs `extract_lean_deps.py` when Lean source hashes change).

| Item | Count | Source of truth |
|------|-------|-----------------|
| Lean theorems | **3066+** (post-Phase-5i-Wave-4; 37 new theorems from 4c/4d modules + mulReduce bug fix; authoritative count via `update_counts.py`) | counts.json — package-module-bound count |
| Placeholders (True := trivial) | **78** | Module summaries + content placeholders; see PLACEHOLDER_THEOREMS in constants.py |
| Aristotle-proved | **322** (machine) | ARISTOTLE_THEOREMS in constants.py; 44 Aristotle runs total |
| **Sorry gaps** | **0** | Project-wide. Uqsl2Hopf, Uqsl2AffineHopf, Uqsl3, Uqsl3Hopf all 0 sorry. CenterFunctor 0 sorry (2 tracked hypotheses as `Prop` defs). |
| **Axioms** | **1** | gapped_interface_axiom in SPTClassification.lean |
| Lean modules | **141** | All `.lean` files in `lean/SKEFTHawking/*` (excluding `ExtractDeps.lean`). +2 since last sync: Phase 5w Wave 2 DiracFluidMetric.lean (9 thms), Wave 3 GrapheneHawking.lean (7 thms). |
| Lean definitions | **2400** | counts.json |
| Python source modules | **53** | |
| Test files | **48** | +2: test_graphene_metric.py (26), test_graphene_hawking.py (21) |
| Test count | 1660+ | `pytest tests/ -q` |
| Figures | **103** | `grep -c "^def fig_" src/core/visualizations.py` (+2: graphene T_H sweep, dissipation window) |
| Notebooks | **49** | `ls notebooks/*.ipynb` (+1: Phase5w_GrapheneDiracFluid_Technical) |
| Papers | **15** | `ls papers/paper*/paper_draft.tex` |
| Validation checks | 16 | `python scripts/validate.py --list` |
| Stakeholder docs | 22 | See Section 9 of inventory |
| Aristotle runs | 44 | See Aristotle run table in full inventory |
| Deep research tasks | 18 + 8 + 6 + 6 | 18 Phase-5 + 8 Phase-5a + 6 Phase-5b + 6 Phase-5e


---

## Inventory Sections → What to update

| Section | Covers | When to update |
|---------|--------|----------------|
| 1. Python Source | All `src/` modules with purpose + line counts | New module added or module purpose changes |
| 2. Lean Verification | 94-module table: lines, theorem count, key results | Theorem added/removed, module added |
| 3. Aristotle | Run table with dates + theorem counts | New Aristotle submission |
| 4. Notebooks | 42-notebook table: phase, topic | Notebook added or topic changes |
| 5. Papers | 14-paper table: format, lines, topic, key claims | Paper content changes |
| 6. Tests | 43-file table: test counts, coverage | Test file added or count changes |
| 7. Scripts | 14-script table | Script added or purpose changes |
| 8. Configuration | Dependency table | Dependency added |
| 9. Documentation | Reference, roadmap, stakeholder, analysis tables | Doc added/moved/content changes |
| 10. Key Formulas | Physics formulas with Lean refs | Formula added to formulas.py |
| Summary Table | All counts | Any count changes (run verification commands above) |

---

## Source module map (module → purpose, one line each)

### Core (`src/core/`)
- `constants.py` — Physical constants, experimental params, Aristotle registry, NJL/ADW model params
- `formulas.py` — Canonical physics formulas with Lean refs (137 functions including SM anomaly, Weingarten, NJL, fracton, Planck, quantum group, SU(2)_k fusion/S-matrix, E8/Rokhlin)
- `transonic_background.py` — 1D BEC transonic flow solver
- `visualizations.py` — All 80 Plotly figure functions + COLORS palette
- `aristotle_interface.py` — Aristotle API + sorry gap registry (24 unfilled across 3 Lean modules)
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
- `adw/tetrad_gap_solver.py` — NJL-type gap equation solver, Δ*(G) curve, MF-guided scan params (Phase 5d)
- `adw/tetrad_observables.py` — MC observables: O_tet, O_met, Binder U₄, spatial correlator C(r) (Phase 5d)
- `chirality/gioia_thorngren.py` — Gioia-Thorngren chirality analysis (Phase 5a)

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
| DiracFluidMetric | 9 | **Phase 5w Wave 2:** 3×3 Dirac fluid acoustic metric, c_s = v_F/√2, block-diag for quasi-1D, horizon at v=c_s, Lorentzian signature (**ALL PROVED, zero sorry**) |
| GrapheneHawking | 7 | **Phase 5w Wave 3:** Dispersive correction bound, T_eff positivity, EFT validity (D<1), subluminal robustness, dissipative negligibility (**ALL PROVED, zero sorry**) |
| SKDoubling | 9 | Uniqueness, FDR, zeroTemp_nontrivial |
| HawkingUniversality | 9 | Universality theorem |
| SecondOrderSK | 24 | Counting formula, positivity constraint; Phase 5u Wave 1b added `GammaH`, `gammaH_def/_via_kH/_nonneg`, `deltaDissFromTransport`, `deltaDissFromTransport_eq/_zero_iff` — grounds Γ_H = (γ₁+γ₂)(κ/c_s)² identification |
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
| GoltermanShamir | 14 | 9 conditions as substantive Props (C2 via ExteriorAlgebra, C3 via spectralGap, C5 via ground state, I1 via Hermitian, C4/C6 via resolvent), TPF evasion, Pauli exclusion, anti-commutation (axiom removed) |
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
| QNumber | 11 | q-integers [n]_q as Laurent polynomials, classical limit [n]_1=n, [2]_1^4=16=DG_COEFF (**ALL PROVED**, Aristotle `7d8efa8f`) |
| Uqsl2 | 6 | **FIRST quantum group in a proof assistant**: U_q(sl_2) via FreeAlgebra+RingQuot, zero axioms, Chevalley relations (**ALL PROVED**, Aristotle `7d8efa8f`) |
| Uqsl2Hopf | 66 | **FIRST Hopf algebra in a proof assistant**: Bialgebra + HopfAlgebra instances on U_q(sl₂), coproduct/counit/antipode via liftAlgHom, S²=Ad(K), Serre coproduct (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4` + `79e07d55`) |
| Uqsl3 | 21 | **Phase 5i**: **FIRST rank-2 quantum group in any proof assistant**: U_q(sl₃) via FreeAlgebra+RingQuot, 8 generators, A₂ Cartan matrix [[2,-1],[-1,2]], 21 Chevalley relations (**ALL PROVED, zero sorry**, native proofs, 6.4s build) |
| Uqsl3Hopf | 189 | **Phase 5i Wave 2 / Tranche E COMPLETE 2026-04-14**: Full Hopf algebra wiring for U_q(sl₃). Coproduct Δ + counit ε + antipode S defined via RingQuot.liftAlgHom; all 21 Δ/ε/S relation-respect proofs done (incl. 4 antipode q-Serre cubics E12/E21/F12/F21 closed via palindromic Serre atom-bridge). S² = Ad(K₁²K₂²) per generator (Drinfeld theorem, Tranche D). 24 per-generator evaluation lemmas. 4 derived F·K commutation rules at module scope. 3 coalgebra axioms (coassoc + 2 counital). 16 antipode convolution helpers (8 right + 8 left + algebraMap + mul_step). **`Bialgebra` instance** (via Bialgebra.ofAlgHom) and **`HopfAlgebra` instance** (via direct constructor) wired. **0 sorry**, ~5230 lines. |
| SU2kFusion | 29 | **SU(2)_k fusion at k=1,2,3**: universal truncated CG rule, Ising (sigma²=1+psi), Fibonacci (tau²=1+tau), charge conjugation, assoc+comm, Fibonacci subcategory closed (**ALL PROVED by native_decide, zero sorry**) |
| Uqsl2Affine | 9 | U_q(sl_2 hat) affine quantum group: 6 generators, Chevalley + cross-relations, K invertibility, coideal property statement (**ALL PROVED, zero sorry**) |
| SU2kSMatrix | 16 | SU(2)_k S-matrices at k=1,2: unitarity S*S^T=I, Verlinde formula, non-degeneracy/modularity (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| RestrictedUq | 11 | Restricted quantum group u_q(sl_2): E^ell=F^ell=0, K^ell=1 nilpotency/torsion, Chevalley→restricted, small_uq→SU(2)_k connection (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| RibbonCategory | 4 | BalancedCategory, RibbonCategory, MTC definitions, su2k1/su2k2 modular (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| E8Lattice | 19 | E8 Cartan matrix: det=1, even diagonal, symmetric, positive definite, Rokhlin gap σ=8, hyperbolic plane, Serre mod 8, classification (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| AlgebraicRokhlin | 10 | Algebraic Serre theorem σ≡0 mod 8, unimodular/even/symmetric defs, characteristic vectors, E8 bridge (**ALL PROVED, zero sorry**) |
| QSqrt2 | 3 | Q(√2) for Ising MTC. **Phase 5i Wave 4a refactor (2026-04-15)**: Mul delegates to `PolyQuotQ.mulReduce 2 ![2, 0]` via toPoly/ofPoly; struct API preserved (**ALL PROVED, zero sorry**) |
| QSqrt5 | 7 | Q(√5) for Fibonacci MTC: golden ratio φ²=φ+1, φ·φ⁻¹=1, Fibonacci F²=I. **Phase 5i Wave 4b refactor (2026-04-15)**: Mul delegates via `mulReduce 2 ![5, 0]` (**ALL PROVED by native_decide**) |
| FibonacciMTC | 11 | Fibonacci MTC: F-symbols in Q(√5) isotopy gauge, F²=I PROVED, PreModularData instance, chirality (**ALL PROVED, zero sorry** — native_decide over Q(√5)) |
| Uqsl2AffineHopf | 201 | U_q(ŝl₂) Hopf algebra: coproduct/counit/antipode via RingQuot.liftAlgHom. **ALL PROVED, zero sorry** — all 8 q-Serre proofs closed (4 comul + 4 antipode). Bialgebra + HopfAlgebra instances WIRED. **Phase 5e Wave 8 complete 2026-04-15**: 20 new theorems for per-generator antipode (`uqAff_antipode_*`) + K-conjugation helpers + per-generator S² identities (`uqAff_antipode_squared_*`). Wave 8 original spec `S² = Ad(K₀K₁)` mathematically wrong for affine (rank-deficient Cartan); corrected to per-generator form with inline historical note. |
| VerifiedStatistics | 6 | Statistics extension: sample variance non-neg PROVED, Cauchy-Schwarz bound, jackknife mean-case, N_eff ≤ N (**ALL PROVED, zero sorry**, Aristotle `986b9f66`) |
| KerrSchild | 7 | Kerr-Schild metrics: null vector, radial_null PROVED, Sherman-Morrison inverse, Schwarzschild, DOF counting (**ALL PROVED, zero sorry**, Aristotle `986b9f66`) |
| SU2kMTC | 11 | **Phase 5d**: Ising F-symbols (F^σ_{ψσψ}=-1 corrected), pentagon, ModularTensorData instance (**ALL PROVED, zero sorry** — native_decide over Q(√2)) |
| CoidealEmbedding | 6 | **Phase 5d**: Coideal subalgebra embedding B_i into U_q(ŝl₂), Dolan-Grady from Chevalley (**ALL PROVED, zero sorry**, Aristotle `986b9f66`) |
| RepUqFusion | 13 | **Phase 5d**: Rep(u_q) → SU(2)_k fusion data correspondence, dim formulas, Peter-Weyl (**ALL PROVED, zero sorry**, Aristotle `986b9f66`) |
| SpinBordism | 8 | Spin bordism → Rokhlin → Wang chain, SpinBordismData structure, anomaly with/without ν_R (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| VerifiedJackknife | 5 | First verified statistical estimators: jackknife variance non-neg, autocovariance_zero non-neg, intAutocorrTime bounds (**ALL PROVED, zero sorry**, Aristotle `78dcc5f4`) |
| TetradGapEquation | 20 | **First tetrad gap equation in any formalism**: NJL-type Δ=G·N_f·Δ·I(Δ), gapIntegral, criticalCoupling=8π²/(N_f·Λ²) (PROVED, matches ADW V_eff), IVT existence, Banach uniqueness, bifurcation at G_c, vestigial connection (**ALL PROVED, zero sorry**, Aristotle `79e07d55` + `986b9f66`) |
| StimulatedHawking | 11 | **Phase 5d**: Stimulated Hawking amplification, signal-to-noise, phonon statistics (**ALL PROVED, zero sorry**, Aristotle `986b9f66`) |
| CenterFunctor | 9 | **Phase 5d**: Center(Vec_G) ⥤ ModuleCat(DG) — **0 sorry, 2 tracked hypotheses** (H_CF1, H_CF2 as `def ... : Prop`). Data-level evidence via CenterEquivalenceZ2 + S3CenterAnyons. |
| QCyc16 | 6 | **Phase 5e**: Q(ζ₁₆) cyclotomic field: ζ⁸=-1, ζ¹⁶=1, (√2)²=2 (**ALL PROVED by native_decide, zero sorry**) |
| QCyc5 | 9 | **Phase 5e**: Q(ζ₅) cyclotomic field: ζ⁵=1, cyclotomic relation, Fibonacci hexagon E1-E3, twist consistency (**ALL PROVED by native_decide, zero sorry**) |
| IsingBraiding | 25 | **Phase 5e**: COMPLETE braided Ising MTC: R-matrix, twist, 6 hexagon eqs, 4 ribbon conditions, Gauss sum, **trefoil=-1** (**ALL PROVED by native_decide, zero sorry, FIRST verified knot invariant**) |
| QSqrt3 | 8 | **Phase 5e**: Q(√3) for SU(2)₄ S-matrix: unitarity diagonal+off-diag, det non-zero (**ALL PROVED by native_decide, zero sorry**) |
| QLevel3 | 19 | **Phase 5e**: Q[x]/(20x⁴-10x²+1) for SU(2)₃ S-matrix: ALL 10 unitarity entries, quantum dim golden ratio (**ALL PROVED by native_decide, zero sorry**) |
| SU3kFusion | 99 | **Phase 5i**: **FIRST SU(3)_k fusion in any proof assistant**: SU(3)₁ Z₃ fusion (3 objects) + SU(3)₂ (6 anyons, Fibonacci subcategory τ⊗τ=1+τ), charge conjugation, associativity+commutativity (**ALL PROVED by native_decide, zero sorry**) |
| GaugingStep | 34 | **Phase 5h**: Gauging obstruction: NotOnSiteSymmetry, SymmetryDisentangler, GT Models 1+2, SM anomaly 16≡0 mod 16, SMGPhaseData (BCH+HW), Golterman-Shamir propagator-zero, ChiralityWall3DStatus (**ALL PROVED, zero sorry**) |
| FermiPointTopology | 33 | **Phase 5j W1-3**: Fermi-point gauge emergence: VZ Theorem 2.1 (|N|=1 → U(1)+vierbein), Mechanism A vs B, charge splitting, multi-Weyl classification (|N|≤3), SU(2) emergence chain (3 theorem + 2 heuristic + 1 speculative), SU(3) more speculative than SU(2), full emergence chain status, bridges to EmergentGravityBounds/GaugingStep/SPT (**ALL PROVED, zero sorry**) |
| PolyQuotQ | 1 | **Phase 5i Wave 4a+4c-part1+4d (2026-04-15)**: **First generic computable polynomial quotient ring over ℚ in any proof assistant**. Parametric `PolyQuotQ n` structure (`Fin n → ℚ` coeff tuples, `deriving DecidableEq`). `mulReduce n r x y` via `Array (Array ℚ)` power table + eager output materialization — avoids both exponential-recursion and lazy-closure-reeval pitfalls that disabled earlier designs under native_decide. O(n³) per mul at arbitrary degree × density. Mathlib-upstream-ready (standard copyright + docstring). QCyc3 extracted to own module (4d). Wave 4d `bf5efce`. |
| PolyQuotOver | 1 | **Phase 5i Wave 4b.ext+4d (2026-04-15)**: Generic tower extension `PolyQuotOver K m` over arbitrary `[DecidableEq K]` base ring. `mulReduce2` (degree-2 specialization, eager materialization) is the current tower primitive; `mulReduceOver` (general m) retained with documented performance caveats. First non-trivial user is QCyc15SqrtPhi (Q(ζ₁₅)[w]/(w²-φ)). Mathlib-upstream-ready. |
| QCyc3 | 9 | **Phase 5i Wave 4d (2026-04-15)**: Q(ζ₃) = ℚ[x]/(x²+x+1) concrete instance of `PolyQuotQ 2` with reduction `![-1,-1]`. Extracted from old PolyQuotQ.lean during Mathlib-style cleanup. Preserves original 9 theorems (ζ²=-1-ζ, ζ³=1, cyclotomic_sum, ζ≠1, ζ²≠1, SU(3)₁ S-matrix row orthogonality). Mathlib-style docstring. |
| QCyc15 | 8 | **Phase 5i Wave 4c-part1 (2026-04-15)**: Q(ζ₁₅) = ℚ[x]/Φ₁₅(x) as `abbrev QCyc15 := PolyQuotQ 8`. Reduction `![-1, 1, 0, -1, 1, -1, 0, 1]` (7 nonzero terms — densest cyclotomic at degree 8). Key constants: ζ, ζ², ..., ζ⁷, √5, φ, 1/φ, ω₃=ζ⁵. Theorems: ζ¹⁵=1 (4-mul chain), (√5)²=5, φ²=φ+1, φ·(1/φ)=1, ω₃³=1, cube-root sum = 0. First PolyQuotQ instance at degree 8 for a proper cyclotomic. |
| QCyc15SqrtPhi | 5 | **Phase 5i Wave 4c-part3 (2026-04-15)**: **First non-cyclotomic number field in the project**, Q(ζ₁₅, √φ) = Q(ζ₁₅)[w]/(w²-φ), degree 16 over ℚ, via `PolyQuotOver QCyc15 2`. Non-Galois — √φ escapes every cyclotomic field per Kronecker-Weber (x⁴-x²-1 splitting field contains ±i/√φ). Theorems: w²=φ, φ·(1/φ)=1, (1/√φ)²=1/φ, w≠0. Enables SU(3)_2 Fibonacci F-symbols. |
| SU3k2SMatrix | 14 | **Phase 5i Wave 4c-part2 (2026-04-15)**: **First rank-6 MTC modular data in any proof assistant**. 9 S-matrix entry classes A-I (×15 scaling) as QCyc15 values, full 6×6 S-matrix, 6 T-matrix diagonal entries (4 distinct: ζ¹³, ζ², ζ⁸, ζ⁷). Theorems: S=Sᵀ (native_decide over 36 entries), Z₃ simple-current identities (G=A·ω₃, H=A·ω₃², I=-A, orbit sum = 0), T¹⁵=1 for all 4 distinct T-matrix values (14-deep chained muls each), T₀·T₃=ζ⁶, Fibonacci subcategory entries (S₀₀=A, S₀₅=B, S₅₅=I). |
| SU3k2FSymbols | 9 | **Phase 5i Wave 4c-part3 (2026-04-15)**: **First SU(3)₂ F-symbols in any proof assistant**. Fibonacci 2×2 F-matrix over Q(ζ₁₅, √φ): F=[[1/φ, 1/√φ], [1/√φ, -1/φ]]. F²=I proved entry-by-entry (4 entries, all native_decide). Supporting: golden ratio φ²=φ+1 in the non-cyclotomic tower, 1/φ²+1/φ=1, Fibonacci equation (1/φ)²+(1/√φ)²=1. Full 120-entry catalog deferred (requires external Ardonne-Slingerland data). |

---

## Pipeline invariants (from WAVE_EXECUTION_PIPELINE.md)

1. `formulas.py` is canonical — only place physics formulas live
2. `constants.py` is canonical — only place constants + Aristotle registry live
3. `visualizations.py` is canonical — only place figure functions live
4. Every formula has a Lean theorem (zero sorry)
5. Every computed quantity has bounds (CHECK 12)
6. Every paper claim traces to computation (CHECK 14)
7. Narrative derives from data (feasibility claims need computed support)
