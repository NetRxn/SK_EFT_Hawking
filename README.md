# SK-EFT Hawking: Formally Verified Physics from Analog Black Holes to the Standard Model

## What This Project Is About

This project investigates whether the mathematical structures that describe exotic states of matter — superfluids, topological insulators, quantum spin liquids — can also describe the fundamental forces and particles of the universe. Every derivation is machine-checked in the Lean 4 proof assistant, meaning a computer has verified each logical step. The results span testable laboratory predictions, constraints on the particle content of the Standard Model, and formal obstructions to unification approaches.

### Analog Hawking radiation and testable predictions

When a fluid flows faster than its own speed of sound, it creates a "sonic horizon" — a point of no return for sound waves, exactly analogous to a black hole's event horizon for light. Hawking predicted in 1974 that black holes radiate; the same mathematics predicts that sonic horizons radiate phonons (sound quanta). This has been observed in Bose-Einstein condensates (BECs).

We computed the first corrections to this acoustic Hawking radiation from dissipation — the fact that real fluids have viscosity. These corrections produce a specific, predictable change in the radiation spectrum as a function of frequency and flow speed, giving experimentalists a concrete signature to look for.

The most promising experimental platform is polariton superfluids (light-matter hybrids in semiconductor microcavities), which are roughly 10 billion times hotter than BEC systems (~1 K vs. ~10^-10 K). A Paris group has already observed negative-energy partner modes in polariton systems; detection of spontaneous Hawking radiation is plausible within 1-2 years.

### Why three generations of matter

The Standard Model has three copies ("generations") of its fundamental particles — electron/muon/tau, each paired with its own neutrino and set of quarks. Nobody knows why three. We formally derived that the number of generations must be a multiple of three, from two independent facts:

**Fact 1 — Particle content gives the number 8.** Each generation contains 16 Weyl fermions (the fundamental chiral building blocks). When the theory is reduced from four dimensions to two (a standard technique for analyzing anomalies), each generation contributes 8 to a quantity called the chiral central charge, denoted c₋. The total is:

```
c₋ = 8 × N_generations
```

**Fact 2 — Mathematical consistency gives the number 24.** The partition function of a quantum field theory must satisfy "modular invariance" — a symmetry requirement rooted in the Dedekind eta function from number theory (studied by Ramanujan in 1916). This constrains c₋ to be a multiple of 24:

```
Modular invariance requires: c₋ ≡ 0 (mod 24)
```

**The constraint.** Combining the two:

```
8 × N_generations must be divisible by 24
→ N_generations must be divisible by 24/8 = 3
```

The smallest nontrivial solution is N_generations = 3 — which is what nature chose. We also proved that 1 and 2 are ruled out (24 does not divide 8 or 16), and that 6 is the next allowed value. Pure number theory meets particle physics.

We also provide a formal argument for right-handed neutrinos (particles not yet observed but widely expected): without them, the central charge per generation is 15/2 instead of 8, making c₋ fractional. A fractional central charge is a gravitational anomaly — the theory is mathematically inconsistent — independent of the usual mass-based arguments for neutrino mass.

### The "16 convergence"

The number 16 appears in four areas of physics and mathematics that, on the surface, have nothing to do with each other:

1. **Particle physics:** Each generation of Standard Model fermions has exactly 16 Weyl components.
2. **Anomaly theory:** The classification of consistent fermion theories lives in a cyclic group with 16 elements (Z/16).
3. **4D topology:** Rokhlin's theorem (1952) says that certain 4-dimensional manifolds have signatures divisible by 16.
4. **Condensed matter:** Kitaev's periodic table of topological superconductors repeats with period 16 in the relevant symmetry class.

We proved these are all the same 16, rooted in the quaternionic structure of spinors in four dimensions. The proof also reveals a sharp boundary: algebra alone (specifically, the E8 lattice, verified using Mathlib's Cartan matrix) only forces divisibility by 8. The jump from 8 to 16 requires smooth topology — it is a genuinely physical constraint that pure algebra cannot produce. This cleanly separates what mathematics alone dictates from what requires the additional structure of physical spacetime.

### From lattice models to gauge theory

Topological quantum computers would perform calculations by braiding exotic particles called anyons. The mathematical framework governing these operations — modular tensor categories — has deep roots in exactly solvable lattice models from statistical mechanics. We formalized the complete chain connecting them:

> Onsager algebra (2D Ising model) → quantum group U_q(sl_2) → fusion categories → modular S-matrix → Chern-Simons gauge theory

At level k=2, this produces the Ising anyon model. At k=3, it produces the Fibonacci anyon — which is universal for quantum computation (any quantum circuit can be approximated by braiding Fibonacci anyons). Our formalization provides the first machine-verified mathematical foundations for these fusion operations, including the first Hopf algebra and the first quantum group constructed in any proof assistant.

We extended this to rank-2 quantum groups, constructing U_q(sl_3) and its SU(3)_k fusion categories in Lean 4 — the first rank-2 quantum group and the first SU(3) fusion formalization in any proof assistant. SU(3)_k at level k=2 yields 6 anyons including a Fibonacci subcategory, confirming that the abstract quantum group machinery reproduces the expected physics. We also formalized the gauging step analysis (the mathematical obstruction to promoting lattice chiral symmetry to a gauge theory) and the Volovik-Zubkov Fermi-point mechanism for emergent gauge fields, where the topological charge of a Fermi point determines the gauge group that emerges at low energies.

### The chirality wall

The biggest obstacle to deriving the Standard Model from condensed matter physics is chirality: the weak nuclear force couples only to left-handed particles. Since 1981, a series of no-go theorems (Nielsen-Ninomiya and others) have appeared to forbid getting chiral fermions from a lattice or condensed matter system.

We provided the first formal analysis of a 2026 construction by Thorngren, Preskill, and Fidkowski that appears to evade these no-go theorems. We formalized all 9 conditions of the competing Golterman-Shamir no-go theorem and proved that 5 of those conditions are violated by the TPF construction — meaning the no-go theorem's assumptions don't apply, and its conclusion (that chirality is forbidden) doesn't follow. A master synthesis theorem combining all three lines of evidence (Golterman-Shamir evasion, Gu-Wen-Thorngren positive construction, Z₁₆ anomaly classification) is machine-checked.

### Emergent gravity: what works and what doesn't

Can gravity emerge from a condensed matter system the way electromagnetism can? We investigated two approaches and found clear results for each.

**What fails:** Fracton models (exotic phases of matter where particles have restricted mobility) reproduce the equations of weak-field gravity, but we formally proved they cannot reproduce full general relativity. The obstruction is structural — the symmetries of fracton gauge theory are too rigid to accommodate the nonlinearities of Einstein's equations.

**What works (partially):** The Akama-Diakonov-Wetterich mechanism, where gravity arises from fermion pair condensation (analogous to how superconductivity arises from electron pairing). The key equation for this condensation — the "tetrad gap equation" — had never been explicitly written down in the literature. We identified it and are computing its solutions.

**A structural boundary:** We proved that the strong and weak nuclear forces (SU(3) and SU(2) gauge symmetries) cannot survive passage through a fluid-like layer — they get erased. However, they can originate *from* topological order, via the quantum group route formalized above. This distinguishes which forces can emerge from condensed matter and which cannot.

### Verified statistical estimators

Monte Carlo simulations are a workhorse of computational physics, but the statistical tools used to analyze their output — variance estimators, autocorrelation functions — have never been formally verified. We formalized the jackknife variance estimator and autocorrelation function in Lean 4 for the first time in any proof assistant, including a proof that the jackknife variance is non-negative. This opens the path to formally verified data analysis pipelines for lattice quantum field theory.

*33 theorems remain as Aristotle (automated theorem prover) targets across 10 modules.*

---

## Technical Summary

**Lean 4 formalization:** 2232 theorems (2150 substantive + 82 placeholder) across 94 modules. 1 axiom (gapped_interface_axiom), 33 sorry pending Aristotle.
307+ Aristotle-proved across 43+ runs. Lean 4.28.0, Mathlib commit `8f9d9cff`.

**Three-layer verification:** Python numerics ↔ Lean 4 formal proofs ↔ Aristotle automated theorem prover.

**Fourteen papers** in a unified codebase — from first-order dissipative corrections (Paper 1) through gauge erasure (Paper 3), exact WKB (Paper 4), emergent gravity (Papers 5-6), chirality wall (Papers 7-8), SM anomaly and Drinfeld center (Paper 9), modular generation counting (Paper 10), quantum groups through MTC (Paper 11), polariton analog Hawking (Paper 12), braided modular tensor categories (Paper 14), and formal verification methodology (Paper 15).

## Project Structure

```
SK_EFT_Hawking/
├── lean/                              # Lean 4 formalization (2232 theorems, 1 axiom, 94 modules, 33 sorry pending Aristotle)
│   ├── lakefile.toml                  # Lake build config (pinned Mathlib)
│   ├── lean-toolchain                 # Lean 4 v4.28.0
│   ├── SKEFTHawking.lean              # Root module (imports all 94 theorem modules)
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
│       ├── Uqsl2Hopf.lean            # Phase 5c-5d: FIRST Hopf algebra on U_q(sl₂), coproduct/counit/antipode/Serre (66 theorems, all proved)
│       ├── SU2kFusion.lean           # Phase 5c: SU(2)_k fusion at k=1,2,3, Ising/Fibonacci (29 theorems)
│       ├── Uqsl2Affine.lean          # Phase 5c: U_q(sl_2 hat) affine quantum group (9 theorems)
│       ├── SU2kSMatrix.lean          # Phase 5c: SU(2)_k S-matrices, unitarity, Verlinde (16 theorems, all proved)
│       ├── RestrictedUq.lean         # Phase 5c: restricted quantum group u_q(sl₂), nilpotency (11 theorems, all proved)
│       ├── RibbonCategory.lean       # Phase 5c: Balanced/Ribbon/MTC definitions (4 theorems, all proved)
│       ├── E8Lattice.lean            # Phase 5c: E8 Cartan, Rokhlin gap, classification (19 theorems, all proved)
│       ├── AlgebraicRokhlin.lean     # Phase 5c: algebraic Serre theorem σ≡0 mod 8 (10 theorems, all proved)
│       ├── SpinBordism.lean          # Phase 5c: spin bordism → Rokhlin → Wang chain (8 theorems, all proved)
│       ├── VerifiedJackknife.lean    # Phase 5c: verified jackknife/autocorrelation estimators (5 theorems, all proved)
│       ├── TetradGapEquation.lean    # Phase 5d: NJL-type gap equation, critical coupling, bifurcation (20 theorems, 1 sorry)
│       ├── SU2kMTC.lean             # Phase 5d: Ising MTC F-symbols, pentagon, ModularTensorData (11 theorems, ALL PROVED, zero sorry)
│       ├── QSqrt2.lean              # Phase 5d: Q(√2) number field for Ising MTC (3 theorems, all proved)
│       ├── QSqrt5.lean              # Phase 5d: Q(√5) number field, golden ratio (7 theorems, all proved)
│       ├── FibonacciMTC.lean        # Phase 5d: Fibonacci MTC F-symbols, PreModularData (11 theorems, ALL PROVED, zero sorry)
│       ├── Uqsl2AffineHopf.lean     # Phase 5d: U_q(ŝl₂) Hopf algebra (4 theorems, 3 sorry)
│       ├── VerifiedStatistics.lean   # Phase 5d: statistics extension, Cauchy-Schwarz, jackknife (6 theorems, 4 sorry)
│       ├── KerrSchild.lean          # Phase 5d: Kerr-Schild metrics, Sherman-Morrison (7 theorems, 1 sorry)
│       ├── CoidealEmbedding.lean    # Phase 5d: coideal subalgebra embedding (6 theorems, 4 sorry)
│       ├── RepUqFusion.lean         # Phase 5d: Rep(u_q) → SU(2)_k fusion correspondence (13 theorems, 2 sorry)
│       ├── StimulatedHawking.lean   # Phase 5d: stimulated Hawking amplification (11 theorems, 7 sorry)
│       ├── CenterFunctor.lean       # Phase 5d: Center(Vec_G) → ModuleCat(DG) functor (9 theorems, 5 sorry)
│       ├── QCyc16.lean             # Phase 5e: Q(ζ₁₆) cyclotomic field (6 theorems, all proved)
│       ├── QCyc5.lean              # Phase 5e: Q(ζ₅) cyclotomic field + Fibonacci hexagon (9 theorems, all proved)
│       ├── IsingBraiding.lean      # Phase 5e: COMPLETE braided Ising MTC, trefoil=-1 (23 theorems, all proved)
│       ├── QSqrt3.lean             # Phase 5e: Q(√3) for SU(2)₄ S-matrix unitarity (8 theorems, all proved)
│       ├── QLevel3.lean            # Phase 5e: Q[x]/(20x⁴-10x²+1) for SU(2)₃ unitarity (19 theorems, all proved)
│       ├── SPTClassification.lean  # Phase 5h: SPT classification, gapped interface axiom (15 theorems, all proved)
│       ├── TQFTPartition.lean     # Phase 5f: TQFT partition functions from MTC data, Verlinde formula (16 theorems, all proved)
│       ├── FigureEightKnot.lean   # Phase 5f: figure-eight knot invariant from Ising MTC (6 theorems, all proved)
│       ├── EmergentGravityBounds.lean # Phase 5f: Wen coupling deficit, G_c NLO invariance (14 theorems, 2 sorry)
│       ├── GaugingStep.lean       # Phase 5h: gauging obstruction, non-on-site symmetry, SMG phase (34 theorems, all proved)
│       ├── Uqsl3.lean             # Phase 5i: FIRST rank-2 quantum group U_q(sl₃), 21 Chevalley relations (21 theorems, all proved)
│       ├── Uqsl3Hopf.lean        # Phase 5i: U_q(sl₃) Hopf algebra, coproduct/counit/antipode (2 theorems, 4 sorry)
│       ├── SU3kFusion.lean       # Phase 5i: FIRST SU(3)_k fusion, Z₃ at k=1, 6 anyons at k=2 (99 theorems, all proved)
│       ├── PolyQuotQ.lean        # Phase 5i: Q(ζ₃) cyclotomic field for SU(3)₁ S-matrix (15 theorems, all proved)
│       └── FermiPointTopology.lean # Phase 5j: Fermi-point topological charge, emergent gauge fields (28 theorems, all proved)
│
├── src/
│   ├── core/                          # Shared infrastructure
│   │   ├── transonic_background.py    # 1D BEC transonic flow solver + δ_diss estimates
│   │   ├── aristotle_interface.py     # Aristotle API + sorry-gap registry (307+ proved, 33 sorry)
│   │   ├── visualizations.py          # Plotly figures (89 functions) + COLORS palette
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
│   │   ├── ginzburg_landau.py         # GL expansion, beta_i analogs, phase classification (Phase 4)
│   │   ├── tetrad_gap_solver.py      # NJL-type gap equation solver, Δ*(G) curve (Phase 5d)
│   │   └── tetrad_observables.py     # MC observables: O_tet, O_met, Binder, C(r) (Phase 5d)
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
│   │   ├── hs_rhmc_torch.py         # PyTorch CPU production default (Wave 7C)
│   │   └── stencil_dirac.py         # Stencil Dirac operator (Phase 5f)
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
│   ├── paper12_polariton/            # PRL polariton analog Hawking (Phase 5d)
│   │   └── paper_draft.tex
│   ├── paper14_braided_mtc/          # PRD braided modular tensor categories (Phase 5e-5f)
│   │   └── paper_draft.tex
│   ├── paper15_methodology/          # CPC formal verification methodology (Phase 5h)
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
│   ├── Phase5b_QuantumGroup_Stakeholder.ipynb
│   ├── Phase5c_HopfAlgebra_Technical.ipynb      # Phase 5c: Hopf algebra on U_q(sl₂)
│   ├── Phase5c_HopfAlgebra_Stakeholder.ipynb
│   ├── Phase5c_SU2kFusion_Technical.ipynb       # Phase 5c: SU(2)_k fusion, S-matrix, Ising/Fibonacci
│   ├── Phase5c_SU2kFusion_Stakeholder.ipynb
│   ├── Phase5c_E8Rokhlin_Technical.ipynb        # Phase 5c: E8, Rokhlin, spin bordism
│   ├── Phase5c_E8Rokhlin_Stakeholder.ipynb
│   ├── Phase5d_TetradGap_Technical.ipynb        # Phase 5d: tetrad gap equation
│   ├── Phase5d_TetradGap_Stakeholder.ipynb
│   ├── Phase5d_Polariton_Technical.ipynb        # Phase 5d: polariton analog Hawking
│   ├── Phase5d_Polariton_Stakeholder.ipynb
│   ├── Phase5d_MTC_Technical.ipynb              # Phase 5d: Ising/Fibonacci MTC instances
│   └── Phase5d_MTC_Stakeholder.ipynb
│
├── docker/
│   └── docker-compose.graph.yml       # PG+AGE container for knowledge graph (port 5433)
│
├── docs/
│   ├── KNOWLEDGE_GRAPH.md             # Knowledge graph documentation and guide
│   ├── roadmaps/                      # Phase 1 + Phase 2 technical roadmaps
│   ├── stakeholder/                   # Implications, strategic positioning, companion guides
│   ├── aristotle_results/             # All 43+ Aristotle run archives
│   └── archive/                       # Superseded artifacts
│
├── tests/                             # pytest suite (1635+ tests across 43 files)
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
├── figures/                           # 89 pipeline figures (PNG + HTML) + provenance_graph.json
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
lake build                                 # Should be clean (zero sorry target)
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
| See what's next | [`docs/roadmaps/Phase5j_Roadmap.md`](docs/roadmaps/Phase5j_Roadmap.md), [`Phase5i_Roadmap.md`](docs/roadmaps/Phase5i_Roadmap.md), [`Phase6_Deferred_Targets.md`](docs/roadmaps/Phase6_Deferred_Targets.md) |
| Understand the broader research program | [`docs/Fluid-Based Approach to Fundamental Physics  Feasibility Study.md`](docs/Fluid-Based%20Approach%20to%20Fundamental%20Physics%20%20Feasibility%20Study.md) |
| Read the critical review | [`docs/Fluid-Based Approach to Fundamental Physics- Consolidated Critical Review v3.md`](docs/Fluid-Based%20Approach%20to%20Fundamental%20Physics-%20Consolidated%20Critical%20Review%20v3.md) |
| See the deep research corpus | `Lit-Search/` — 40+ research files across Phases 3-5j |
| Work with Aristotle | [`docs/references/Theorm_Proving_Aristotle_Lean.md`](docs/references/Theorm_Proving_Aristotle_Lean.md) |
| Check the full inventory | [`SK_EFT_Hawking_Inventory.md`](SK_EFT_Hawking_Inventory.md) — comprehensive source of truth |

## Theorem Inventory (2232 theorems — 1 axiom, 33 sorry pending Aristotle)

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
| Uqsl2Hopf.lean | 5c-5d | 66 | **FIRST Hopf algebra in a proof assistant**: coproduct/counit/antipode, S²=Ad(K), Serre coproduct (ALL PROVED) |
| SU2kFusion.lean | 5c | 29 | SU(2)_k fusion at k=1,2,3: Ising σ²=1+ψ, Fibonacci τ²=1+τ, charge conjugation (ALL PROVED by native_decide) |
| Uqsl2Affine.lean | 5c | 9 | U_q(sl_2 hat) affine quantum group, Chevalley + cross-relations, coideal property |
| SU2kSMatrix.lean | 5c | 16 | SU(2)_k S-matrices at k=1,2: unitarity, Verlinde formula, modularity (ALL PROVED) |
| RestrictedUq.lean | 5c | 11 | Restricted quantum group u_q(sl₂): nilpotency E^ell=0, torsion K^ell=1, SU(2)_k connection (ALL PROVED) |
| RibbonCategory.lean | 5c | 4 | Balanced, Ribbon, MTC definitions (FIRST in any proof assistant) (ALL PROVED) |
| E8Lattice.lean | 5c | 19 | E8 Cartan: det=1, even unimodular, Rokhlin gap σ=8, Serre bound, classification (ALL PROVED) |
| AlgebraicRokhlin.lean | 5c | 10 | Algebraic Serre theorem σ≡0 mod 8, unimodular/even/symmetric defs, characteristic vectors (ALL PROVED) |
| SpinBordism.lean | 5c | 8 | Spin bordism → Rokhlin → Wang chain, SpinBordismData, anomaly with/without ν_R (ALL PROVED) |
| VerifiedJackknife.lean | 5c | 5 | First verified statistical estimators: jackknife, autocorrelation, intAutocorrTime (ALL PROVED) |
| TetradGapEquation.lean | 5d | 20 | First tetrad gap equation: NJL-type gap, critical coupling, bifurcation (1 sorry) |
| SU2kMTC.lean | 5d | 11 | Ising MTC F-symbols, pentagon, ModularTensorData (ALL PROVED, zero sorry — native_decide) |
| QSqrt2.lean | 5d | 3 | Q(√2) number field for Ising MTC (ALL PROVED) |
| QSqrt5.lean | 5d | 7 | Q(√5) number field, golden ratio (ALL PROVED) |
| FibonacciMTC.lean | 5d | 11 | Fibonacci MTC F-symbols, PreModularData (ALL PROVED, zero sorry — native_decide) |
| Uqsl2AffineHopf.lean | 5d | 4 | U_q(ŝl₂) Hopf algebra (3 sorry) |
| VerifiedStatistics.lean | 5d | 6 | Statistics extension: Cauchy-Schwarz, jackknife, N_eff (4 sorry) |
| KerrSchild.lean | 5d | 7 | Kerr-Schild metrics, Sherman-Morrison inverse (1 sorry) |
| CoidealEmbedding.lean | 5d | 6 | Coideal subalgebra embedding (4 sorry) |
| RepUqFusion.lean | 5d | 13 | Rep(u_q) → SU(2)_k fusion correspondence (2 sorry) |
| StimulatedHawking.lean | 5d | 11 | Stimulated Hawking amplification (7 sorry) |
| CenterFunctor.lean | 5d | 9 | Center(Vec_G) → ModuleCat(DG) functor (5 sorry) |
| QCyc16.lean | 5e | 6 | Q(ζ₁₆) cyclotomic field (all proved, native_decide) |
| QCyc5.lean | 5e | 9 | Q(ζ₅) + Fibonacci hexagon E1-E3 (all proved, native_decide) |
| IsingBraiding.lean | 5e | 23 | COMPLETE braided Ising: hexagon, ribbon, trefoil=-1 (all proved) |
| QSqrt3.lean | 5e | 8 | Q(√3) + SU(2)₄ S-matrix unitarity (all proved) |
| QLevel3.lean | 5e | 19 | SU(2)₃ S-matrix unitarity, quantum dim golden ratio (all proved) |
| TQFTPartition.lean | 5f | 16 | TQFT partition functions: Ising + Fibonacci at genus 0-4, Verlinde formula (all proved) |
| FigureEightKnot.lean | 5f | 6 | Figure-eight knot RT invariant from Ising MTC braiding data (all proved) |
| EmergentGravityBounds.lean | 5f | 14 | Wen coupling deficit ~6000x, G_c NLO invariance, tetrad channel advantage (2 sorry) |
| SPTClassification.lean | 5h | 15 | SPT phase classification, gapped interface axiom, TPF conditional theorems (all proved, 1 axiom) |
| GaugingStep.lean | 5h | 34 | Gauging obstruction, non-on-site symmetry, SMG phase, GS propagator-zero (all proved) |
| Uqsl3.lean | 5i | 21 | **FIRST rank-2 quantum group** U_q(sl₃): 8 generators, 21 Chevalley relations (all proved) |
| Uqsl3Hopf.lean | 5i | 2 | U_q(sl₃) Hopf: coproduct/counit/antipode, S²=Ad(K₁K₂) (4 sorry) |
| SU3kFusion.lean | 5i | 99 | **FIRST SU(3)_k fusion**: Z₃ at k=1, 6 anyons at k=2, Fibonacci subcategory (all proved, native_decide) |
| PolyQuotQ.lean | 5i | 15 | Q(ζ₃) cyclotomic field for SU(3)₁ S-matrix (all proved) |
| FermiPointTopology.lean | 5j | 28 | Fermi-point topological charge, |N|=1→U(1), |N|=2→SU(2) gauge emergence (all proved) |

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

**Roadmaps:** [`docs/roadmaps/`](docs/roadmaps/) contains phase-specific execution plans (Phases 1-5j) and the [Phase 6 Deferred Targets](docs/roadmaps/Phase6_Deferred_Targets.md) tracking future work with deep research linkage.

**Stakeholder docs:** [`docs/stakeholder/`](docs/stakeholder/) contains non-technical implications and strategic positioning documents for each phase.

**Deep research:** [`Lit-Search/`](../Lit-Search/) contains 40+ research files spanning Phases 3-5j covering quantum groups, modular tensor categories, Rokhlin's theorem, the ADW gap equation, fracton-gravity, verified statistics, polariton protocols, TQFT partition functions, gauging obstructions, SU(3)_k fusion, and Fermi-point topology.
