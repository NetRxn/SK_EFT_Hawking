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

### A fluid-based test of dark-matter phenomenology

Three sub-chains connect the emergent-physics infrastructure to observable dark-sector phenomenology. First, ℤ₁₆-anomaly-driven hidden-sector classification enumerates SM-singlet Weyl configurations (`HiddenSectorClassification.lean`, `HiddenSectorMixedCharge.lean`) — the T-0 TQFT candidate is invisible to all planned direct-detection experiments. Second, a superfluid-dark-matter cluster-merger forecast (`SFDMMergerForecast.lean` + Paper 17 "money plot") predicts a sonic-boom step function in κ-profiles at the galaxy-cluster Mach transition; stacking ≥ 30 mergers with Euclid × Roman reaches 3.5–5.7σ, with first 3σ detectable around 2028. Third, fracton dark matter is machine-checked viable in a p-wave dipole superfluid phase at MeV–TeV scales (`FractonDarkMatter.lean`), while Fang–Gu torsion DM is kinematically excluded at CDM level (`FangGuTorsionDM.lean`). A synthesis module pins the empirical-hook ranking (cluster mergers > direct detection) to Lean-decidable ground (`DarkSectorSynthesis.lean`).

### A structural no-go for emergent dark energy

A sequence of deep-research rounds on Klinkhamer–Volovik-style emergent-vacuum mechanisms (four q-theory realizations + vestigial-gravity reframes) returned a uniform NO-GO for DESI DR2 compatibility. The obstruction is machine-checked and structural: `GibbsDuhemTheorem.lean` proves that any single-scalar self-tuning emergent-vacuum framework with Gibbs–Duhem equilibrium locks `w_vac = −1` by Lorentz invariance, realization-independently. Paired with the first closed-form derivation of the vestigial-gravity EOS `w_vest(τ) = (1 − τ²)/(5τ² − 1)` (`VestigialEOS.lean`) and the four-factor orthogonality decomposition (`DarkEnergyObstructionPrinciple.lean`), the result sharpens the architecture's scope: Layer 3 predictive physics covers SM + GR cleanly, but the dark-energy sector is outside the tested predictive scope under the Volovik-family mechanisms. Full accounting in `docs/ARCHITECTURE_SCOPE.md`.

### A solid-state experimental platform: the graphene Dirac fluid

The BEC + polariton experimental tracks are now joined by a solid-state one. The Dean group at Columbia realized the first electronic sonic horizon in bilayer graphene in 2025. Modules `DiracFluidMetric.lean`, `GrapheneHawking.lean`, `DiracFluidSK.lean`, `GrapheneNoiseFormula.lean`, and `QuasiOneDReduction.lean` carry the SK-EFT chain across to 2+1D: the 3×3 acoustic metric block-diagonalizes for quasi-1D flow, letting the existing WKB machinery apply directly (~92% theorem reuse). Predicted T_H ≈ 2.4 K for the Dean bilayer nozzle — nine orders above BEC — with a current-noise-spectroscopy detection path (Keldysh FDT + Landauer–Büttiker formula). Paper 16a documents the platform end to end.

### A formally verified geometric quantum gate

A finite-dimensional target completes the picture. `FermiHubbardDimer.lean` formalizes a two-site Fermi-Hubbard doublon system and proves a minimal Berry-phase theorem: under a π-sweep the dark state picks up a −1 sign, the dynamical phase vanishes under the kernel-angle condition, and the accumulated phase is purely geometric. The SWAP unitary on the 3-dimensional singlet sector is realized as a Householder reflection in an explicit orthonormal eigenbasis. This is the first formally verified symmetry-protected (non-topological) two-qubit gate — complementary to the Fibonacci-braiding universality proof, which protects gates via topological order rather than chiral symmetry. Paper 18 documents the result.

### Linearized Einstein equations from ADW microscopic theory

Phase 6a Track A formalizes the linearized Einstein field equations as the load-bearing first wave of the post-SK-EFT gravitational-dynamics roadmap. `LinearizedEFE.lean` formalizes the linearized Einstein tensor in momentum-space de Donder gauge, `G^(1)_μν(k) = -(1/2) k² h̄_μν`, with full algebra of trace-reversal and the spin-2 kinetic operator; the Sakharov-Adler closed form `G_N = 12π/(N_f Λ²)` tied to the existing ADW critical coupling `G_c = 8π²/(N_f Λ²)` via the algebraic identity `G_N^Sakharov = (3/2π)·G_c`; and the ADW emergent Newton constant `G_N^emerg = α_ADW · G_N^Sakharov` with sign theorem and correctness-push biconditional. At the natural Planck anchor `Λ = M_P^obs`, the match condition `G_N^emerg = G_N^obs` reduces to `α_ADW · 12π = N_f`, giving `α_ADW* ∈ [0.40, 1.27]` for SM `N_f ∈ {15, 16, 45, 48}` — comfortably inside the Vergeles natural range `[0.1, 10]`. A directed deep-research survey of the primary ADW literature found that no published paper extracts `α_ADW` in closed form; Wave 1 ships three Vergeles-derived structural Lean Props (positivity, critical-limit collapse, deep-gap reduction to Sakharov-Adler) and the linear ansatz `α_ADW(G/G_c) = 1 - G_c/G` proven to satisfy all three. `FLRWDynamics.lean` (Wave 4) follows as the ODE reduction, formalizing Friedmann I/II + conservation + Bianchi consistency + Phase 5y DESI-DR2 cross-reference. Paper 23 documents both waves.

### Gravitational waves under the vestigial-second-sound graviton identification (GW170817 falsification)

Phase 6a Track B (Wave 2) formalizes gravitational-wave propagation under the Volovik (JETP Lett. 119, 564 (2024)) identification of the vestigial second-sound mode as the spin-2 graviton, with leading-order propagation `c_GW = c · √χ_vest` from the metric-channel susceptibility `χ_vest`. `GravitationalWaves.lean` ships the deviation formula `Δc/c = √χ_vest − 1`, the GW170817 correctness-push biconditional `LigoSatisfied(Δc/c) ↔ χ_vest ∈ [(1−τ)², (1+τ)²]` at `τ = 3 × 10⁻¹⁵` (Abbott et al. ApJL 848, L13 (2017)), and the **load-bearing falsification result**: the natural susceptibility range `χ_vest ∈ [0.1, 10]` (matching the Wave 1 α_ADW natural range) gives `Δc/c ∈ [-0.68, +2.16]`, exceeding the GW170817 cap by `~7 × 10¹⁴` — both endpoints proved as Lean falsifier theorems. The Phase 5y H1 caveat (the second-sound mode is NOT derived as a propagating DOF) is encoded as the existential meta-theorem `second_sound_graviton_not_derived_DOF`. Paper 25 documents the result as the strongest published falsification of the Volovik identification at the natural-range level; recovery requires a derived-DOF mechanism for χ_vest = 1 (Phase 5y H1 follow-up wave) or recognition that the metric-channel susceptibility is a separate UV input not coincident with second sound (Phase 6e).

### Bekenstein-Hawking entropy from MTC state counting (Kaul-Majumdar SU(2)_k closed form + Outcome-3 tracked-hypothesis bundle)

Phase 6a Track C (Wave 3) formalizes the Bekenstein-Hawking entropy `S = A/(4 G_N) − (3/2)log(A/(4 G_N)) + c_0` at a horizon labeled by simple objects of a Modular Tensor Category (MTC). Per the deep-research literature survey (`Lit-Search/Phase-6a/6a-Horizon MTC boundary conditions...Wave 3.md`, 2026-04-25), no published paper places any specific MTC at the horizon of a 4D non-extremal black hole in an ADW substrate, so `BHEntropyMicroscopic.lean` ships in **Outcome-3 tracked-hypothesis mode** for the general case + an **Outcome-2 SU(2)_k sub-corollary** anchored on the Kaul-Majumdar derivation (gr-qc/0002040). Three machine-checked structural results: (i) the −3/2 log coefficient decomposes as (−1/2 from the Gaussian saddle) + (−1 from the SU(2) singlet projection in the I₀ − I₁ cancellation, Kaul-Majumdar Eq. (15)); (ii) the leading 1/4 prefactor is structurally a TUNING (Immirzi γ; Domagala-Lewandowski 0.2375 vs Meissner 0.2739 yield identical −3/2 under their respective counting prescriptions); (iii) Sen 2013 (arXiv:1205.0971) heat-kernel result for 4D Schwarzschild gives c_log = +(212/45 − 3) ≈ +1.71, an explicit non-universality witness encoded as `sen_4d_disagrees_with_kaul_majumdar`. The general-MTC tracked hypothesis bundles as `H_HorizonBoundaryCondition` with five falsifier theorems; the toric-code abelian falsifier triggers F2 (log d_max = 0 ⇒ κ_C = 0). Wave 3 introduces one new axiom `gaussianSaddleAsymptotic` (eliminability: hard, classified in `AXIOM_METADATA`) — the Laplace-method asymptotic bound, which a Mathlib PR could eventually retire. Paper 26 documents the synthesis "SU(2)_k MTC + ADW substrate + Walker-Wang Z₂-time-reversal anomaly inflow" as a research-level conjecture novelty-flagged across the manuscript.

---

## Technical Summary

**Lean 4 formalization:** **~3,950 theorems** (~3,840 substantive + ~110 placeholder) across **166 modules**. **1 axiom** (`gapped_interface_axiom`, eliminability: hard — the 4+1D gapped-interface conjecture, a standard open problem in lattice QFT and not a project-originated assumption). **0 sorry project-wide**. 322 theorems Aristotle-proved across 44 runs. Lean 4.29.0, Mathlib commit `8850ed93`.

**Representative formal-verification firsts** (each phase has delivered at least one):
- First formally verified anomaly constraint in particle physics (`N_f ≡ 0 mod 3`, Phases 5a–5b–5q).
- First quantum group (U_q(sl₂)) and Hopf-algebra non-trivial instance in any proof assistant (Phases 5b–5c–5d).
- First rank-2 quantum group (U_q(sl₃)) and SU(3)_k fusion formalization (Phase 5i).
- First parameterized `QuantumGroup k A` typeclass over arbitrary Cartan matrices + first Kac–Walton fusion algorithm (Phase 5m).
- First complete braided modular tensor category (Ising) and first formally verified knot invariants (trefoil = −1, figure-eight; Phase 5e–5f).
- First Temperley–Lieb algebra, first Jones–Wenzl idempotents, first end-to-end WRT TQFT pipeline (Phase 5k).
- First Muger-center formalization and first general machine-checked dual-closure theorem (Phase 5p).
- First Fermi-point → emergent-gauge-group formalization (|N|=1 → U(1), |N|=2 → SU(2); Phase 5j).
- First Fidkowski–Kitaev 2+1D Cayley-calibrated gapped-interface construction (Phase 5s).
- First machine-checked Ext^n_{A(1)}(F₂, F₂) computation over any Steenrod sub-algebra (Phase 5q).
- First change-of-rings discharge of `Ext_A ≅ Ext_{A(1)}` topological hypothesis H2 (Phase 5r).
- First verified jackknife + autocorrelation estimators for lattice Monte Carlo (Phase 5c).
- First Fermi-Hubbard geometric SWAP + minimal Berry-phase theorem (Phase 5t).
- First graphene-Dirac-fluid analog-Hawking formalization with Keldysh + Landauer–Büttiker noise formula (Phase 5w).
- First Gibbs–Duhem emergent-vacuum obstruction theorem + closed-form vestigial-gravity EOS (Phase 5y).

**Three-layer verification:** Python numerics ↔ Lean 4 formal proofs ↔ Aristotle automated theorem prover.

**Eighteen papers** in a unified codebase: first-order dissipative corrections (Paper 1), second-order (Paper 2), gauge erasure (Paper 3), exact WKB (Paper 4), ADW gap equation (Paper 5), vestigial gravity + MC (Paper 6), chirality formal (Paper 7), chirality master (Paper 8), SM anomaly + Drinfeld center (Paper 9), modular generation (Paper 10), quantum groups through MTC (Paper 11), polariton analog Hawking (Paper 12), braided MTC + knot invariants (Paper 14), verification methodology (Paper 15), graphene Dirac-fluid SK-EFT (Paper 16a), WRT TQFT pipeline formalization (Paper 16b), dark-sector connections (Paper 17), and geometric quantum gate (Paper 18).

## Project Structure

```
SK_EFT_Hawking/
├── lean/                              # Lean 4 formalization (4049 theorems, 1 axiom, 170 modules, 0 sorry)
│   ├── lakefile.toml                  # Lake build config (pinned Mathlib 8850ed93)
│   ├── lean-toolchain                 # Lean 4 v4.29.0
│   ├── SKEFTHawking.lean              # Root module (imports all 131 theorem modules)
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
│   │   ├── aristotle_interface.py     # Aristotle API + sorry-gap registry (322 proved, 0 sorry)
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
│   ├── fracton/                       # Fracton hydrodynamics (Phase 4 Waves 2-3, extended 5x)
│   │   ├── sk_eft.py                  # Fracton SK-EFT transport coefficients
│   │   ├── information_retention.py   # UV information comparison
│   │   ├── gravity_connection.py      # Fracton-gravity Kerr-Schild + bootstrap
│   │   └── non_abelian.py             # Non-Abelian fracton analysis
│   ├── dark_sector/                   # Dark-sector phenomenology (Phase 5x)
│   │   ├── z16_hidden_sector.py       # ℤ₁₆-anomaly-driven SM-singlet Weyl enumeration
│   │   ├── adw_cosmological_constant.py # ADW Λ magnitude + Volovik/GH doubling
│   │   ├── fracton_dm.py              # Fracton DM phenomenology
│   │   ├── sfdm_sk_eft.py             # SK-EFT applied to superfluid dark matter
│   │   ├── sfdm_merger_forecast.py    # SFDM cluster-merger sonic-boom forecast
│   │   └── synthesis.py               # Seven cross-connection theorems (Wave 8)
│   ├── fermi_hubbard/                 # Fermi-Hubbard dimer (Phase 5t)
│   │   └── dimer.py                   # Dimer Hamiltonian, dark state, SWAP, Berry-phase helpers
│   └── graphene/                      # Graphene Dirac-fluid platform (Phase 5w)
│       ├── bilayer_eos.py             # Bilayer graphene equation of state
│       ├── hawking_predictions.py     # T_H + dissipative corrections for the Dean bilayer
│       ├── platform_comparison.py     # BEC ↔ polariton ↔ graphene platform comparison
│       ├── transport_counting.py      # 2+1D charged conformal-fluid transport coefficients
│       └── wkb_spectrum.py            # Quasi-1D WKB spectrum for graphene
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
│   ├── paper16_graphene_sk_eft/     # Graphene Dirac-fluid analog Hawking (Phase 5w)
│   │   └── paper_draft.tex
│   ├── paper16_wrt_tqft/            # First formal WRT TQFT pipeline (Phase 5k)
│   │   └── paper_draft.tex
│   ├── paper17_dark_sector/         # Dark-sector connections + Gibbs-Duhem no-go (Phase 5x-5y)
│   │   └── paper_draft.tex
│   ├── paper18_doublon_gate/        # Formal verification of a geometric quantum gate (Phase 5t)
│   │   └── paper_draft.tex
│   ├── AutomatedReviews/            # Stage 13 adversarial-reviewer output per paper (Phase 5v)
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
├── tests/                             # pytest suite (2841+ tests across 61 files)
│   ├── test_transonic_background.py   # Physics validation (12 tests)
│   ├── test_second_order.py           # Enumeration + WKB tests (12 tests)
│   ├── test_gauge_erasure.py          # Gauge erasure theorem tests (25 tests)
│   ├── test_wkb_connection.py         # Exact WKB connection tests (65 tests)
│   ├── test_adw.py                    # ADW gap equation tests (78 tests)
│   ├── test_cross_validation.py       # Cross-layer validation (7 tests)
│   ├── test_lean_integrity.py         # Module structure + sorry-gap regression (9 tests)
│   ├── test_vestigial.py             # MC, SU(2), TRG, 4D, NJL, susceptibility (159 tests)
│   ├── test_gauge.py                 # SO(4) gauge, quaternion, Majorana (146 tests)
│   ├── test_hs_rhmc.py              # HS+RHMC algorithm (32 tests)
│   └── test_paper_provenance_v2.py    # Phase 5v Wave 10 sentence-level pipeline (16 tests)
│
├── figures/                           # 113 pipeline figures (PNG + HTML) + provenance_graph.json
├── scripts/
│   ├── submit_to_aristotle.py         # Aristotle submission + integration script
│   ├── validate.py                    # 17 cross-layer validation checks (incl. graph_integrity, claim_clusters_fresh)
│   ├── build_graph.py                 # Knowledge graph extraction (25 node types, 25 edge types)
│   ├── graph_integrity.py             # Graph integrity queries (orphans, conflicts, chains, sentence-level)
│   ├── extract_lean_deps.py           # Lean declaration + axiom-deps registry extraction
│   ├── update_counts.py               # Regenerate docs/counts.json + counts.tex
│   ├── render_paper_tables.py         # Per-paper auto-generated tables/*.tex from spec
│   ├── render_paper_html.py           # Pandoc-free LaTeX→HTML for paper bodies
│   ├── readiness_gates.py             # Per-paper × per-gate state evaluators (11 gates × 18 papers)
│   ├── citation_cache.py              # 90-day citation verification cache (Stage 13 amortizer)
│   ├── qi_register.py                 # Auto-generate docs/QI_REGISTER.md
│   ├── sync_graph_to_pg.py            # Idempotent PG+AGE sync (Wave 9f)
│   │
│   │  # — Phase 5v Wave 10 sentence-level provenance pipeline —
│   ├── sentence_state.py              # Sole writer to prose_state.json + audit_log.jsonl;
│   │                                  # mark / validate / ingest_agent_run / supersede / tombstone-sweep /
│   │                                  # reconcile / rebuild_prose_state (replay-canonical recovery)
│   ├── verification_state.py          # Sole writer to docs/verification_log.jsonl (cross-tab change-bus);
│   │                                  # record (with optional triggered_by) / list / apply / prune
│   ├── last_modified.py               # Cross-precision-safe freshness propagation across dependency edges
│   ├── cluster_detect.py              # Cross-paper exact + normalized claim clusters → claim_clusters.json
│   ├── test_helpers.py                # Isolated tmp_path fixtures (isolated_v2_state) + v2 builders
│   │
│   ├── datastar_helpers.py            # Flask glue for Datastar SSE
│   ├── provenance_dashboard.py        # Datastar+Flask 10-tab dashboard
│   │                                  # (Parameters / Formulas / Proof Architecture / Citations / KG /
│   │                                  #  Paper Readiness / Process Health / Research Status /
│   │                                  #  Paper Provenance v2 — sentence-level 3-column UI)
│   └── templates/
│       ├── dashboard.html             # Dashboard shell (Datastar v1.0.1 CDN)
│       └── partials/
│           ├── graph_tab.html         # D3 knowledge graph visualization
│           ├── readiness_tab.html     # 11-gate × 18-paper heatmap + focus pane
│           ├── qi_tab.html            # QI register cards
│           ├── chains_tab.html        # Research Status (chain L0/L1)
│           └── paper_provenance_tab.html  # 3-column sentence-level UI w/ keyboard nav
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
| See the big picture assessment | [`docs/RESEARCH_STATUS_OVERVIEW.md`](docs/RESEARCH_STATUS_OVERVIEW.md) — proven chains, gaps, implications |
| See what's been built and its status | [`SK_EFT_Hawking_Inventory_Index.md`](SK_EFT_Hawking_Inventory_Index.md) — counts, module map |
| Understand the execution process | [`docs/WAVE_EXECUTION_PIPELINE.md`](docs/WAVE_EXECUTION_PIPELINE.md) — 12-stage pipeline |
| Explore the provenance graph | [`docs/KNOWLEDGE_GRAPH.md`](docs/KNOWLEDGE_GRAPH.md) — interactive D3 visualization |
| Browse the dashboard | `uv run python scripts/provenance_dashboard.py` → http://localhost:8050 |
| Read non-technical summaries | `docs/stakeholder/` — implications and strategic positioning per phase |
| See what's next | [`docs/roadmaps/Phase6_Deferred_Targets.md`](docs/roadmaps/Phase6_Deferred_Targets.md), [`Phase6_Roadmap.md`](docs/roadmaps/Phase6_Roadmap.md), and [`Phase6_VerifiedStatistics_Roadmap.md`](docs/roadmaps/Phase6_VerifiedStatistics_Roadmap.md). For phase-specific context see the full roadmap series [`docs/roadmaps/`](docs/roadmaps/) (Phase 1 through Phase 5y). |
| Understand predictive scope | [`docs/ARCHITECTURE_SCOPE.md`](docs/ARCHITECTURE_SCOPE.md) — Layer 3 boundary: SM+GR in scope, dark-energy sector out under tested mechanisms |
| Understand the broader research program | [`docs/Fluid-Based Approach to Fundamental Physics  Feasibility Study.md`](docs/Fluid-Based%20Approach%20to%20Fundamental%20Physics%20%20Feasibility%20Study.md) |
| Read the critical review | [`docs/Fluid-Based Approach to Fundamental Physics- Consolidated Critical Review v3.md`](docs/Fluid-Based%20Approach%20to%20Fundamental%20Physics-%20Consolidated%20Critical%20Review%20v3.md) |
| See the deep research corpus | [`Lit-Search/`](../Lit-Search/) — research files organized Phase-1 through Phase-5z |
| Work with Aristotle | [`docs/references/Theorm_Proving_Aristotle_Lean.md`](docs/references/Theorm_Proving_Aristotle_Lean.md) |
| Check the full inventory | [`SK_EFT_Hawking_Inventory.md`](SK_EFT_Hawking_Inventory.md) — comprehensive source of truth |

## Theorem Inventory (~3,950 theorems — 1 axiom, **0 sorry**)

**Canonical counts** live in `docs/counts.json`, regenerated by `scripts/update_counts.py`. The table below summarizes the module-level inventory by phase; for live numbers consult the JSON.

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
| FermiPointTopology.lean | 5j | 28+ | Fermi-point topological charge, |N|=1→U(1), |N|=2→SU(2) gauge emergence (all proved) |
| TemperleyLieb.lean | 5k | — | First TL algebra in any proof assistant; Jones–Wenzl prerequisite |
| SurgeryPresentation.lean | 5k | — | Kirby-calculus surgery presentation of 3-manifolds |
| WRTInvariant.lean | 5k | — | Witten–Reshetikhin–Turaev TQFT invariant (definition) |
| WRTComputation.lean | 5k | — | WRT invariants of S³, S²×S¹, lens spaces, figure-eight complement |
| JonesWenzl.lean | 5l | — | Jones–Wenzl idempotents at roots of unity |
| IsingGates.lean | 5l | — | Ising anyon gates generate the Clifford group (Microsoft-Majorana relevance) |
| FibonacciBraiding.lean | 5l | — | Fibonacci braid-group action at level k=3 |
| FibonacciUniversality.lean | 5l | — | Braiding Lie-algebra spanning → universality for quantum computation |
| FibonacciQutrit.lean | 5l | — | Qutrit braid construction |
| FibonacciQutritUniversality.lean | 5l | — | Qutrit universality |
| StringNet.lean | 5l | — | First string-net condensation formalization; toric code from Vec_{ℤ/2} |
| QuantumGroupGeneric.lean | 5m | 29 | `QuantumGroup k A` over arbitrary Cartan matrix A — first parameterized QG |
| QuantumGroupCoproduct.lean | 5m | 44 | Generic coproduct Δ for U_q(𝔤) |
| QuantumGroupAntipode.lean | 5m | 25 | Generic antipode S for U_q(𝔤) via MulOpposite |
| QuantumGroupHopf.lean | 5m | 31 | First generic HopfAlgebra instance for U_q(𝔤) |
| QuantumGroupInstantiation.lean | 5m | 39 | Equivalences qgA1 ≃ Uqsl2, qgA2 ≃ Uqsl3 |
| QuantumGroupMeta.lean | 5m | 16 | Exceptional Cartan matrices E₆/E₇/E₈/F₄ |
| KacWaltonFusion.lean | 5m | 63 | First Kac–Walton fusion algorithm in any proof assistant |
| KMatrixAnomaly.lean | 5n | — | K-matrix anomaly inflow / 3450 model gappability |
| VillainHamiltonian.lean | 5n | — | First Villain Hamiltonian formalization |
| TPFDisentangler.lean | 5n | — | TPF disentangler properties (chirality-wall 1+1D) |
| SPTStacking.lean | 5n | — | SPT phase stacking (chirality-wall 1+1D) |
| MugerCenter.lean | 5p | — | First Muger-center formalization; general dual-closure theorem |
| FPDimension.lean | 5p | — | Frobenius–Perron dimensions derived from fusion matrices |
| D2Formula.lean | 5p | — | Global-dimension formula D² = Σ (dim V)² |
| A1Ring.lean | 5q | — | A(1) Steenrod sub-algebra as F₂-algebra (structure + ring) |
| A1Resolution.lean | 5q | — | Minimal free resolution of F₂ over A(1) through degree 5 |
| A1Ext.lean | 5q | — | Ext dimensions 1, 2, 2, 2, 3, 4 — first Ext over a Steenrod sub-algebra |
| ExtBordismBridge.lean | 5q | — | Bridge from Ext to spin-bordism (H1/H3/H4 as focused hypotheses) |
| ChangeOfRings.lean | 5r | — | Ext_A ≅ Ext_{A(1)} via Hom-tensor adjunction; discharges topological H2 |
| FKGappedInterface.lean | 5s | — | First Fidkowski–Kitaev 2+1D Cayley-calibrated gapped interface, Δ=14 |
| ModularityTheorem.lean | 5s | — | General det(S) ≠ 0 → Z₂ trivial (pure linear algebra) |
| InstantonZeroModes.lean | 5s | — | Zero-mode counting bypassing the 4D index theorem via Clifford separation |
| CenterFunctorZ2.lean + CenterFunctorZ2Equiv.lean | 5s | — | Continuation of Center(Vec_{ℤ/2}) ≅ Rep(D(ℤ/2)) formalization |
| FermiHubbardDimer.lean | 5t | 143 | Fermi-Hubbard doublon geometric SWAP + minimal Berry-phase theorem |
| DiracFluidMetric.lean | 5w | 9 | 3×3 graphene Dirac-fluid acoustic metric, block-diag for quasi-1D |
| GrapheneHawking.lean | 5w | 7 | Dispersive correction, T_eff positivity, EFT validity for graphene |
| DiracFluidSK.lean | 5w | 9 | Conformal transport, KSS bound, EFT perturbativity |
| GrapheneNoiseFormula.lean | 5w | 8 | ΔS_I(ω) from Keldysh FDT + Landauer–Büttiker |
| QuasiOneDReduction.lean | 5w | — | Quasi-1D bound correction + greybody validation |
| HiddenSectorClassification.lean | 5x | — | ℤ₁₆-anomaly-driven SM-singlet Weyl enumeration |
| HiddenSectorMixedCharge.lean | 5x | — | Wan–Wang mixed-charge hidden-sector channel |
| CosmologicalConstant.lean | 5x | 8 | ADW-derived Λ magnitude + Volovik/Gibbons-Hawking doubling |
| FangGuTorsionDM.lean | 5x | 10 | Fang–Gu torsion-DM kinematic obstruction (w = 1/3) |
| FractonDarkMatter.lean | 5x | 25 | p-wave dipole superfluid viability; Arrhenius + BBN conditions |
| SFDMMergerForecast.lean | 5x | 30 | SFDM merger sonic-boom forecast; Rankine–Hugoniot closed form |
| DarkSectorSynthesis.lean | 5x | 22 | Seven cross-connection theorems; empirical-hook ranking |
| GibbsDuhemTheorem.lean | 5y | 16 | First emergent-vacuum obstruction: `w_vac = −1` locked by Lorentz + Gibbs–Duhem |
| QTheoryNoGoTheorem.lean | 5y | 12 | Obstruction realization-independent across 4 KV q-theory constructions |
| DarkEnergyObstructionPrinciple.lean | 5y | 8 | Four-factor orthogonality decomposition |
| DESIComparison.lean | 5y | 8 | DESI DR2 comparison infrastructure |
| VestigialEOS.lean | 5y | 20 | First closed-form `w_vest(τ) = (1−τ²)/(5τ²−1)` + `c_s²`, `ζ_vest` |
| VestigialMapping.lean | 5y | 8 | Charge-4e superconductor → vestigial-gravity dictionary |
| CondensedMatterAnalog.lean | 5y | 10 | Fernandes–Fu condensed-matter EOS correspondence |
| ClassificationTableDark.lean | 5y | 8 | Dark-sector candidate classification consolidation |
| ExtractDeps.lean | infra | — | Environment walker / axiom-closure extractor (Invariant #10 exception) |

## Build Environment

- **Lean:** 4.29.0 with Mathlib (pinned in `lean/lakefile.toml`, currently commit `8850ed93`).
- **Python:** ≥ 3.14, managed via uv. Key deps: numpy, scipy, sympy, mpmath, plotly, aristotlelib, torch, maturin.
- **Rust:** PyO3 extension for RHMC (`rust/src/lib.rs`). Rebuild with `PYO3_USE_ABI3_FORWARD_COMPATIBILITY=1 uv pip install -e rust/ --force-reinstall --no-deps`.
- **Visualization:** Plotly (not matplotlib). Color scheme: #2E86AB steel blue, #A23B72 berry, #F18F01 amber.

## Key References

**Project documentation:**
- [Wave Execution Pipeline](docs/WAVE_EXECUTION_PIPELINE.md) — the 12-stage process governing all work
- [Inventory Index](SK_EFT_Hawking_Inventory_Index.md) — quick reference: module map, counts, pipeline invariants
- [Knowledge Graph](docs/KNOWLEDGE_GRAPH.md) — interactive provenance visualization
- [Dashboard](docs/DASHBOARD.md) — parameter verification, proof architecture, paper claims

**Roadmaps:** [`docs/roadmaps/`](docs/roadmaps/) contains phase-specific execution plans (Phases 1 through 5y) and three Phase 6 forward-looking documents: [Phase6_Roadmap.md](docs/roadmaps/Phase6_Roadmap.md) (HPC-dependent vestigial-MC tracks), [Phase6_Deferred_Targets.md](docs/roadmaps/Phase6_Deferred_Targets.md) (continuously updated "future-work" register), and [Phase6_VerifiedStatistics_Roadmap.md](docs/roadmaps/Phase6_VerifiedStatistics_Roadmap.md) (formal-verification extension of the statistics pipeline).

**Stakeholder docs:** [`docs/stakeholder/`](docs/stakeholder/) contains non-technical implications and strategic positioning documents per phase, plus the Phase 5y closure memo and its four cross-phase impact notes.

**Deep research:** [`Lit-Search/`](../Lit-Search/) is organized by phase (`Phase-1-and-Background` through `Phase-5z`) covering quantum groups, modular tensor categories, Rokhlin's theorem, the ADW gap equation, fracton hydrodynamics and gravity, verified statistics, polariton protocols, TQFT partition functions, gauging obstructions, SU(3)_k fusion, Fermi-point topology, chirality-wall 3+1D, FK gapped interface, instanton zero-mode counting, graphene Dirac-fluid transport, dark-sector phenomenology, and Klinkhamer–Volovik q-theory obstruction analysis.

---

*Last updated: 2026-04-24-1439. Counts are a rolling snapshot — `docs/counts.json` is the single source of truth (regenerated by `scripts/update_counts.py`).*
