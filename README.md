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

Phase 6a Track C (Wave 3) formalizes the Bekenstein-Hawking entropy `S = A/(4 G_N) − (3/2)log(A/(4 G_N)) + c_0` at a horizon labeled by simple objects of a Modular Tensor Category (MTC). Per the deep-research literature survey (`Lit-Search/Phase-6a/6a-Horizon MTC boundary conditions...Wave 3.md`, 2026-04-25), no published paper places any specific MTC at the horizon of a 4D non-extremal black hole in an ADW substrate, so `BHEntropyMicroscopic.lean` ships in **Outcome-3 tracked-hypothesis mode** for the general case + an **Outcome-2 SU(2)_k sub-corollary** anchored on the Kaul-Majumdar derivation (gr-qc/0002040). Three machine-checked structural results: (i) the −3/2 log coefficient decomposes as (−1/2 from the Gaussian saddle) + (−1 from the SU(2) singlet projection in the I₀ − I₁ cancellation, Kaul-Majumdar Eq. (15)); (ii) the leading 1/4 prefactor is structurally a TUNING (Immirzi γ; Domagala-Lewandowski 0.2375 vs Meissner 0.2739 yield identical −3/2 under their respective counting prescriptions); (iii) Sen 2013 (arXiv:1205.0971) heat-kernel result for 4D Schwarzschild gives c_log = +(212/45 − 3) ≈ +1.71, an explicit non-universality witness encoded as `sen_4d_disagrees_with_kaul_majumdar`. The general-MTC tracked hypothesis bundles as `H_HorizonBoundaryCondition` with five falsifier theorems; the toric-code abelian falsifier triggers F2 (log d_max = 0 ⇒ κ_C = 0). Wave 3 originally introduced one new axiom `gaussianSaddleAsymptotic` — the Laplace-method asymptotic bound — which was subsequently retired in Phase 6a Wave 7 by shipping a project-local `LaplaceMethod.lean` derivation. Paper 26 documents the synthesis "SU(2)_k MTC + ADW substrate + Walker-Wang Z₂-time-reversal anomaly inflow" as a research-level conjecture novelty-flagged across the manuscript. **Adversarial-review followup pass closed 2026-04-26-0330**: 14 Stage 13 findings (5 BLOCKER + 7 REQUIRED + 2 RECOMMENDED) all addressed and verified closed by re-invocation; substantive `H_HorizonBoundaryCondition_implies_nonabelian_envelope` theorem replaces the prior trivial-projection corollary; +10 golden-identity tests in `tests/test_bh_entropy.py` (47 → 57); 16 paper26-related bibkeys flipped `doi_verified: True` after WebFetch verification.

### BCH four laws + regime partition for emergent-gravity ADW black holes (Schwarzschild ↔ ADW-extremality, Schottky-saturation cooling-toward-extremality)

Phase 6a Track C (Wave 5) formalizes the Bardeen-Carter-Hawking four laws of black-hole mechanics in two regimes of the ADW emergent-gravity substrate, separated by a critical mass `M_c = (N_f · Λ_UV) / (12π · α_ADW)` (Wave 5 deep-research §3 dimensional ansatz; not pinned by any published primary source). The structural anchor is Jacobson-Koike (in *Artificial Black Holes*, World Scientific 2002, arXiv:cond-mat/0205174) Eq. (13): `T_H(v) = T_H(0) · (1 − v²/c_⊥²)` for an analog black hole in ³He-A — the only published primary-source closed form for a sign-inverted Hawking temperature in an emergent-gravity substrate. The qualitative "BHs cool toward extremality" claim appears verbatim in Jacobson-Volovik (PRD 58, 064021, arXiv:cond-mat/9801308) §VIII. `BHThermodynamicsFourLaws.lean` ships **18 theorems, 0 sorry, 0 new axioms** under tracked-hypothesis mode (Outcome-3): a decidable `Regime` classifier (Schwarzschild | Boundary | ADWExtremality), the `T_H_schottky` Schottky-saturation form, two `FourLaws_*` Prop bundles with opposite heat-capacity signs, and a tracked-hypothesis bundle `H_RegimePartition` parameterized by *externally-supplied* `slope` and `delta` real numbers (explicit ∃-absorption avoidance). The substrate-response coefficient ansatz `δ_ADW = (α_ADW − 1) · Λ_UV` (deep-research §9) vanishes in the bare Sakharov-Adler limit `α_ADW = 1`. The second law uses Glorioso-Liu SK-EFT entropy-current monotonicity (arXiv:1612.07705) without invoking pointwise NEC. The third law preserves Israel's strong form in the natural Schottky branch but admits Kehle-Unger-style violation (arXiv:2211.15742) in BPS-violating matter sectors, conditional on Reall (PRD 110, 124059, arXiv:2410.11956) restoration. Four falsifier theorems: quadratic-form, boundary-character (Davies vs Dymnikova), third-law-form, χ_vest dependence. Cross-wave bridges to Wave 1's `G_N^emerg` and Wave 3's `kaulMajumdarS` (the latter establishes weak-Nernst preserved + strong-Nernst violated in the ADW-extremality regime). Paper 27 documents the regime partition criterion as project-original; the ADW-substrate-specific `M_c(α_ADW, Λ_UV, N_f, χ_vest)` is unpinned by any published derivation.

### Heat-kernel calibration and higher-curvature structure (Phase 6e)

Phase 6e formalizes the heat-kernel calibration of the emergent-gravity action against the Christensen-Duff Dirac heat-kernel coefficients (a₀ cosmological-constant, a₂ Einstein-Hilbert, a₄ four-derivative Stelle basis), giving the closed-form Stelle (α, β, γ) coefficients at order a₄ in terms of N_f and Λ_UV. Order-by-order *nonlinear* diffeomorphism invariance is verified for the emergent action expansion. A variational nonlinear EFE is shipped as a Decision Gate biconditional (`linearized ↔ full nonlinear matching` under the heat-kernel calibration). Multi-channel post-Newtonian (PPN) bookkeeping demonstrates that the substrate's higher-curvature corrections sit inside published Solar-System bounds. The cosmological constant appears in *emergent* form (a₀-driven, not a UV input). The Einstein-Cartan extension formalizes torsion in the substrate and discharges Kostelecky / Hughes-Drever–type Lorentz-violation bounds, including the substrate-induced spin-torsion coupling. Papers 39–43 document the heat-kernel calibration, Stelle basis, nonlinear EFE Decision Gate, multi-channel PPN, and Einstein-Cartan extension respectively.

### Classical-GR algebraic backbone (Phase 6f)

Phase 6f delivers what is, to our knowledge, the first formalization in any proof assistant of the classical-GR algebraic backbone: the algebraic Riemann tensor (with all its symmetries — antisymmetry on each pair, pair-exchange symmetry, first Bianchi identity), the Ricci and Einstein tensors, and the four classical energy conditions WEC / NEC / DEC / SEC (with the conditional implications between them). On top of this skeleton sits an exact-solutions catalog — Minkowski, de Sitter, anti-de Sitter, Schwarzschild — together with a Λ-vacuum biconditional characterizing which exact solutions correspond to which sign of the cosmological constant. The ADM 3+1 decomposition is formalized at structural level: the Hamiltonian and momentum constraints are stated as biconditionals against the spatial Einstein equations restricted to a constant-time slice. The tetrad formalism is added on the side, including Cartan's structure equations relating the connection 1-form, the curvature 2-form, and the torsion 2-form. This module collection forms the substrate against which the Phase 6g singularity / no-hair results, the Phase 6m thermo-GR programme, and the Phase 6n math-substrate work are stated.

### Singularities and no-hair (Phase 6g)

Phase 6g formalizes the causal-structure axioms of Wald §8.1 (chronology, strong causality, global hyperbolicity at the Prop level) and the Penrose singularity hypothesis bundle, with the Riccati focusing equation as the load-bearing analytic core. The Hawking-Penrose SEC variant is shipped as a sibling theorem under the SEC instead of NEC. A Schwarzschild-specific monotone-mass area theorem is proved against the algebraic Schwarzschild solution from Phase 6f. The Kerr no-hair theorem appears in conditional form, with sub-extremality `J² ≤ M⁴` as a Prop hypothesis on the parameter space rather than a derived bound. The Cauchy problem for the vacuum Einstein equations is scoped at the structural-Prop level — full well-posedness is gated on Mathlib PDE infrastructure that does not yet exist, and is documented as a fallback boundary in the bundle.

### Three-track dark-energy closure (Phase 6m)

Phase 6m delivers a synthesis closure on emergent dark energy across three independent mechanism tracks. **Track A — causal-set DE:** three NO-GO theorems plus three publishable structural caveats, all independent of DESI DR2. **Track B — entropic-gravity DE:** an 8-out-of-8 unanimous NO-GO across the Verlinde / Tsallis / Barrow / Padmanabhan / Cai-Kim / Easson-Frampton-Smoot / Komatsu-Kimura / Odintsov mechanism family — the **first complete-mechanism-family unanimous NO-GO closure for dark energy in the literature** (8/8 disfavoured at varying information-criteria thresholds, with 3-of-8 Bayes-decisive at Jeffreys ≳ 5). **Track C — Jacobson-thermo-GR DE:** five-or-more R5-survivor mechanisms, of which the strongest CLEARED-R5 candidate is M3 EGJ f(R) Exp+ArcTanh, at Plaza-Kraiselburd ΔAIC ≃ ΔBIC ≳ 20. The Phase 6e Sakharov 4-criterion cross-bridge classifies known substrates: ³He-A satisfies all four, while FLS BEC violates condition (ii); Wave 4a (2026-05-08, verdict B) retired the previously-asserted Λ_J = Λ_HK biconditional in favour of a one-way implication plus a load-bearing depletion field, with primary-source evidence from Volovik-Jannes 2012 and Finazzi-Liberati-Sindoni 2012. A 7-class GD (gravitational-decoupling) taxonomy with a 3-tier applicability gradient closes the synthesis. See `docs/ARCHITECTURE_SCOPE.md` for the full Phase 6m closure verdict.

### Math substrate (Phase 6n)

Phase 6n consolidates the mathematical substrate underneath the three-layer architecture. The Glorioso-Liu axiomatic skeleton for SK-EFT is reframed with `FirstOrderKMS` cast as a first-order projection of the full Glorioso-Liu axioms (rather than a competing axiomatization). The Perarnau-Llobet quantum-Crooks NO-GO is formalized including the ℂ-form higher-dimensional no-go. An LDP linear-response framework lifts the `W`-form Gallavotti-Cohen identity to an abstract `IsLDPRateFunction` typeclass, which is consumed by the Phase 6o stochastic-calculus track. The Sakharov ↔ horizon-Crooks unification holds at the horizon temperature β_H, bridging emergent-gravity substrate physics to the quantum-Crooks NO-GO architecture. The SymTFT audit substrate is built end-to-end: the Drinfeld center via DMNO 2010 Witt-equivalence; `FreeKLinearCategory` with monoidal, braided, and `MonoidalPreadditive`/`Linear` structure; the Deligne tensor as a quotient with all coherence laws plus a `CategoricalCcStructure`; and a `PseudoUnitary` predicate at restricted-form layer with a strict refinement that breaks the trivial-witness equivalence and exposes genuine DMNO 2010 Theorem 5.2 content. These are first-of-kind formalizations in any proof assistant for the categorical-cc and Deligne-tensor coherence layers.

### Phase 6o substrate findings

Phase 6o ships substantive first-of-kind results across five tracks. **Boostless / Carrollian soft theorems** are formalized on three substrates — BEC, ADW, and polariton — closing the Strominger triangle (asymptotic symmetries ↔ soft theorems ↔ memory effects) at the substrate-physics level. **G4 — Kerr-Schild classical double-copy** on a Petrov-type-D acoustic metric: this is the **first explicit classical double-copy on an analog-gravity substrate in the literature**, accompanied by a 3-obstruction strong-form BCJ NO-GO that bounds where the double-copy generalizes. **APS-η for analog horizons:** parity-symmetric BEC and ADW substrates give η = 0; ³He-A gives a non-zero APS-η, distinguishing the substrates at the index-theory level. **G1 — Schellekens chain reframing:** the divisibility `24 | c₋` is reframed as a corollary of Möller-Scheithauer 2024 c = 24 holomorphic-VOA classification, sharpening the Phase 5b modular-generation argument. **ETH-α refutation tableau:** three concrete refutation theorems on five candidate predicates close the eigenstate-thermalization-hypothesis branch at the substrate level. The Itô calculus + LDP framework + `LDPCompatibleSKEFT` typeclass form the substrate for the I3 publication bundle ("Verified Stochastic Calculus for Mathlib4").

### Fibonacci-anyon density and quantitative Solovay–Kitaev (Phase 5 Step 13 + Phase 6t)

Two interlocking results close the topological-quantum-computation chain at the kernel-verified level. **Phase 5 Step 13 (2026-05-22)** ships the unconditional density half of the Freedman–Kitaev–Larsen–Wang theorem: the two-strand braid representation of the Fibonacci anyon model, restricted to the Fibonacci subsector and embedded as a homomorphism `B_2 → SU(2)`, has dense image in `SU(2)`. The terminal theorem `SKEFTHawking.FKLW.fibonacci_density_F21_unconditional` has axiom closure `[propext, Classical.choice, Quot.sound]` (Lean standard kernel only) and zero tracked propositional hypotheses; it is the first kernel-verified unconditional FKLW density statement for Fibonacci anyons in any proof assistant. The proof was discharged via a Cartan v4 Inverse Function Theorem 3-direction composition through `↥𝔰𝔲(2)` (~370 LoC), much lighter than the originally scoped closed-subgroup classification route. Supporting modules under `lean/SKEFTHawking/FKLW/` include `SU2BCHBracketClosure.lean`, `OneParameterSubgroupSU2.lean`, `SU2LieAlgebra.lean`, `SU2MatrixExp.lean`, `SU2LocalDiffeo.lean`, `SU2InteriorBridge.lean`, and `FibonacciDensityConditional.lean`.

**Phase 6t Path A Option C (2026-05-23)** instantiates this on the compiler side: a constructive Dawson–Nielsen Solovay–Kitaev compiler `skApproxC` with VISIBLE composition (no opaque `Classical.choose`) is fully discharged for the tight-ε regime via a Y_h Lipschitz π/2 tightening (Mathlib-PR-quality substrate cascade, ~900 LoC). The strict headline `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` is UNCONDITIONAL for ε ∈ (0, ε₀] and bundles BOTH the error bound `‖ρ(compile U ε) − U‖ ≤ ε` AND the length bound `skLength ≤ skLengthConst · (log(1/ε))^skLengthExponent` at the same algorithmic compile level (with `skLengthExponent := log 5 / log(3/2) ≈ 3.97`, the canonical Dawson–Nielsen exponent). This is the **first kernel-verified quantitative Solovay–Kitaev length bound in any proof assistant**. Paper bundle D4 documents the end-to-end chain; see `docs/PHASE6T_QUANTITATIVE_SK_COMPLETE.md` for the canonical ship summary.

---

## Technical Summary

**Lean 4 formalization:** **7,342 theorems** (7,317 substantive + 25 placeholder) across **389 modules**. **0 axioms project-wide** (Phase 5h Wave 1, 2026-05-19: the last structural axiom `gapped_interface_axiom` was retired by conversion into the tracked-Prop `TPFConjecture` — see `docs/PERMANENT_TRACKED_HYPOTHESES.md`; the prior `gaussianSaddleAsymptotic` was retired in Phase 6a Wave 7 via a project-local `LaplaceMethod.lean` derivation). The project's posture is that load-bearing research-grade physical assumptions are carried as explicit *tracked-Prop hypotheses* on consumer theorems rather than as global axioms — making the claim surface visible at the type-signature level. **0 sorry project-wide**. 322 theorems Aristotle-proved across 44 runs. Lean 4.29.1, Mathlib commit `5e932f97` (Mathlib v4.29.1 tag, 2026-04-17). **Synced 2026-05-23 PM** post Phase 6q close — counts refreshed from `docs/counts.json` (generated 2026-05-23T16:12).

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
- First kernel-verified unconditional density of the Fibonacci-anyon two-strand braid representation in SU(2) — the density half of the Freedman–Kitaev–Larsen–Wang theorem (Phase 5 Step 13, 2026-05-22).
- First kernel-verified quantitative Solovay–Kitaev length bound in any proof assistant, instantiated for the Fibonacci-anyon compiler (Phase 6t Path A Option C, 2026-05-23).

**Three-layer verification:** Python numerics ↔ Lean 4 formal proofs ↔ Aristotle automated theorem prover.

**42 per-paper drafts in a unified codebase, consolidated into 14 publication-bundle targets per the Phase 7 paper-strategy reframe** (see `docs/PAPER_STRATEGY.md` and `docs/PAPER_DRAFT_MAPPING.md`). The per-paper drafts in `papers/paperN_*/` remain as historical/source material; external communication routes through the bundles defined below.

## Paper Strategy and Phase 7 Bundle Architecture

Beginning Phase 6i Wave 7, the project's external communication is organized as **14 publication targets** rather than as one paper per wave. The architecture is one Tier-0 flagship review (F) + five Tier-1 themed deep papers (D1–D5) + three Tier-2 PRL-style headline letters (L1–L3) + three Tier-3 infrastructure papers (I1, I2, I3) + two Tier-4 experimental letters (E1, E2). I3 ("Verified Stochastic Calculus for Mathlib4") was added in Phase 6n Session 4 on top of the original 13-bundle architecture. As of the 2026-05-23 heatmap regeneration, **bundles D1, D2, L1, L2, L3, I1, I2, I3, E1, and E2 are GREEN**; bundles F, D3, D4, and D5 carry open Stage-13 findings (post-supersession) and are working toward closure (D4 was closed at GREEN with cross-bundle reciprocity advisories on 2026-05-23 PM; the remaining RED bundles are tracked in `docs/BUNDLE_READINESS_HEATMAP.md`).

The frozen 14-step lift procedure for moving per-paper draft content into a bundle is documented at `docs/BUNDLE_LIFT_PROCEDURE.md`; the protocol for absorbing late Phase-6 waves into already-drafted bundles (without redrafting) is at `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`. Phase 7 absorption Sessions 1–5 (2026-05-06 → 2026-05-08) absorbed all Phase 6n / 6o substrate content into the bundles via D.2 / D.3 / D.4 branches of the absorption protocol.

## Project Structure

```
SK_EFT_Hawking/
├── lean/                              # Lean 4 formalization (7213 theorems, 0 axioms, 389 modules, 0 sorry)
│   ├── lakefile.toml                  # Lake build config (pinned Mathlib 5e932f97, v4.29.1)
│   ├── lean-toolchain                 # Lean 4 v4.29.1
│   ├── SKEFTHawking.lean              # Root module (imports all theorem modules; 389 modules in `docs/counts.json`)
│   └── SKEFTHawking/                  # 389 modules organized into nine functional areas
│       │                              # (acoustic-Hawking foundation; emergent gauge fields & chirality;
│       │                              #  anomaly classification & modular invariance; quantum groups,
│       │                              #  Hopf algebras & fusion categories; modular tensor categories,
│       │                              #  braiding & TQFT; topological quantum computation; emergent
│       │                              #  gravity; dark sector; verified statistics & substrate
│       │                              #  infrastructure). See "Formalization at a Glance" below and
│       │                              #  `SK_EFT_Hawking_Inventory_Index.md` for the per-module map.
│       ├── Basic.lean                 # Shared types and definitions
│       ├── FKLW/                      # Phase 5-6t: FKLW density, Solovay-Kitaev compiler,
│       │                              #             Cartan substrate, BCH bracket closure
│       ├── QuantumCrooks/             # Phase 6n: Quantum-Crooks no-go architecture
│       ├── CrooksAnalogHawking/       # Phase 6c: Sakharov ↔ horizon-Crooks unification
│       └── …                          # Module-by-module breakdown lives in `SK_EFT_Hawking_Inventory.md`;
│                                      # authoritative list at `docs/counts.json::module_names`.
│
├── src/
│   ├── core/                          # Shared infrastructure
│   │   ├── transonic_background.py    # 1D BEC transonic flow solver + δ_diss estimates
│   │   ├── aristotle_interface.py     # Aristotle API + sorry-gap registry (322 proved, 0 sorry)
│   │   ├── visualizations.py          # Plotly figures (156 functions) + COLORS palette
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
├── papers/                            # 42 per-wave drafts + 14 publication bundles (F, D1-D5, L1-L3, I1-I3, E1-E2)
│   │                                  # Per-wave drafts (`paperN_*/paper_draft.tex`) are historical source material;
│   │                                  # external communication routes through the bundles per `docs/PAPER_STRATEGY.md`.
│   │                                  # Current bundle readiness lives in `docs/BUNDLE_READINESS_HEATMAP.md`.
│   ├── F/                             # Tier 0: flagship review (1 paper)
│   ├── D1/ … D5/                      # Tier 1: themed deep papers (5 papers, PRD/JHEP-class)
│   ├── L1/ L2/ L3/                    # Tier 2: PRL-style headline letters (3 papers)
│   ├── I1/ I2/ I3/                    # Tier 3: infrastructure papers (3 papers, including I3 "Verified Stochastic Calculus for Mathlib4")
│   ├── E1/ E2/                        # Tier 4: experimental letters (2 papers)
│   ├── paperN_*/                      # 42 per-wave drafts (paper1_first_order through paper45_phase6m_review)
│   ├── AutomatedReviews/              # Stage 13 adversarial-reviewer output per paper (Phase 5v)
│   ├── claim_clusters.json            # Cross-paper claim clusters
│   ├── cluster_bundle_index.json      # Cross-bundle cluster registry
│   └── experimental_predictions/      # Standalone prediction tables (Phase 4)
│       └── prediction_tables.tex
│
├── notebooks/                         # 89 Jupyter notebooks, one Technical + one Stakeholder version per wave
│   │                                  # spanning Phases 1, 2, 3a-3d, 4a-4b, 5a-5z, 6b-6t.
│   │                                  # Technical notebooks reproduce the wave's full computation pipeline
│   │                                  # (Plotly figures, transport-coefficient tables, MC histograms);
│   │                                  # Stakeholder notebooks present the lay-audience narrative.
│   │                                  # Recent additions: `Phase6t_SolovayKitaev_{Technical,Stakeholder}.ipynb`
│   │                                  # (the quantitative Dawson-Nielsen compiler).
│
├── docker/
│   └── docker-compose.graph.yml       # PG+AGE container for knowledge graph (port 5433)
│
├── docs/
│   ├── KNOWLEDGE_GRAPH.md             # Knowledge graph documentation and guide
│   ├── roadmaps/                      # Per-phase execution roadmaps (Phase 1 through Phase 5y + Phase 6 forward register)
│   ├── stakeholder/                   # Implications, strategic positioning, companion guides
│   ├── aristotle_results/             # All 44 Aristotle run archives (322 theorems proved)
│   └── archive/                       # Superseded artifacts
│
├── tests/                             # pytest suite (4195 tests across 100 files; default `uv run pytest tests/` is fast (deselects `slow`); add `-m ''` for full run)
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
├── figures/                           # 156 figure functions (PNG + HTML rendered in `figures/`) + provenance_graph.json
├── scripts/
│   ├── submit_to_aristotle.py         # Aristotle submission + integration script
│   ├── validate.py                    # ~28 cross-layer validation checks (incl. graph_integrity, claim_clusters_fresh, bundle_consistency, bundle_source_freshness, bibitem_title_primary_source — run `validate.py --list` for the live set)
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
| Understand the execution process | [`docs/WAVE_EXECUTION_PIPELINE.md`](docs/WAVE_EXECUTION_PIPELINE.md) — 14-stage pipeline |
| Explore the provenance graph | [`docs/KNOWLEDGE_GRAPH.md`](docs/KNOWLEDGE_GRAPH.md) — interactive D3 visualization |
| Browse the dashboard | `uv run python scripts/provenance_dashboard.py` → http://localhost:8050 |
| Read non-technical summaries | `docs/stakeholder/` — implications and strategic positioning per phase |
| See what's next | [`docs/roadmaps/Phase6_Deferred_Targets.md`](docs/roadmaps/Phase6_Deferred_Targets.md), [`Phase6_Roadmap.md`](docs/roadmaps/Phase6_Roadmap.md), and [`Phase6_VerifiedStatistics_Roadmap.md`](docs/roadmaps/Phase6_VerifiedStatistics_Roadmap.md). For phase-specific context see the full roadmap series [`docs/roadmaps/`](docs/roadmaps/) (Phase 1 through Phase 5y). |
| Understand predictive scope | [`docs/ARCHITECTURE_SCOPE.md`](docs/ARCHITECTURE_SCOPE.md) — Layer 3 boundary: SM+GR in scope, dark-energy sector out under tested mechanisms |
| Understand the broader research program | [`docs/Fluid-Based Approach to Fundamental Physics  Feasibility Study.md`](docs/Fluid-Based%20Approach%20to%20Fundamental%20Physics%20%20Feasibility%20Study.md) |
| Read the critical review | [`docs/Fluid-Based Approach to Fundamental Physics- Consolidated Critical Review v3.md`](docs/Fluid-Based%20Approach%20to%20Fundamental%20Physics-%20Consolidated%20Critical%20Review%20v3.md) |
| See the deep research corpus | [`Lit-Search/`](../Lit-Search/) — research files organized Phase-1 through Phase-6t |
| Work with Aristotle | [`docs/references/Theorm_Proving_Aristotle_Lean.md`](docs/references/Theorm_Proving_Aristotle_Lean.md) |
| Check the full inventory | [`SK_EFT_Hawking_Inventory.md`](SK_EFT_Hawking_Inventory.md) — comprehensive source of truth |

## Formalization at a Glance

**7,342 theorems across 378 Lean 4 modules, with 0 axioms and 0 sorry project-wide.** Canonical counts live in `docs/counts.json`, regenerated by `scripts/update_counts.py`; the full per-module breakdown lives in [`SK_EFT_Hawking_Inventory_Index.md`](SK_EFT_Hawking_Inventory_Index.md) and [`SK_EFT_Hawking_Inventory.md`](SK_EFT_Hawking_Inventory.md).

### Library architecture

The Lean library is organized into roughly nine functional areas:

- **Acoustic-Hawking foundation** — acoustic metric, SK doubling, universality, WKB and exact WKB connection formula, second- and third-order SK-EFT, CGL FDR derivation, dispersive corrections.
- **Emergent gauge fields and chirality** — gauge erasure (no non-Abelian gauge survives the fluid layer), Fermi-point topological charge → emergent U(1) and SU(2), chirality-wall analysis (Golterman–Shamir conditions, TPF evasion, three-pillar master synthesis).
- **Anomaly classification and modular invariance** — Z₁₆ classification, Pauli matrices, Wilson mass, BdG Hamiltonian, GT commutation `[H, Q_A] = 0`, Steenrod A(1) algebra, the SM ℤ₁₆-anomaly computation, the generation constraint `N_f ≡ 0 (mod 3)` and its modular-invariance derivation.
- **Quantum groups, Hopf algebras, and fusion categories** — the first quantum group `U_q(sl₂)` in any proof assistant, its Hopf-algebra structure, the first rank-2 quantum group `U_q(sl₃)` with `SU(3)_k` fusion, a parameterized `QuantumGroup k A` typeclass over arbitrary Cartan matrices, the Kac–Walton fusion algorithm, restricted quantum groups, generic Hopf instance.
- **Modular tensor categories, braiding, and TQFT** — Ising and Fibonacci MTC F-symbols and pentagon equations, hexagon, ribbon, Reshetikhin–Turaev knot invariants (trefoil = −1, figure-eight), TQFT partition functions on closed surfaces, WRT invariants via surgery, Temperley–Lieb, Jones–Wenzl, Müger center, Frobenius–Perron dimensions, dual-closure, string-net condensation.
- **Topological quantum computation** — Ising anyon gates (Clifford group), Fibonacci braiding and universality (Lie-algebra spanning), `SU(3)_k` Fibonacci subcategory at level 2, the FKLW density theorem for Fibonacci anyons in `SU(2)` (first kernel-verified unconditional version), the constructive Dawson–Nielsen Solovay–Kitaev compiler with quantitative length bound (Phase 6t), the Fermi-Hubbard doublon geometric SWAP gate.
- **Emergent gravity** — ADW tetrad-condensation gap equation, fracton hydrodynamics → full-GR obstruction, vestigial gravity, the linearized Einstein equations and their Sakharov–Adler form, FLRW cosmology with Friedmann I/II and Bianchi consistency, gravitational-wave propagation under the vestigial-graviton identification (and its GW170817 falsification), Bekenstein–Hawking entropy from MTC state counting, the BCH four laws partitioned by mass regime, the classical-GR algebraic backbone (Riemann/Ricci/Einstein tensors, energy conditions, exact solutions, ADM 3+1), causal structure, singularities, no-hair, three-track dark-energy closure.
- **Dark sector** — ℤ₁₆-anomaly-driven SM-singlet hidden sectors, fracton dark matter, Fang–Gu torsion DM, the superfluid-dark-matter merger forecast, the Gibbs–Duhem emergent-vacuum no-go, the closed-form vestigial-gravity EOS, the four-factor dark-energy obstruction principle, DESI DR2 comparison infrastructure.
- **Verified statistics and substrate infrastructure** — jackknife variance and autocorrelation estimators (first verified in any proof assistant), Cauchy–Schwarz, effective sample size; the Glorioso–Liu SK-EFT axiomatic skeleton, the quantum-Crooks no-go architecture, Itô calculus and large-deviation linear-response, the SymTFT audit substrate (Drinfeld center via Witt-equivalence, Deligne tensor, pseudo-unitarity).

### Headline theorems

The following kernel-verified theorems are the load-bearing public claims of the project. Each is closed under the standard Lean kernel `[propext, Classical.choice, Quot.sound]` and carries 0 sorry.

| Theorem | Module | What it says |
|---|---|---|
| `fibonacci_density_F21_unconditional` | `SKEFTHawking/FKLW/SU2BCHBracketClosure.lean` | The two-strand Fibonacci-anyon braid representation has dense image in `SU(2)` — first kernel-verified unconditional FKLW density statement (Phase 5 Step 13, 2026-05-22). |
| `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` | `SKEFTHawking/FKLW/SolovayKitaevPathA.lean` | A constructive Dawson–Nielsen compiler achieves error `‖ρ(compile U ε) − U‖ ≤ ε` and length `≤ skLengthConst · (log(1/ε))^{log 5 / log(3/2)}` at the same compile level — first kernel-verified quantitative Solovay–Kitaev length bound (Phase 6t, 2026-05-23). |
| `generation_constraint_iff` | `SKEFTHawking/GenerationConstraint.lean` | The number of Standard-Model generations satisfies `3 ∣ N_f` iff `24 ∣ 8 N_f` — first formally verified anomaly constraint on SM particle content. |
| `wang_bridge_full_chain` | `SKEFTHawking/WangBridge.lean` | The 16-Weyl spectrum forces the chiral central charge `c₋ = 8 N_f`; fractional `c₋` requires right-handed neutrinos. |
| `pillar1_tpf_escapes` + `pillar2_chiral_symmetry_exists` + `pillar3_z16_strengthens` | `SKEFTHawking/ChiralityWallMaster.lean` | Three-pillar chirality-wall synthesis: TPF construction escapes the Golterman–Shamir no-go, GT positive construction realizes a chiral charge with `[H, Q_A] = 0`, and the Z₁₆ anomaly anchors the algebraic side. |
| `gauge_erasure` + `su2_erased` + `su3_erased` + `u1_survives` | `SKEFTHawking/GaugeErasure.lean` | Non-Abelian gauge symmetries (SU(2), SU(3)) cannot survive passage through a fluid-like layer; only U(1) is preserved. |
| `dof_mismatch_4d` + `bootstrap_gap_order_2` + `fracton_fails_diffeo` | `SKEFTHawking/FractonGravity.lean` | Fracton hydrodynamics reproduce weak-field gravity (order 1) but disagree with full GR from order 2 onward; structural DoF mismatch (4 vs 2 in 4D) and diffeomorphism-invariance failure. |
| `wVac_eq_neg_one_of_rhoV_ne_zero` + `selftuning_two_cases` | `SKEFTHawking/GibbsDuhemTheorem.lean` | Any single-scalar self-tuning emergent-vacuum framework with Gibbs–Duhem equilibrium locks `w_vac = −1` (or `ρ_vac = 0`) by Lorentz invariance — first machine-checked emergent-vacuum obstruction. |
| `vestigial_natural_range_violates_ligo` + `natural_range_disjoint_from_ligo_window` | `SKEFTHawking/GravitationalWaves.lean` | Under the Volovik vestigial-second-sound graviton identification, the natural susceptibility range gives `Δc/c ∈ [−0.68, +2.16]`, exceeding the GW170817 cap by `~7 × 10¹⁴` — both endpoints proved as falsifier theorems. |
| `G_N_emerg_match_at_planck_anchor` | `SKEFTHawking/LinearizedEFE.lean` | The ADW emergent Newton constant is `G_N^emerg = α_ADW · 12π / (N_f Λ²)`; at the Planck anchor `Λ = M_P^obs` the match `G_N^emerg = G_N^obs` reduces to `α_ADW · 12π = N_f`, giving `α_ADW* ∈ [0.40, 1.27]` for SM `N_f ∈ {15, 16, 45, 48}` (inside the Vergeles natural range). |
| `kaul_majumdar_log_coefficient` + `kaul_majumdar_log_decomposition` | `SKEFTHawking/BHEntropyMicroscopic.lean` | The Bekenstein–Hawking entropy is `S = A/(4 G_N) − (3/2) log(A/(4 G_N)) + c₀` with the −3/2 log coefficient decomposing as `(−1/2)` (Gaussian saddle) + `(−1)` (SU(2) singlet projection) — first formal MTC-state-counting derivation. |
| `agp_threshold_steane_strict` | `SKEFTHawking/FaultTolerance/AGP/Threshold.lean` | Threshold theorem under the Aharonov–Ben-Or AGP rate: logical-error suppression at every fault-tolerant level for sufficiently small per-gate error. |
| `jackknifeVariance_nonneg` | `SKEFTHawking/VerifiedJackknife.lean` | The jackknife variance estimator is non-negative — first verified statistical estimator in any proof assistant. |
| `dark_state_dynamical_phase_vanishes` + `geometric_phase_minus_one_on_pi_loop` | `SKEFTHawking/FermiHubbardDimer.lean` | The Fermi-Hubbard doublon dark state has vanishing dynamical phase under a π-sweep and picks up a purely geometric −1 holonomy — first formally verified symmetry-protected (non-topological) two-qubit gate. |
| `diracFluidMetric_txBlock_lorentzian_at_horizon` + `diracFluid_hawkingTemp_eq_BEC` | `SKEFTHawking/DiracFluidMetric.lean` | The 3×3 graphene Dirac-fluid acoustic metric block-diagonalizes for quasi-1D flow (the t–x block is Lorentzian at the horizon and the Hawking temperature reduces to the BEC form), enabling reuse of the BEC WKB machinery for the Dean bilayer-graphene sonic horizon. |

### Tracked-hypothesis Props

The project carries **four load-bearing tracked-hypothesis Props** on consumer theorems rather than as global axioms — `H_VestigialModeIsGraviton`, `H_DESICompatibility`, `H_RT_Formula_Valid`, and `TPFConjecture` (the last converted from the former `gapped_interface_axiom` on 2026-05-19). Each is documented with its physics status, non-vacuity witnesses, consumers, and discharge posture in [`docs/PERMANENT_TRACKED_HYPOTHESES.md`](docs/PERMANENT_TRACKED_HYPOTHESES.md). This makes the project's claim surface visible at the type-signature level: any theorem that depends on a research-grade physical assumption propagates that dependency explicitly.

## Build Environment

- **Lean:** 4.29.1 with Mathlib (pinned in `lean/lakefile.toml` at commit `5e932f97`, the v4.29.1 tag). The Lean REPL (used by the `lean-lsp-mcp` interactive dev loop) is pinned at v4.29.0 — patch-level compatible with the toolchain since the REPL is a thin protocol wrapper.
- **Python:** ≥ 3.14, managed via uv. Key deps: numpy, scipy, sympy, mpmath, plotly, aristotlelib, torch, maturin.
- **Rust:** PyO3 extension for RHMC (`rust/src/lib.rs`). Rebuild with `PYO3_USE_ABI3_FORWARD_COMPATIBILITY=1 uv pip install -e rust/ --force-reinstall --no-deps`.
- **Visualization:** Plotly (not matplotlib). Color scheme: #2E86AB steel blue, #A23B72 berry, #F18F01 amber.

## Key References

**Project documentation:**
- [Wave Execution Pipeline](docs/WAVE_EXECUTION_PIPELINE.md) — the 14-stage process governing all work
- [Inventory Index](SK_EFT_Hawking_Inventory_Index.md) — quick reference: module map, counts, pipeline invariants
- [Knowledge Graph](docs/KNOWLEDGE_GRAPH.md) — interactive provenance visualization
- [Dashboard](docs/DASHBOARD.md) — parameter verification, proof architecture, paper claims

**Roadmaps:** [`docs/roadmaps/`](docs/roadmaps/) contains phase-specific execution plans (Phases 1 through 5y) and three Phase 6 forward-looking documents: [Phase6_Roadmap.md](docs/roadmaps/Phase6_Roadmap.md) (HPC-dependent vestigial-MC tracks), [Phase6_Deferred_Targets.md](docs/roadmaps/Phase6_Deferred_Targets.md) (continuously updated "future-work" register), and [Phase6_VerifiedStatistics_Roadmap.md](docs/roadmaps/Phase6_VerifiedStatistics_Roadmap.md) (formal-verification extension of the statistics pipeline).

**Stakeholder docs:** [`docs/stakeholder/`](docs/stakeholder/) contains non-technical implications and strategic positioning documents per phase, plus the Phase 5y closure memo and its four cross-phase impact notes.

**Deep research:** [`Lit-Search/`](../Lit-Search/) is organized by phase (`Phase-1-and-Background` through `Phase-6t`) covering quantum groups, modular tensor categories, Rokhlin's theorem, the ADW gap equation, fracton hydrodynamics and gravity, verified statistics, polariton protocols, TQFT partition functions, gauging obstructions, SU(3)_k fusion, Fermi-point topology, chirality-wall 3+1D, FK gapped interface, instanton zero-mode counting, graphene Dirac-fluid transport, dark-sector phenomenology, Klinkhamer–Volovik q-theory obstruction analysis, classical-GR backbone, heat-kernel calibration, three-track dark-energy closure, and the FKLW + quantitative Solovay–Kitaev substrate.

---

*Last updated: 2026-05-23. Counts are a rolling snapshot — `docs/counts.json` is the single source of truth (regenerated by `scripts/update_counts.py`).*
