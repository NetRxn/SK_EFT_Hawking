# SK-EFT Hawking: Formally Verified Physics from Analog Black Holes to the Standard Model

> One project, one machine-checked Lean 4 library, one consistent thesis.
> **Can the mathematics of exotic matter — superfluids, topological insulators, fault-tolerant quantum codes — also describe the fundamental forces, the Standard Model's particle content, and the conditions under which gravity and dark physics emerge?**
> Every derivation in this repository is verified end-to-end by the Lean 4 proof assistant. As of the date below: **7,713 theorems across 445 modules, 0 axioms, 0 `sorry`**.

---

## Where to start, depending on who you are

| If you are a… | Start here |
|---|---|
| Physicist scanning for testable predictions | [§1 Analog Hawking radiation](#1--analog-hawking-radiation-the-lab-foothold) (BEC / polariton / graphene Dirac fluid) and [§2 The Standard Model fingerprints](#2--standard-model-fingerprints-anomalies-generations-and-the-16-convergence) |
| Formal-methods researcher | [§7 Verification methodology](#how-the-verification-works) (three-layer Python ↔ Lean ↔ Aristotle, the 14-stage wave pipeline, the no-axiom posture) and [Headline theorems](#headline-theorems) |
| Quantum-computing researcher | [§3 Topological & fault-tolerant quantum computation](#3--topological-and-fault-tolerant-quantum-computation) (Fibonacci density, quantitative Solovay–Kitaev, Clifford+T, gauging-QEC overhead, APM-LDPC, Shor T-counts) |
| Cosmologist / dark-sector physicist | [§5 Dark sector and dark energy](#5--dark-sector-and-dark-energy) (Gibbs–Duhem no-go, three-track dark-energy closure, superfluid-DM merger forecast) |
| Categorical / SymTFT person | [§6 The SymTFT unification](#6--the-symtft-unification-and-where-the-program-might-fit-under-one-umbrella) and [§4 Emergent gravity](#4--emergent-gravity-from-fluid-to-einstein-and-back) |
| Newcomer who wants the whole picture | Read the [Thesis](#the-thesis) and [Three-layer architecture](#the-three-layer-architecture) sections below in order. |

---

## The thesis

The project investigates a single hypothesis and a single counter-hypothesis, and tries to keep them both honest:

- **Constructive side.** A fluid-like substrate (BEC, polariton condensate, graphene Dirac fluid, topological-order phases) hosts an emergent low-energy effective theory whose anomalies, fusion rules, and gravitational sector reproduce Standard-Model + General-Relativity physics — *in the parts of the theory where it can*.
- **NO-GO side.** Where this picture breaks, the project tries to *prove* the breakage rather than ignore it: gauge erasure (no non-Abelian gauge survives the fluid layer), GW170817 falsification of the second-sound-graviton identification at its natural range, the three-track dark-energy unanimous NO-GO, Gibbs–Duhem locking `w_vac = −1`, and others.

Both sides live side by side in the same Lean library. Tracked-hypothesis `Prop`s carry the conditional / research-grade claims explicitly at the type-signature level, so consumers always see what's being assumed.

---

## The three-layer architecture

```
  Layer 1 — Laboratory platforms                                BEC / polariton / graphene Dirac fluid
            (where the substrate physics is or can be measured)        + Fermi–Hubbard dimer quantum gate

  Layer 2 — Formal substrate                                    Schwinger–Keldysh EFT, acoustic Hawking,
            (the verified mathematical machinery)               anomaly classification (Z₁₆), quantum groups,
                                                                 modular tensor categories, verified statistics,
                                                                 SymTFT audit substrate, LDP linear response

  Layer 3 — Emergent-physics targets                            Standard Model particle content,
            (what Layer 2 is alleged to produce)                three generations, chirality wall + escape,
                                                                 ADW emergent gravity, GW propagation,
                                                                 BH entropy + four laws, dark sector,
                                                                 fault-tolerant quantum computation
```

Predictive scope sits cleanly inside the SM + GR sector under tested mechanisms. The dark-energy sector is **explicitly out of scope under tested mechanisms** — see [`docs/ARCHITECTURE_SCOPE.md`](docs/ARCHITECTURE_SCOPE.md) for the boundary statement and the Phase 5y / 6m closure verdict.

---

# Results by domain

The next eight sections summarize the kernel-verified results, organized by physics question rather than by phase. Each section carries (a) what's been proven, (b) what's been ruled out, and (c) what's conditional — the project's three modes of progress.

## §1 — Analog Hawking radiation: the lab foothold

When a fluid flows faster than its own speed of sound, it creates a "sonic horizon" — a point of no return for sound waves, analogous to a black hole's event horizon for light. Hawking's 1974 prediction implies sonic horizons radiate phonons, and this has been observed in Bose-Einstein condensates.

**Proven (kernel-verified).**
- First corrections to acoustic Hawking radiation from dissipation (real fluids have viscosity), at orders 1, 2, and 3 in the Schwinger–Keldysh EFT, with the **exact WKB connection formula** through the dispersive horizon.
- Three experimental platforms formalized as the same Lean theorem instantiated on three substrates: BEC, polariton condensate, and **bilayer graphene Dirac fluid** (the Dean group's 2025 electronic sonic horizon, predicted `T_H ≈ 2.4 K` — nine orders above BEC). The 3×3 Dirac-fluid acoustic metric block-diagonalizes for quasi-1D flow, reusing ~92 % of the BEC WKB machinery via `diracFluidMetric_txBlock_lorentzian_at_horizon`.
- **Drude–Kadanoff–Martin transport bootstrap** (Phase 6q) on the SK-EFT-Hawking horizon: a bimodal result — *positive uniqueness on graphene* (and polariton, after the Phase 6v.3 occupancy-bound resolution) plus a *sharpened NO-GO* on super-factorial-unbounded substrates such as BEC Bogoliubov continuum-bosonic systems. Both outcomes ship as theorems on substrate-distinguishing witnesses (`DKMBootstrap/HorizonTransportBootstrap.lean`, `BECBogoliubovBosonicGrowth.lean`).

**Experimental hook.** Polariton condensates run ~10 billion times hotter than BEC systems; a Paris group has already observed negative-energy partner modes, and detection of spontaneous Hawking radiation is plausible within 1–2 years. The Penn TMD nanocavity platform was demarcated *out* of the Tier-1 perturbative-dissipation patch by Phase 6v.4 (ratio `Γ_LP/κ ≈ 39 ≫ 0.1`), sharpening the platform map.

## §2 — Standard-Model fingerprints: anomalies, generations, and the "16 convergence"

The Standard Model has three copies of its fundamental particles, sixteen Weyl components per generation, and a modular invariance condition that meets number theory through the Dedekind eta function. The project formally derives the constraints that link these.

**Proven.**
- **Number of generations is a multiple of three** (`generation_constraint_iff`). Each generation contributes 8 to the chiral central charge `c₋ = 8 N_f`; modular invariance forces `24 ∣ c₋`; therefore `3 ∣ N_f`. First formally verified anomaly constraint in particle physics.
- **The "16 convergence."** The number 16 in four otherwise-unrelated areas — Weyl components per generation, the Z₁₆ anomaly group, Rokhlin's theorem on 4-manifold signatures, Kitaev's period-16 topological-superconductor table — is **one** 16, rooted in the quaternionic structure of 4D spinors. The proof reveals a sharp algebra-vs-topology boundary: pure algebra (E₈ lattice, verified using Mathlib's Cartan matrix) only forces divisibility by 8; the jump 8 → 16 requires smooth topology.
- **Right-handed neutrinos** are forced for mathematical consistency: without them, `c₋ = 15/2` per generation, making it fractional, which is a gravitational anomaly independent of mass-based arguments (`wang_bridge_full_chain`).
- **Ext computations.** First machine-checked `Ext^n_{A(1)}(F₂, F₂)` computation over any Steenrod sub-algebra (Phase 5q); first change-of-rings discharge of `Ext_A ≅ Ext_{A(1)}` (Phase 5r).
- **The chirality wall and its escape.** Five of the nine Golterman–Shamir no-go conditions are violated by the 2026 Thorngren–Preskill–Fidkowski (TPF) lattice construction, so the no-go's conclusion (chirality forbidden) does not follow. A three-pillar master synthesis combines GS evasion, the Gu–Wen–Thorngren positive construction with `[H, Q_A] = 0`, and the Z₁₆ anomaly anchor (`pillar1_tpf_escapes + pillar2_chiral_symmetry_exists + pillar3_z16_strengthens`).

**Conditional.** The 3+1D / 4+1D TPF gapped-interface conjecture is shipped as a tracked `Prop` (`TPFConjecture`) with proven 1+1D and 2+1D analogs in two independent frameworks. Consumers carry the dependency at the type signature.

## §3 — Topological and fault-tolerant quantum computation

Universal quantum computation can be performed by braiding non-Abelian anyons, and at the hardware level by compiling onto a fault-tolerant universal gate set (Clifford + T, Clifford + CCZ, etc.). The project formalizes both layers and the bridge between them.

**The topological layer (proven).**
- **First quantum group `U_q(sl₂)` and first Hopf-algebra non-trivial instance in any proof assistant** (Phases 5b–5d), extended to **`U_q(sl₃)` and `SU(3)_k` fusion** as the first rank-2 quantum group formalization (Phase 5i), then to a parameterized `QuantumGroup k A` typeclass over arbitrary Cartan matrices plus the Kac–Walton fusion algorithm (Phase 5m).
- **First complete braided modular tensor category (Ising)**, including F-symbols, pentagon and hexagon equations, ribbon structure, and the first formally verified knot invariants `trefoil = −1` and figure-eight (Phase 5e–5f). First Temperley–Lieb, first Jones–Wenzl idempotents, first end-to-end WRT TQFT pipeline (Phase 5k), first Müger center and dual-closure (Phase 5p).
- **First kernel-verified unconditional Fibonacci-anyon density** (`fibonacci_density_F21_unconditional`, Phase 5 Step 13, 2026-05-22): the two-strand Fibonacci-anyon braid representation embedded into `SU(2)` has dense image. Discharged via a Cartan-v4 Inverse Function Theorem 3-direction composition through `↥𝔰𝔲(2)`. Standard kernel only.
- **First Fermi-point → emergent-gauge-group formalization** (`|N|=1 → U(1)`, `|N|=2 → SU(2)`, Phase 5j) and **first 2+1D Fidkowski–Kitaev Cayley-calibrated gapped-interface construction** (Phase 5s).

**The compiler layer (proven).**
- **First kernel-verified quantitative Solovay–Kitaev length bound in any proof assistant** (`solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight`, Phase 6t, 2026-05-23). A constructive Dawson–Nielsen compiler achieves `‖ρ(compile U ε) − U‖ ≤ ε` with length `≤ skLengthConst · (log(1/ε))^{log 5 / log(3/2)}`, both bundled at the same compile level. UNCONDITIONAL for `ε ∈ (0, ε₀]`.
- **Generic-alphabet substrate** (Phase 6u). The Fibonacci ship is reframed as the *first instance* of a parametric substrate, `GeneratingSet`, that takes any generating subset of `SU(2)` with proven closure-density and an ε₀-net witness and mechanically produces the same bundled-strict quantitative compilation theorem. The substrate is validated by a second instance: **Clifford + T** (`CliffordT*.lean`), discharged UNCONDITIONAL via a Niven-based closure-density witness.

**The fault-tolerance layer (proven; the new D6 bundle).**

Phase 6v lifts four 2025–2026 FT-QC-frontier results into a unified kernel-verified substrate and creates the **15th publication-bundle target, D6 — "Formally Verified Fault-Tolerant Quantum Computation Substrate"**:

- **Williamson–Yoder gauging-QEC overhead bound** (`FaultTolerance/GaugingQEC.lean`): auxiliary-qubit count `W · polylog(W)` for logical-operator measurement of weight `W`. The substantive falsifier `quadraticOverhead_not_linear` proves the polylog factor is unavoidable for any scheme that includes the W² baseline — making this a genuine class-separation, not a constant-factor improvement.
- **Shor ECC-256 T-gate-count upper bound** (`FaultTolerance/ShorTGateCount.lean`): 630 M T-gates (1200-qubit config) or 490 M (1450-qubit config), combining Babbush–Gidney 2026 with the Bravyi–Kitaev exact 7-factor decomposition. Both fit inside the natural 1 G T-gate FT-QC envelope with 370 M / 510 M headroom.
- **APM-LDPC rate substrate + Shannon-capacity hashing-bound predicate** (`FaultTolerance/APMLdpcHashingBound.lean`): the QuEra/Harvard/MIT `[[1152, 580, ≤12]]` code's rate `> 1/2`, non-vacuously witnessed against the rate-exactly-1/2 `[[2k, k]]` falsifier class at the representative Komoto–Kasai 53/100 threshold.
- **W-state QFT in `Q(ζ_N)`** (`FaultTolerance/WStateQFT.lean`): exponential-vs-polynomial separation between the n-element `Z_n` cyclic-shift basis and the full `2^n` Hilbert basis, witnessed at the project's existing cyclotomic sizes `n ∈ {5, 8, 40}`.
- **AGP threshold theorem** (`FaultTolerance/AGP/Threshold.lean`): logical-error suppression at every fault-tolerant level under the Aharonov–Ben-Or AGP rate (`agp_threshold_steane_strict`).
- **NbRe noncentrosymmetric triplet superconductor** (Phase 6v Wave 6v.8 + 6v.9): the Fu–Kane / Sato–Fujimoto TRIM-product Pfaffian `Z₂` invariant places NbRe in the same Rokhlin period-16 structure that anchors the SM `Z₁₆` anomaly classification, with general-n `Matrix.pfaffian` substrate and a load-bearing orthorhombic-lattice-constant derivation.

**Auxiliary.**
- **First formally verified symmetry-protected two-qubit gate** (Phase 5t): the Fermi–Hubbard doublon picks up a purely geometric `−1` holonomy on a π-sweep with vanishing dynamical phase — complementary to topological-anyon protection (`dark_state_dynamical_phase_vanishes + geometric_phase_minus_one_on_pi_loop`).
- **First verified statistical estimators in any proof assistant** (Phase 5c): jackknife variance + autocorrelation, including `jackknifeVariance_nonneg`. Opens the path to verified Monte Carlo data-analysis pipelines for lattice QFT.

## §4 — Emergent gravity: from fluid to Einstein, and back

The project investigates whether gravity arises emergently from a condensed-matter-like substrate, and proves where this works, where it doesn't, and against which observations.

**What works (proven, conditional, or partial).**
- **Linearized Einstein equations from ADW microscopic theory** (Phase 6a Track A). Linearized Einstein tensor in de Donder gauge `G^(1)_μν(k) = −(1/2) k² h̄_μν`; the Sakharov–Adler closed form `G_N = 12π/(N_f Λ²)` tied to the existing ADW critical coupling `G_c = 8π²/(N_f Λ²)` via `G_N^Sakharov = (3/2π)·G_c`; the emergent Newton constant `G_N^emerg = α_ADW · G_N^Sakharov`. At the natural Planck anchor, the match `G_N^emerg = G_N^obs` reduces to `α_ADW · 12π = N_f`, giving `α_ADW* ∈ [0.40, 1.27]` for SM `N_f ∈ {15, 16, 45, 48}` — comfortably inside the Vergeles natural range. `FLRWDynamics.lean` ships the ODE reduction with Friedmann I/II and Bianchi consistency.
- **Bekenstein–Hawking entropy from MTC state counting** (Phase 6a Track C Wave 3). The `−3/2 log(A/(4 G_N))` coefficient decomposes as `(−1/2)` (Gaussian saddle) + `(−1)` (SU(2) singlet projection). The Sen 2013 heat-kernel disagreement with Kaul–Majumdar (`c_log = +(212/45 − 3) ≈ +1.71` for 4D Schwarzschild) is shipped as an explicit non-universality witness.
- **BCH four laws + regime partition** for emergent-gravity ADW black holes (Phase 6a Track C Wave 5). A decidable `Regime` classifier (Schwarzschild | Boundary | ADW-extremality), two `FourLaws_*` Prop bundles with opposite heat-capacity signs, the Schottky-saturation `T_H` form, and a `H_RegimePartition` tracked Prop parameterized by *externally-supplied* slope and δ (explicit ∃-absorption avoidance).
- **Heat-kernel calibration + higher-curvature structure** (Phase 6e). Closed-form Stelle (α, β, γ) at order a₄ in `N_f` and `Λ_UV`. Multi-channel PPN bookkeeping inside Solar-System bounds. The cosmological constant appears *emergent* (a₀-driven, not a UV input). Einstein–Cartan extension discharges Kostelecky / Hughes–Drever Lorentz-violation bounds.
- **Classical-GR algebraic backbone** (Phase 6f). To our knowledge the first formalization in any proof assistant of the algebraic Riemann tensor (with all its symmetries), Ricci and Einstein tensors, the four classical energy conditions (with conditional implications), exact-solutions catalog (Minkowski / dS / AdS / Schwarzschild), the Λ-vacuum biconditional, ADM 3+1 decomposition (Hamiltonian + momentum constraints), and Cartan's tetrad structure equations.
- **Causal structure, singularities, no-hair** (Phase 6g). Wald §8.1 chronology / strong-causality / global-hyperbolicity axioms; Penrose singularity hypothesis bundle; Riccati focusing equation; Hawking–Penrose SEC variant; Schwarzschild-specific monotone-mass area theorem; conditional Kerr no-hair with sub-extremality `J² ≤ M⁴` as a Prop hypothesis.

**What's been ruled out (load-bearing NO-GOs).**
- **Fracton hydrodynamics ⇏ general relativity** (`dof_mismatch_4d + bootstrap_gap_order_2 + fracton_fails_diffeo`). Fracton models reproduce weak-field gravity at order 1 but disagree from order 2 onward; structural DoF mismatch (4 vs 2 in 4D) and diffeomorphism-invariance failure.
- **GW170817 falsification of the vestigial-second-sound graviton identification** (`vestigial_natural_range_violates_ligo`). Under the Volovik proposal, the natural susceptibility range `χ_vest ∈ [0.1, 10]` gives `Δc/c ∈ [−0.68, +2.16]`, exceeding the GW170817 cap of `~3 × 10⁻¹⁵` by a factor of `~7 × 10¹⁴`. Both endpoints are proved as falsifier theorems. The H1 caveat — that the second-sound mode is not derived as a propagating degree of freedom — is encoded as a tracked Prop `H_VestigialModeIsGraviton`.
- **Gauge erasure** (`gauge_erasure + su2_erased + su3_erased + u1_survives`). Non-Abelian SU(2) and SU(3) symmetries cannot survive passage through a fluid-like layer; only U(1) is preserved. (The non-Abelian forces must therefore enter Layer 3 *from* topological order, via the §3 quantum-group / fusion-category route.)

## §5 — Dark sector and dark energy

The project takes the architecture's predictive scope seriously and asks where it does and doesn't reach.

**Predictive (proven dark-sector connections).**
- **`Z₁₆`-anomaly-driven hidden-sector classification.** Enumerates SM-singlet Weyl configurations; the T-0 TQFT candidate is invisible to all planned direct-detection experiments (`HiddenSectorClassification.lean`, `HiddenSectorMixedCharge.lean`).
- **Superfluid-dark-matter cluster-merger forecast** (`SFDMMergerForecast.lean`). Predicts a sonic-boom step function in κ-profiles at the galaxy-cluster Mach transition; stacking ≥ 30 mergers with Euclid × Roman reaches 3.5–5.7σ, with first 3σ detectable around 2028.
- **Fracton dark matter machine-checked viable** in a p-wave dipole superfluid phase at MeV–TeV scales (`FractonDarkMatter.lean`).
- **Fang–Gu torsion DM kinematically excluded** at CDM level (`FangGuTorsionDM.lean`).
- **Empirical-hook ranking** pinned to Lean-decidable ground: cluster mergers > direct detection (`DarkSectorSynthesis.lean`).

**Ruled out (NO-GO closures).**
- **Gibbs–Duhem emergent-vacuum no-go** (`wVac_eq_neg_one_of_rhoV_ne_zero`). Any single-scalar self-tuning emergent-vacuum framework with Gibbs–Duhem equilibrium locks `w_vac = −1` (or `ρ_vac = 0`) by Lorentz invariance, realization-independently. First machine-checked emergent-vacuum obstruction.
- **Closed-form vestigial-gravity EOS** `w_vest(τ) = (1 − τ²)/(5τ² − 1)` (`VestigialEOS.lean`).
- **Three-track dark-energy unanimous NO-GO closure** (Phase 6m). Track A (causal-set DE) yields three NO-GO theorems + three structural caveats. Track B (entropic-gravity DE) yields an **8-of-8 unanimous NO-GO** across the Verlinde / Tsallis / Barrow / Padmanabhan / Cai–Kim / Easson–Frampton–Smoot / Komatsu–Kimura / Odintsov mechanism family — the first complete-mechanism-family unanimous NO-GO closure for dark energy in the literature, with 3-of-8 Bayes-decisive at Jeffreys `≳ 5`. Track C (Jacobson-thermo-GR DE) yields five R5-survivor mechanisms with the strongest CLEARED-R5 at Plaza–Kraiselburd `ΔAIC ≃ ΔBIC ≳ 20`.
- **Architectural scope verdict.** Layer 3 cleanly covers SM + GR. The dark-energy sector is **outside the tested predictive scope under the Volovik-family mechanisms** — see [`docs/ARCHITECTURE_SCOPE.md`](docs/ARCHITECTURE_SCOPE.md).

## §6 — The SymTFT unification, and where the program might fit under one umbrella

Phase 6r promotes the project's substrate-level audit to a substantive Symmetry-Topological-Field-Theory formalization, connecting the substrate physics of §1–§5 to a single bulk: a Symmetry TFT in one higher dimension whose topological boundaries correspond to symmetry-charged matter on the physical side. Phase 6r-prime substantively discharges 11 of the 12 tracked `Prop`s that the predicate-substrate ship introduced.

**Proven (kernel-verified).**
- **First formalization of `Ω_4^{Pin⁺}(pt) ≅ ℤ/16` in Lean 4** (the underlying topological-bordism mathematics due to Kirby–Taylor 1990). The Pin⁺ manifold structure on RP⁴ is fully formalized with `IsManifold (𝓡 4) ω RP4` (Phase 6r-prime Session 3), via a chart-transition decomposition over the antipodal-disjoint cover.
- **Drinfeld center via DMNO 2010 Witt-equivalence** with `FreeKLinearCategory` carrying monoidal / braided / `MonoidalPreadditive` / `Linear` structure; the Deligne tensor as a quotient with all coherence laws; `PseudoUnitary` predicate at restricted-form layer with a strict refinement that breaks the trivial-witness equivalence and exposes genuine DMNO Theorem 5.2 content (Phase 6n + Phase 6r).
- **Anderson-dual `TP_5(Pin⁺) ≅ ℤ/16`** via the substantive Pontryagin chain `TP5PinPlus := AddChar (ZMod 16) Circle` + `circleEquivComplex.trans zmodAddEquiv.symm` (Phase 6r-prime W1.4).
- **Vacuum + electric Lagrangian algebra on `Center (VecG_Cat k G2)`** via `Center.ofBraided.Monoidal` (Phase 6r-prime Session 5). First object-level Z₂ fusion-rule lemma `e ⊗ e ≅ 𝟙` in the Drinfeld center, with the half-braiding-equality discharged via a 5-step associator-naturality + braiding-naturality + signEndo-square chain.
- **APS-η partition by substrate** (Phase 6o): parity-symmetric BEC and ADW substrates give `η = 0`; ³He-A gives a non-zero APS-η, distinguishing the substrates at the index-theory level.
- **Soft theorems and classical double-copy on analog backgrounds** (Phase 6o). Boostless / Carrollian soft theorems formalized on BEC, ADW, and polariton; **first explicit classical Kerr-Schild double-copy on an analog-gravity substrate** in the literature, on a Petrov-type-D acoustic metric.

**Conditional.** Two of the original twelve Phase 6r tracked `Prop`s remain in *KEEP* posture as genuinely research-grade conjectures: `IsKirbyTaylorPinPlusBordism` (full geometric ISO needs Stiefel–Whitney + Pin reductions absent in Mathlib v4.29.1) and `IsDMNOBiconditional` (forward direction Witt-trivial → has Lagrangian algebra needs MTC typeclass + Lagrangian-algebra construction infrastructure that does not yet exist). Both are scheduled for upstream Mathlib contributions in Phase 7+.

## §7 — Verified statistics and mathematical substrate

The project carries its own foundational substrate so that the rest of the library doesn't accumulate hidden assumptions.

- **First verified jackknife + autocorrelation estimators in any proof assistant** (Phase 5c). Cauchy–Schwarz, effective sample size, `jackknifeVariance_nonneg`. Enables verified data analysis for lattice QFT Monte Carlo.
- **Glorioso–Liu axiomatic skeleton for SK-EFT** reframed (Phase 6n) so that `FirstOrderKMS` is a first-order projection of the full axiom set, not a competing axiomatization.
- **Perarnau-Llobet quantum-Crooks NO-GO** including the ℂ-form higher-dimensional no-go.
- **LDP linear-response framework** (Phase 6n / 6o). Lifts the `W`-form Gallavotti–Cohen identity to an abstract `IsLDPRateFunction` typeclass; consumed by the Itô-calculus stochastic-calculus track (the I3 publication target "Verified Stochastic Calculus for Mathlib4").
- **Sakharov ↔ horizon-Crooks unification** at the horizon temperature `β_H`, bridging emergent-gravity substrate physics to the quantum-Crooks NO-GO architecture.
- **Itô calculus + `LDPCompatibleSKEFT` typeclass** as the substrate for I3.

## §8 — At the frontier (where the live work is)

Two phases are scoped and active or imminent:

- **Phase 6w — Classical simulability & quantum advantage in analog Hawking** (tensor-network substrate). When do belief-propagation TN methods (Tindall–Sels, *Science* 392, 868, 2026) and Chebyshev TN methods (Aalto's quasicrystal Chern-mosaic work, PRL April 2026) *classically simulate* analog-Hawking observables, and by contrapositive — when does a quantum processor genuinely have an advantage? Deliverables span new substrate (BP on factor graphs, Chebyshev TN contraction, aperiodic-lattice formalization) and headline theorems (LDP-controlled BP convergence, categorical-Chern ↔ real-space-Chern bridge, combined quantum-advantage demarcation). **Starting today (2026-05-26) in parallel with this README update.**
- **Phase 6x — Additional-alphabet quantum-compiler instantiations + Mathlib upstreaming.** Three additional alphabets on the Phase 6u generic substrate (Read–Rezayi `SU(2)_k` for `k ∈ {5, 7}`; Clifford + CCZ; trapped-ion Mølmer–Sørensen + single-qubit), plus three Mathlib upstream-PR-quality lemma extractions (SU(2) Lie-group infrastructure currently sitting inside the FKLW substrate).

The deferred-targets register at [`docs/roadmaps/Phase6_Deferred_Targets.md`](docs/roadmaps/Phase6_Deferred_Targets.md) is the continuously-updated future-work list.

---

# How the verification works

## Three-layer verification

Every claim in this repository sits in one of three layers, all cross-checked:

```
   Python numerics  ───────────  Lean 4 formal proofs  ───────────  Aristotle automated theorem prover
   (numerical evidence,           (kernel-verified statements,        (fills `sorry` gaps; 322 theorems
    Monte Carlo simulation,        the substrate's source of truth)    proved across 44 runs)
    figure generation)
```

`src/core/formulas.py` is the **canonical home for physics formulas**; every formula references its Lean theorem and Aristotle run ID. `src/core/constants.py` is the canonical home for physical constants, experimental parameters, the Aristotle registry, and axiom-eliminability metadata. `src/core/visualizations.py` is the canonical home for figures (156 functions, Plotly only).

## The 14-stage wave pipeline

All substantive work follows [`docs/WAVE_EXECUTION_PIPELINE.md`](docs/WAVE_EXECUTION_PIPELINE.md) — a 14-stage process with explicit gates between deep-research dispatch, Lean substrate ship, Python integration, figure generation, paper drafting, adversarial review (Stage 9 / 10 / 13), and bundle absorption. No stage skipping.

## The no-axiom posture

The project's posture is that **axioms are temporary scaffolding, not permanent commitments** (Pipeline Invariant #15). As of 2026-05-26, the project carries **0 project-local axioms** — the prior `gaussianSaddleAsymptotic` was retired in Phase 6a Wave 7 via a project-local `LaplaceMethod.lean` derivation, and the prior `gapped_interface_axiom` was converted to the tracked `Prop` `TPFConjecture` on 2026-05-19 (Phase 5h Wave 2).

**Tracked-hypothesis `Prop`s** are the *constructive* alternative to axioms: load-bearing research-grade physical assumptions are carried as explicit `Prop` hypotheses on consumer theorems rather than as global axioms, making the project's claim surface visible at the type-signature level. The current ledger (synced 2026-05-26, see [`docs/PERMANENT_TRACKED_HYPOTHESES.md`](docs/PERMANENT_TRACKED_HYPOTHESES.md)):

| Prop | Posture | Reason |
|---|---|---|
| `H_VestigialModeIsGraviton` | KEEP | Volovik 2024 second-sound graviton bridge is research-grade |
| `H_DESICompatibility` | DISCHARGE in Phase 6b.2 | Derivable from ADW perturbation theory; future work |
| `H_RT_Formula_Valid` | KEEP | Project-scope boundary |
| `TPFConjecture` | KEEP | Open at the literature frontier in 3+1D / 4+1D |
| `IsKirbyTaylorPinPlusBordism` | KEEP | Geometric Kirby–Taylor ISO needs Mathlib infrastructure not yet present |
| `IsDMNOBiconditional` | KEEP | DMNO 2010 main theorem; needs MTC + Lagrangian-algebra infra absent in Mathlib |
| `SolovayKitaevQuantitativeContract` | DISCHARGED at tight ε; Mathlib-PR-quality K-margin tightening upstream | Phase 6t Path A Option C shipped UNCONDITIONAL for `ε ∈ (0, ε₀]` |

The Phase 6r SymTFT predicate-substrate originally introduced 12 tracked `Prop`s; the Phase 6r-prime substantive-discharge phase reduced the **honest legitimate count to 2** (the two listed above as KEEP under `Is…`), via A1–A4 audit remediation (5 P5/P2 anti-pattern deletions, 1 reclassification to substantive definition, 3 restructurings to substantive content via Pontryagin / Drinfeld biproduct / hidden-sector witness ships).

---

# Publication architecture (Phase 7 bundle layout)

Beginning Phase 6i Wave 7, external communication is organized as **15 publication targets**: one Tier-0 flagship review, six Tier-1 themed deep papers, three Tier-2 PRL-style headline letters, three Tier-3 infrastructure papers, and two Tier-4 experimental letters. The new D6 bundle ("Formally Verified Fault-Tolerant Quantum Computation Substrate", sibling to D4) was created by Phase 6v Wave 6v.1.

| Tier | Target | Title (working) | Stage-13 verdict |
|:---:|:---:|---|:---:|
| 0 | **F** | Flagship review | 🔴 RED (open Stage-13 findings) |
| 1 | **D1** | Themed deep paper | 🟢 GREEN |
| 1 | **D2** | Themed deep paper | 🟢 GREEN |
| 1 | **D3** | Themed deep paper | 🔴 RED |
| 1 | **D4** | TQC foundations | 🟢 GREEN (closed 2026-05-23) |
| 1 | **D5** | NO-GO landscape | 🔴 RED |
| 1 | **D6** | Formally Verified Fault-Tolerant Quantum Computation Substrate | 🟢 GREEN (skeleton; Phase 6v close 2026-05-26) |
| 2 | **L1, L2, L3** | PRL-style headline letters | 🟢 GREEN |
| 3 | **I1, I2** | Infrastructure papers | 🟢 GREEN |
| 3 | **I3** | Verified Stochastic Calculus for Mathlib4 | 🟢 GREEN |
| 4 | **E1** | Experimental letter | 🟢 GREEN |
| 4 | **E2** | Experimental letter | 🟢 GREEN |

The 42 per-wave drafts in `papers/paperN_*/` remain as historical / source material; external communication routes through the bundles. Current bundle readiness: [`docs/BUNDLE_READINESS_HEATMAP.md`](docs/BUNDLE_READINESS_HEATMAP.md). The frozen 14-step lift procedure: [`docs/BUNDLE_LIFT_PROCEDURE.md`](docs/BUNDLE_LIFT_PROCEDURE.md). The protocol for absorbing late Phase-6 waves into already-drafted bundles: [`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`](docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md).

---

# Formalization at a glance

**Headline counts** (canonical source: [`docs/counts.json`](docs/counts.json), regenerated by `scripts/update_counts.py`):

- **7,713 Lean 4 theorems** (7,688 substantive + 25 placeholder) across **445 modules** (470 `.lean` files on disk after Phase 6v close).
- **0 axioms project-wide.**
- **0 `sorry` project-wide.**
- **322 Aristotle-proved theorems across 44 runs.**
- **131 Python modules, 4,220 pytest cases across 101 test files, 89 Jupyter notebooks, 156 figures.**
- Lean 4.29.1, Mathlib commit `5e932f97` (v4.29.1 tag, 2026-04-17). Lean REPL pinned at v4.29.0.

## Library architecture

The Lean library is organized into nine functional areas. The per-module map is in [`SK_EFT_Hawking_Inventory_Index.md`](SK_EFT_Hawking_Inventory_Index.md).

- **Acoustic-Hawking foundation** — acoustic metric, SK doubling, universality, exact WKB connection formula, second- and third-order SK-EFT, CGL FDR derivation, dispersive corrections, DKM transport bootstrap.
- **Emergent gauge fields and chirality** — gauge erasure, Fermi-point topological charge → emergent U(1)/SU(2), chirality wall and TPF evasion, three-pillar master synthesis.
- **Anomaly classification and modular invariance** — Z₁₆ classification, Steenrod A(1) algebra, the SM Z₁₆ anomaly computation, modular-invariance generation constraint.
- **Quantum groups, Hopf algebras, fusion categories** — `U_q(sl₂)`, `U_q(sl₃)` and `SU(3)_k`, parameterized `QuantumGroup k A`, Kac–Walton algorithm, restricted quantum groups.
- **Modular tensor categories, braiding, TQFT** — Ising and Fibonacci MTC, pentagon/hexagon, ribbon, RT knot invariants, TQFT partition functions, WRT via surgery, Temperley–Lieb, Jones–Wenzl, Müger center, Frobenius–Perron, dual-closure, string-net.
- **Topological + fault-tolerant quantum computation** — Ising / Fibonacci anyon gates and universality, FKLW density, Phase 6t quantitative SK compiler (Fibonacci), Phase 6u generic-alphabet substrate + Clifford+T instance, Fermi–Hubbard doublon geometric SWAP, Phase 6v D6 FT-QC substrate (Williamson–Yoder gauging-QEC, APM-LDPC hashing, Shor T-counts, W-state QFT, AGP threshold, NbRe triplet SC).
- **Emergent gravity** — ADW gap equation, fracton hydrodynamics + GR obstruction, vestigial gravity + GW170817 falsification, linearized EFE, FLRW, BH entropy, BCH four laws, heat-kernel calibration, classical-GR algebraic backbone, causal structure, singularities, no-hair, three-track dark-energy closure.
- **SymTFT, substrate-bulk correspondence, Drinfeld center** — Phase 6r SymTFT formalization, Phase 6r-prime substantive discharge: Pin⁺ bordism + RP4 manifold, Anderson dual via Pontryagin, Lagrangian algebra on Center, APS-η partition, SM-matter-as-topological-boundary, Witten–Yonekura inflow.
- **Dark sector** — Z₁₆-anomaly hidden sectors, fracton DM, Fang–Gu torsion DM, SFDM merger forecast, Gibbs–Duhem emergent-vacuum no-go, vestigial-gravity EOS, four-factor obstruction principle, DESI DR2 comparison.
- **Verified statistics and substrate infrastructure** — jackknife + autocorrelation, Glorioso–Liu SK-EFT skeleton, quantum-Crooks no-go, Itô calculus, LDP linear-response, SymTFT audit substrate (Drinfeld center, Deligne tensor, pseudo-unitarity).

## Headline theorems

The following kernel-verified theorems are the load-bearing public claims of the project. Each is closed under the standard Lean kernel `[propext, Classical.choice, Quot.sound]` only and carries 0 `sorry`.

| Theorem | Module | What it says |
|---|---|---|
| `generation_constraint_iff` | `GenerationConstraint.lean` | `3 ∣ N_f ↔ 24 ∣ 8 N_f` — first formally verified anomaly constraint on SM particle content. |
| `wang_bridge_full_chain` | `WangBridge.lean` | 16-Weyl spectrum forces `c₋ = 8 N_f`; fractional `c₋` requires right-handed neutrinos. |
| Three-pillar chirality wall | `ChiralityWallMaster.lean` | TPF escapes Golterman–Shamir; GT positive construction realizes `[H, Q_A] = 0`; Z₁₆ anchor. |
| `gauge_erasure + su2_erased + su3_erased + u1_survives` | `GaugeErasure.lean` | Only U(1) survives the fluid layer; SU(2) and SU(3) must enter from topological order. |
| `dof_mismatch_4d + bootstrap_gap_order_2 + fracton_fails_diffeo` | `FractonGravity.lean` | Fracton hydrodynamics ⇏ GR from order 2 onward; structural NO-GO. |
| `wVac_eq_neg_one_of_rhoV_ne_zero + selftuning_two_cases` | `GibbsDuhemTheorem.lean` | Gibbs–Duhem locks single-scalar emergent vacuum to `w_vac = −1` (or `ρ_vac = 0`). |
| `vestigial_natural_range_violates_ligo` | `GravitationalWaves.lean` | Vestigial-second-sound graviton identification violates GW170817 by `~7 × 10¹⁴` over its natural range. |
| `G_N_emerg_match_at_planck_anchor` | `LinearizedEFE.lean` | ADW emergent Newton constant matches `G_N^obs` for `α_ADW* ∈ [0.40, 1.27]` at SM `N_f ∈ {15, 16, 45, 48}`. |
| `kaul_majumdar_log_decomposition` | `BHEntropyMicroscopic.lean` | BH entropy `−3/2 log` coefficient = `−1/2` (Gaussian saddle) + `−1` (SU(2) singlet projection). |
| `dark_state_dynamical_phase_vanishes + geometric_phase_minus_one_on_pi_loop` | `FermiHubbardDimer.lean` | First formally verified symmetry-protected (non-topological) two-qubit gate. |
| `diracFluidMetric_txBlock_lorentzian_at_horizon + diracFluid_hawkingTemp_eq_BEC` | `DiracFluidMetric.lean` | Quasi-1D bilayer-graphene sonic horizon reuses the BEC WKB machinery; `T_H ≈ 2.4 K`. |
| `fibonacci_density_F21_unconditional` | `FKLW/SU2BCHBracketClosure.lean` | Fibonacci-anyon two-strand braid representation is dense in SU(2) — first kernel-verified unconditional FKLW density. |
| `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` | `FKLW/SolovayKitaevPathA.lean` | Constructive Dawson–Nielsen compiler: error `ε`, length `polylog(1/ε)` at same compile level; UNCONDITIONAL for `ε ∈ (0, ε₀]`. First kernel-verified quantitative SK in any prover. |
| `solovayKitaev_generic_quantitative + CliffordT instance discharge` | `FKLW/GenericSolovayKitaevQuantitative.lean`, `FKLW/CliffordTQuantitative.lean` | Alphabet-independent SK substrate parameterized by `GeneratingSet`; Clifford+T instance UNCONDITIONAL. |
| Williamson–Yoder gauging-QEC + quadratic-overhead falsifier | `FaultTolerance/GaugingQEC.lean` | Linear-polylog auxiliary-qubit count for logical-operator measurement, class-separated from the W² baseline. |
| APM-LDPC hashing-bound predicate | `FaultTolerance/APMLdpcHashingBound.lean` | QuEra/Harvard/MIT `[[1152, 580]]` rate > 1/2; rate-exactly-1/2 `[[2k,k]]` falsifier class; hashing-bound predicate non-vacuously witnessed. |
| Shor ECC-256 T-gate-count upper bound | `FaultTolerance/ShorTGateCount.lean` | 630 M / 490 M T-gates for 1200 / 1450-qubit configs; both inside 1 G T-gate envelope. First kernel-verified end-to-end. |
| `agp_threshold_steane_strict` | `FaultTolerance/AGP/Threshold.lean` | Logical-error suppression at every fault-tolerant level under Aharonov–Ben-Or rate. |
| `jackknifeVariance_nonneg` | `VerifiedJackknife.lean` | First verified statistical estimator in any proof assistant. |
| Vacuum + electric Lagrangian algebra on Center | `SymTFT/A5VacuumPlusElectric.lean`, `SymTFT/A5LagrangianCenterUnit.lean` | First object-level `e ⊗ e ≅ 𝟙` half-braiding equality in `Center (VecG_Cat k G2)`; Phase 6r-prime W4. |
| Pin⁺ bordism `Ω_4^{Pin⁺}(pt) ≅ ℤ/16` substrate + RP⁴ `IsManifold` | `SymTFT/PinBordism.lean`, `SymTFT/RP4IsManifold.lean` | First Pin⁺ bordism group formalization in Lean 4; full chart-transition discharge on RP⁴. |

---

# Project structure

```
SK_EFT_Hawking/
├── lean/                              # Lean 4 formalization (counts above; canonical in docs/counts.json)
│   ├── lakefile.toml                  # Lake build config (pinned Mathlib 5e932f97, v4.29.1)
│   ├── lean-toolchain                 # Lean 4 v4.29.1
│   ├── SKEFTHawking.lean              # Root module
│   └── SKEFTHawking/                  # 470 .lean files organized into nine functional areas
│       ├── Basic.lean
│       ├── FKLW/                      # Fibonacci density, generic-alphabet SK, Clifford+T
│       ├── FaultTolerance/            # D6 FT-QC substrate (gauging-QEC, APM-LDPC, Shor, W-state, AGP, Steane)
│       ├── SymTFT/                    # Phase 6r SymTFT + Phase 6r-prime substantive discharge
│       ├── APSEta/                    # APS-η partition by substrate (BEC / ADW / He³-A)
│       ├── CrossBridges/              # SM matter as SymTFT topological boundary
│       ├── DKMBootstrap/              # Phase 6q DKM transport bootstrap
│       ├── QuantumCrooks/             # Quantum-Crooks no-go architecture
│       ├── CrooksAnalogHawking/       # Sakharov ↔ horizon-Crooks unification
│       └── …                          # See SK_EFT_Hawking_Inventory_Index.md for the full per-module map
│
├── src/
│   ├── core/                          # Canonical homes: formulas.py, constants.py, visualizations.py,
│   │                                  # aristotle_interface.py, provenance.py, citations.py
│   ├── first_order/ second_order/     # Phase-1/2 SK-EFT analysis
│   ├── gauge_erasure/                 # Non-Abelian gauge erasure theorem
│   ├── wkb/                           # Exact WKB connection formula + Bogoliubov + spectrum + backreaction
│   ├── adw/                           # ADW gap equation + tetrad solver + observables + ginzburg–landau
│   ├── experimental/                  # Platform tables, κ-scaling sweeps, polariton predictions
│   ├── chirality/                     # GS conditions vs TPF evasion
│   ├── vestigial/                     # Vestigial-gravity MC, SU(2) / 4D / Grassmann TRG, HS-RHMC, JAX/Torch
│   ├── fracton/                       # Fracton SK-EFT, information retention, gravity connection, non-Abelian
│   ├── dark_sector/                   # Z₁₆ hidden sector, ADW Λ, fracton DM, SFDM merger forecast, synthesis
│   ├── fermi_hubbard/                 # Fermi–Hubbard dimer (geometric SWAP)
│   └── graphene/                      # Bilayer graphene Dirac fluid, T_H predictions, platform comparison
│
├── papers/                            # 42 per-wave drafts + 15 publication bundles
│   ├── F/                             # Tier 0 flagship review
│   ├── D1/ D2/ D3/ D4/ D5/ D6/        # Tier 1 deep papers (D6 added 2026-05-26 by Phase 6v Wave 6v.1)
│   ├── L1/ L2/ L3/                    # Tier 2 PRL-style headline letters
│   ├── I1/ I2/ I3/                    # Tier 3 infrastructure papers (I3 = Verified Stochastic Calculus for Mathlib4)
│   ├── E1/ E2/                        # Tier 4 experimental letters
│   ├── paperN_*/                      # 42 per-wave drafts (paper1_first_order through paper45_phase6m_review)
│   └── AutomatedReviews/              # Stage-13 adversarial-reviewer output per paper
│
├── notebooks/                         # 89 Jupyter notebooks: one Technical + one Stakeholder version per wave
│
├── docker/                            # docker-compose.graph.yml — PG + AGE knowledge-graph container (port 5433)
│
├── docs/
│   ├── WAVE_EXECUTION_PIPELINE.md     # 14-stage process governing all work
│   ├── BUNDLE_LIFT_PROCEDURE.md       # Frozen 14-step bundle-lift procedure
│   ├── LATE_PHASE6_ABSORPTION_PROTOCOL.md  # Frozen Stage A–G protocol for late-wave bundle absorption
│   ├── PAPER_STRATEGY.md              # Canonical 15-bundle architecture
│   ├── PAPER_DRAFT_MAPPING.md         # Per-existing-draft → per-bundle assignment table
│   ├── BUNDLE_READINESS_HEATMAP.md    # Per-bundle Stage-13 readiness summary (auto-regenerated)
│   ├── ARCHITECTURE_SCOPE.md          # Three-layer predictive boundary (Layer 3: SM + GR in scope, DE out)
│   ├── PERMANENT_TRACKED_HYPOTHESES.md  # Tracked-Prop ledger (synced 2026-05-26)
│   ├── KNOWLEDGE_GRAPH.md             # Provenance graph documentation + interactive D3 visualization
│   ├── counts.json / counts.tex       # Single source of truth for counts
│   ├── stakeholder/                   # Per-phase Implications + Strategic_Positioning docs (through Phase 6v)
│   ├── roadmaps/                      # Phase 1 → Phase 6x roadmaps (+ Phase 7 + Phase 7a bundle reframe)
│   ├── aristotle_results/             # All 44 Aristotle run archives (322 theorems proved)
│   └── archive/                       # Superseded artifacts
│
├── tests/                             # 4,220 pytest cases across 101 files; default fast (deselects `slow`)
├── figures/                           # 156 figure functions (PNG + HTML) + provenance_graph.json
└── scripts/                           # validate.py, update_counts.py, submit_to_aristotle.py, build_graph.py,
                                       #   sentence_state.py, verification_state.py, last_modified.py,
                                       #   readiness_gates.py, citation_cache.py, qi_register.py,
                                       #   bundle_readiness.py, provenance_dashboard.py (10-tab Datastar UI), …
```

---

# Quick start

### Python
```bash
cd SK_EFT_Hawking
uv sync                                                # Install dependencies
uv run python -m pytest tests/ -v                       # Fast tests (deselects `slow`; ~2 s)
uv run python -m pytest tests/ -m '' -v                 # Full run (~10 min; required before bundle ship)
uv run python scripts/validate.py                       # ~28 cross-layer validation checks
uv run python scripts/provenance_dashboard.py           # Provenance command center on localhost:8050
```

### Lean
```bash
cd SK_EFT_Hawking/lean
lake build                                              # Library only (per defaultTargets); should be clean (0 sorry)
lake build SKEFTHawking.ExtractDeps                     # Library + ExtractDeps.olean (graph pipeline / validate.py)
# Clean rebuild baseline:
rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps
```

### Interactive Lean (preferred dev loop)
```bash
# .mcp.json at the workspace root auto-loads the lean-lsp MCP server when you launch Claude Code from there.
# Tools: lean_goal, lean_multi_attempt (5× faster in REPL mode), lean_diagnostic_messages, lean_hover_info,
#        lean_file_outline, lean_local_search, lean_verify (axiom check), lean_build (slow — only for new imports)
```

### Aristotle
```bash
uv run python scripts/submit_to_aristotle.py --dry-run                      # Preview sorry gaps
uv run python scripts/submit_to_aristotle.py --submit --priority 1          # Submit by priority batch
uv run python scripts/submit_to_aristotle.py --retrieve <ID> --integrate    # Retrieve and integrate
# Batch plan: docs/references/aristotle_batch_plan.md
# Reference:  docs/references/Theorm_Proving_Aristotle_Lean.md
```

### Provenance knowledge graph
```bash
uv run python scripts/provenance_dashboard.py           # http://localhost:8050
# 10 tabs: Parameters / Formulas / Proof Architecture / Citations / Knowledge Graph /
#          Paper Readiness / Process Health / Research Status / Paper Provenance v2
# See docs/KNOWLEDGE_GRAPH.md for full documentation.
```

---

# Documentation guide

| If you want to… | Start here |
|---|---|
| Understand the physics and results | This README (above) |
| See the big-picture assessment by chain | [`docs/RESEARCH_STATUS_OVERVIEW.md`](docs/RESEARCH_STATUS_OVERVIEW.md) |
| Understand the predictive scope (what's in, what's out) | [`docs/ARCHITECTURE_SCOPE.md`](docs/ARCHITECTURE_SCOPE.md) |
| See what's been built and its status | [`SK_EFT_Hawking_Inventory_Index.md`](SK_EFT_Hawking_Inventory_Index.md) |
| Check the full inventory | [`SK_EFT_Hawking_Inventory.md`](SK_EFT_Hawking_Inventory.md) |
| Understand the execution process | [`docs/WAVE_EXECUTION_PIPELINE.md`](docs/WAVE_EXECUTION_PIPELINE.md) |
| See the bundle architecture and Stage-13 readiness | [`docs/PAPER_STRATEGY.md`](docs/PAPER_STRATEGY.md) + [`docs/BUNDLE_READINESS_HEATMAP.md`](docs/BUNDLE_READINESS_HEATMAP.md) |
| Lift draft content into a bundle | [`docs/BUNDLE_LIFT_PROCEDURE.md`](docs/BUNDLE_LIFT_PROCEDURE.md) |
| Absorb a late wave into an already-drafted bundle | [`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`](docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md) |
| See the tracked-hypothesis ledger | [`docs/PERMANENT_TRACKED_HYPOTHESES.md`](docs/PERMANENT_TRACKED_HYPOTHESES.md) |
| Explore the provenance graph interactively | [`docs/KNOWLEDGE_GRAPH.md`](docs/KNOWLEDGE_GRAPH.md) + `scripts/provenance_dashboard.py` |
| Read non-technical summaries | [`docs/stakeholder/`](docs/stakeholder/) — Implications + Strategic_Positioning pairs (through Phase 6v) |
| See what's next | [`docs/roadmaps/`](docs/roadmaps/) — Phase 1 → 6x (16 Phase-6 sub-roadmaps a through x) + Phase 7 / 7a |
| Read the deep-research corpus | [`Lit-Search/`](../Lit-Search/) — organized Phase-1 through Phase-6w |
| Work with Aristotle | [`docs/references/Theorm_Proving_Aristotle_Lean.md`](docs/references/Theorm_Proving_Aristotle_Lean.md) |
| Read the project's feasibility study | [`docs/Fluid-Based Approach to Fundamental Physics  Feasibility Study.md`](docs/Fluid-Based%20Approach%20to%20Fundamental%20Physics%20%20Feasibility%20Study.md) |
| Read the critical review | [`docs/Fluid-Based Approach to Fundamental Physics- Consolidated Critical Review v3.md`](docs/Fluid-Based%20Approach%20to%20Fundamental%20Physics-%20Consolidated%20Critical%20Review%20v3.md) |

---

# Build environment

- **Lean:** 4.29.1 with Mathlib pinned at commit `5e932f97` (v4.29.1 tag, 2026-04-17). Lean REPL pinned at v4.29.0 (the protocol wrapper used by the `lean-lsp-mcp` interactive dev loop).
- **Python:** ≥ 3.14, managed via `uv`. Key deps: numpy, scipy, sympy, mpmath, plotly, aristotlelib, torch, maturin.
- **Rust:** PyO3 extension for RHMC (`rust/src/lib.rs`). Rebuild with `PYO3_USE_ABI3_FORWARD_COMPATIBILITY=1 uv pip install -e rust/ --force-reinstall --no-deps`.
- **Visualization:** Plotly (not matplotlib). Colorblind-accessible palette: `#2E86AB` steel blue, `#A23B72` berry, `#F18F01` amber.
- **MCP servers:** `lean-lsp` (auto-loaded from `.mcp.json` at the workspace root); approve on first launch.

---

# Key references

**Project documentation:**
- [Wave Execution Pipeline](docs/WAVE_EXECUTION_PIPELINE.md) — the 14-stage process governing all work
- [Inventory Index](SK_EFT_Hawking_Inventory_Index.md) — LLM-friendly quick reference: module map, counts, pipeline invariants
- [Architecture Scope](docs/ARCHITECTURE_SCOPE.md) — Layer-3 predictive boundary (SM + GR in scope, dark-energy sector out under tested mechanisms)
- [Permanent Tracked Hypotheses](docs/PERMANENT_TRACKED_HYPOTHESES.md) — the project's load-bearing tracked `Prop` ledger
- [Knowledge Graph](docs/KNOWLEDGE_GRAPH.md) — interactive provenance visualization
- [Dashboard](docs/DASHBOARD.md) — parameter verification, proof architecture, paper claims

**Roadmaps.** [`docs/roadmaps/`](docs/roadmaps/) contains phase-specific execution plans for **Phase 1 → Phase 6x** (the active Phase-6 series runs `Phase6a_Roadmap.md` through `Phase6x_Roadmap.md`, with per-wave sub-roadmaps under `Phase6v/`, etc.), plus [Phase7_Roadmap.md](docs/roadmaps/Phase7_Roadmap.md) and [Phase7a_Roadmap.md](docs/roadmaps/Phase7a_Roadmap.md) for the bundle-architecture reframe. Forward-looking general targets are tracked in [Phase6_Deferred_Targets.md](docs/roadmaps/Phase6_Deferred_Targets.md).

**Stakeholder docs.** [`docs/stakeholder/`](docs/stakeholder/) contains non-technical Implications and Strategic_Positioning pairs per phase, currently extending through Phase 6v (plus the Phase 5y closure memo and its four cross-phase impact notes). Companion guide at `docs/stakeholder/companion_guide.md`.

**Deep research.** [`Lit-Search/`](../Lit-Search/) is organized by phase (`Phase-1-and-Background` through `Phase-6w`) covering quantum groups, modular tensor categories, Rokhlin's theorem, the ADW gap equation, fracton hydrodynamics and gravity, verified statistics, polariton protocols, TQFT partition functions, gauging obstructions, `SU(3)_k` fusion, Fermi-point topology, chirality wall 3+1D, FK gapped interface, instanton zero-mode counting, graphene Dirac-fluid transport, dark-sector phenomenology, Klinkhamer–Volovik q-theory obstruction analysis, classical-GR backbone, heat-kernel calibration, three-track dark-energy closure, FKLW + quantitative Solovay–Kitaev, generic-alphabet SK + Clifford+T, FT-QC frontier alignment (Williamson–Yoder gauging-QEC, APM-LDPC, Shor ECC-256, W-state QFT, AGP threshold, NbRe triplet SC), DKM transport bootstrap, SymTFT formalization, and Phase 6w tensor-network classical simulability.

---

*Last updated: 2026-05-26 (post Phase 6q strengthening + Phase 6r + Phase 6r-prime + Phase 6u + Phase 6v close; Phase 6w starting in parallel with this update). Counts are a rolling snapshot — [`docs/counts.json`](docs/counts.json) is the single source of truth, regenerated by `scripts/update_counts.py`.*
