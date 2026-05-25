# SK-EFT Hawking — Inventory Index

**Purpose.** LLM-friendly comprehensive index for the SK-EFT Hawking project. **This file is pointers only — no embedded content.** Every entry is `file path + one-line summary`. For full content read the pointed-to file. For comprehensive prose see `SK_EFT_Hawking_Inventory.md`. For live counts read `docs/counts.json`.

**Last synced:** 2026-05-25 (Phase 6q strengthening close). **Sync source:** `docs/counts.json` (generated 2026-05-25T08:12 after strengthening + B.1/B.2/B.3 substantive lifts ship) + live filesystem.

**Size discipline.** Target ~50–80 KB. Keep under 100 KB so future LLM bootstraps can read it in a single `Read` call (the harness truncates files >256 KB and may skip files much smaller than that). When this file approaches 100 KB, prune narrative — move it to `SK_EFT_Hawking_Inventory.md` or `temporary/working-docs/`. Do NOT inline session logs, wave-history, or per-commit detail; those belong in `temporary/working-docs/` or the prose inventory.

**Sibling docs (read on bootstrap):**
- `README.MD` — project framing (public-facing).
- `CLAUDE.md` (workspace) and `CLAUDE.md` (project) — agent guidance and conventions.
- `docs/WAVE_EXECUTION_PIPELINE.md` — 14-stage wave protocol and 15 pipeline invariants.
- `docs/PAPER_STRATEGY.md` — 14-bundle publication architecture.
- `docs/PERMANENT_TRACKED_HYPOTHESES.md` — load-bearing tracked Props.
- `docs/BUNDLE_READINESS_HEATMAP.md` — per-bundle Stage-13 readiness.
- `SK_EFT_Hawking_Inventory.md` — full prose inventory (the upstream this index summarizes).

---

## 1. One-page state snapshot

**Counts (from `docs/counts.json`, generated 2026-05-25T08:12 post Phase 6q strengthening close):**

| Metric | Value |
|---|---:|
| Lean theorems (total) | 7339 |
| Lean theorems (substantive) | 7314 |
| Lean theorems (placeholder `True := trivial`) | 25 |
| Lean modules | 390 |
| Lean total declarations | 13628 |
| Lean definitions | 5553 |
| Lean structures | 257 |
| Lean instances | 391 |
| Lean inductives | 88 |
| Lean axioms | **0** (project-local) |
| Lean sorries | **0** |
| Aristotle-proved theorems | 322 |
| Aristotle runs | 44 |
| Python source modules | 131 |
| Test files | 101 |
| Pytest cases | 4218 |
| Figures (PNG) | 156 |
| Notebooks | 89 |
| Papers (drafts) | 42 |
| Publication bundles (per PAPER_STRATEGY) | 14 |

**Toolchain pins:**
- Lean: `leanprover/lean4:v4.29.1` (`lean/lean-toolchain`).
- Mathlib: rev `5e932f97dd25535344f80f9dd8da3aab83df0fe6` (v4.29.1 tag, 2026-04-17) — `lean/lakefile.toml`.
- Lean REPL: tag `v4.29.0` (must match toolchain) — `lean/lakefile.toml`.
- Python: `>=3.14`, uv-managed (`pyproject.toml`).
- Rust: PyO3 abi3-forward-compat (`rust/`).

**Recent ships (newest first):**
- **2026-05-25** Phase 6q strengthening close + 3 substantive deferred-item lifts SHIPPED — §A 20-item resolution (5 deletions, 3 abbrev demotions, A.6 conjunct cleanup, A.3 substantive companion, A.4/A.7 docstring strengthening) + B.1 Python graphene MIR companion (substantive `(2·β_2/(4π))^(1/3) ≈ 0.0756`; the Lean substrate-level `1/2` placeholder is a safe upper bound) + B.2 reverse-direction LDP biconditional + B.3 BEC Bogoliubov substantive unbounded-norm proof (new module `BECBogoliubovBosonicGrowth.lean` with witnessed concrete `(2κ)!` sequence; both halves of bimodal outcome now witnessed by distinct concrete substrates). All headlines kernel-only; lake build 8638 jobs clean; pytest 4220 total / 4152 default-run / 68 slow-deselected, 0 failures; zero new axioms. See `docs/roadmaps/Phase6q_Roadmap.md` Sessions log Session 2.
- **2026-05-23 PM** Phase 6q DKM transport bootstrap SUBSTANTIVELY CLOSED — all 5 Waves shipped in single autonomous-loop session; 10 new Lean modules under `lean/SKEFTHawking/DKMBootstrap/` (~2,375 LoC Session 1; zero sorries, zero new axioms); bimodal outcome BOTH halves shipped substantively (positive uniqueness on graphene + sharpened NO-GO on super-factorial-unbounded substrates). Bundle placement BOTH L2 + D5. See `temporary/working-docs/phase6q/wave_2c_positioning.md` for full closing positioning.
- **2026-05-23** Phase 6t Path A Option C ship — `SkApproxCSuperQuadraticBound_holds` + unconditional tight-ε strict headline `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` in `lean/SKEFTHawking/FKLW/SolovayKitaevPathA.lean`. Kernel-only. See `docs/PHASE6T_QUANTITATIVE_SK_COMPLETE.md`.
- **2026-05-23** D4 bundle closed at GREEN-with-advisories (Stage 9/10/13 round-2 cycle). 10/14 bundles GREEN. See `docs/BUNDLE_READINESS_HEATMAP.md`.
- **2026-05-22** Phase 5 Step 13 — `fibonacci_density_F21_unconditional` discharged kernel-only in `lean/SKEFTHawking/FKLW/SU2BCHBracketClosure.lean`. See `docs/PHASE5_STEP13_COMPLETE.md`.
- **2026-05-19** Phase 5h Wave 2 — `axiom gapped_interface_axiom` retired into `TPFConjecture` tracked Prop; project axiom count 1 → 0.

**Build state (as of 2026-05-23 PM, post Phase 6q close):**
- `lake build SKEFTHawking` clean (8637 jobs).
- `uv run python -m pytest tests/` clean (4195 cases default fast suite; +slow suite via `-m slow`).
- `uv run python scripts/validate.py` PASS (21 checks).

---

## 2. Public-facing framing pointers

For the public narrative of what the project does, see `README.MD`. Key story arcs:
- **Analog Hawking radiation** — SK-EFT corrections to BEC / polariton / graphene-Dirac-fluid sonic horizons (Bundle D1).
- **Three generations from anomaly + modular invariance** — `c₋ = 8·N_f` and `24 | c₋` force `3 | N_f` (Bundle D2).
- **The "16 convergence"** — SM Weyl count, ℤ₁₆ classification, Rokhlin theorem, Kitaev DIII period all the same 16 (Bundle D2).
- **Chirality wall** — formal analysis of Thorngren-Preskill-Fidkowski's 5-of-9 evasion of Golterman-Shamir (Bundle D2).
- **Emergent gravity from microscopy** — ADW + tetrad gap equation + GW170817 vestigial-graviton falsification (Bundle D3).
- **Topological quantum computation** — Onsager → U_q(sl₂) → Hopf algebra → SU(2)_k → trefoil → Fibonacci universality (Bundle D4).
- **Dark sector under substrate constraints** — Gibbs-Duhem NO-GO for emergent dark energy; SFDM merger forecast; fracton DM viability (Bundle D5).
- **Formally verified statistical estimators + geometric quantum gate** — jackknife variance non-negativity + Fermi-Hubbard doublon SWAP.

---

## 3. Lean module map

378 Lean modules under `lean/SKEFTHawking/`. Grouped by subdirectory or topical family. For full per-module theorem counts + key results, see `SK_EFT_Hawking_Inventory.md` Section 2. For the canonical module-name list, see `docs/counts.json` field `lean.module_names`.

### 3.1 Subdirectory families (sub-packages)

| Subdirectory | Purpose | Pointer |
|---|---|---|
| `lean/SKEFTHawking/FKLW/` | Freedman-Kitaev-Larsen-Wang Fibonacci SU(2) density program (Phase 6p R5.4 + Phase 6t quantitative Solovay-Kitaev). Includes `SolovayKitaevPathA.lean` (2565 LoC, Path A Option C tight-ε ship). | `ls lean/SKEFTHawking/FKLW/` |
| `lean/SKEFTHawking/FaultTolerance/` | Fault-tolerance noise-model substrate. | `ls lean/SKEFTHawking/FaultTolerance/` |
| `lean/SKEFTHawking/CrooksAnalogHawking/` | Sakharov-horizon Crooks bridge; SK-EFT entropy current + Gallavotti-Cohen. | `ls lean/SKEFTHawking/CrooksAnalogHawking/` |
| `lean/SKEFTHawking/GloriosoLiu/` | Glorioso-Liu SK-EFT axiomatic skeleton + Onsager reciprocity + KMS. | `ls lean/SKEFTHawking/GloriosoLiu/` |
| `lean/SKEFTHawking/QuantumCrooks/` | Quantum Crooks no-go (Perarnau-Llobet) + Tasaki / Åberg / Kafri-Deffner / Kirkwood-Dirac variants. | `ls lean/SKEFTHawking/QuantumCrooks/` |
| `lean/SKEFTHawking/SymTFTAudit/` | SymTFT applicability audit + Drinfeld center + Witt-class + free k-linear / Deligne-tensor closure. | `ls lean/SKEFTHawking/SymTFTAudit/` |
| `lean/SKEFTHawking/LDP/` | Large-deviation framework (Cramér, Sanov, Varadhan, contraction). | `ls lean/SKEFTHawking/LDP/` |
| `lean/SKEFTHawking/Resurgence/` | SK-EFT resurgence + Borel summation + Stokes bound. | `ls lean/SKEFTHawking/Resurgence/` |
| `lean/SKEFTHawking/Itô/` | Stochastic calculus (Itô isometry / lemma / Novikov / quadratic variation / semimartingale). Phase 6o I3 target. | `ls lean/SKEFTHawking/Itô/` |
| `lean/SKEFTHawking/APSEta/` | Atiyah-Patodi-Singer η-invariant for analog horizons. | `ls lean/SKEFTHawking/APSEta/` |
| `lean/SKEFTHawking/Schellekens/` | Schellekens chain (anomaly polynomial, holomorphic VOA c=24, Niemeier lattice, spin bordism). | `ls lean/SKEFTHawking/Schellekens/` |
| `lean/SKEFTHawking/DoubleCopy/` | Gauge-theory ⇄ gravity scattering double-copy (BCJ, Petrov-D, single-copy, Weyl spinor). | `ls lean/SKEFTHawking/DoubleCopy/` |
| `lean/SKEFTHawking/SoftTheorems/` | Boostless / Carrollian cosmological soft theorems; dissipative no-go; noise-floor prediction. | `ls lean/SKEFTHawking/SoftTheorems/` |
| `lean/SKEFTHawking/ETH/` | Eigenstate thermalization hypothesis refutation on horizon-MTC substrate. | `ls lean/SKEFTHawking/ETH/` |
| `lean/SKEFTHawking/QCyc40/` | Q(ζ₄₀) cyclotomic-field substrate (Phase 6p T-gate compiler). | `ls lean/SKEFTHawking/QCyc40/` |
| `lean/SKEFTHawking/DKMBootstrap/` | Phase 6q DKM transport bootstrap on SK-EFT-Hawking horizon transport (Chowdhury-Hartnoll-Hebbar-Khondaker arXiv:2509.18255 specialization). **11 modules, 2,716 LoC** (Session 1: 10 modules, ~2,375 LoC, 2026-05-23; Session 2: BECBogoliubovBosonicGrowth.lean, 341 LoC, 2026-05-25 strengthening close); zero sorries, zero new axioms. Track 1 (Predicates/AxiomSet/KMSConsistency/NoCrossing/SDPStructure/LinearFunctionals/LDPBridge) builds DKM substrate + resolves three Phase 6o Wave 1c NO-GO obstructions; Track 2 (SKEFTSpecialization/E1E2CrossBridge/HorizonTransportBootstrap) specializes to 3 platforms (graphene/BEC/polariton) with bimodal outcome (positive uniqueness on graphene + sharpened NO-GO on super-factorial-unbounded). Wave 2b.4 module `BECBogoliubovBosonicGrowth.lean` lifts the sharpened-NO-GO half to a witnessed concrete substrate-level stand-in sequence `(2κ)!` (substantive Lieb-Robinson-for-bosons derivation deferred). Python numerical companion at `src/dkm_bootstrap/` ships substantive graphene MIR constant `(2·β_2/(4π))^(1/3) = 0.07562892800257...` (30 dps mpmath). | `ls lean/SKEFTHawking/DKMBootstrap/` |

### 3.2 Topical groupings (top-level `.lean` files)

For each topical area below, modules live directly under `lean/SKEFTHawking/`. Browse via `ls lean/SKEFTHawking/` and `grep "^theorem " lean/SKEFTHawking/<Module>.lean | wc -l` for counts.

- **Hawking pipeline core** — `AcousticMetric.lean`, `WKBAnalysis.lean`, `WKBConnection.lean`, `SKDoubling.lean`, `SecondOrderSK.lean`, `ThirdOrderSK.lean`, `HigherOrderSK.lean`, `CGLTransform.lean`, `HawkingUniversality.lean`, `StimulatedHawking.lean`.
- **Analog platforms** — `PolaritonTier1.lean`, `DiracFluidMetric.lean`, `DiracFluidSK.lean`, `DiracFluidWKB.lean`, `GrapheneHawking.lean`, `GrapheneNoiseFormula.lean`, `QuasiOneDReduction.lean`.
- **ADW emergent gravity** — `ADWMechanism.lean`, `TetradGapEquation.lean`, `TetradFormalism.lean`, `EinsteinCartanExtension.lean`, `LinearizedEFE.lean`, `NonlinearEFE.lean`, `FLRWDynamics.lean`, `EmergentGravityBounds.lean`, `GravitationalWaves.lean`, `EquivalencePrinciple.lean`, `HeatKernelExpansion.lean`, `HigherCurvatureStructure.lean`, `MicroscopicCoefficientMatch.lean`.
- **Classical-GR algebra (Phase 6f)** — `Curvature.lean`, `EinsteinTensor.lean`, `EnergyConditions.lean`, `ExactSolutions.lean`, `ADMFormalism.lean`, `LeviCivita.lean`, `LorentzianMetric.lean`, `LorentzianBundle.lean`, `RiemannianConnection.lean`, `RiemannCoordinate.lean`, `RiemannDifferentialBianchi.lean`, `BundleRiemann.lean`, `BundleRiemannAux.lean`.
- **Singularity / causal structure (Phase 6g)** — `CausalStructure.lean`, `NullGeodesic.lean`, `RaychaudhuriEquation.lean`, `FocalPoint.lean`, `PenroseSingularity.lean`, `PenroseSingularityCurveTheoretic.lean`, `HawkingPenroseSingularity.lean`, `HawkingPenroseSingularityCurveTheoretic.lean`, `AreaTheorem.lean`, `AreaTheoremCurveTheoretic.lean`, `CauchyProblem.lean`, `NoHairTheorem.lean`, `NonlinearDiffInvariance.lean`.
- **Black-hole thermodynamics** — `BHEntropyMicroscopic.lean`, `BHThermodynamicsFourLaws.lean`, `BHLGaugeEmbedding.lean`, `KerrSchild.lean`, `JacobsonThermoGRDarkEnergy.lean`, `RTReplicaTrickOnMTC.lean`, `RTCasiniHuertaBounds.lean`, `CasiniHuertaModularHamiltonianMTC.lean`, `QECHolographyBridge.lean`, `HolographicCFunctionMTC.lean`, `ScramblingTimeQuantitative.lean`.
- **Chirality wall / Z₁₆ / anomaly** — `ChiralityWall.lean`, `ChiralityWallMaster.lean`, `GoltermanShamir.lean`, `TPFEvasion.lean`, `TPFDisentangler.lean`, `SPTClassification.lean`, `SPTStacking.lean`, `Z16Classification.lean`, `Z16AnomalyComputation.lean`, `Z16AnomalyForcesThetaBar.lean`, `GenerationConstraint.lean`, `ModularInvarianceConstraint.lean`, `RokhlinBridge.lean`, `AlgebraicRokhlin.lean`, `WangBridge.lean`, `SpinBordism.lean`, `SteenrodA1.lean`, `A1Ring.lean`, `A1Resolution.lean`, `A1Ext.lean`, `ChangeOfRings.lean`, `ExtBordismBridge.lean`, `SMFermionData.lean`, `SMGClassification.lean`, `KMatrixAnomaly.lean`, `VillainHamiltonian.lean`, `FKGappedInterface.lean`, `ModularityTheorem.lean`, `InstantonZeroModes.lean`, `Mat13K5Ext.lean`.
- **Goltern-Shamir / lattice fermions** — `LatticeHamiltonian.lean`, `MajoranaKramers.lean`, `MajoranaRung.lean`, `MajoranaRungDecoupling.lean`, `MajoranaRungSMG.lean`, `BdGHamiltonian.lean`, `PauliMatrices.lean`, `WilsonMass.lean`, `GTCommutation.lean`, `GTWeylDoublet.lean`, `FermiPointTopology.lean`, `FermionBag4D.lean`, `GaugeFermionBag.lean`, `GaugeErasure.lean`, `GaugeEmergence.lean`, `GaugingStep.lean`, `QuarkRungMajoranaChannel.lean`, `QuarkRungScalarChannel.lean`, `ScalarRungInterpretation.lean`.
- **Topological QC — quantum groups + MTCs** — `Uqsl2.lean`, `Uqsl2Hopf.lean`, `Uqsl2Affine.lean`, `Uqsl2AffineHopf.lean`, `Uqsl3.lean`, `Uqsl3Hopf.lean`, `QuantumGroupGeneric.lean`, `QuantumGroupCoproduct.lean`, `QuantumGroupAntipode.lean`, `QuantumGroupHopf.lean`, `QuantumGroupInstantiation.lean`, `QuantumGroupMeta.lean`, `RestrictedUq.lean`, `RepUqFusion.lean`, `CoidealEmbedding.lean`, `OnsagerAlgebra.lean`, `OnsagerContraction.lean`, `KLinearCategory.lean`, `FusionCategory.lean`, `FusionExamples.lean`, `VecG.lean`, `VecGMonoidal.lean`, `KacWaltonFusion.lean`, `SphericalCategory.lean`, `RibbonCategory.lean`, `MugerCenter.lean`, `FPDimension.lean`, `D2Formula.lean`, `DrinfeldCenterBridge.lean`, `DrinfeldDouble.lean`, `DrinfeldDoubleAlgebra.lean`, `DrinfeldDoubleRing.lean`, `DrinfeldEquivalence.lean`, `CenterEquivalenceZ2.lean`, `CenterFunctor.lean`, `CenterFunctorZ2.lean`, `CenterFunctorZ2Equiv.lean`, `S3CenterAnyons.lean`, `ToricCodeCenter.lean`, `StringNet.lean`, `TQFTPartition.lean`, `TemperleyLieb.lean`, `JonesWenzl.lean`, `WRTInvariant.lean`, `WRTComputation.lean`, `SurgeryPresentation.lean`, `FigureEightKnot.lean`.
- **SU(2)_k / SU(3)_k / Ising / Fibonacci** — `SU2kFusion.lean`, `SU2kMTC.lean`, `SU2kSMatrix.lean`, `SU3kFusion.lean`, `SU3k2FSymbols.lean`, `SU3k2SMatrix.lean`, `IsingBraiding.lean`, `IsingGates.lean`, `FibonacciMTC.lean`, `FibonacciBraiding.lean`, `FibonacciQutrit.lean`, `FibonacciQutritUniversality.lean`, `FibonacciUniversality.lean`, `FibonacciQuintetTrueRep.lean`, `FibonacciQuintetUniversality.lean`, `FibonacciQuintetUniversalityExt.lean`, `FibonacciSextetTrueRep.lean`, `BraidGroup.lean`, `TgateFibBraid.lean`, `CNOTBraidTQSim.lean`, `GateCompilation.lean`, `ChiralSSB_QCD.lean`.
- **Number-field substrate** — `QNumber.lean`, `QSqrt2.lean`, `QSqrt3.lean`, `QSqrt5.lean`, `QCyc3.lean`, `QCyc5.lean`, `QCyc5Ext.lean`, `QCyc15.lean`, `QCyc15SqrtPhi.lean`, `QCyc16.lean`, `QCyc40Ext.lean`, `QCyc80.lean`, `QCyc80Ext.lean`, `QLevel3.lean`, `PolyQuotQ.lean`, `PolyQuotOver.lean`, `PolyQuotQCharacterisation.lean`, `E8Lattice.lean`, `MazurSigmaModelRigidity.lean`.
- **Fracton / vestigial / dark sector** — `FractonDarkMatter.lean`, `FractonFormulas.lean`, `FractonGravity.lean`, `FractonHydro.lean`, `FractonNonAbelian.lean`, `VestigialGravity.lean`, `VestigialEOS.lean`, `VestigialMapping.lean`, `VestigialSusceptibility.lean`, `VestigialInflationNoGo.lean`, `CondensedMatterAnalog.lean`, `GibbsDuhemTheorem.lean`, `QTheoryNoGoTheorem.lean`, `DarkEnergyObstructionPrinciple.lean`, `DESIComparison.lean`, `DarkSectorSynthesis.lean`, `DarkSectorClassificationExtension.lean`, `ClassificationTableDark.lean`, `HiddenSectorClassification.lean`, `HiddenSectorMixedCharge.lean`, `FangGuTorsionDM.lean`, `SFDMMergerForecast.lean`, `CausalSetDarkEnergy.lean`, `EntropicGravityDarkEnergy.lean`, `CosmologicalConstant.lean`, `CosmologicalPerturbations.lean`.
- **QCD strong-coupling + center-symmetry** — `CFLChiralLagrangian.lean`, `CenterSymmetryConfinement.lean`, `ChiralSSB_QCD.lean`, `CPPhaseSubstrate.lean`, `StrongCPTopologicalDE.lean`, `SubstrateAxion.lean`, `SubstrateInstantonSpectrum.lean`, `ThetaVacuumFiniteT.lean`, `EWPhaseTransition.lean`, `EWBaryogenesisChiralityWall.lean`, `LightQuarkHierarchyFallthrough.lean`, `CKMApexSubstrateConstraint.lean`, `NeutrinoMixing.lean`, `BBN.lean`.
- **Statistical estimators** — `VerifiedStatistics.lean`, `VerifiedJackknife.lean`.
- **Lattice / MC support** — `HubbardStratonovichRHMC.lean`, `WetterichNJL.lean`, `SU2PseudoReality.lean`, `SO4Weingarten.lean`, `QuaternionGauge.lean`, `WaveEquation1D.lean`.
- **Fermi-Hubbard** — `FermiHubbardDimer.lean`.
- **Infrastructure / utilities** — `Basic.lean`, `ArrayHelpers.lean`, `ExtractDeps.lean` (environment walker), `BundleRiemannAux.lean`, `RiccatiComparison.lean`, `LaplaceMethod.lean`, `MatrixBCH.lean`, `MatrixBCHCubic.lean`, `MatrixTaylor.lean`, `FermiHubbardDimer.lean`, `RouabahExplicit.lean`.

For a fully alphabetized list, see `docs/counts.json` field `lean.module_names` (378 entries).

---

## 4. Headline theorem index

Load-bearing top-level theorems. Each row: fully-qualified name + module path + one-line statement. For the full theorem list, use `grep "^theorem " lean/SKEFTHawking/<Module>.lean` per module, or the upstream `extract_lean_deps.py` outputs in `lean/lean_deps.json`.

### 4.1 Solovay-Kitaev / FKLW topological-QC density (Phase 5–7)

| Theorem | Module | One-line |
|---|---|---|
| `fibonacci_density_F21_unconditional` | `FKLW/SU2BCHBracketClosure.lean` | F.21 Fibonacci density in SU(3)_2 ↪ SU(2) — kernel-only, zero tracked Props (2026-05-22). |
| `SkApproxCSuperQuadraticBound_holds` | `FKLW/SolovayKitaevPathA.lean` (line 1716) | Unconditional super-quadratic convergence of the Dawson-Nielsen compiler at K_compose = 1024 (2026-05-23). |
| `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` | `FKLW/SolovayKitaevPathA.lean` (line 2523) | Unconditional Path A strict headline for ε ∈ (0, ε₀] bundling error + length (2026-05-23). |
| `solovayKitaev_dawson_nielsen_quantitative_fibonacci` | `FKLW/SolovayKitaevQuantitative.lean` | First kernel-verified quantitative Solovay-Kitaev length bound (conditional on `SolovayKitaevQuantitativeContract`). |
| `bridge_FKLW_unitary_hom` | `FKLW/AharonovAradBridgeIteration.lean` | Aharonov-Arad bridge from accumulation-at-1 to closure-equals-univ. |
| `H_Fib_v4_witness_unconditional` | `FKLW/OneParameterSubgroupSU2.lean` | Unconditional v4 anchor for Phase 5 Step 13. |

### 4.2 Standard-Model anomaly / chirality / Z₁₆

| Theorem | Module | One-line |
|---|---|---|
| `generation_constraint_iff` | `GenerationConstraint.lean` | 3 ∣ N_f ↔ 24 ∣ 8·N_f (three generations from anomaly + modular invariance). |
| `c_minus_eight_N_f` | `WangBridge.lean` | c₋ = 8·N_f from SM Weyl fermion content. |
| `modular_invariance_24` | `ModularInvarianceConstraint.lean` | Framing anomaly 24 ∣ c₋ ↔ phase = 1. |
| `tpf_outside_gs_scope_main` | `TPFEvasion.lean` | Master TPF-evasion theorem: 5-of-9 Golterman-Shamir conditions violated. |
| `anomaly_free_implies_chiral_gauge` | `SPTClassification.lean` | Anomaly-free ⟹ chiral-gauge (consumes `TPFConjecture` tracked Prop). |
| `rokhlin_sixteen` | `RokhlinBridge.lean` | The "16 convergence" — SM Weyl / ℤ₁₆ / Rokhlin / Kitaev DIII all the same 16. |

### 4.3 Quantum groups / MTCs / TQFT

| Theorem | Module | One-line |
|---|---|---|
| `Uqsl2` (HopfAlgebra instance) | `Uqsl2Hopf.lean` | First Hopf-algebra instance on a quantum group in any proof assistant (66 thms, 0 sorry). |
| `Uqsl3` (HopfAlgebra instance) | `Uqsl3Hopf.lean` | First rank-2 quantum-group Hopf algebra in any proof assistant (189 thms, 0 sorry). |
| `QuantumGroup k A` (HopfAlgebra instance) | `QuantumGroupHopf.lean` | First generic parameterized U_q(𝔤) HopfAlgebra in any proof assistant. |
| `kacWaltonFusion` | `KacWaltonFusion.lean` | First Kac-Walton fusion algorithm in any proof assistant (SU(5)₁ Z₅, SU(2)/SU(3)/SU(4)/G₂/B₂ verified). |
| `trefoil_eq_neg_one` | `IsingBraiding.lean` | Trefoil knot Jones polynomial = -1 — first machine-verified knot invariant. |
| `fibonacci_universality` | `FibonacciUniversality.lean` | Fibonacci braiding generates SU(2)_3 image dense in SU(2) (Lie-algebra spanning). |
| `wrt_S3` / `wrt_S2_S1` / `wrt_figure_eight_complement` | `WRTComputation.lean` | First WRT TQFT invariants of canonical 3-manifolds in any proof assistant. |
| `wittEquivalentMTC_braided_implies_wittClass_eq` | `SymTFTAudit/DrinfeldCenter.lean` | Davydov-Müger-Nikshych-Ostrik 2010 braided-Witt equivalence ⟹ integer-mod-24 Witt-class equality. |
| `stage5_11_pseudoUnitary_closure` | `SymTFTAudit/PseudoUnitary.lean` | DMNO 2010 Theorem 5.2 pseudo-unitary subclass discharge. |

### 4.4 Gravity / black holes / cosmology

| Theorem | Module | One-line |
|---|---|---|
| `G_N_emerg_eq_alpha_ADW_times_Sakharov` | `LinearizedEFE.lean` | Emergent Newton constant `G_N^emerg = α_ADW · 12π / (N_f · Λ²)` from ADW microscopic theory. |
| `c_GW_equals_c_iff_chi_vest_eq_one` | `GravitationalWaves.lean` | GW170817 falsifies the vestigial-second-sound graviton identification by 7×10¹⁴ (under `H_VestigialModeIsGraviton`). |
| `BHEntropy_eq_area_minus_three_halves_log` | `BHEntropyMicroscopic.lean` | `S = A/(4G_N) − (3/2)log(A/(4G_N))` with Kaul-Majumdar SU(2)_k decomposition. |
| `four_laws_consistent_with_adw_bhs_cool_toward_extremality` | `BHThermodynamicsFourLaws.lean` | BCH four laws partitioned by regime at `M_c = (N_f · Λ_UV) / (12π · α_ADW)`. |
| `penrose_singularity_curve_theoretic` | `PenroseSingularityCurveTheoretic.lean` | Curve-theoretic Penrose composition theorem. |
| `raychaudhuri_focusing_ineq_under_NEC` | `RaychaudhuriEquation.lean` | Raychaudhuri focusing inequality `dθ/dλ ≤ -θ²/(n−1)` under NEC. |
| `hubbleSquared_ADW_pos` | `FLRWDynamics.lean` | ADW emergent-gravity Friedmann positivity. |
| `vestigial_w_eq_one_minus_tau_sq_over_5tau_sq_minus_one` | `VestigialEOS.lean` | First closed-form vestigial-gravity EOS `w_vest(τ) = (1−τ²)/(5τ²−1)`. |
| `gibbs_duhem_locks_w_vac_eq_neg_one` | `GibbsDuhemTheorem.lean` | First machine-checked emergent-vacuum obstruction (any single-scalar self-tuning ⟹ w_vac ≡ -1). |
| `q_theory_no_go_main` | `QTheoryNoGoTheorem.lean` | Klinkhamer-Volovik q-theory NO-GO across all 4 realizations. |

### 4.4b DKM transport bootstrap on SK-EFT-Hawking (Phase 6q)

| Theorem | Module | One-line |
|---|---|---|
| `kms_replaces_unitarity_thm` | `DKMBootstrap/KMSConsistency.lean` | Substantive resolution of Phase 6o Wave 1c Obstruction (I): CGL `hasReflectionPositivity` + `hasDynamicalKMS_algebraic` produces CHHK F4 positivity at 2-pt-function level. |
| `vertical_bootstrap_bypasses_crossing` | `DKMBootstrap/NoCrossing.lean` | Substantive resolution of Phase 6o Wave 1c Obstruction (II): vertical bootstrap + F4/F5/F6 ⇒ full CHHK axiom set without any crossing identity. |
| `dkm_axiom_set_iff_vertical_plus_f4f5f6` | `DKMBootstrap/NoCrossing.lean` | Equivalence: `IsDKMAxiomSet ↔ IsVerticalBootstrap ∧ F4 ∧ F5 ∧ F6`. |
| `dkm_rate_function_is_LDPRateFunction` | `DKMBootstrap/LDPBridge.lean` | **Highest-leverage cross-bridge of Phase 6q**: Phase 6n abstract `IsLDPRateFunction` class instantiated on Phase 6q DKM substrate via FDT-pinned variance `σ²:=χ·D`. |
| `chhk_F4_existence_iff_LDP_rate_function_holds` | `DKMBootstrap/LDPBridge.lean` | Substrate-level biconditional closure of the Wave 2a.1 DR §6 cross-bridge (Wave 2b.2 substantive lift 2026-05-25). |
| `horizon_transport_uniqueness_graphene_witness_one_half` | `DKMBootstrap/HorizonTransportBootstrap.lean` | **Positive uniqueness half of Phase 6q bimodal outcome** — graphene Dirac fluid substrate's collective mean free path bounded below by `mirConst = 1/2` (substantive constant `(2·β_2/(4π))^(1/3) ≈ 0.0756` ships Python-side in `src/dkm_bootstrap/graphene_mir.py`; the Lean `1/2` placeholder is a safe upper bound). |
| `sharpened_no_go_super_factorial` | `DKMBootstrap/HorizonTransportBootstrap.lean` | **Sharpened NO-GO half of Phase 6q bimodal outcome** — CHHK bootstrap inapplicable to super-factorial-unbounded commutator-norm substrates (BEC Bogoliubov case via Yin-Lucas/Kuwahara-Saito Lieb-Robinson-for-bosons). |
| `becBogoliubovCommutatorNorm_isSuperFactorialUnbounded` | `DKMBootstrap/BECBogoliubovBosonicGrowth.lean` | **Wave 2b.4 substantive lift (2026-05-25)** — concrete BEC Bogoliubov-bosonic commutator-norm sequence `(2κ)!` substantively instantiates the `IsSuperFactorialUnbounded` predicate, witnessing the sharpened-NO-GO half at concrete-substrate-instance level. |
| `bec_falls_under_sharpened_no_go` | `DKMBootstrap/BECBogoliubovBosonicGrowth.lean` | Wave 2b.4 cross-bridge: BEC platform fails CHHK F3 operator-growth axiom for any positive microscopic constants. |
| `platform_kms_qualities_pairwise_distinct` | `DKMBootstrap/E1E2CrossBridge.lean` | Classifier-level distinctness: graphene (Strong) / BEC (Approximate) / polariton (EffectiveOnly) KMS-quality classifications are pairwise-distinct. Substantive companion: `bec_distinguishes_from_graphene_super_factorial` in `BECBogoliubovBosonicGrowth.lean`. |
| `f2_orthogonal_to_skeft_axioms`, `f3_orthogonal_to_skeft_axioms` | `DKMBootstrap/AxiomSet.lean` | Substantive structural finding: CHHK F2 (f-sum rule) and F3 (operator-growth) microscopic axioms are NOT implied by CGL `SKEFTAxioms` — they carry genuinely new microscopic-lattice content. |

### 4.5 Hawking pipeline / SK-EFT

| Theorem | Module | One-line |
|---|---|---|
| `count_N_eq_floor_plus_one` | `SecondOrderSK.lean` | Transport-coefficient counting `count(N) = ⌊(N+1)/2⌋ + 1`. |
| `parity_alternation_general_N` | `ThirdOrderSK.lean` | Parity alternation theorem for SK-EFT gradient expansion. |
| `wkb_connection_unitarity_broken` | `WKBConnection.lean` | Exact WKB through complex turning point — modified unitarity. |
| `hawking_universality_main` | `HawkingUniversality.lean` | Hawking universality theorem (BEC/polariton/graphene). |
| `dispersion_within_ligo_iff` | `GravitationalWaves.lean` | SK-EFT dispersion biconditional vs LIGO. |
| `dirac_fluid_block_diagonal` | `DiracFluidMetric.lean` | 3×3 graphene Dirac-fluid acoustic metric block-diagonalizes for quasi-1D (92% theorem reuse). |

### 4.6 Statistical / numerical estimators

| Theorem | Module | One-line |
|---|---|---|
| `jackknifeVariance_nonneg` | `VerifiedJackknife.lean` | First verified jackknife variance non-negativity in any proof assistant. |
| `sampleVariance_nonneg` | `VerifiedStatistics.lean` | Sample variance non-negativity. |
| `intAutocorrTime_bounds` | `VerifiedJackknife.lean` | Integrated autocorrelation time bounds. |
| `multi_shift_cg_correctness` | `HubbardStratonovichRHMC.lean` | Multi-shift CG correctness for RHMC. |

### 4.7 Topological quantum gates (Fermi-Hubbard + Berry phase)

| Theorem | Module | One-line |
|---|---|---|
| `swap_unitary_minus_one_sign` | `FermiHubbardDimer.lean` | First formally verified symmetry-protected (non-topological) two-qubit gate. |
| `berry_phase_geometric_at_kernel_angle` | `FermiHubbardDimer.lean` | Berry phase is purely geometric under kernel-angle condition. |

### 4.8 Dark sector

| Theorem | Module | One-line |
|---|---|---|
| `sfdm_merger_signature` | `SFDMMergerForecast.lean` | SFDM Rankine-Hugoniot density jump closed form γ=2; sonic-boom step at Mach transition. |
| `fracton_dm_viable_in_p_wave_dipole_superfluid` | `FractonDarkMatter.lean` | Fracton DM viable in p-wave dipole superfluid at MeV–TeV. |
| `fg_cdm_obstruction` | `FangGuTorsionDM.lean` | Fang-Gu torsion DM kinematically excluded at CDM level (traceless T_μν ⟹ w = 1/3). |
| `hidden_sector_minimal_singlet_count` | `HiddenSectorClassification.lean` | ℤ₁₆-classified hidden sector — T-0 TQFT candidate invisible to direct detection. |

---

## 5. Tracked Props (load-bearing hypotheses)

Project posture: **axioms are temporary scaffolding, not permanent commitments** (Pipeline Invariant #15). The constructive alternative is a tracked `def`-Prop that propagates explicitly through every consumer's type signature. Project axiom count is **0** (counts.json `axiom_names: []`, 2026-05-23 regen).

Full catalogue: `docs/PERMANENT_TRACKED_HYPOTHESES.md`.

| Tracked Prop | Status | Module | Discharge LoE |
|---|---|---|---|
| `H_VestigialModeIsGraviton` | KEEP (permanent) | `GravitationalWaves.lean:326` | N/A — requires different microscopic substrate (out of project scope). |
| `H_DESICompatibility` | DISCHARGE_FUTURE_PHASE | `FLRWDynamics.lean:272` | ~50 person-hours; Phase 6b.2 (not active). |
| `H_RT_Formula_Valid` | KEEP (permanent) | `RTCasiniHuertaBounds.lean:87` | N/A — project-scope boundary (RT formula is AdS/CFT holographic working assumption). |
| `TPFConjecture` | KEEP (permanent; converted from `axiom gapped_interface_axiom` on 2026-05-19) | `SPTClassification.lean:254` | N/A — open at literature frontier in 3+1D / 4+1D (proven in 1+1D + 2+1D). |
| `SolovayKitaevQuantitativeContract` | DISCHARGE_IN_PROGRESS | `FKLW/SolovayKitaevQuantitative.lean` | Phase 6t Path A Option C tight-ε regime SHIPPED 2026-05-23; loose-ε bundled headline also SHIPPED. Substantive remaining: K-margin tightening as Mathlib-PR-quality follow-on. |

Search live: `grep -rn "H_VestigialModeIsGraviton\|H_DESICompatibility\|H_RT_Formula_Valid\|TPFConjecture\|SolovayKitaevQuantitativeContract" lean/`.

---

## 6. Pipeline invariants (15)

Authority: `docs/WAVE_EXECUTION_PIPELINE.md` §"Pipeline Invariants". One-line summary each:

1. **`formulas.py` is canonical** — only place physics formulas live; all other code imports from it.
2. **`constants.py` is canonical** — only place experimental parameters, physical constants, and the Aristotle theorem registry live.
3. **`visualizations.py` is canonical** — only place figure functions live; notebooks reference via `# viz-ref:` tags.
4. **Every formula has a Lean theorem** with zero sorry.
5. **Every computed quantity has bounds** enforced by CHECK 12.
6. **Every paper claim traces to computation** within 0.5%, enforced by CHECK 14.
7. **Narrative derives from data** — feasibility claims need computed support.
8. **Every experimental parameter has verified provenance** in `src/core/provenance.py`, enforced by CHECK 15.
9. **Placeholder theorems are non-load-bearing** — `True := trivial` theorems are doc markers only; substantive count = total − placeholders.
10. **No heartbeat overrides in proof bodies** (exception: metaprograms like `ExtractDeps.lean` walking O(project-size)).
11. **Every external bibitem has a primary-source cache file** under `Lit-Search/Phase-X/primary-sources/<bibkey>.{pdf,abstract.txt,json}`, enforced by CHECK 19.
12. **Provenance DOIs resolve to the registry** — every DOI in `PARAMETER_PROVENANCE` must resolve to a `CITATION_REGISTRY` bibkey (CHECK 20).
13. **Stage 14 QI register is auto-regen + manually-curated** — open items regenerated; closed items preserved verbatim across regens.
14. **Every paper-shaped output lifts into a `PAPER_STRATEGY.md` bundle** (F, D1–D5, L1–L3, I1, I2, I3, E1, E2) — recorded in `docs/PAPER_DRAFT_MAPPING.md`.
15. **Every new project-local `axiom` requires explicit user sign-off** + discharge plan or no-feasible-proof argument; `AXIOM_METADATA` registration mandatory.

---

## 7. Bundle status (14 publication targets)

Authority: `docs/PAPER_STRATEGY.md` (architecture) + `docs/PAPER_DRAFT_MAPPING.md` (per-draft → per-bundle assignment) + `docs/BUNDLE_READINESS_HEATMAP.md` (per-bundle Stage-13 readiness, auto-regen via `scripts/bundle_readiness.py --heatmap`).

| Bundle | Tier | Title | Status (2026-05-23) |
|---|---:|---|:---:|
| **F** | 0 (flagship review) | "Fluid-Based Approaches to Fundamental Physics — A Formally Verified Survey" | 🔴 RED (8 blockers; ships last). |
| **D1** | 1 (deep) | Formally Verified Analog Hawking Radiation Across Three Platforms | 🟢 GREEN. |
| **D2** | 1 (deep) | Anomaly Constraints on Standard-Model Particle Content | 🟢 GREEN. |
| **D3** | 1 (deep) | Emergent Gravity from Microscopy — Linearized EFE through BH Thermodynamics | 🔴 RED (5 blockers). |
| **D4** | 1 (deep) | Topological Quantum Computation — First Machine-Verified Foundations | 🔴 RED (1 blocker; closed at GREEN-with-advisories 2026-05-23). |
| **D5** | 1 (deep) | The Dark Sector under Substrate Constraints | 🔴 RED (2 blockers). |
| **L1** | 2 (PRL letter) | GW170817 vs Vestigial-Graviton — 7×10¹⁴ Falsification | 🟢 GREEN. |
| **L2** | 2 (PRL letter) | Three Generations from Modular Invariance | 🟢 GREEN. |
| **L3** | 2 (PRL letter) | BCH Four Laws by Regime | 🟢 GREEN. |
| **I1** | 3 (infrastructure) | Verification Methodology + Lean Tooling | 🟢 GREEN. |
| **I2** | 3 (infrastructure) | Sentence-Level Paper Provenance Pipeline | 🟢 GREEN. |
| **I3** | 3 (infrastructure) | Verified Stochastic Calculus for Mathlib4 | 🟢 GREEN. |
| **E1** | 4 (experimental letter) | Paris-LKB Polariton Analog-Hawking Detection Path | 🟢 GREEN. |
| **E2** | 4 (experimental letter) | Dean-Kim-Lucas Graphene Bilayer Sonic Horizon | 🟢 GREEN (1 minor advisory). |

**Bundle directories:** `papers/{F,D1,D2,D3,D4,D5,L1,L2,L3,I1,I2,I3,E1,E2}/`. Bundle architecture canon: `docs/PAPER_STRATEGY.md` (14 targets); `docs/PAPER_DRAFT_MAPPING.md` (per-existing-draft → bundle table); `docs/BUNDLE_LIFT_PROCEDURE.md` (14-step lift workflow); `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` (absorbing late-phase waves into already-drafted bundles).

---

## 8. Python source modules

130 Python modules under `src/`. Grouped by sector. For per-module docstrings + signatures, browse `src/<sector>/` directly or read `SK_EFT_Hawking_Inventory.md` Section 1.

### 8.1 Core (canonical singletons)

| File | Purpose |
|---|---|
| `src/core/constants.py` | Physical constants, experimental params, `ARISTOTLE_THEOREMS` registry, `AXIOM_METADATA`, `PLACEHOLDER_THEOREMS`. Pipeline Invariant #2. |
| `src/core/formulas.py` | Canonical physics formulas with Lean + Aristotle refs (~137 functions). Pipeline Invariant #1. |
| `src/core/visualizations.py` | All Plotly figure functions + `COLORS` palette. Pipeline Invariant #3. |
| `src/core/transonic_background.py` | 1D BEC transonic flow solver. |
| `src/core/aristotle_interface.py` | Aristotle API + sorry-gap registry. |
| `src/core/sm_anomaly.py` | SM anomaly computation in ℤ₁₆: fermion data, anomaly index, generation constraint. |
| `src/core/provenance.py` | `PARAMETER_PROVENANCE` registry (tiers + verification dates). |
| `src/core/citations.py` | `CITATION_REGISTRY` (DOI + arXiv + primary-source-path tracking). |

### 8.2 Phase 1–2: dissipative SK-EFT

| Directory | Modules |
|---|---|
| `src/first_order/` | (empty — content moved to `formulas.py`). |
| `src/second_order/` | `enumeration.py` (count(N) = ⌊(N+1)/2⌋+1), `coefficients.py`, `wkb_analysis.py`, `cgl_derivation.py` (CGL dynamical KMS → FDR). |

### 8.3 Phase 3: gauge erasure / WKB / ADW

| Directory | Modules |
|---|---|
| `src/gauge_erasure/` | `erasure_theorem.py` (non-Abelian gauge erasure → U(1) survives). |
| `src/wkb/` | `connection_formula.py`, `bogoliubov.py`, `spectrum.py`, `backreaction.py`. |
| `src/adw/` | `wen_model.py`, `hubbard_stratonovich.py`, `gap_equation.py`, `fluctuations.py`, `ginzburg_landau.py`, `tetrad_gap_solver.py`, `tetrad_observables.py`. |

### 8.4 Phase 4: experimental / chirality / fracton / vestigial

| Directory | Modules |
|---|---|
| `src/experimental/` | `predictions.py`, `kappa_scaling.py`, `polariton_predictions.py`, `doublon_gate.py`. |
| `src/chirality/` | `gioia_thorngren.py`, `tpf_gs_analysis.py`. |
| `src/fracton/` | `sk_eft.py`, `information_retention.py`, `gravity_connection.py`, `non_abelian.py`. |
| `src/vestigial/` | `mean_field.py`, `lattice_model.py`, `monte_carlo.py`, `phase_diagram.py`, `finite_size.py`, `su2_integration.py`, `grassmann_trg.py`, `lattice_4d.py`, `fermion_bag.py`, `wetterich_model.py`, `phase_scan.py`, `quaternion.py`, `so4_gauge.py`, `gauge_fermion_bag.py`, `gauge_fermion_bag_majorana.py`, `hs_rhmc.py`, `hs_rhmc_jax.py`, `hs_rhmc_torch.py`, `stencil_dirac.py`, `verified_analysis.py`. |

### 8.5 Phase 5 sectors

| Directory | Topic |
|---|---|
| `src/graphene/` | Bilayer-graphene Dirac fluid (Phase 5w): `bilayer_eos.py`, `hawking_predictions.py`, `platform_comparison.py`, `transport_counting.py`, `wkb_spectrum.py`. |
| `src/dark_sector/` | Phase 5x dark-sector: `adw_cosmological_constant.py`, `fracton_dm.py`, `sfdm_merger_forecast.py`, `sfdm_sk_eft.py`, `synthesis.py`, `z16_hidden_sector.py`. |
| `src/scalar_rung/` | Phase 5z scalar-rung Higgs prediction: `bhl_embedding.py`, `ew_mass_matrix.py`, `higgs_prediction.py`. |
| `src/fermi_hubbard/` | Phase 5t Fermi-Hubbard doublon: `dimer.py`. |
| `src/vestigial_inflation/` | Phase 6b vestigial-inflation NO-GO: `ns_r_prediction.py`, `planck_bicep_check.py`, `slow_roll.py`. |

### 8.6 Phase 6 sectors

| Directory | Topic |
|---|---|
| `src/emergent_gravity/` | Phase 6a Track A: `G_N_emerg.py`, `linearized_efe.py`, `vergeles_unitarity.py`. |
| `src/gravitational_waves/` | Phase 6a Track B: `c_GW_computation.py`, `dispersion_relation.py`, `ligo_constraint_check.py`. |
| `src/bh_entropy/` | Phase 6a Track C: `entropy_coefficient.py`, `horizon_spectrum.py`, `mtc_state_counting.py`. |
| `src/bh_thermodynamics/` | Phase 6a Wave 5: `acoustic_evolution.py`, `falsifier_checks.py`, `four_laws_data.py`, `regime_classifier.py`. |
| `src/cosmological_perturbations/` | Phase 6b: `cmb_spectrum.py`, `linear_perturbations.py`, `planck_comparison.py`. |
| `src/bbn/` | Phase 6c BBN: `abundances.py`, `candidate_checker.py`. |
| `src/equivalence_principle/` | Phase 6c: `mechanism_classifier.py`. |
| `src/qec_holography/` | Phase 6c: `code_distance.py`, `scrambling_time.py`. |
| `src/center_symmetry/` | Phase 6d: `eta_over_s_prediction.py`, `polyakov_loop.py`, `svetitsky_yaffe.py`. |
| `src/chiral_ssb/` | Phase 6d GMOR: `gmor_check.py`, `quark_condensate.py`, `tetrad_ratio.py`. |
| `src/cfl/` | Phase 6d CFL: `cfl_lagrangian.py`, `topological_order_check.py`, `z3_one_form_action.py`. |
| `src/strong_cp_de/` | Phase 6e: `combined_de_consistency.py`, `zhitnitsky_eval.py`. |
| `src/heat_kernel/` | Phase 6e: `a2_computation.py`, `a4_computation.py`, `seeley_dewitt.py`. |
| `src/higher_curvature/` | Phase 6e: `curvature_basis.py`, `gauss_bonnet_check.py`, `observational_bound_check.py`. |
| `src/einstein_cartan/` | Phase 6e: `ec_residual_assessment.py`, `observational_bounds.py`, `torsion_amplitude.py`. |
| `src/nonlinear_efe/` | Phase 6f: `T_emerg_vs_matter.py`, `efe_solver.py`, `observable_prediction.py`. |
| `src/diff_invariance/` | Phase 6f: `anomaly_hunt.py`, `variational_check.py`. |
| `src/micro_macro_match/` | Phase 6f: `cc_problem_assessment.py`, `g_n_emerg_from_micro.py`, `lambda_emerg_from_micro.py`. |
| `src/rt_ch_bounds/` | Phase 6j: `ch_bound_check.py`, `rt_comparison.py`. |
| `src/ew_phase_transition/` | Phase 6g/6k: `baryogenesis_compatibility.py`, `order_classifier.py`, `potential.py`. |
| `src/ew_baryogenesis/` | Phase 6g: `bridge_check.py`, `sphaleron_computation.py`. |
| `src/resurgence/` | Phase 6n: `bdg_self_energy.py`, `borel.py`. |
| `src/dkm_bootstrap/` | Phase 6q Wave 2b numerical companion (2026-05-25 strengthening close): `graphene_mir.py` — CHHK MIR constant `(2·β_2/(4π))^(1/3) ≈ 0.0756` with Crossno 2016 graphene-data confrontation. Canonical formulas in `src/core/formulas.py` (`chhk_beta_d`, `chhk_mir_constant`, `graphene_mir_constant`, `graphene_mir_constant_mpmath`, `unit_sphere_surface`); platform-specific specialization here. |

---

## 9. Aristotle integration

**322 theorems machine-proved across 44 runs.** Authority: `ARISTOTLE_THEOREMS` registry in `src/core/constants.py`. Run table in `SK_EFT_Hawking_Inventory.md` Section 3.

**Submission tooling:**
- `scripts/submit_to_aristotle.py` — `--dry-run` previews; `--submit --priority N` submits; `--retrieve <ID> --integrate` integrates returned proofs.
- `docs/references/Theorm_Proving_Aristotle_Lean.md` — mandatory pre-read.
- `docs/references/aristotle_batch_plan.md` — current batch plan.

**Posture:** Aristotle is Stage-4 fallback in the wave pipeline. As of Phase 6, MCP-interactive proving via `lean-lsp-mcp` is the primary loop; Aristotle reserved for (i) sorries that survive interactive decomposition, or (ii) batch submissions. No Aristotle runs in any 6-prefix phase as of 2026-05-23 — all Phase 6n/6o/6p/6t ships MCP-proven.

**Toolchain caveat:** Aristotle runs on Lean 4.28.0 + earlier Mathlib pin; project is on 4.29.1 + `5e932f97`. Use sparingly when project uses 4.29-specific features.

---

## 10. Other docs (pointers)

### 10.1 `docs/` reference

| File | Purpose |
|---|---|
| `docs/ARCHITECTURE_SCOPE.md` | Layer 3 scope statement (what is and is not predicted under the project's mechanisms). |
| `docs/BUNDLE_DIRECTORY_SCHEMA.md` | Per-bundle file layout. |
| `docs/BUNDLE_LIFT_PROCEDURE.md` | 14-step procedure for lifting per-paper drafts into a publication bundle. |
| `docs/BUNDLE_READINESS_HEATMAP.md` | Per-bundle Stage-13 readiness, auto-regen via `scripts/bundle_readiness.py`. |
| `docs/DASHBOARD.md` | Provenance command-center documentation (`scripts/provenance_dashboard.py`, localhost:8050). |
| `docs/KNOWLEDGE_GRAPH.md` | Project knowledge-graph schema + Postgres+AGE setup. |
| `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` | Stage A–G protocol for absorbing late-phase waves into already-drafted bundles. |
| `docs/PAPER_DRAFT_MAPPING.md` | Per-existing-draft → per-bundle assignment table. |
| `docs/PAPER_STRATEGY.md` | 14-bundle publication architecture (canonical). |
| `docs/PAPER_TABLES_STATUS.md` | Per-paper LaTeX table generation status. |
| `docs/PERMANENT_TRACKED_HYPOTHESES.md` | 5-Prop catalogue (tracked-Prop posture, status, discharge LoE). |
| `docs/PHASE5_STEP13_COMPLETE.md` | Phase 5 Step 13 (F.21 unconditional) ship summary. |
| `docs/PHASE6T_QUANTITATIVE_SK_COMPLETE.md` | Phase 6t quantitative Solovay-Kitaev ship summary. |
| `docs/QI_REGISTER.md` | Stage 14 quality-improvement register (auto-regen + manually-curated). |
| `docs/READINESS_GATES.md` | Per-paper Stage-13 readiness companion to bundle heatmap. |
| `docs/RESEARCH_STATUS_OVERVIEW.md` | High-level research-status overview. |
| `docs/WAVE_EXECUTION_PIPELINE.md` | 14-stage wave protocol + 15 pipeline invariants. |
| `docs/counts.json` | Live counts ground truth (regen via `scripts/update_counts.py`). |
| `docs/counts.tex` | LaTeX `\input{}` counts macros for papers. |

### 10.2 `docs/roadmaps/` — phase roadmaps

Per-phase roadmaps (Phase 1 through Phase 7a) in `docs/roadmaps/Phase<N>_Roadmap.md`. Active roadmaps as of 2026-05-25: Phase 6v (external-substrate alignment + creates D6 bundle, 7 waves NOT STARTED), Phase 6w (classical-simulability + tensor-network substrate, 7 waves NOT STARTED), Phase 6t (quantitative SK — Path A Option C close 2026-05-23), Phase 7a (paper-bundle architecture freeze). Phase 6u (Generic-Alphabet SK substrate) is a NOT-STARTED planning skeleton with T-A2 / T-B tracks re-slotted from "(likely Phase 6w)" to Phase 6x or later per ADR 008. All Phase 5+ phases through 6p are substantively closed.

### 10.3 `docs/references/` — manuals

- `docs/references/Theorm_Proving_Aristotle_Lean.md` — mandatory Aristotle pre-read.
- `docs/references/Datastar_Dashboard_Reference.md` — provenance-dashboard reference.
- `docs/references/production_rhmc.md` — RHMC production reference.

### 10.4 `docs/adrs/` — architecture decision records

- `docs/adrs/ADR-001-commring-qcyc5ext-roadmap.md`.

### 10.5 `docs/agents/` — agent prompts

- `docs/agents/claims-reviewer-bundle-prompts.md` — Stage-13 anchor list per bundle.
- `docs/agents/claims_reviewer.md` — claims-reviewer agent prompt.

### 10.6 `docs/stakeholder/` — per-phase stakeholder docs

Implications + strategic-positioning notes per phase, `docs/stakeholder/Phase<N>_*.md` (~22 docs).

### 10.7 `docs/analysis/` and `docs/validation/`

- `docs/analysis/` — cross-cutting analysis docs.
- `docs/validation/` — validation reports.

---

## 11. Scripts (53 in `scripts/`)

**Validation + counts:**
- `scripts/validate.py` — full validation suite (21 checks); `--list` enumerates; `--check <name>` runs one.
- `scripts/update_counts.py` — regenerates `docs/counts.json` (re-runs `extract_lean_deps.py` if Lean source hashes changed).
- `scripts/extract_lean_deps.py` — extracts Lean declaration taxonomy + axiom dependencies (via `ExtractDeps.lean`).
- `scripts/graph_integrity.py` — graph-integrity checks for the knowledge graph.
- `scripts/build_graph.py` — builds the project knowledge graph (Postgres + AGE).
- `scripts/last_modified.py` — sentence-level freshness propagation.
- `scripts/sentence_state.py` — sole-writer sentence-state CLI (paper-provenance v2).
- `scripts/verification_state.py` — verification-state cross-tab change-bus.

**Bundle ops (Phase 7a):**
- `scripts/bundle_append.py` — append-and-supersede across bundles.
- `scripts/bundle_clusters.py` — claim-cluster bundle projection.
- `scripts/bundle_migration.py` — bundle migration tooling.
- `scripts/bundle_readiness.py` — regenerates `docs/BUNDLE_READINESS_HEATMAP.md`.
- `scripts/bundle_source_manifest.py` — bundle source manifest.
- `scripts/check_bundle_source_freshness.py` — freshness check.
- `scripts/datastar_bundles.py` — provenance-dashboard Bundles-tab JSON.

**Citation + provenance:**
- `scripts/back_fill_primary_sources.py` — populates `Lit-Search/Phase-X/primary-sources/` cache files.
- `scripts/promote_primary_sources.py` — writes successful fetches back into `CITATION_REGISTRY`.
- `scripts/extract_missing_bibkeys.py` — extracts `\bibitem` stubs from modified papers.
- `scripts/citation_cache.py` — citation cache management.
- `scripts/audit_paper_lean_refs.py` — auditor for paper ↔ Lean references.

**Aristotle:**
- `scripts/submit_to_aristotle.py` — submission + retrieval + integration.
- `scripts/review_runner.py` — review-runner orchestration.

**Figures + papers:**
- `scripts/review_figures.py` — generates PNGs + structural figure checks.
- `scripts/render_paper_tables.py` — paper-table rendering.
- `scripts/paper_tables/` — per-bundle table generators.
- `scripts/templates/` — paper templates.

**MC production:**
- `scripts/run_rhmc_production.py`, `scripts/run_rhmc_epochs.sh`, `scripts/run_majorana_production.py`, `scripts/run_vestigial_production.py`, `scripts/run_vestigial_inflation_preliminary.py`, `scripts/analyze_majorana_results.py`, `scripts/view_vestigial_mc.py`, `scripts/benchmark_rust_parallel.py`.

**T-gate compilers (Phase 6p):**
- `scripts/phase6p_tgate_compiler.py` (+ `_v4`, `_v6`, `_v7`, `_v8`), `scripts/phase6p_tgate_exact_frob.py`.

**Other:**
- `scripts/extract_sigma_symbolic.py`, `scripts/generate_a1_resolution.py`, `scripts/wave2_flip_provenance.py`, `scripts/sync_graph_to_pg.py`, `scripts/cluster_detect.py`, `scripts/qi_register.py`, `scripts/readiness_gates.py`, `scripts/datastar_helpers.py`, `scripts/provenance_dashboard.py`, `scripts/test_helpers.py`, `scripts/test_pseudofermion_convention.py`, `scripts/pre-commit-notebooks.sh`.

---

## 12. Cross-references

- **Memory (per-conversation):** `~/.claude/projects/-Users-johnroehm-Programming-PythonEnvironments-Physics-Fluid-Based-Physics-Research/memory/MEMORY.md` — index of topic files (project ships, feedback notes, next-session openers).
- **Lit-Search deep research:** `Lit-Search/` workspace-level — phase-specific deep-research deliverables (`Phase-5*/`, `Phase-6*/`, `Phase-7*/`); primary-source cache at `Lit-Search/Phase-X/primary-sources/`; pending tasks at `Lit-Search/tasks/`.
- **Workspace docs:** `../CLAUDE.md` — workspace-level agent guidance.
- **Working docs (transient):** `temporary/working-docs/` — proof-state notes, per-wave working memos, archive of misplaced narrative.
- **Archived old Inventory_Index:** `temporary/working-docs/inventory_index_handoff_archive_2026-05-23.md` — the previous 488KB session-log-style index, preserved for audit.

---

## 13. Maintenance protocol

**When to update this file:**
- New top-level theorem ships → add to §4.
- New tracked Prop → add to §5 (after `PERMANENT_TRACKED_HYPOTHESES.md` is updated).
- New subdirectory in `lean/SKEFTHawking/` → add to §3.1.
- Bundle status change (RED ↔ GREEN) → update §7 (or re-regen heatmap and link to it).
- Counts move ≥1% → refresh §1 from `docs/counts.json`.

**What NOT to put here:**
- Per-session ship narrative (belongs in `temporary/working-docs/` or `MEMORY.md` topic files).
- Per-commit changelog (belongs in git history).
- Per-wave deep prose (belongs in `SK_EFT_Hawking_Inventory.md`).
- Full theorem statements (belongs in `.lean` files; this index gives names + one-line).

**Size budget check after edit:** `wc -c SK_EFT_Hawking_Inventory_Index.md` — keep under 100,000 bytes. Current target: ~50–80 KB.
