import SKEFTHawking.Basic
-- Phase 6n.γ Stage 2-3 — Glorioso-Liu axiomatic skeleton
-- (Phase 6n session 5: substantive Stage 2-3 refactor shipped — all 7
-- modules now parameterized over SKDoubling.SKAction with substantive
-- predicates and concrete zero-action existence witnesses.)
-- Phase1Reconciliation: substantive partition recovery from KMSSymmetry
-- (R1 hold LIFTED per session-5 commit `bbb34ce`).
import SKEFTHawking.GloriosoLiu.Axioms
import SKEFTHawking.GloriosoLiu.DynamicalKMS
import SKEFTHawking.GloriosoLiu.LocalEquilibrium
import SKEFTHawking.GloriosoLiu.EntropyCurrent
import SKEFTHawking.GloriosoLiu.LocalSecondLaw
import SKEFTHawking.GloriosoLiu.OnsagerReciprocity
import SKEFTHawking.GloriosoLiu.FirstOrderProjection
import SKEFTHawking.GloriosoLiu.Phase1Reconciliation
-- Phase 6n Session 9 (2026-05-05): Wave 2a × Wave 1b cross-track unification
-- bridge — extends SKEFTAxioms to SKEFTAxiomsExt on the second-order
-- extended field space and projects to γ_{2,1}+γ_{2,2}=0 parity-alternation
-- that KMSParityAlternationCompatible (Wave 1b Stage 3) references.
-- Substantive proof-body chain: SKEFTAxiomsExt → fullSecondOrder_uniqueness
-- (Aristotle run c4d73ca8) → combined_positivity_constraint → parity-alternation
-- → cross-track bridge to KMSParityAlternationCompatible.
import SKEFTHawking.GloriosoLiu.SecondOrderProjection
-- Phase 6n.α Wave (G2 Resurgence) Stage 1 substrate (sub-wave 6n.α.4):
-- Borel transform + Gevrey-1 predicate + Λ_UV-from-IR predictor + Stokes
-- constant + non-perturbative-content existence theorem. Python-side
-- numerical infrastructure at src/resurgence/borel.py (17 tests passing).
import SKEFTHawking.Resurgence.Basic
import SKEFTHawking.Resurgence.BorelAction
import SKEFTHawking.Resurgence.StokesBound
-- Phase 6n Wave 2b (QCrooks-α; was 6n.δ) Stage 1 substrate: parallel-axiomatization
-- tableau on quantum-Crooks fluctuation theorems. Setup + 4 candidate axiomatizations
-- (Tasaki-TPM, Åberg-coherent, Kafri-Deffner-unital, Kirkwood-Dirac quasiprobability)
-- + Perarnau-Llobet et al. obstruction predicates. Stage-1 ships predicate-level shapes
-- + trivial-scheme well-posedness witnesses (zero sorry); Stage 2-3 + Aristotle ship
-- substantive content + the no-go theorem itself per appendix §5.
import SKEFTHawking.QuantumCrooks.Setup
import SKEFTHawking.QuantumCrooks.Tasaki
import SKEFTHawking.QuantumCrooks.Aberg
import SKEFTHawking.QuantumCrooks.KafriDeffner
import SKEFTHawking.QuantumCrooks.Quasiprobability
import SKEFTHawking.QuantumCrooks.PerarnauLlobet
-- Phase 6n Wave 2b Stage 2-3 substantive lift: the canonical 2-level
-- Perarnau-Llobet counterexample, made concrete. Specializes the parametric
-- no-go to the substantive quantum no-go via direct Matrix (Fin 2) (Fin 2) ℝ
-- computation + the disagreement witness `perarnau_h_disagree`.
import SKEFTHawking.QuantumCrooks.Concrete
-- Phase 6n Wave 2b Stage 2-3 ℂ-extension (Session 10, 2026-05-05):
-- Matrix (Fin 2) (Fin 2) ℂ generalization of the canonical 2-level
-- Perarnau-Llobet substrate. Includes σ_y (genuinely complex Hermitian
-- Hamiltonian) as a non-trivial example, ℂ-form disagreement witness,
-- ℂ-form quantum no-go theorem, and cross-bridge to the ℝ form.
import SKEFTHawking.QuantumCrooks.ConcreteComplex
-- Phase 6n Wave 2c (Crooks-on-analog-Hawking) Stage 1 substrate:
-- HorizonDetailedBalance generalizes IsCrooksRatio to nonlinear entropy-
-- production functionals σ : ℝ → ℝ; bridge to classical Crooks via the
-- σ(W) = β·W special case. GallavottiCohen LDP rate-function symmetry
-- is the long-time limit. Stage 2-3 derives the analog-Hawking spectrum
-- inequality (third Sakharov-style biconditional candidate).
import SKEFTHawking.CrooksAnalogHawking.HorizonDetailedBalance
import SKEFTHawking.CrooksAnalogHawking.GallavottiCohen
-- Phase 6n Wave 2d Stage 1 substrate: Sakharov ↔ horizon-Crooks reformulation.
-- Bundles existing JacobsonThermoGRDarkEnergy.SakharovConditions (Phase 6m
-- Track C substrate) with the new HorizonDetailedBalance predicate (Wave 2c).
-- Concrete witnesses: ³He-A (Jacobson-consistent) and FLS BEC (not).
-- Verlinde-vs-Jacobson distinction preserved at every Lean statement.
import SKEFTHawking.CrooksAnalogHawking.SakharovHorizonCrooks
-- Phase 6n Wave 2d Stage 2-3 substantive biconditional: 4-conjunct
-- horizon-Crooks-side projection of the Sakharov criterion;
-- sakharov_iff_horizon_crooks biconditional theorem proved at the
-- Bool-projection level; ³He-A and FLS BEC specializations.
-- Verlinde-vs-Jacobson distinction preserved at every projection step.
import SKEFTHawking.CrooksAnalogHawking.BiconditionalReformulation
-- Phase 6n Wave 2c Stage 2-3 substantive bundling: third Sakharov-style
-- biconditional candidate. AnalogHawkingEmissionScheme bundles HDB +
-- LDP rate function; monotonicity ↔ GC biconditional shipped at
-- predicate-bundle level (compat_hyp precondition).
import SKEFTHawking.CrooksAnalogHawking.AnalogHawkingBiconditional
-- Phase 6n Wave 2d Stage 4 substantive substrate-level bridge: SKEFTAxioms
-- (Wave 2a algebraic-FDR machinery) at horizon temperature β_H feeds the
-- HorizonDetailedBalance predicate (Wave 2c) via load-bearing Noether
-- entropy density extraction + reflection-positivity. Establishes the
-- substrate-level (not Bool-projection) form of Sakharov ⇒ horizon-Crooks
-- with FDR-pinned σ = β_H · W. Substrate concrete instances: ³He-A
-- substantively Jacobson-consistent under any SKEFTAxioms; FLS BEC NOT
-- (Sakharov-(ii) failure obstructs no matter the SKEFTAxioms).
import SKEFTHawking.CrooksAnalogHawking.SKEFTHorizonBridge
-- Phase 6n Wave 2c Stage 4 substantive substrate-level bridge: SKEFTAxioms
-- machinery to W-form Gallavotti-Cohen rate-function symmetry. Ships the
-- W-form GC predicate (`I(W) - I(-W) = -β·W`), the FDT-pinned linear-response
-- Gaussian rate function (mean = β·σ²/2, variance = σ²) which satisfies
-- W-form GC algebraically for any σ² ≠ 0, the load-bearing-A theorem
-- extracting `c : FirstOrderCoeffs` from `A.dynamical_KMS` for the W-form
-- GC at noise variance σ² = c.i₂, the concrete dissipative substrate
-- witness (firstOrderDissipativeAction with γ₂ > 0 unconditionally yields
-- W-form GC), and the composed Stage-4 substrate (FDR-pinned σ = β·W +
-- Noether-density positivity + W-form GC together via single c extraction).
-- Cross-bridge to existing σ-form GallavottiCohenSymmetry via change of
-- variable σ = β·W and sign flip. Parallels Wave 2d Stage 4 SKEFTHorizonBridge.
import SKEFTHawking.CrooksAnalogHawking.SKEFTGallavottiCohen
-- Phase 6n Wave 1b Stage 3 substrate: SymTFT applicability verdict +
-- discrete-sector predicates. The Stage-2 audit verdict (PartiallyApplicable
-- per direct primary-source fetch of arXiv:2507.05350, Schäfer-Nameki et al.)
-- instantiates 3 ship-able discrete-sector candidates non-vacuously
-- (chiralCentralChargeMod24, Z16AnomalyEta, KMSParityAlternation).
-- Continuous-sector candidates deferred to Phase 6o.
import SKEFTHawking.SymTFTAudit.Applicability
-- Phase 6n Wave 1b Stage 4 cross-bridges: predicate-level connections from
-- the SymTFT discrete-sector candidate predicates to existing program
-- threads (KMSParityAlternation ↔ SecondOrderSK.combined_positivity_constraint;
-- Z16AnomalyEta ↔ Z16AnomalyForcesThetaBar.Z16AnomalyCancels).
-- chiralCentralChargeMod24 cross-bridge deferred (requires Mathlib Witt-group).
import SKEFTHawking.SymTFTAudit.CrossBridges
-- Phase 6n Wave 1b Stage 5 (Session 10, 2026-05-05) project-local
-- Witt-class infrastructure: lifts the Stage-4c arithmetic biconditional
-- (3 ∣ n ↔ 24 ∣ 8·n) to the abelian-group / Witt-invariant level via
-- `WittInvariant := ZMod 24` + `fromChiralCentralCharge : ℤ →+ ZMod 24`
-- AddMonoidHom. Closes the chiralCentralChargeMod24 ↔ Witt-class
-- biconditional at predicate + abelian-group level. Mathlib upstream-PR
-- candidate per `feedback_mathlib_upstream_pr_track_record.md` — full MTC
-- Witt-group infrastructure (Davydov-Müger-Nikshych-Ostrik 2013) remains
-- a multi-year community project; this project-local form captures the
-- chiral-central-charge piece load-bearing for the Schellekens chain.
import SKEFTHawking.SymTFTAudit.WittClass
import SKEFTHawking.HigherOrderSK
import SKEFTHawking.AcousticMetric
import SKEFTHawking.SKDoubling
import SKEFTHawking.SecondOrderSK
import SKEFTHawking.HawkingUniversality
import SKEFTHawking.WKBAnalysis
import SKEFTHawking.CGLTransform
import SKEFTHawking.ThirdOrderSK
import SKEFTHawking.GaugeErasure
import SKEFTHawking.WKBConnection
import SKEFTHawking.ADWMechanism
import SKEFTHawking.ChiralityWall
import SKEFTHawking.VestigialGravity
import SKEFTHawking.FractonHydro
import SKEFTHawking.FractonGravity
import SKEFTHawking.FractonNonAbelian
import SKEFTHawking.FractonFormulas
import SKEFTHawking.KappaScaling
import SKEFTHawking.PolaritonTier1
import SKEFTHawking.SU2PseudoReality
import SKEFTHawking.FermionBag4D
import SKEFTHawking.LatticeHamiltonian
import SKEFTHawking.GoltermanShamir
import SKEFTHawking.TPFEvasion
import SKEFTHawking.KLinearCategory
import SKEFTHawking.SphericalCategory
import SKEFTHawking.FusionCategory
import SKEFTHawking.FusionExamples
import SKEFTHawking.VecG
import SKEFTHawking.DrinfeldDouble
import SKEFTHawking.GaugeEmergence
import SKEFTHawking.SO4Weingarten
import SKEFTHawking.WetterichNJL
import SKEFTHawking.VestigialSusceptibility
import SKEFTHawking.QuaternionGauge
import SKEFTHawking.GaugeFermionBag
import SKEFTHawking.MajoranaKramers
import SKEFTHawking.HubbardStratonovichRHMC
import SKEFTHawking.OnsagerAlgebra
import SKEFTHawking.OnsagerContraction
import SKEFTHawking.Z16Classification
import SKEFTHawking.SMGClassification
import SKEFTHawking.SteenrodA1
import SKEFTHawking.PauliMatrices
import SKEFTHawking.WilsonMass
import SKEFTHawking.BdGHamiltonian
import SKEFTHawking.GTCommutation
import SKEFTHawking.GTWeylDoublet
import SKEFTHawking.ChiralityWallMaster
import SKEFTHawking.SMFermionData
import SKEFTHawking.Z16AnomalyComputation
import SKEFTHawking.GenerationConstraint
import SKEFTHawking.HiddenSectorClassification
import SKEFTHawking.HiddenSectorMixedCharge
import SKEFTHawking.CosmologicalConstant
import SKEFTHawking.QuasiOneDReduction
import SKEFTHawking.DrinfeldCenterBridge
import SKEFTHawking.VecGMonoidal
import SKEFTHawking.ToricCodeCenter
import SKEFTHawking.S3CenterAnyons
import SKEFTHawking.D2Formula
import SKEFTHawking.CenterEquivalenceZ2
import SKEFTHawking.CenterFunctorZ2
import SKEFTHawking.CenterFunctorZ2Equiv
import SKEFTHawking.DrinfeldDoubleAlgebra
import SKEFTHawking.DrinfeldDoubleRing
import SKEFTHawking.DrinfeldEquivalence
import SKEFTHawking.WangBridge
import SKEFTHawking.ModularInvarianceConstraint
import SKEFTHawking.RokhlinBridge
import SKEFTHawking.QNumber
import SKEFTHawking.Uqsl2
import SKEFTHawking.Uqsl2Hopf
import SKEFTHawking.Uqsl3
import SKEFTHawking.Uqsl3Hopf
import SKEFTHawking.SU2kFusion
import SKEFTHawking.SU3kFusion
import SKEFTHawking.Uqsl2Affine
import SKEFTHawking.SU2kSMatrix
import SKEFTHawking.RestrictedUq
import SKEFTHawking.RibbonCategory
import SKEFTHawking.E8Lattice
import SKEFTHawking.VerifiedJackknife
import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.SpinBordism
import SKEFTHawking.TetradGapEquation
import SKEFTHawking.ScalarRungInterpretation
import SKEFTHawking.BHLGaugeEmbedding
import SKEFTHawking.MajoranaRung
import SKEFTHawking.NeutrinoMixing
import SKEFTHawking.MajoranaRungDecoupling
import SKEFTHawking.MajoranaRungSMG
import SKEFTHawking.QuarkRungScalarChannel
import SKEFTHawking.QuarkRungMajoranaChannel
import SKEFTHawking.LightQuarkHierarchyFallthrough
import SKEFTHawking.CKMApexSubstrateConstraint
import SKEFTHawking.CPPhaseSubstrate
import SKEFTHawking.EWPhaseTransition
import SKEFTHawking.EWBaryogenesisChiralityWall
import SKEFTHawking.QSqrt2
import SKEFTHawking.QSqrt5
import SKEFTHawking.SU2kMTC
import SKEFTHawking.FibonacciMTC
import SKEFTHawking.Uqsl2AffineHopf
import SKEFTHawking.VerifiedStatistics
import SKEFTHawking.KerrSchild
import SKEFTHawking.CoidealEmbedding
import SKEFTHawking.RepUqFusion
import SKEFTHawking.CenterFunctor
import SKEFTHawking.StimulatedHawking
import SKEFTHawking.QCyc16
import SKEFTHawking.QCyc5
import SKEFTHawking.IsingBraiding
import SKEFTHawking.QSqrt3
import SKEFTHawking.QLevel3
import SKEFTHawking.TQFTPartition
import SKEFTHawking.FigureEightKnot
import SKEFTHawking.EmergentGravityBounds
import SKEFTHawking.SPTClassification
import SKEFTHawking.GaugingStep
import SKEFTHawking.FermiPointTopology
import SKEFTHawking.PolyQuotQ
import SKEFTHawking.PolyQuotOver
import SKEFTHawking.QCyc3
import SKEFTHawking.QCyc15
import SKEFTHawking.QCyc15SqrtPhi
import SKEFTHawking.SU3k2SMatrix
import SKEFTHawking.SU3k2FSymbols
import SKEFTHawking.QuantumGroupGeneric
import SKEFTHawking.TemperleyLieb
import SKEFTHawking.JonesWenzl
import SKEFTHawking.SurgeryPresentation
import SKEFTHawking.WRTInvariant
import SKEFTHawking.QuantumGroupHopf
import SKEFTHawking.QuantumGroupCoproduct
import SKEFTHawking.QuantumGroupAntipode
import SKEFTHawking.KMatrixAnomaly
import SKEFTHawking.WRTComputation
import SKEFTHawking.FibonacciBraiding
import SKEFTHawking.IsingGates
import SKEFTHawking.SPTStacking
import SKEFTHawking.TPFDisentangler
import SKEFTHawking.QCyc5Ext
import SKEFTHawking.FibonacciQutrit
import SKEFTHawking.FibonacciUniversality
import SKEFTHawking.FibonacciQutritUniversality
import SKEFTHawking.StringNet
import SKEFTHawking.VillainHamiltonian
import SKEFTHawking.KacWaltonFusion
import SKEFTHawking.FPDimension
import SKEFTHawking.MugerCenter
import SKEFTHawking.A1Ring
import SKEFTHawking.A1Resolution
import SKEFTHawking.A1Ext
import SKEFTHawking.ExtBordismBridge
import SKEFTHawking.ChangeOfRings
import SKEFTHawking.FKGappedInterface
import SKEFTHawking.ModularityTheorem
import SKEFTHawking.InstantonZeroModes
import SKEFTHawking.DiracFluidMetric
import SKEFTHawking.GrapheneHawking
import SKEFTHawking.DiracFluidSK
import SKEFTHawking.GrapheneNoiseFormula
import SKEFTHawking.DiracFluidWKB
import SKEFTHawking.VestigialInflationNoGo
import SKEFTHawking.QuantumGroupInstantiation
import SKEFTHawking.QuantumGroupMeta
import SKEFTHawking.FractonDarkMatter
import SKEFTHawking.FangGuTorsionDM
import SKEFTHawking.DarkSectorSynthesis
import SKEFTHawking.SFDMMergerForecast
import SKEFTHawking.FermiHubbardDimer
import SKEFTHawking.GibbsDuhemTheorem
import SKEFTHawking.QTheoryNoGoTheorem
import SKEFTHawking.DESIComparison
import SKEFTHawking.DarkEnergyObstructionPrinciple
import SKEFTHawking.CondensedMatterAnalog
import SKEFTHawking.VestigialMapping
import SKEFTHawking.VestigialEOS
import SKEFTHawking.ClassificationTableDark
import SKEFTHawking.CausalSetDarkEnergy
import SKEFTHawking.EntropicGravityDarkEnergy
import SKEFTHawking.JacobsonThermoGRDarkEnergy
import SKEFTHawking.DarkSectorClassificationExtension
import SKEFTHawking.LinearizedEFE
import SKEFTHawking.HeatKernelExpansion
import SKEFTHawking.HigherCurvatureStructure
import SKEFTHawking.NonlinearDiffInvariance
import SKEFTHawking.NonlinearEFE
import SKEFTHawking.MicroscopicCoefficientMatch
import SKEFTHawking.EinsteinCartanExtension
import SKEFTHawking.FLRWDynamics
import SKEFTHawking.GravitationalWaves
import SKEFTHawking.BHEntropyMicroscopic
import SKEFTHawking.BHThermodynamicsFourLaws
import SKEFTHawking.EnergyConditions
import SKEFTHawking.Curvature
import SKEFTHawking.EinsteinTensor
import SKEFTHawking.ExactSolutions
import SKEFTHawking.ADMFormalism
import SKEFTHawking.TetradFormalism
import SKEFTHawking.CausalStructure
import SKEFTHawking.PenroseSingularity
import SKEFTHawking.HawkingPenroseSingularity
import SKEFTHawking.AreaTheorem
import SKEFTHawking.NoHairTheorem
import SKEFTHawking.CauchyProblem
import SKEFTHawking.LaplaceMethod
import SKEFTHawking.EquivalencePrinciple
import SKEFTHawking.BBN
import SKEFTHawking.CosmologicalPerturbations
import SKEFTHawking.CenterSymmetryConfinement
import SKEFTHawking.ChiralSSB_QCD
import SKEFTHawking.CFLChiralLagrangian
import SKEFTHawking.StrongCPTopologicalDE
import SKEFTHawking.Z16AnomalyForcesThetaBar
import SKEFTHawking.SubstrateAxion
import SKEFTHawking.SubstrateInstantonSpectrum
import SKEFTHawking.ThetaVacuumFiniteT
import SKEFTHawking.QECHolographyBridge
import SKEFTHawking.RTCasiniHuertaBounds
import SKEFTHawking.RTReplicaTrickOnMTC
import SKEFTHawking.CasiniHuertaModularHamiltonianMTC
import SKEFTHawking.ScramblingTimeQuantitative
import SKEFTHawking.HolographicCFunctionMTC
import SKEFTHawking.LorentzianMetric
import SKEFTHawking.RiemannianConnection
import SKEFTHawking.RiemannCoordinate
import SKEFTHawking.RiemannDifferentialBianchi
import SKEFTHawking.BundleRiemannAux
import SKEFTHawking.BundleRiemann
import SKEFTHawking.LeviCivita
import SKEFTHawking.LorentzianBundle
import SKEFTHawking.NullGeodesic
import SKEFTHawking.RaychaudhuriEquation
import SKEFTHawking.FocalPoint
import SKEFTHawking.PenroseSingularityCurveTheoretic
import SKEFTHawking.RiccatiComparison
import SKEFTHawking.MazurSigmaModelRigidity
import SKEFTHawking.HawkingPenroseSingularityCurveTheoretic
import SKEFTHawking.AreaTheoremCurveTheoretic
import SKEFTHawking.WaveEquation1D

/-!
# SK-EFT Hawking Paper: Lean Formalization

Formal verification of mathematical structures underlying the paper
"Dissipative EFT Corrections to Analog Hawking Radiation."

## Three Structures

- **Structure A (AcousticMetric):** The acoustic metric theorem — for a barotropic,
  irrotational, inviscid fluid, the linearized phonon EOM is equivalent to the
  massless Klein-Gordon equation on a curved background with metric determined
  algebraically by (v, c_s, ρ).

- **Structure B (SKDoubling):** The Schwinger-Keldysh doubling structure — given
  an action with global U(1) symmetry, the SK doubled action satisfying the
  three axioms (normalization, positivity, KMS) is uniquely determined at each
  derivative order up to transport coefficients.

- **Structure C (HawkingUniversality):** Hawking temperature universality — for
  any UV modification of the phonon dispersion satisfying adiabaticity, the
  effective temperature satisfies T_eff = T_H(1 + O(T_H/Λ)²).

## Methodology

Blueprint+sorry: algebraic identities are fully formalized; PDE well-posedness,
asymptotic analysis, and derivative expansion convergence are left as `sorry`.
The `sorry` gaps are documented and flagged for Aristotle automated filling.
-/
