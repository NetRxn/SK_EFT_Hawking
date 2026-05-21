import SKEFTHawking.Basic
-- Array helper lemmas (bang-indexed ofFn simp lemma) for cyclotomic-substrate
-- symbolic reasoning. Upstream-contribution-quality; gating step for the
-- CommRing QCyc5Ext roadmap (see docs/adrs/ADR-001-commring-qcyc5ext-roadmap.md).
import SKEFTHawking.ArrayHelpers
-- ADR-001 Unit 1b: buildPowerTable static characterisation. Combines with
-- ArrayHelpers (Unit 1a) to dissolve simp opacity in `PolyQuotQ.mulReduce`
-- output; structurally unblocks Path B of the CommRing QCyc5Ext roadmap
-- (Units 2-5).
import SKEFTHawking.PolyQuotQCharacterisation
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
-- Phase 6n Wave 1a.3 Path A — Stage 3 Lean lift (Session 12, 2026-05-05):
-- Closed-form kinematic-dispersive coefficient sequence γ_n^(kin-disp)/γ_1
-- = (-1)^(n-1) · C(2(n-1), n-1) / 16^(n-1); central-binomial bound C(2k,k)
-- ≤ 4^k via Nat.choose_le_two_pow → geometric-rate-1/4 theorem
-- IsGeometric kinDispSeq 1 (1/4); convergence radius 2·Λ_UV. Python
-- counterpart at src/resurgence/bdg_self_energy.py (Session 11).
import SKEFTHawking.Resurgence.KinematicDispersive
-- Phase 6n Wave 1a.3 Path A — Stage 4a Lean lift (Session 13, 2026-05-05):
-- Structural envelope theorem: under the bounded-coupling assumption
-- IsGeometric γ_loop M_loop r_loop, the full γ_n = kinDispSeq + γ_loop is
-- IsGeometric (1 + M_loop) (max (1/4) r_loop), and its Borel transform
-- decays super-geometrically — substrate-level near-definitive Wave 1a.3
-- verdict pending the explicit Beliaev-Galitskii 1959 γ_2^(loop) value.
import SKEFTHawking.Resurgence.LoopEnvelope
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
-- Phase 6n Wave 2b higher-dimensional ℂ generalization (Session 13, 2026-05-05):
-- Block-diagonal embedding of the canonical 2-level Perarnau-Llobet ℂ substrate
-- into Matrix (Sum (Fin 2) T) (Sum (Fin 2) T) ℂ for arbitrary Fintype T —
-- closes the Wave 2b "further ℂ generalization" target listed in the
-- Phase 6n Roadmap recommended-next-up #8. Substantive content: trace +
-- multiplication + diagonal compatibility of the embedding; reduction of
-- embedded averages to 2-level averages; substantive higher-dimensional
-- Perarnau-Llobet no-go theorem perarnau_llobet_no_go_higher_dim.
import SKEFTHawking.QuantumCrooks.HigherDimensional
-- Phase 6n Wave 2b (QCrooks-α) typeclass connections (Session 14, 2026-05-05):
-- Wave 2a → Wave 2b cross-bridge linking SKEFTAxioms substrate to the four
-- Stage-1 axiomatization predicates (Tasaki / Åberg / Kafri-Deffner / Kirkwood-
-- Dirac) via the FDT-pinned linear-response Gaussian work distribution.
-- First non-trivial substantive witnesses for IsTasakiTPMScheme / etc. (the
-- previously-shipped trivialScheme_is_* used the zero distribution).
-- skeft_substrate_yields_TPM_scheme extracts c : FirstOrderCoeffs from
-- A.dynamical_KMS via algebraic FDR; firstOrderDissipative_yields_TPM_scheme
-- ships unconditional concrete witness for γ₂ > 0; closure summary
-- wave_2b_typeclass_connections_closure bundles all four axiomatization
-- predicates simultaneously satisfied by a single MeasurementScheme.
import SKEFTHawking.QuantumCrooks.SKEFTConnection
-- Phase 6n Wave 2b reservoir-coupled / Lindblad-DB forms (Session 14, 2026-05-05):
-- Adds IsReservoirCoupled + IsLindbladDetailedBalance predicates strengthening
-- IsCrooksRatio with non-vacuity at W=0. Trivial zero scheme is NOT reservoir-
-- coupled (substantive separation). Linear-response Gaussian is the first
-- non-trivial witness. Wave 2a → Wave 2b cross-bridge skeft_substrate_yields_-
-- lindbladDB_scheme. Concrete firstOrderDissipativeAction(γ₂>0) witness.
-- Closure summary wave_2b_reservoir_coupled_closure bundles all 4 axiomatization
-- predicates + reservoir-coupling + Lindblad-DB into single MeasurementScheme.
import SKEFTHawking.QuantumCrooks.ReservoirCoupled
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
-- Phase 6n Wave 2c Stage 5 LDP starter (Session 13, 2026-05-05): in-program
-- build of LDP rate-function infrastructure for the linear-response Gaussian
-- substrate. LDPLinearResponseData structure with positivity witnesses;
-- canonical AnalogHawkingEmissionScheme construction; substantive substrate-
-- level monotonicity (σ(W) = β·W ≥ 0 for W ≥ 0) AND W-form GC at β. First
-- concrete substrate-level discharge of the third Sakharov-style biconditional
-- in horizon-Crooks language at the W-form-GC level. Mathlib-upstream-PR
-- target retained for full measure-theoretic LDP machinery.
import SKEFTHawking.CrooksAnalogHawking.LDPLinearResponse
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
-- Phase 6n Wave 1b Stage 5.8 (Session 15, 2026-05-05): Witt-equivalence-via-
-- Drinfeld-center predicate. Lifts the Davydov-Müger-Nikshych-Ostrik 2010
-- (arXiv:1009.2117) categorical characterization of Witt equivalence to
-- Lean substrate using Mathlib's `CategoryTheory.Center`. Establishes
-- `WittEquivalentMTC` as an equivalence relation (refl/symm/trans inherited
-- from Mathlib's Equivalence apparatus) and ships the cross-bridge to
-- integer-level `WittEquivalent` / `WittClass.mk` under a Prop-level
-- central-charge-preservation hypothesis (no new axiom). First step toward
-- the full Witt group of MTCs (continuations: braided equivalence in 5.9,
-- Deligne tensor product as group operation in 5.10, DMNO theorem on
-- pseudo-unitary subclass in 5.11).
import SKEFTHawking.SymTFTAudit.DrinfeldCenter
-- Phase 6n Wave 1b.5.11 (Session 17, 2026-05-05): pseudo-unitary substrate +
-- DMNO 2010 Theorem 5.2 discharge restricted to the pseudo-unitary subclass.
-- `IsPseudoUnitary` predicate at category level + concrete trivial witness;
-- `S² = I` substantive consequence of unitarity + symmetry; restricted
-- hypothesis schema `CentralChargePreservesDrinfeldCenter_pseudoUnitary` with
-- weakening cross-bridges to/from the unrestricted Wave 1b.5.9 form; cross-
-- bridge to integer-mod-24 `WittClass.mk` quotient; closure summary.
import SKEFTHawking.SymTFTAudit.PseudoUnitary
-- Phase 6n Wave 1b.5.10a (Session 18, 2026-05-05): free k-linear envelope
-- of an arbitrary category C, the substrate for Deligne's tensor product
-- C ⊠ D as a Witt-group operation. `FreeKLinear C k` type synonym +
-- `Category` instance built on `Finsupp` morphism k-modules + bilinear
-- composition; `Preadditive` + `Linear k` instances; faithful inclusion
-- `incl : C ⥤ FreeKLinear C k`; universal property `lift : (C ⥤ D) →
-- (FreeKLinear C k ⥤ D)` for k-linear D, with `incl ⋙ lift F = F`.
-- First-session deliverable; continuations: monoidal/braided extension
-- (5.10b-d), Deligne ⊠ proper as quotient (5.10e), and cross-bridge to
-- WittClass via central-charge additivity under ⊠ (5.10g).
import SKEFTHawking.SymTFTAudit.FreeKLinearCategory
-- Phase 6n Wave 1b.5.10b (Session 19, 2026-05-05): morphism-side of the free
-- k-linear monoidal extension. `freeTensorHom` k-bilinear extension of C's
-- `tensorHom` via double-`Finsupp.sum` (analog to Session 18's `freeComp`),
-- with bilinearity helpers, identity-tensor-identity, and the load-bearing
-- interchange law `freeTensorHom (freeComp α β) (freeComp α' β') =
-- freeComp (freeTensorHom α α') (freeTensorHom β β')`. **Partial** Stage 5.10b
-- closure: object-level associator/unitor lifts + pentagon/triangle laws +
-- full `MonoidalCategory (FreeKLinear C k)` instance deferred to follow-on
-- sub-sessions (5.10b.2/5.10b.3).
import SKEFTHawking.SymTFTAudit.FreeKLinearMonoidal
-- Phase 6n Wave 1b.5.10c (Session 21, 2026-05-05): underlying-category construction
-- of the Deligne tensor product `C ⊠ D` of two k-linear categories, defined as the
-- quotient of `FreeKLinear (C × D) k` (Wave 1b.5.10a) by the bilinearity-respecting
-- congruence `DeligneRel C D k`. The `DeligneRel` inductive bakes its `Congruence`
-- closure (refl/symm/trans/comp_left/comp_right) and the additivity/smul-respect
-- hypotheses required by `Quotient.preadditive` / `Quotient.linear` directly into
-- its constructors, so the quotient is a k-linear category by direct Mathlib-
-- substrate transport. `DeligneTensor C D k := CategoryTheory.Quotient (DeligneRel
-- C D k)` (abbrev for typeclass transparency); inherits `Category`/`Preadditive`/
-- `Linear k`. Continuations: 5.10d monoidal lift, 5.10e closure-with-ext,
-- 5.10f braided lift, 5.10g WittClass cross-bridge.
import SKEFTHawking.SymTFTAudit.DeligneTensor
import SKEFTHawking.APSEta.Predicate
import SKEFTHawking.APSEta.BECAcoustic
import SKEFTHawking.APSEta.ADWHorizon
import SKEFTHawking.APSEta.He3A
import SKEFTHawking.APSEta.SymTFTBridge
import SKEFTHawking.APSEta.RegimePartition
import SKEFTHawking.ETH.Predicates
import SKEFTHawking.ETH.ConcreteWitness
import SKEFTHawking.ETH.RefutationTableau
import SKEFTHawking.SoftTheorems.Boostless
import SKEFTHawking.SoftTheorems.Carrollian
import SKEFTHawking.SoftTheorems.EmergentGraviton
import SKEFTHawking.SoftTheorems.DissipativeNoGo
import SKEFTHawking.SoftTheorems.NoiseFloorPrediction
import SKEFTHawking.DoubleCopy.PetrovD
import SKEFTHawking.DoubleCopy.SingleCopy
import SKEFTHawking.DoubleCopy.WeylSpinor
import SKEFTHawking.DoubleCopy.BCJNoGo
import SKEFTHawking.DoubleCopy.PolaritonCrossBridge
import SKEFTHawking.Schellekens.SpinBordism
import SKEFTHawking.Schellekens.AnomalyPolynomial
import SKEFTHawking.Schellekens.ModularInvariance
import SKEFTHawking.Schellekens.NiemeierLattice
import SKEFTHawking.Schellekens.HolomorphicVOAc24
import SKEFTHawking.Schellekens.Chain
import SKEFTHawking.Itô.StochasticIntegral
import SKEFTHawking.Itô.QuadraticVariation
import SKEFTHawking.Itô.Semimartingale
import SKEFTHawking.Itô.ItoIsometry
import SKEFTHawking.Itô.ItoLemma
import SKEFTHawking.Itô.Novikov
import SKEFTHawking.LDP.CramerIID
import SKEFTHawking.LDP.Sanov
import SKEFTHawking.LDP.Contraction
import SKEFTHawking.LDP.CramerLowerBound
import SKEFTHawking.LDP.Varadhan
import SKEFTHawking.LDP.LDPCompatibleSKEFT
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
-- Wave 1.D.4 (f) Phase 1.2 substrate: hand-rolled 13×13 matrix type over
-- Q(ζ₅, √φ), Mat5K analog for the 6-strand Fibonacci fusion space
-- (5-dim c=1 sector + 8-dim c=τ sector = 13-dim total). Phase 1.2
-- (this commit) ships Mat13K_5Ext + monoid laws + smoke tests;
-- Phase 1.3 ships the σ_1..σ_5 generator matrices that populate it.
import SKEFTHawking.Mat13K5Ext
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
import SKEFTHawking.CNOTBraidTQSim
-- Phase 6p Wave 2d.2-followup (2026-05-12): Matrix Taylor remainder bound.
-- In-tree substrate ship — Sub-lemma A of the Dawson-Nielsen Lemma 3 discharge
-- plan. Lifts scalar `Complex.norm_exp_sub_sum_le_exp_norm_sub_sum` to the
-- matrix algebra `Matrix (Fin d) (Fin d) ℂ` (linftyOp norm). 254 LoC, zero
-- axioms, zero sorries. Consumed by MatrixBCH.matrix_exp_order3_bound_hermitian.
import SKEFTHawking.MatrixTaylor
-- Phase 6p Wave 2d.2 (2026-05-12): Dawson-Nielsen Lemma 3 order-2 BCH
-- cubic-remainder bound for matrix exponentials. Strictly-weaker analytic
-- axiom replacing the retired sk_axiom_Dawson_Nielsen (Wave 2b.2). First-
-- formalization-territory across all proof assistants. Wave 2d.2-followup
-- (2026-05-12 PM) ships Sub-lemma A (matrix Taylor remainder) + Sub-lemma C
-- kernel (Hermitian commutator norm bound) in-tree; Sub-lemma B (four-fold
-- product expansion ~150 LoC) remains as the residual gap behind the axiom.
import SKEFTHawking.MatrixBCH
-- Phase 6p Wave 2d.4 (2026-05-12): ε-net base case + UniversalGateSet
-- substrate for the constructive Solovay-Kitaev discharge.
import SKEFTHawking.FKLW.EpsilonNet
-- Phase 6p Wave 2d.5 (2026-05-12): Constructive Solovay-Kitaev refinement.
-- SolovayKitaevWithLengthBound predicate (substantive D-N length bound)
-- and bridges from ClosureDenseProp. Companion to FKLW.SolovayKitaev's
-- length-bound-free constructive theorem.
import SKEFTHawking.FKLW.SolovayKitaevConstructive
-- Phase 6p Wave 2c.4c (2026-05-12): Aharonov-Arad Bridge constructive
-- content. Substantive bridging lemma `LieSpan_implies_bridge_exists`
-- (axiom-free; d ≥ 2): the strong LieSpanProp forces existence of a braid
-- with non-zero off-diagonal image entry. Closes the gap between the
-- strong LieSpanProp and the natural Aharonov-Arad BridgeHypothesis modulo
-- the externally-supplied `image_infinite` witness. Pipeline Invariant #15
-- compliant: zero new axioms. The substantive Bridge Lemma 4.1 + 6.1/6.2
-- iteration discharge is a Wave 2c.4a.full follow-up.
import SKEFTHawking.FKLW.AharonovAradBridgeProof
-- Phase 6p Wave 2c.4a-substrate (2026-05-12): Mathlib-grade topological
-- substrate for SU(d) and U(d). `IsCompact` on the carrier sets plus
-- `CompactSpace` instances on the Submonoid-coerced subtypes for any
-- `d : ℕ`. Pure linear-algebra-and-topology proof (entry-modulus ≤ 1
-- inside compact d×d-bounding box; closed as preimage of {1} under
-- continuous M ↦ M Mᴴ; closed-of-compact ⇒ compact). Zero new axioms;
-- Mathlib-PR-shaped.
import SKEFTHawking.FKLW.SpecialUnitaryTopology
-- Phase 6p Wave 2c.4a-substrate-PathConnected (2026-05-12): the companion
-- ship adding `PathConnectedSpace` + `ConnectedSpace` instances on
-- `Matrix.unitaryGroup` and `Matrix.specialUnitaryGroup`. Routes through
-- Mathlib's `Unitary.instLocPathConnectedSpace` on `CStarMatrix` +
-- phase-shift construction + finite-spectrum avoidance (via
-- `Matrix.finite_spectrum`) + det-correction for SU(d). The substantive
-- analytical content for Aharonov-Arad Lemma 6.1 vector transport.
-- Zero new axioms; Mathlib-PR-shaped.
import SKEFTHawking.FKLW.SpecialUnitaryPathConnected
-- Phase 6p Wave 2c.4a-FULL (2026-05-12): substantive Aharonov-Arad Bridge
-- Lemma iteration substrate. Ships
-- `liespan_not_implies_dense_counterexample` (proves the original Wave 2c.4
-- `bridge_axiom_FKLW_general` was unsound), constructive d ∈ {0, 1}
-- discharges for the sound `DenseInSpecialUnitary` predicate, and the sound
-- residual `bridge_axiom_FKLW_unitary_general` axiom (2 ≤ d + unitary ρ).
-- The unsound `bridge_axiom_FKLW_general` is now gone from
-- `AharonovAradBridge.lean` (Wave 2c.4a-cleanup) and the live FKLW path
-- routes exclusively through this module's `bridge_FKLW_unitary` theorem.
import SKEFTHawking.FKLW.AharonovAradBridgeIteration
-- Phase 6p Wave 2c.4a-R4.1 (2026-05-13): infinite-order witness infrastructure
-- for `h_inf : (Set.range ρ_hom).Infinite` discharge of the amended
-- `aa_residual_interior_at_one_for_hom` axiom. Structural lemmas
-- (`matrix_no_pow_eq_one_of_eigenvalue_not_rootOfUnity`,
-- `not_finOrder_of_eigenvalue_not_rootOfUnity`,
-- `complex_exp_not_root_of_unity`) factor any future Fibonacci
-- eigenvalue-witness work; plus a concrete `BraidGroup 3 →* SU(2)`
-- MonoidHom `demo3StrandRep` with infinite-cyclic image (validates
-- the discharge path end-to-end; does NOT satisfy `LieSpanProp` —
-- combined-with-LieSpan Fibonacci witness is R4.2+).
import SKEFTHawking.FKLW.FibRepInfiniteOrder
-- Phase 6p Wave 2c.4a-R5.1 (2026-05-13): axiom-free topological substrate
-- for the constructive discharge of `aa_residual_interior_at_one_for_hom`.
-- Ships `one_accPt_of_infinite_closed_subgroup` (generic compact-group
-- topology: infinite closed subgroup ⇒ 1 is an accumulation point) and
-- the FKLW specialization `accPt_one_in_topClosure_of_hom`. The full AA
-- discharge requires BCH cubic-bound K·δ³ (deferred — substrate gap).
import SKEFTHawking.FKLW.AharonovAradLemma6
-- Phase 6p Wave 2c.4a-R4.2.a (2026-05-13): concrete Fibonacci 3-strand SU(2)
-- representation substrate (complex-matrix layer). Ships R-eigenvalues
-- R1_C/Rtau_C as exp(-4πi/5)/exp(3πi/5) with unit-modulus proofs, golden
-- ratio φ_C with φ² = φ + 1, and the F-matrix involution F²=I. Substrate
-- for R4.2.b (σ_1, σ_2, YB), R4.2.c (MonoidHom), R4.2.d (density).
import SKEFTHawking.FKLW.FibSU2Rep
-- Phase 6p Wave 2c.4a-R4.2.d.1 (2026-05-13): Fibonacci SU(2) density Phase D1
-- — structural facts about σ_Fib_{1,2}_SU. Ships powers/orders, non-commutation,
-- trace invariants, plus `fibonacci_density_conditional` framing the residual
-- hypothesis for full constructive density discharge.
import SKEFTHawking.FKLW.FibSU2Density
-- Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-A (2026-05-19, session 35):
-- Foundational Lie algebra substrate 𝔰𝔲(2) as traceless skew-Hermitian 2x2
-- complex matrices. Ships Matrix.IsSkewHermitian + tracelessSkewHermitian
-- ℝ-submodule + Pauli anti-Hermitian generators (i·σ_x, i·σ_y, i·σ_z).
-- Mathlib4-PR-quality general substrate.
import SKEFTHawking.FKLW.SU2LieAlgebra
-- Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-B (2026-05-19, session 36):
-- Matrix exponential substrate. Ships Matrix.IsSkewHermitian.exp_mem_unitaryGroup
-- (exp of skew-Hermitian is unitary, via exp_conjTranspose + exp_add_of_commute
-- + exp_zero) + expAmbient alias + expAmbient_zero. Mathlib4-PR-quality
-- companion to existing Matrix.IsHermitian.exp.
import SKEFTHawking.FKLW.SU2MatrixExp
-- Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-C (2026-05-19, session 37):
-- IFT-derived local-diffeo at identity. Ships expAmbient_hasStrictFDerivAt_zero
-- + expAmbient_hasStrictFDerivAt_zero_equiv (equivalence form for IFT API) +
-- expAmbient_map_nhds_zero (map exp (𝓝 0) = 𝓝 1) + expAmbient_image_nhds_zero_subset_nhds_one
-- (consumer-friendly: every nbhd 0 contains pre-image of nbhd 1).
-- Mathlib4 IFT (HasStrictFDerivAt.toOpenPartialHomeomorph + map_nhds_eq_of_equiv) applied.
import SKEFTHawking.FKLW.SU2LocalDiffeo
-- Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-D (2026-05-19, session 38):
-- Architectural composition layer. Ships closure_eq_univ_from_subset_exp_image
-- — the conditional bridge from `exp '' U ⊆ H (in SU(2))` to `closure H = univ`.
-- Composes Cartan-C IFT + Subtype.val continuity + mem_interior_iff_mem_nhds +
-- closure_eq_univ_of_one_mem_interior. Plus H_Fib specialization.
import SKEFTHawking.FKLW.SU2InteriorBridge
-- Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer E (2026-05-19, session 39):
-- Final Fibonacci density theorem composition. Ships
-- fibonacci_density_from_exp_image_subset — conditional on the BCH-spanning
-- witness hypothesis (exp '' U ⊆ H_Fib for some open U ∋ 0), produces
-- DenseInSpecialUnitary 3 2 ρ_Fib_SU2. Direct composition of Cartan-D
-- + H_Fib_eq_top_iff_closure_eq_univ + fibonacci_density_from_H_Fib_eq_top.
import SKEFTHawking.FKLW.FibonacciDensityConditional
-- Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer F.13 (FibSU2LieBundle, session 48):
-- bridges general SU2LieAlgebra Ad-action API (F.9-F.12) to σ_Fib_*_SU-specific
-- 3-bundle. Ships σ_Fib_lie_bundle X = (X, Ad(σ_Fib_1)X, Ad(σ_Fib_2)X) + closure
-- of each component in 𝔰𝔲(2) + pauliDet shortcut. Substrate for F.14+: showing
-- the 3-bundle's pauliDet is non-zero generically (via Layer F.8 Cramer-rule
-- lin-indep) closes the spanning argument.
import SKEFTHawking.FKLW.FibSU2LieBundle
-- Phase 6p Wave 2d.3-followup (2026-05-14): qubit Bloch-sphere balanced commutator
-- (D-N Lemma 2 §4.1 Eq. 10-13). Ships `qubit_balanced_commutator_z_axis` —
-- the substantive Z-axis-case existence of F, G hermitian with ‖F‖, ‖G‖ ≤
-- √(θ/2) and F*G - G*F = -i·H, for H = θ•σ_z. Construction: F := √(θ/2)•σ_y,
-- G := √(θ/2)•σ_x. Pauli substrate (σ_x, σ_y, σ_z + comm_σ_x_σ_y) reused
-- from `PauliMatrices.lean`. General-axis case predicate scaffold for
-- Wave 2d.3-followup-general. Zero new axioms.
import SKEFTHawking.FKLW.QubitBalancedCommutator
-- Phase 6p Wave 2d.5-followup-full (Z-axis ship, 2026-05-14): substantive
-- single-step Dawson-Nielsen refinement for the qubit Z-axis case. Composes
-- `QubitBalancedCommutator.balanced_commutator_z_core` (Wave 2d.3-followup)
-- with `MatrixBCHCubic.bch_order_2_cubic_thm` (Wave 2d.2-followup-R5.2b).
-- Headline: `dn_lemma3_z_axis` — `‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - exp(iH)‖
-- ≤ 320·(θ/2)^{3/2}` for the explicit construction F = √(θ/2)·σ_y,
-- G = √(θ/2)·σ_x, H = θ·σ_z, ∀ θ ∈ [0, 1]. Full SU(2) recursion + ε-net
-- base case deferred to follow-up sub-waves. Zero new axioms.
import SKEFTHawking.FKLW.SKZAxisStep
-- Phase 6p Wave 3a.2.2c-followup (2026-05-14): split-braid Frobenius
-- infrastructure for the Rouabah 30-crossing Hadamard. Ships
-- `fibRep3Qubit_rouabah_eq_split` — the substantive structural lemma
-- factoring `fibRep3Qubit rouabah_hadamard` into a 15-deep prefix +
-- 15-deep foldl continuation via `List.foldl_append` (NO Mat2K_40_Ext
-- monoid laws required). Plus `RouabahHadamardFrobValue` predicate +
-- biconditional reducing the full-form discharge to the split-form.
-- Final ε-discharge (Python-precomputed QCyc40Ext literal + QCyc40Ext
-- real-projection ordering) deferred to follow-up sub-wave. Zero new axioms.
import SKEFTHawking.FKLW.RouabahSplitBraid
-- Phase 6p Wave 2c.4a-R4.2.d.4.3.d.1 (2026-05-14): Cartan substrate / identity-
-- component infrastructure for the formal `H_Fib = ⊤` discharge. Ships generic
-- §1 substrate (closed subgroup of compact T1 group + DiscreteTopology ⇒
-- Finite; Finite ⇒ trivial identity component) + `H_Fib` specialization
-- (`H_Fib_idComponent : Subgroup H_Fib`, finite ⇒ trivial) + dichotomy
-- headlines (`H_Fib_dichotomy_discrete_or_accPt` composing D4.3.a with R5.1;
-- `H_Fib_idComponent_ne_bot_implies_infinite` contrapositive). Cartan's
-- closed-subgroup theorem + 1-parameter subgroup theorem + maximal-torus
-- classification (D4.3.d.2+) remain Mathlib4 v4.29.0 gaps. Zero new axioms.
import SKEFTHawking.FKLW.CartanSubstrate
-- Phase 6p Wave 2c.4a-R4.2.d.R5.4 Cartan strengthening (2026-05-21):
-- Von Neumann 1-parameter subgroup theorem for SU(2) — discharges the
-- strengthened gap-#2 predicate `OneParamSubgroupFromAccPt_SU2`
-- (defined in CartanSubstrate §4.7). This ship §1: local matrix
-- logarithm `su2Log` extracted from existing IFT substrate
-- (Mathlib-upstream-PR-quality). Subsequent ships: §2 `su2Log h ∈ su(2)`,
-- §3 von Neumann construction, §4 discharge. Zero new axioms.
import SKEFTHawking.FKLW.OneParameterSubgroupSU2
-- Phase 6p Wave 2d.2-followup-R5.2.1 (2026-05-13): order-2 Taylor polynomial
-- product algebraic infrastructure (BCH cubic-bound prep). Ships `T2pos`,
-- `T2neg`, `bchPolyRem`, `bchPoly_decomp`. The cubic norm bound
-- `‖bchPolyRem F G‖ ≤ C·δ³` is deferred (R5.2a, multi-session) and is the
-- load-bearing gate for the cubic upgrade of `bch_order_2_thm` (currently
-- linear `200·δ`), which in turn gates the AA Bridge Lemma 6.1
-- quadratic-shrinkage iteration.
import SKEFTHawking.MatrixBCHCubic
-- Phase 6p Wave 1c (2026-05-12): MeasureTheory-grounded Bernoulli-product
-- noise model. BernoulliProductModel structure + bridge to abstract
-- LocalStochasticNoise; joint-failure probability ε^k EXACT (not just upper
-- bound) under per-location-independence semantics. Load-bearing AGP-
-- compatibility check at k=2 (the recursion-rate exponent). Zero new axioms.
import SKEFTHawking.FaultTolerance.NoiseModelMT
-- Phase 6p Wave 3a.2.2a (2026-05-12): QCyc40Ext = Q(ζ₄₀, √φ) — degree-32
-- non-cyclotomic extension field substrate for Fibonacci F-matrix off-
-- diagonal √φ entry. Required because Q(√φ)/Q is non-abelian D₄
-- (Kronecker-Weber obstruction; the roadmap's "√φ → phi" placeholder
-- mapping was incorrect). Multiplication via (a+bw)(c+dw) = (ac+bd·φ)+(ad+bc)w.
import SKEFTHawking.QCyc40Ext
-- Phase 6p Wave 3a.2.2 (2026-05-12): Fibonacci 3-strand qubit-sector
-- representation over Q(ζ₄₀, √φ); load-bearing F² = I + Yang-Baxter
-- braid relation σ₁σ₂σ₁ = σ₂σ₁σ₂ verified by native_decide on Mat2K_40_Ext.
-- Substrate for explicit Rouabah Hadamard ε-discharge (full 30-deep
-- native_decide deferred to 3a.2.2c-followup).
import SKEFTHawking.RouabahExplicit
-- Phase 6p Wave 3a.2.3c (2026-05-12): Externally-compiled (Python brute-
-- force beam search via `scripts/phase6p_tgate_compiler.py`) Fibonacci
-- 3-strand T-gate braid. First Fibonacci T-gate braid published anywhere
-- per Wave 3a.2.3c DR audit. ε ≈ 7.5e-2 first-attempt; refinement to
-- ε ≤ 10⁻³ via SK-iteration or GA-SK is mechanical (replace braid literal).
-- RE-ENABLED 2026-05-12 PM (Phase 6p Wave 3a.2.3c-substrate-upgrade
-- optimization). The original QCyc80 mulReduce compile-time failure
-- was resolved via:
--   1. PolyQuotQ.mulReduceWithTable (Nat.fold instead of Finset.univ.sum,
--      `@[noinline]` to prevent compiler-side inlining blowup).
--   2. QCyc80 as `abbrev := PolyQuotQ 32` (function-backed representation
--      `Fin 32 → ℚ` for lighter DecidableEq vs 32-field struct).
--   3. native_decide algebraic-identity theorems deferred to a separate
--      Verify module (still provable, just compiled on demand).
-- See QCyc80.lean module docstring for full rationale.
import SKEFTHawking.TgateFibBraid
-- Phase 6p Wave 2b.3.2 partial (2026-05-12): Iterated-commutator extension
-- of the block-extended Fibonacci quintet representation. Ships 8 of 24
-- target conjuncts via native_decide on {0,1,2}-block iterated commutators.
-- SUPERSEDED 2026-05-12 by FibonacciQuintetTrueRep.lean (per Wave 2b.3.2-followup
-- DR §5.3 R5: block-extension architecture is not the true 4-strand rep, and
-- the 24-conjunct dim-𝔰𝔲(5) target is structurally unreachable by braiding —
-- the correct target is dim 𝔰𝔲(3) ⊕ 𝔰𝔲(2) ⊕ 𝔲(1) = 12). Retained for legacy
-- linkage only.
import SKEFTHawking.FibonacciQuintetUniversalityExt
-- Phase 6p Wave 2b.3.2-followup (2026-05-12): TRUE 4-strand Fibonacci
-- representation on Mat5K over ℚ(ζ₅, √φ) per Lit-Search/Phase-6p/Phase 6p
-- Wave 2b.3.2-followup — HZBS Fig 4 .md (DR returned 2026-05-12). Ships
-- σ₁/σ₂/σ₃ true 4-strand matrices, block-diagonality theorems, Yang-Baxter
-- + far-commutativity, Pentagon-equation corollary, and 12-conjunct
-- structurally-honest spanning closure for 𝔰𝔲(3) ⊕ 𝔰𝔲(2) ⊕ 𝔲(1) (DR §5.3 R5).
import SKEFTHawking.FibonacciQuintetTrueRep
-- Wave 1.D.4 (f) Phase 1.3 (2026-05-17): TRUE 6-strand Fibonacci representation
-- on Mat13K_5Ext over ℚ(ζ₅, √φ) per DR Phase 6p Wave 3a.2.3b (HZBS Fig 15 /
-- Tounsi 2023 §3). Ships σ_1..σ_5 + σ_1⁻¹..σ_5⁻¹ true 6-strand matrices
-- (230 nonzero entries across 5 forward + 5 inverse, all closed-form
-- Q(ζ₅, √φ) elements) + 10 inverse-identity theorems via native_decide.
-- Public-side substrate for the 280-letter 6-strand CNOT braid word downstream.
import SKEFTHawking.FibonacciSextetTrueRep

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
