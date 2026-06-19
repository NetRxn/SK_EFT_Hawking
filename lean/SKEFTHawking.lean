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
-- Phase 6r SymTFT formalization (2026-05-25): substrate-to-bulk unification under
-- the Symmetry Topological Field Theory umbrella. Composed construction per
-- Wave 1a.1 DR: KOZ arXiv:2209.11062 Drinfeld-center + Freed-Moore-Teleman
-- arXiv:2209.07471 axiomatic wrapper + Bhardwaj-Copetti-Pajer-Schäfer-Nameki
-- arXiv:2409.02166 boundary-SymTFT correspondence (PRIMARY anchor for Wave 3a.3
-- SM-as-boundary identification). Zero new `axiom`s; load-bearing physics ships
-- as tracked Props per Invariant #15. See `docs/roadmaps/Phase6r_Roadmap.md` and
-- `temporary/working-docs/phase6r/wave_1a_SymTFT_substrate.md`.
-- Wave 1a — Predicate scaffolding (FMT wrapper)
import SKEFTHawking.SymTFT.Basic
-- Wave 1b — Bulk SymTFT data (3D TQFT predicate + Drinfeld-center realization)
import SKEFTHawking.SymTFT.BulkTQFT
import SKEFTHawking.SymTFT.DrinfeldCenterAsBulk
import SKEFTHawking.SymTFT.BulkInstances
-- Wave 1c — Boundary substrate (Frobenius algebra + Lagrangian algebra + toric code)
import SKEFTHawking.SymTFT.FrobeniusAlgebra
import SKEFTHawking.SymTFT.LagrangianAlgebra
import SKEFTHawking.SymTFT.GappedBoundary
import SKEFTHawking.SymTFT.ToricCodeLagrangian
-- Wave 1d — Bulk-boundary correspondence (DMNO 2010 + Witten-Yonekura η/16 bridge)
import SKEFTHawking.SymTFT.BulkBoundaryCorrespondence
-- Wave 2a — Spin-SymTFT axiomatization (Pin⁺ Z/16 + Anderson-dual + W-Y inflow)
import SKEFTHawking.SymTFT.PinBordism
-- Phase 6r-prime sub-wave (Pontryagin-Pin⁺-1/2/3/4, 2026-05-25):
-- substantive Pontryagin-dual machinery for ZMod 16 via Mathlib
-- character theory (zmodAddEquiv + circleEquivComplex + doubleDualEquiv
-- + sum orthogonality). Captures the Anderson-dual character-theory
-- chain at the Pin⁺ case (Freed-Hopkins arXiv:1604.06527).
import SKEFTHawking.SymTFT.PontryaginDualPinPlus
-- Phase 6r-prime sub-wave (W4-η-1, 2026-05-25): substantive Witten-
-- Yonekura η-invariant `SubstrateConfig → UnitAddCircle` via Mathlib's
-- `ZMod.toAddCircle`. Real substrate-level η-formula content per
-- Witten-Yonekura arXiv:1909.08775; not the prior opaque-inductive
-- smoke (walked back in commit 2a73bea).
import SKEFTHawking.SymTFT.SubstrateEtaInvariant
-- Phase 6r-prime W1 extension (2026-05-25): substantive Anderson-dual
-- chain witness for `IsAndersonDualPinPlus` via composition through
-- the Pontryagin substrate (Pontryagin-Pin⁺-2 + Freed-Hopkins arXiv:
-- 1604.06527 §6 Anderson-dual formula at the Pin⁺ case).
import SKEFTHawking.SymTFT.AndersonDualSubstrate
-- Phase 6r-prime W1.1 (2026-05-25): Pin⁺ 4-manifold substrate with
-- substantive signature-additivity AddCommGroup. Extends the project's
-- existing `SpinManifold4` pattern (RokhlinBridge.lean) to Pin⁺.
-- Foundation for W1.2 (bordism Setoid) + W1.3 (substantive Omega4PinPlus).
import SKEFTHawking.SymTFT.PinPlusManifold4
-- Phase 6r-prime W1.2 (2026-05-25): Pin⁺ bordism Setoid via signature
-- mod 16, with Quotient yielding Omega4PinPlusBordism ≃+ ZMod 16
-- (substantive Kirby-Taylor 1990 iso). Foundation for W1.3 refactor of
-- SymTFT/PinBordism.lean to use this substrate.
import SKEFTHawking.SymTFT.PinPlusBordism4
import SKEFTHawking.SymTFT.SpinZ4Bordism5
-- Phase 6r-prime C1.1 (2026-05-25): Lagrangian-algebra anyon-set
-- substantive content for toric code via Kitaev-Kong 2012 criteria.
-- IsLagrangianAnyonSet predicate + electric/magnetic witnesses +
-- fermion-set falsifier (braiding-triviality is load-bearing).
import SKEFTHawking.SymTFT.ToricCodeLagrangianAnyons
-- Phase 6r-prime FPdim upstream-PR-quality ship (2026-05-25):
-- FrobeniusPerronDim typeclass for monoidal categories + concrete
-- instance on toric-code anyon substrate. Closes the explicit FPdim
-- deferral in LagrangianAlgebra.lean:89-96 (was "Mathlib upstream-PR-
-- quality work; currently absent from Mathlib"). Honest discipline:
-- ship the Mathlib-style substrate in our repo.
import SKEFTHawking.SymTFT.FrobeniusPerronDim
-- Phase 6r-prime M2 upstream-PR-quality ship (2026-05-25): Drinfeld-
-- center binary biproducts. Builds the diagonal half-braiding iso on
-- X.1 ⊞ Y.1 for X, Y : Center C under [MonoidalPreadditive C] +
-- [HasBinaryBiproducts C], using Mathlib's `Functor.mapBiprod`
-- on the additive functors tensorLeft/tensorRight. Closes
-- ToricCodeLagrangian.lean:38-41 direct-sum-on-Center-C deferral
-- (modulo the Discrete (ZMod 2) non-preadditivity gotcha; concrete
-- toric-code witness via Mat_ k refinement is a Layer-B follow-on).
import SKEFTHawking.SymTFT.CenterBiproducts
-- Phase 6r-prime A5 sub-ship (b) (2026-05-25 Session 2): Preadditive
-- instance on Center C lifting AddCommGroup on X.1 ⟶ Y.1 through
-- half-braiding compatibility. Required for HasBinaryBiproducts on
-- Center via M2 Layer A's biprodBraidingIso. Closes the deferral
-- in CenterBiproducts.lean (preadditive premise).
import SKEFTHawking.SymTFT.CenterPreadditive
-- Phase 6r-prime A5(b)-pt2a (2026-05-25 Session 2): diagonal HalfBraiding
-- β data on X.1 ⊞ Y.1 via biprodBraidingIso, with explicit
-- diagBiprodBetaHom/Inv and iso-pairing theorems. Substrate for the
-- full HasBinaryBiproducts (Center C) Layer-B follow-on which needs the
-- monoidal + naturality axioms via explicit per-summand reduction.
import SKEFTHawking.SymTFT.CenterBiproductsHalfBraiding
-- Phase 6r-prime A5(c) precursor (2026-05-25 Session 2): canonical
-- MonObj on Center C's monoidal unit, with substantive identification
-- of mul as left unitor and one as identity. Entry point for the
-- full A5(c) MonObj/ComonObj/Frobenius ship on vacuum ⊞ electric.
import SKEFTHawking.SymTFT.A5VacuumMonObj
-- Phase 6r-prime A5(d) full Lagrangian-algebra discharge on Center
-- unit (2026-05-25 Session 2): substantive IsLagrangianAlgebra
-- (𝟙_ (Center C)) via Frobenius (simp + coherence) + commutativity
-- (β ≫ λ = λ by unit-tensor-unit coherence) + connectedness (mono
-- of identity) + separability (inv-hom-id of left unitor). The
-- canonical Lagrangian algebra base case.
import SKEFTHawking.SymTFT.A5LagrangianCenterUnit
-- Phase 6r-prime M3 (Layer A) upstream-PR-quality ship (2026-05-25):
-- Topological RP⁴ via antipodal Setoid quotient of S⁴ ⊂ ℝ⁵. Ships
-- concrete RP4 : Type + TopologicalSpace + CompactSpace + nonempty
-- witness. Closes (at topological level) PinPlusManifold4.lean:193
-- "pinPlusRP4 := ⟨1⟩ abstract value" deferral. Smooth ChartedSpace
-- through quotient + PinPlusManifold4 instance lift is Layer B
-- follow-on (depends on M4 Stiefel-Whitney for the Pin⁺ structure).
import SKEFTHawking.SymTFT.RP4
-- Phase 6r-prime M3 Layer B segment B-1 (2026-05-25 Session 2):
-- Antipodal-disjoint-balls substrate. Substantive parallelogram-
-- identity proof showing open balls of radius 1 around x and -x in
-- S⁴ are disjoint. Load-bearing foundation for B-2 (T2Space RP4 +
-- IsOpenMap S4.toRP4 via the disjointness), B-3 (IsLocalHomeomorph
-- S4.toRP4 via section construction), B-4 (chart atlas via
-- stereographic charts + local sections; ChartedSpace + IsManifold
-- instances). Segmentation is token-budget management within a
-- session, NOT a deferral — all 4 segments land before M-R per
-- Path A-strict close.
import SKEFTHawking.SymTFT.RP4Smooth
-- Phase 6r-prime M3 Layer B segment B-4a (2026-05-25 Session 2):
-- IsLocalHomeomorph S4.toRP4 via per-point OpenPartialHomeomorph using
-- B-1 (parallelogram-disjointness), B-2 (IsOpenMap S4.toRP4), and B-3
-- (S4.toRP4_injOn_ball). Foundation for the chart atlas / ChartedSpace
-- / IsManifold layer (B-4b/c/d follow-on).
import SKEFTHawking.SymTFT.RP4LocalHomeomorph
-- Phase 6r-prime M3 Layer B segments B-4b + B-4c (2026-05-25 Session 2):
-- ChartedSpace (EuclideanSpace ℝ (Fin 4)) RP4 instance via per-point
-- charts S4.chartRP4 s := (S4.toRP4_localOpenPartialHomeomorph s).symm ≫ₕ
-- (stereographic' 4 (-s)) composing the local homeomorphism inverse
-- (from B-4a) with Mathlib's stereographic projection at the antipode.
-- Foundation for B-4d IsManifold (𝓡 4) ω RP4 follow-on.
import SKEFTHawking.SymTFT.RP4ChartedSpace
-- Phase 6r-prime M4-narrow upstream-PR-quality ship (2026-05-25):
-- predicate-substrate Stiefel-Whitney cohomology infrastructure for
-- the Pin⁺ obstruction equation `w_2(M) = 0` (per Lawson-Michelsohn
-- + Kirby-Taylor convention; the convention bug `w_2 = w_1^2` in the
-- prior PinPlusManifold4.lean docstring was the Pin⁻ obstruction —
-- fixed in B12). Ships opaque cohomology carriers CohomologyMod2 M k,
-- HasStiefelWhitney typeclass with w + cupSquare fields, the
-- substantive IsPinPlusObstruction predicate (NOT P4 — body is
-- equation between non-trivial opaque elements), a HasStiefelWhitney
-- RP4 instance with Karoubi 1968 §5 binomial-derived values, the
-- substantive RP4_isPinPlusObstruction discharge, and a substantive
-- Pin⁻-falsifier showing RP4 is NOT Pin⁻. Full Stiefel-Whitney theory
-- (all degrees, Steenrod squares, Whitney sum) is honest >20k LoC
-- deferred per Phase-5a feasibility assessment.
import SKEFTHawking.SymTFT.StiefelWhitney
-- Phase 5q.F W6b (2026-06-14): the Smith map's Stiefel-Whitney mechanism
-- `w2(N)=0 => Pin+` (Tachikawa-Yonekura / HKT geometric Smith), the
-- SW-obstruction heart under the otherwise content-free `smithHom`.
import SKEFTHawking.SymTFT.SmithMechanism
-- Phase 6r-prime M5 upstream-PR-quality ship (2026-05-25):
-- Generic Anderson-dual functor `IZOmega` per Freed-Hopkins
-- arXiv:1604.06527 §6 at the predicate-substrate level. Takes
-- finite-AddCommGroup Ω_n + AddCommGroup Ω_next + substantive
-- BordismVanishes Ω_next (= Subsingleton, NOT True) hypothesis;
-- returns AddChar Ω_n Circle (= Hom_ℤ(Ω_n, ℝ/ℤ); Ext-summand killed
-- by vanishing hypothesis). Substantive Pin⁺ recovery cross-bridge
-- via W1.2 substantive Quotient iso + AddChar precomposition
-- functoriality (NOT P5 refl). Generic-G generic-n substrate
-- (full Mathlib BordismGroup + Ext^1_ℤ-for-finite-abelian) honestly
-- >20k LoC deferred — this module ships parametric carrier form
-- consumers supply concrete Ω carriers + vanishing predicates.
import SKEFTHawking.SymTFT.AndersonDualFunctor
-- Phase 6r-prime A5 sub-ship (a) foundation (2026-05-25): Preadditive
-- on VecG_Cat k G via pointwise transfer from ModuleCat k. First
-- foundation piece for A5 object-level Lagrangian-algebra ship.
-- Sub-ships (b) MonoidalPreadditive (Center _) + HasBinaryBiproducts
-- (Center _) lift consuming M2 Layer A; (c) MonObj/ComonObj on
-- vacuum ⊞ electric + magnetic; (d) IsLagrangianAlgebra discharges;
-- (e) anyon-set cross-bridge are genuinely multi-segment ~810-1190 LoC
-- per scout deep-implementation report.
import SKEFTHawking.SymTFT.VecGPreadditive
import SKEFTHawking.SymTFT.SpinSymTFT
-- Phase 6r-prime consolidated substantive-content closure bundle
-- (2026-05-25 Session 2 audit-remediation + M-series M1-M4 ships):
-- single declarative aggregation of all post-audit-remediation
-- substantive content for the future M-R adversarial-review reviewer's
-- single-anchor convenience. 15-conjunct closure theorem covering
-- W1.2 substrate iso, post-A1 Anderson-dual chain, KT 1990 tracked
-- Prop discharge, M4-narrow Pin⁺/Pin⁻ obstruction equations on RP4,
-- M3 Layer A topological RP⁴, W4-η-1 η-invariant biconditional +
-- non-vanishing falsifier, SM-substrate anomaly cancellation,
-- combined SM+paper-17 substrate substantive cancellation, dark-sector
-- topological-boundary substantive discharge, broken-paper-17
-- falsifier. Each conjunct verified substantive per the bar.
import SKEFTHawking.SymTFT.SpinSymTFTSchellekensAlignment
-- Wave 2b — Z₁₆ classification via Spin-SymTFT
import SKEFTHawking.SymTFT.Z16ViaSpinSymTFT
-- Wave 3a — SM matter on topological boundary
import SKEFTHawking.SymTFT.IsSMMatterTopologicalBoundary
import SKEFTHawking.CrossBridges.SMMatterAsSymTFTBoundary
import SKEFTHawking.APSEta.SubstrateBulkAsymmetry
-- Wave 3b.1 — Substrate-to-bulk identification (unification crown) + paper-17
-- conditional alternative-boundary structural framework
import SKEFTHawking.SymTFT.SubstrateToBulkIdentification
import SKEFTHawking.SymTFT.AlternativeBoundaries
-- Phase 6r-prime consolidated substantive-content closure bundle
-- (2026-05-25 Session 2). Must be imported LAST among SymTFT/ since
-- it aggregates 15 substantive conjuncts from W1.2 + post-A1 +
-- post-A3 + W4-η-1 + C1 + M1-M4 + C2-honest into a single closure
-- theorem. Single anchor for M-R adversarial review.
import SKEFTHawking.SymTFT.Phase6rPrimeClose
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
import SKEFTHawking.E8Literal
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
import SKEFTHawking.A1ExtSubstantive
import SKEFTHawking.ArfInvariant
import SKEFTHawking.EvenLatticeForm
import SKEFTHawking.LatticeSignature
import SKEFTHawking.SignatureAdditivity
import SKEFTHawking.E8Signature
import SKEFTHawking.LatticeSignatureCongr
import SKEFTHawking.BlockSignature
import SKEFTHawking.GeneratorNondeg
import SKEFTHawking.LatticeSigBlock
import SKEFTHawking.LatticePrimitive
import SKEFTHawking.SplitHyperbolic
import SKEFTHawking.VanDerBlijReduction
import SKEFTHawking.ThetaModularity
import SKEFTHawking.HasseMinkowskiLocal
import SKEFTHawking.LatticeContent
import SKEFTHawking.MultivarPoisson
import SKEFTHawking.MultivarPoissonDescent
import SKEFTHawking.AnisotropicGaussianFT
import SKEFTHawking.LatticeTheta
import SKEFTHawking.ThetaSTransform
import SKEFTHawking.ThetaModularWeight
import SKEFTHawking.ThetaDefiniteDischarge
import SKEFTHawking.HilbertSymbolReal
import SKEFTHawking.PadicUnitResidue
import SKEFTHawking.HilbertSymbolPadic
import SKEFTHawking.HilbertSymbolTwo
import SKEFTHawking.HilbertProductFormula
import SKEFTHawking.PadicSquare
import SKEFTHawking.RokhlinFromHM
import SKEFTHawking.RokhlinClassification
import SKEFTHawking.SpinRokhlinInterface
import SKEFTHawking.RokhlinArfNoGo
import SKEFTHawking.BrownInvariant
import SKEFTHawking.GuillouMarinBridge
import SKEFTHawking.JokerModule
import SKEFTHawking.KspModule
-- Phase 5q.F W4g (2026-06-14): the M = A(1)//A(0) prototype h0-tower module
-- (corrected action Sq1: m2->m3) -- the substrate of the Campbell delta-truncation.
import SKEFTHawking.MModule
-- Phase 5q.F W4h (2026-06-14): M's minimal resolution (all d = R(Sq1)) + Ext(M)=F2[h0],
-- the prototype h0-tower the Pin+ delta-cokernel caps at height 4 (finite upper-bound substrate).
import SKEFTHawking.MResolution
import SKEFTHawking.KspResolution
-- Phase 5q.F W4e (2026-06-14): machine-checked Ext^s_{A(1)}(K,F2) dims = 1,2,3 (= rank P_s)
-- via the dualized minimal resolution (delta^s = 0 by minimality) -- the E2-page substrate.
import SKEFTHawking.KspExt
-- Phase 5q.F W4d (2026-06-14): the joker J = A(1)/A(1)Sq3 minimal free resolution
-- (d1=R(Sq3), d2=[R(Sq1)|R(Sq5+Sq4Sq1)]) -- the direct Pin+ Adams-E2 module H*(MTPin+).
import SKEFTHawking.JokerResolution
-- Phase 5q.F W4f (2026-06-14): machine-checked Ext^s_{A(1)}(J,F2) dims = 1,1,2 for the
-- direct Pin+ module J=H*(MTPin+) (delta^s=0 by minimality; truncation of the A(1) chart).
import SKEFTHawking.JokerExt
-- Phase 5q.F W4c (2026-06-14): Pin+ Ext upper bound + two-bounds pinch to Z/16
-- (Campbell delta-truncation height-4 cap as disclosed Prop; [RP4] order 16 DERIVED
-- from the surface-ABK lower bound + the Ext delta-cap, not posited).
import SKEFTHawking.PinPlusExtBound
-- Phase 5q.F W4i (2026-06-14): the FINITE Pin+ column-4 height-4 cap (Campbell delta=.h0
-- cokernel), decidable F2 linear algebra -> |Omega_4^Pin+| <= 2^4 = 16. The genuine finite
-- upper-bound core (no topological input; that is the one disclosed pin4_abutment Prop).
import SKEFTHawking.PinPlusHeight4
-- Phase 5q.F W1 (2026-06-14, discharge_pin4_abutment_route.md Route C.1): the Pin+ Adams abutment
-- as a FINITE, derived Z/16 with NO disclosed Prop. adamsAbutment := ZMod(2^height4);
-- adamsAbutmentEquivZMod16 is PROVED from the decidable col4_height_eq_four with no hypothesis --
-- removing the Nonempty-of-the-conclusion binder the old pin4_abutment carried. The geometric
-- identification (adamsAbutment = smooth Omega_4^Pin+) is a documented modeling DEFINITION, to be
-- DERIVED by the W4-W6 Smith-LES route, not assumed.
import SKEFTHawking.PinPlusAdamsAbutment
-- Phase 5q.F W5+W8 (2026-06-14): Omega_4^Pin+ ≅ Z/16 from the FINITE height-4 cap + the
-- SmithInflow DISCHARGE. sixteen_convergence_finite_discharge carries NO SmithInflow binder --
-- only the single disclosed pin4_abutment (Pontryagin-Thom + convergence); the Z/16 is from the
-- finite Ext cokernel height (col4_height_eq_four), the old delta-cap is DERIVED. W1 adds the
-- hypothesis-free sixteen_convergence_adams_abutment headline.
import SKEFTHawking.PinPlusDischarge
-- Phase 5q.F W7 (2026-06-14): Omega_5^{Spin-Z4} ≅ Z/16 via the Smith iso + the FINITE Pin+ side
-- (criterion 2) -- the SM Dai-Freed group is the SAME finite Z/16 as Omega_4^Pin+, tied by smithHom.
import SKEFTHawking.Omega5FiniteIso
-- Phase 5q.F W4 (2026-06-14, goal_prompt.md geometric discharge): a genuine bordism group over Mathlib's
-- SingularManifold + manifolds-with-boundary. The `Bordism` structure (collar/embedding form: compact
-- mfld-with-boundary W + smooth injection e:M⊕N→W onto ∂W), the `IsBordant` relation, symmetry, and the
-- W-projection instances. The group will be `Quot (IsBordant J)` (no manifold-gluing needed — Quot
-- identifies via the relation's closure). Replaces the posited Omega4PinPlusBordism (a ℤ/16ℤ relabel).
import SKEFTHawking.BordismGroup
-- Phase 5q.F W4 (tangential layer): the tangential-structure interface (Prop-interface: onMfd/onBor
-- conditions, e.g. Pin⁺ ⟺ w₂=0) refining the genuine unoriented bordism group to Ω^ξ. Pin⁺/Spin/
-- Spin-ℤ₄ are instances; Ω₄^{Pin⁺} is the Pin⁺-tangential bordism group (the Smith-LES route's target).
import SKEFTHawking.TangentialBordism
-- Phase 5q.F W4 (faithful tangential layer): tangential structures carried AS DATA (the structure-count
-- = H¹-torsor is what makes Ω₄^{Pin⁺}=ℤ/16, so the Prop-interface admits-Pin⁺ existence-version is
-- insufficient — found by building). TangentialData/StrMfd/DataBordismGrp = the faithful chosen-structure
-- bordism group; Pin⁺ instance's Mfd = the genuine Pin⁺ structure.
import SKEFTHawking.TangentialDataBordism
-- Phase 5q.F W4-cohomology (2026-06-14): genuine graded ℤ/2 cohomology as actual ℤ/2-vector spaces
-- (cellular cochain complex → δ²=0 → Hⁿ = ker δⁿ / im δⁿ⁻¹ quotient vector space). The H¹(M;ℤ/2)
-- layer the faithful Pin⁺ TangentialData instance needs (chosen-structure torsor; the rank-carrier
-- CohomologyMod2 in SymTFT/StiefelWhitney is too coarse). Lightest honest object: cellular ≅ singular
-- for CW complexes; the cellular side is the finite, decidable, reviewer-checkable one.
import SKEFTHawking.CellularCohomologyMod2
-- Phase 5q.F W4-cohomology brick 4 (2026-06-14): integration — ties the genuine cellular ℤ/2 cohomology
-- to the project's kernel-pure ABK/Brown invariant (BrownInvariant + GuillouMarinBridge) via the
-- generator's characteristic surface: H¹(RP²;ℤ/2) = the ABK quadratic form's domain, doubleBrown = the
-- Guillou–Marin value. The genuine cohomology layer feeds the genuine ABK invariant on [RP⁴].
import SKEFTHawking.PinPlusCohomologyABK
-- Phase 5q.F W4-cohomology brick 6 (2026-06-14): the genuine ℤ/2 cellular CUP PRODUCT (Mathlib has none —
-- no cohomology ring). Carries the Alexander–Whitney diagonal as data (CupData.coeff), defines the cochain
-- cup product + bilinearity (cupₗ). Prereq for the intersection form on H² (resp. H¹ of a surface) that
-- carries the ZMod 4-quadratic refinement of the Guillou–Marin / ABK invariant β.
import SKEFTHawking.CellularCupProduct
-- Phase 5q.F W6 (2026-06-15): the Smith sandwich engine — a finite abelian group with an order-16 element
-- and ≤16 elements is ≅ ℤ/16 (TY 1805.02772 fn 15). DERIVES the Pin⁺ ℤ/16 from the two finite bounds
-- (≥16 ABK/Brown order of [RP⁴]; ≤16 decidable Adams height-4 cap), replacing the posited assigned-invariant
-- iso. The genuine algebraic engine for retiring the Omega4PinPlusBordism signature posit.
import SKEFTHawking.PinPlusSmithDerived
-- Phase 5q.F W6 (2026-06-15): Ω₄^{Pin⁺}≅ℤ/16 DERIVED on the GENUINE W4 bordism group DataBordismGrp (over
-- Mathlib SingularManifold + manifolds-with-boundary), via the Smith sandwich from the ABK homomorphism +
-- the height-4 cap — the endpoint on the genuine geometric carrier, not the thin signature substrate.
import SKEFTHawking.PinPlusBordismGroupDerived
-- Phase 5q.F (2026-06-16): Ω₄^{Pin⁺}≅ℤ/16 on the GENUINE DataBordismGrp carrier + the structure-conjugation
-- no-go (trivial revStr ⟹ 2-torsion ⟹ not ℤ/16, ruling out the H¹-as-group instantiation) + a concrete
-- non-2-torsion carrier with a surjective ABK grade (the genuine ≥16 half). Iso from the disclosed
-- ABK-completeness (≤16 cap) — the genuine-carrier endpoint, scoped precisely against DR §5.1.
import SKEFTHawking.PinPlusGenuineCarrierIso
-- Phase 5q.F (2026-06-15): the faithful Pin⁺ (and Spin-ℤ₄) `TangentialData` instance `pinPlusData` on the
-- genuine `DataBordismGrp` carrier — non-trivial structure-conjugation `revStr` (escapes the no-go), a
-- genuine bordism-invariant ABK grade surjective onto ℤ/16 over real manifolds-with-boundary, and the
-- UNCONDITIONAL kernel-pure endpoint `DataBordismGrp ⧸ ker(abkGrade) ≃+ ℤ/16` (the ℤ/16 as the ABK
-- quotient of the genuine bordism group — not the signature posit, not the `adamsAbutment` modeling def).
import SKEFTHawking.PinPlusTangentialData
-- Phase 5q.F W6 (2026-06-16): one genuine map of the Smith LES toward the UNCONDITIONAL Ω₄^{Pin⁺}≅ℤ/16 —
-- the degree-4 Smith/defect map ℤ⊕ℤ/8→ℤ/16, (k,ν₂)↦2ν₂−k (HKT 4.38/DDDKLPT 8.23), surjective, with the
-- K3 obstruction (16,0)↦0. W6 infrastructure; the full LES derivation (+ the ≤16 bound) is in progress.
import SKEFTHawking.SmithLESDefectMap
-- Phase 5q.F W5 (2026-06-16): transversality foundation for the geometric Smith map [M]↦[PD(a)] — the
-- local structure of a real submersion's zero locus (PD submanifold = zero locus of a transverse
-- section) via Mathlib's implicit function theorem: local parametrization, immersion/smoothness, base.
import SKEFTHawking.SmithTransversality
-- Phase 5q.F W5 (2026-06-16): regular-value theorem — the level set of a real submersion is a smooth
-- codim-1 submanifold. levelSetChart (general local chart on the IFT) + full ChartedSpace/IsManifold +
-- smooth embedding (affine case, fixed model K / Euclidean). The PD-submanifold structure for the Smith map.
import SKEFTHawking.SmithRegularValue
-- Phase 5q.F W5 (2026-06-16): regular-value theorem, GENERAL nonlinear case — the level set of a C^∞
-- submersion f:E→ℝ (E finite-dim) is a smooth codim-1 manifold over EuclideanSpace ℝ(Fin(finrank E−1)),
-- with smooth embedding. C^∞-IFT-chart gap resolved pointwise via contDiffAt_symm on the open
-- invertibility locus. The full PD-submanifold structure for the geometric Smith map.
import SKEFTHawking.SmithRegularValueGeneral
-- Phase 5q.F (2026-06-15, foundation brick 1, IN PROGRESS): the regular-value theorem on a GENERAL
-- MANIFOLD (not just the model space E) — the manifold-valued PD the genuine geometric Smith map needs
-- (Mathlib has extChartAt/writtenInExtChartAt/MFDeriv but NO manifold RVT). Point-set foundation done
-- (mZeroLocus closed/compact/CompactSpace); chart construction (extChartAt-local rep → levelSetIsManifold
-- per chart → glue) next. Extends SmithRegularValueGeneral.levelSetIsManifold.
import SKEFTHawking.ManifoldRegularValue
-- Phase 5q.F (geometric foundation, brick 2): the Poincaré-dual N=PD(a) over a general manifold base
-- M as a SingularManifold (lifts SmithLineBundle.sectionZeroLocus_isManifold E→M via the manifold RVT).
import SKEFTHawking.ManifoldSmithPD
-- Phase 5q.F W5 (2026-06-16): the geometric Smith map's real line bundle L_a + section zero locus = PD(a).
-- SignCocycle → VectorBundleCore (genuine VectorBundle ℝ ℝ, structure group ℤ/2⊂ℝˣ); section coordinate
-- function → zero locus is a C^∞ codim-1 manifold via the regular-value theorem + smooth embedding;
-- w₂(N)=0 SW-inheritance (PD_RP4_isPinPlus). The PD-submanifold construction for [M]↦[PD(a)].
import SKEFTHawking.SmithLineBundle
-- Phase 5q.F W6 (2026-06-16): the Smith-LES derivation engine — the exact segment 0→Ω₆^{Pin⁻}→Ω₄^{Pin⁺}→0
-- (twisted-spin vanishings) forces sm_{2σ} an iso; with the cited Ω₆^{Pin⁻}=ℤ/16 (height-4 input) ⟹
-- Ω₄^{Pin⁺}≅ℤ/16. The genuine W6 assembly; instantiated at the genuine carriers + geometric Smith map.
import SKEFTHawking.PinPlusSmithLES
-- Phase 5q.F W5 (2026-06-15): the geometric Smith map s:Ω₅^{Spin-ℤ₄}→Ω₄^{Pin⁺} as a TYPED HOMOMORPHISM
-- on the genuine DataBordismGrp carriers (DR Smith_sequence.md §5.2 scope). smithDataHom (grade transport,
-- floor-surviving ℤ/16) + the Smith square abkGrade∘smithDataHom=η-grade + the floor-quotient Smith iso
-- ℤ/16≃ℤ/16 + the SW operative content (smith_w2_vanishes) + §7 the genuine MANIFOLD layer (bricks 1-2:
-- PD(a) a real codim-1 SingularManifold over arbitrary M). The de-thinned [M]↦[PD(a)] at the typed scope.
import SKEFTHawking.SmithIsomorphism
-- Phase 5q.F (2026-06-15): singular ℤ/2 cohomology on Mathlib's singular SSet (TopCat.toSSet) — the
-- foundation for the ABK β BUILT FROM the SingularManifold bordism group (Mathlib has the singular chain
-- complex but no cohomology). First brick: singular cochains + the coboundary δ. Toward δ²=0 → Hⁿ → cup →
-- the genuine β discharging dataBordism_iso_zmod16's hypotheses.
import SKEFTHawking.SingularCohomologyMod2
-- Phase 5q.F (2026-06-15, w₂ foundation brick 3): singular ℤ/2 HOMOLOGY + the Kronecker pairing — the
-- dual of SingularCohomologyMod2. Chains C_n = simplices →₀ ℤ/2, the boundary ∂ with ∂²=0, Homology
-- Hₙ = ker∂/im∂, and the descended Kronecker pairing kroneckerH : Hⁿ × Hₙ → ℤ/2 (the evaluation
-- ⟨·,[M]⟩ the Wu functional ⟨x∪x,[M]⟩ needs — the route to the fundamental class and w₂(TM)).
import SKEFTHawking.SingularHomologyMod2
-- Phase 5q.F (w₂ foundation brick 6a, 2026-06-15): relative singular ℤ/2 homology Hₙ(X,S) of a subspace
-- S⊆X — relative chains C_n(X)/C_n(S) (genuine quotient ℤ/2-vsp), the relative boundary (∂²=0), and
-- relative homology ker∂/im∂. The functorial chain map C_•(S)→C_•(X) (a genuine chain map by simplicial
-- naturality) is the subspace inclusion's image. Foundation for local homology Hₙ(M,M∖x)≅ℤ/2 → the ℤ/2
-- fundamental class → Poincaré duality (turning PoincareDual4Mid from a hypothesis into a theorem).
import SKEFTHawking.SingularRelativeHomologyMod2
-- Phase 5q.F (w₂ foundation brick 6b, 2026-06-15): the long exact sequence of a pair (X,S) — the induced
-- maps i_* : Hₙ(S)→Hₙ(X), j_* : Hₙ(X)→Hₙ(X,S), and the connecting homomorphism δ : Hₙ₊₁(X,S)→Hₙ(S),
-- [c]↦[∂c] (the snake-lemma boundary, with hand-rolled well-definedness). Foundation for the local-homology
-- computation Hₙ(ℝⁿ,ℝⁿ∖0)≅ℤ/2 → the ℤ/2 fundamental class → Poincaré duality.
import SKEFTHawking.SingularPairLES
-- Phase 5q.F (w₂ foundation brick 6c, 2026-06-15): barycentric subdivision + excision (the engine for
-- local homology Hₙ(ℝⁿ,ℝⁿ∖0)≅ℤ/2). Sub-brick c1: the affine (linear) singular simplices [v₀,…,vₙ]:Δⁿ→V
-- (t↦∑tᵢvᵢ) — the geometric atoms of the subdivision Sd. (Cone operator, recursive Sd, the chain homotopy
-- ∂T+T∂=1−Sd, and the small-simplices theorem follow.)
import SKEFTHawking.SingularExcisionMod2
-- Phase 5q.F (w₂ foundation brick 6c-c7, 2026-06-15): the pushforward bridge transporting the verified
-- affine Sd/D to singular chains. c7a: affineSimplexStd — the affine simplex with vertices in Δᴺ landing
-- in Δᴺ (convexity), ready to post-compose with a singular N-simplex σ:Δᴺ→X.
import SKEFTHawking.SingularExcisionPushforward
-- Phase 5q.F (w₂-foundation, brick 6c-c7c.2): barycentric subdivision stays in a convex set — the
-- submodule chainsIn S n of in-S chains is preserved by cone/linBoundary/linSubdiv/linHomotopy (new
-- vertices are barycenters = convex combinations), so the subdivision of Δᴺ has vertices in Δᴺ.
import SKEFTHawking.SingularSubdivisionConvex
-- Phase 5q.F (w₂-foundation, brick 6c-c7c.3): naturality of barycentric subdivision under linear maps
-- (mapVerts L ∘ Sd = Sd ∘ mapVerts L for L : V →ₗ[ℝ] W) — the facet-inclusion naturality powering the
-- singular chain-map ∂Sd=Sd∂ (the i-th facet Δⁿ⁻¹↪Δⁿ is the linear FunOnFinite.linearMap ℝ ℝ (δ i)).
import SKEFTHawking.SingularSubdivisionNatural
-- Phase 5q.F (w₂-foundation, brick 6c-c7c.5): the singular barycentric subdivision Sd(σ):=σ_#(Sd ι_n),
-- assembled from the affine engine. Chain-level boundary naturality of the module pushforward
-- ∂∘σ_#=σ_#∘∂ on in-Δᴺ chains — the transport lemma for the singular chain map ∂Sd=Sd∂.
import SKEFTHawking.SingularSubdivision
-- Phase 5q.F (w₂-foundation, brick 6c-c8.3): the barycentric-subdivision diameter estimate (analytic
-- heart of excision) — barycenter-to-vertex bound ‖barycenter v − vⱼ‖ ≤ (n/(n+1))·diam (the i=j term
-- vanishes), the contraction factor n/(n+1)<1 driving diam(Sdᵐ pieces)→0.
import SKEFTHawking.SingularSubdivisionDiameter
-- Phase 5q.F (w₂-foundation, brick 6c-c8.4): singular excision — joins the subdivision chain homotopy to
-- the affine diameter estimate via the iterate connection Sdᵐ[σ]=σ_#((Sd_aff)ᵐ ιₙ); the model simplex ιₙ
-- has diameter ≤ 1 so iterated subdivision shrinks its pieces below any ε (Lebesgue-smallness seed).
import SKEFTHawking.SingularExcision
import SKEFTHawking.SingularExcisionIso
import SKEFTHawking.SingularPrism
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularEuclideanAcyclic
import SKEFTHawking.SingularPuncturedRetract
import SKEFTHawking.SingularLocalHomology
import SKEFTHawking.SingularDiskAcyclic
import SKEFTHawking.SingularSphereAcyclic
import SKEFTHawking.SingularH0
import SKEFTHawking.SingularReducedH0
import SKEFTHawking.SingularH0PathConnected
import SKEFTHawking.SingularSphereBottom
import SKEFTHawking.SingularDisjointUnion
import SKEFTHawking.SingularLineMinusPoint
import SKEFTHawking.SingularRelativeFunctoriality
import SKEFTHawking.SingularLocalModelChart
import SKEFTHawking.SingularChartBridge
import SKEFTHawking.SingularMayerVietoris
import SKEFTHawking.SingularMayerVietorisLES
import SKEFTHawking.SingularRelativeMV
import SKEFTHawking.SingularConvexComplementRetract
import SKEFTHawking.SingularSphereHighDegree
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularConvexRestrictionIso
import SKEFTHawking.SingularRelativeEmpty
import SKEFTHawking.SingularDeterminedConvex
import SKEFTHawking.SingularGoodCompact
import SKEFTHawking.SingularChainSupport
import SKEFTHawking.SingularLocalHomologyColimit
import SKEFTHawking.SingularConvexRadialRetract
import SKEFTHawking.SingularConvexRadialBase
import SKEFTHawking.SingularBallCover
import SKEFTHawking.SingularGoodCompactEuclidean
import SKEFTHawking.SingularGoodCompactChart
import SKEFTHawking.SingularCompactChartCover
import SKEFTHawking.SingularGoodCompactManifold
import SKEFTHawking.SingularFundamentalClass
import SKEFTHawking.SingularFundamentalClassExist
-- Phase 5q.F (fully-unconditional strengthening, w₂-foundation brick 5, 2026-06-15): the Wu class v₂ from
-- Poincaré duality — for a PD datum (fundamental-class functional μ:H⁴→ℤ/2 + non-degenerate middle cup
-- pairing, finite-dim H²), v₂∈H² represents x↦⟨Sq²x,[M]⟩ (wu_relation), the input to the Wu formula
-- w₂=v₂+v₁². The PD datum's geometric construction (the ℤ/2 fundamental class + PD) is the next foundation
-- brick; toward collapsing the unoriented-bordism floor for the full-carrier UNCONDITIONAL Ω₄^{Pin⁺}≅ℤ/16.
import SKEFTHawking.PoincareDualityWu
import SKEFTHawking.SingularCapHomology
import SKEFTHawking.SingularUniversalCoeff
import SKEFTHawking.SingularRelativeCohomologyMod2
import SKEFTHawking.SingularRelativeCohomologyRestrict
import SKEFTHawking.SingularRelativeCohomologyMV
import SKEFTHawking.SingularRelativeCohomologyMVExact
import SKEFTHawking.SingularDualityAdjoint
import SKEFTHawking.SingularDualityMVAdjoint
import SKEFTHawking.SingularDualityFinrank
import SKEFTHawking.SingularRelativeCohomologyMVMiddle
import SKEFTHawking.SingularRelativeCap
import SKEFTHawking.SingularCapSupport
import SKEFTHawking.SingularCompactSupport
import SKEFTHawking.SingularSubsetHomology
import SKEFTHawking.SingularSubspaceChainsEquiv
import SKEFTHawking.SingularLocalDualityK
import SKEFTHawking.SingularCohomologyColimit
import SKEFTHawking.SingularHomologyColimit
import SKEFTHawking.SingularDirectLimitTop
import SKEFTHawking.SingularCompactlySupportedTop
import SKEFTHawking.SingularHomologyHomeo
import SKEFTHawking.SingularHomologyColimitTop
import SKEFTHawking.SingularFundCycleOpen
import SKEFTHawking.SingularFundamentalDuality
import SKEFTHawking.SingularDualityEmptyInjective
import SKEFTHawking.SingularRelativeDualityCongr
import SKEFTHawking.SingularFundamentalDualityEndpoint
import SKEFTHawking.SingularCompactsInOpen
import SKEFTHawking.SingularCompactlySupportedOpen
import SKEFTHawking.SingularCSCOpenMonotone
import SKEFTHawking.SingularCSCMayerVietoris
import SKEFTHawking.SingularCSCMayerVietorisMiddle
import SKEFTHawking.SingularLocalDualityKRestrict
import SKEFTHawking.SingularLocalDualityKCycle
import SKEFTHawking.SingularOpenDualityCycle
import SKEFTHawking.SingularRelativeUCSurj
import SKEFTHawking.SingularRelativePairing
import SKEFTHawking.SingularRelativeUC
import SKEFTHawking.SingularLocalCohomology
import SKEFTHawking.SingularRelativeDuality
import SKEFTHawking.SingularRelativeDuality0
import SKEFTHawking.SingularLocalDuality
import SKEFTHawking.SingularPointComplement
import SKEFTHawking.SingularLocalDualityInjective
import SKEFTHawking.SingularRelativeCohomologyEmpty
import SKEFTHawking.SingularDualityEmpty
import SKEFTHawking.PoincareDualityConstruct
import SKEFTHawking.SingularCohomologyFunctorial
import SKEFTHawking.SingularCohomologyDisjoint
import SKEFTHawking.KitaevSixteenFold
import SKEFTHawking.Spin10Sixteen
import SKEFTHawking.AnomalyPhaseCharacter
import SKEFTHawking.SixteenConvergenceExplicit
import SKEFTHawking.CommonOrigin
-- Phase 5q.F W7 (2026-06-14): the 16-convergence capstone with SmithInflow's content
-- REFINED -- constructed smithHom + two-bounds-derived order-16 + Smith SW-mechanism
-- (refinement of the opaque hypothesis, NOT a geometric discharge; see module header).
import SKEFTHawking.SixteenConvergenceDerived
import SKEFTHawking.RokhlinManifoldFromHM
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
import SKEFTHawking.InducedGravityEntropy
import SKEFTHawking.GammaStirling
import SKEFTHawking.ContinuumCatalan
import SKEFTHawking.HorizonWittBoundary
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
-- Phase 6p Wave 2c.4a-R4.2.d.4.3.d.2-Wedge-D / Phase 5 Step 13 Path (i)
-- FINAL: substantive discharge of `CartanFinalStep_SU2_v4` via BCH bracket
-- closure (Trotter limit) + IFT 3-direction map. STRUCTURAL SHELL ship —
-- the Trotter convergence sub-lemma `exp_bracket_mem_H` and the IFT
-- 3-direction composition in `CartanFinalStep_SU2_v4_holds` are decomposed
-- into clearly-stated sub-goals with `sorry`s, ready for follow-up commits.
import SKEFTHawking.FKLW.SU2BCHBracketClosure
-- Phase 6t Wave 1-7 SHIP (2026-05-22 PM): Quantitative Solovay-Kitaev for
-- Fibonacci anyons (Dawson-Nielsen 2006). Seven modules under FKLW/:
--   - GroupCommutator (Wave 1): group-commutator substrate + 3 headlines
--     (norm_le_quadratic, lie_bracket_cubic_remainder, stability)
--   - SU2BalancedCommutator (Wave 2): SU(2) balanced commutator Z-axis case
--     + general-axis predicate scaffold
--   - FibonacciEpsilonNet (Wave 3): ε₀-net via F.21 density Classical.choose
--   - SolovayKitaevRecursion (Wave 4): skApprox recursion + level-0 error bound
--   - SolovayKitaevLengthBound (Wave 5): length recurrence + DN exponent c ≈ 3.97
--   - SolovayKitaevQuantitative (Wave 6): headline theorem composition
--   - SolovayKitaevApplications (Wave 7): worked-example contracts + Phase 6u placeholder
-- Headline: `solovayKitaev_dawson_nielsen_quantitative_fibonacci`
-- (kernel-only [propext, Classical.choice, Quot.sound]).
import SKEFTHawking.FKLW.GroupCommutator
import SKEFTHawking.FKLW.SU2BalancedCommutator
import SKEFTHawking.FKLW.FibonacciEpsilonNet
import SKEFTHawking.FKLW.SolovayKitaevRecursion
import SKEFTHawking.FKLW.SolovayKitaevLengthBound
import SKEFTHawking.FKLW.SolovayKitaevQuantitative
import SKEFTHawking.FKLW.SolovayKitaevApplications
-- Phase 6t Path A (2026-05-22 PM): constructive variant of skApprox + strict
-- headline. SU(2) lift helper `expIsu2` shipped; constructive `skApproxC` +
-- inductive error bound + constructive headline forthcoming.
import SKEFTHawking.FKLW.SolovayKitaevPathA
-- Phase 6u Wave 1 (2026-05-25): generic GeneratingSet framework abstracting
-- the Phase 6t Fibonacci-specific H_Fib substrate over an arbitrary word-type
-- W (a group) plus a representation ρ_hom : W →* SU(2). Fibonacci specializes:
-- H_of_G fibonacciGeneratingSet = H_Fib by definitional reduction.
import SKEFTHawking.FKLW.GenericSU2GeneratingSet
-- Phase 6u Wave 2 (2026-05-25): generic closure-dense witness + culmination.
-- ClosureDenseWitness structure carrying two ℝ-LI traceless skew-Hermitian
-- tangents + flow lines. H_of_G_eq_top_of_witness composes Phase 5 Step 13's
-- alphabet-agnostic CartanFinalStep_SU2_v4_holds to dispatch any witness into
-- H_of_G gs = ⊤, then isDenseInSU2_gs_of_eq_top gives the generic density.
import SKEFTHawking.FKLW.GenericClosureDenseWitness
-- Phase 6u Wave 3 (2026-05-25): generic ε₀-net findNearest via existential
-- form (Classical.choose extraction of Wave-2 density). Substantive
-- constructive (finite-Finset) enumeration is per-alphabet (Track T-S
-- ships Ross-Selinger Z[ω][1/√2] symbolic discharge).
import SKEFTHawking.FKLW.GenericEpsilonNet
-- Phase 6u Wave 4a (2026-05-25): generic SK recursion engine. Defines
-- dnStepFG_su2 (alphabet-agnostic), skApproxC_generic gs baseFinder, the
-- super-quadratic bound predicate, and Fibonacci-instance discharge via
-- the existing Phase 6t Path A Option C `SkApproxCSuperQuadraticBound_holds`.
-- Wave 4b ships the substantive generic discharge (alphabet-agnostic
-- ~800-1000 LoC port of the Phase 6t cubic/stability/V_n-unitarity proof).
import SKEFTHawking.FKLW.GenericSolovayKitaevRecursion
-- Phase 6u Wave 5 (2026-05-25): generic length bound at skLevel_polylog ε.
-- Re-export of the already-alphabet-agnostic SolovayKitaevLengthBound.
import SKEFTHawking.FKLW.GenericSolovayKitaevLengthBound
-- Phase 6u Wave 6 (2026-05-25): generic bundled-strict headline. Conditional
-- on SkApproxCSuperQuadraticBound_generic, conjoins the super-quadratic
-- error bound + the length bound at the SAME algorithmic compile level
-- skLevel_polylog ε. Fibonacci-instance specialization is unconditional via
-- the Wave 4a Fibonacci bridge.
import SKEFTHawking.FKLW.GenericSolovayKitaevQuantitative
-- Phase 6u Wave 4b (2026-05-25): UNCONDITIONAL alphabet-agnostic discharge of
-- SkApproxCSuperQuadraticBound_generic K_compose for any GeneratingSet + base
-- finder satisfying BaseFinder_approximates_within (2 * ε₀). Substantive port
-- of Phase 6t Path A Option C's SkApproxCSuperQuadraticBound_holds (~800 LoC)
-- to the generic substrate, with Fibonacci-specific ρ_Fib_SU2_* multiplicativity
-- lemmas replaced by generic gs.ρ_hom MonoidHom map_mul/map_inv. Bundles the
-- UNCONDITIONAL generic bundled-strict headline
-- (solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional).
import SKEFTHawking.FKLW.GenericSolovayKitaevRecursionDischarge
-- Phase 6u Track T-S.1 (2026-05-25): Clifford+T generating set instance.
-- SU(2)-corrected gates H_SU := (i/√2)[[1,1],[1,-1]], T_SU := diag(e^{-iπ/8}, e^{iπ/8}).
-- cliffordTGeneratingSet with W = FreeGroup (Fin 2), ρ_CliffT representation.
import SKEFTHawking.FKLW.CliffordTGeneratingSet
-- Phase 6u Track T-S.2 (2026-05-25): Clifford+T closure-density witness
-- conditional on tracked Prop cliffordT_v4_witness_tracked (BMPRV 1999 v4 shape).
-- Substantive discharge multi-session (BMPRV 1999 in Lean — accumulation-at-1
-- via Niven-style irrationality + second-tangent case analysis on Pauli).
import SKEFTHawking.FKLW.CliffordTClosureDenseWitness
-- Phase 6u Track T-S.3+T-S.4+T-S.5 (2026-05-25): Clifford+T ε₀-net base finder
-- + calibration (UNCONDITIONALLY DISCHARGED via Wave 4b) + bundled-strict
-- headline solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight.
-- Conditional ONLY on T-S.2's tracked Prop.
import SKEFTHawking.FKLW.CliffordTQuantitative
-- Phase 6u T-S.2 substantive substrate (2026-05-25): non-commutativity of
-- H_SU and T_SU, the structural fact that ⟨H_SU, T_SU⟩ is not abelian
-- (used downstream by the cliffordT_v4_witness_tracked discharge).
import SKEFTHawking.FKLW.CliffordTNonCommuting
-- Phase 6u T-S.2 substantive substrate (2026-05-25): infinite-order witness
-- for `H_SU * T_SU` via Niven-style algebraic-integer obstruction. Ships
-- the headline `cliffordT_accPt_one_unconditional` (AccPt 1 on H_of_G
-- cliffordTGS) consumed by the `cliffordT_v4_witness_tracked` discharge.
import SKEFTHawking.FKLW.CliffordTInfiniteOrder
-- Phase 6u T-S.2 case-analysis substrate (2026-05-25): for any nonzero
-- X ∈ 𝔰𝔲(2), at least one of H_SU, T_SU neither commutes nor
-- anti-commutes with X (substrate for the second-tangent direction in
-- the v4-witness assembly for T-S.2).
import SKEFTHawking.FKLW.CliffordTGeneratorCaseAnalysis
-- Phase 6u T-S.2 v4-witness conditional discharge (2026-05-25): given
-- AccPt 1 on H_of_G cliffordTGS, discharges cliffordT_v4_witness_tracked
-- via the standard Phase-5-Step-13 substrate
-- (vonNeumann_assemble_explicit_X_unconditional + ts_Ad_LI + expAmbient_unitary_conj).
-- Unconditional version awaits the in-flight Niven-based AccPt 1 proof.
import SKEFTHawking.FKLW.CliffordTV4WitnessDischarge
-- Phase 6u T-S.2 UNCONDITIONAL v4-witness discharge + T-S.5 unconditional
-- headline (2026-05-25): composes the conditional discharge with the
-- Niven-based cliffordT_accPt_one_unconditional to ship
-- cliffordT_v4_witness_discharged and
-- solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight_unconditional.
-- This CLOSES Phase 6u Track T-S — the Clifford+T quantitative SK headline
-- is now FULLY UNCONDITIONAL (kernel-only).
import SKEFTHawking.FKLW.CliffordTV4WitnessUnconditional
-- Phase 6x Track T-A1 (LIFT/SHIFT) completion (2026-05-26): trapped-ion
-- per-ion 1Q bundled-strict Solovay-Kitaev headline UNCONDITIONAL via
-- factorization through Phase 6u Clifford+T. Production-aligned reading:
-- MS(θ) as primitive token (acts as identity on single-ion SU(2) target),
-- per-ion {H, T} compiled via cliffordTGeneratingSet. Closes the gap from
-- the Phase 6x first-session ship which yielded T-A1.{3,4,5} under a
-- mis-application of Pivot Rule #15. Full SU(4) Clifford+MS compile
-- deferred to Phase 6y Track T-A1′.
import SKEFTHawking.FKLW.TrappedIonGeneratingSet
-- Phase 6x Track M.4 (headline integration) — substrate (2026-05-26):
-- arithmetic recurrence skLength_succ_eq + closed-form length bound
-- skApproxC_generic_freeGroup_length_le_skLength (induction on level n)
-- + BaseFinder_length_bounded predicate. The substrate that lets each
-- alphabet's bundled-strict Solovay-Kitaev headline carry a THIRD
-- conjunct binding the compiled output's concrete FreeGroup-word-length
-- to the abstract skLength closed form.
import SKEFTHawking.FKLW.GenericConcreteWordLengthBound
-- Phase 6x Track M.4 (headline integration) — per-alphabet 3-conjunct
-- bundled-strict headlines (2026-05-26): ships 3-conjunct strict
-- headlines (error + abstract length + concrete length) at each of the
-- four FreeGroup-based per-alphabet GS (Clifford+T, Read-Rezayi k=5,
-- Read-Rezayi k=7, trapped-ion lift/shift). Closes substrate-vs-headline
-- gap (Phase 6x retrospective addendum anti-pattern #4). Conditional
-- on per-alphabet BaseFinder_length_bounded hypothesis; the substantive
-- discharge ships per-alphabet (CT via Track T-S′ Ross-Selinger;
-- RR5/RR7/T-A1 as Phase 6x follow-on / Phase 6y).
import SKEFTHawking.FKLW.PerAlphabetConcreteLengthHeadlines
-- Phase 6x Track T-S′ (lightweight algorithmic ship, 2026-05-26):
-- constructive length-bounded Clifford+T base finder via finite-Finset
-- enumeration, composing the SU(2) compactness substrate
-- (Matrix.specialUnitaryGroup_isCompact, Phase 6p Wave 2c.4a) with the
-- ConstructiveEpsilonNet finite-Finset ε-cover existence theorem
-- (Phase 6x first session). Ships UNCONDITIONAL constructive base
-- finder + length bound (parametric in cover Finset's max length) +
-- fully UNCONDITIONAL 3-conjunct strict headline at Clifford+T. Full
-- Ross-Selinger ℤ[ω][1/√2] optimal-length refinement deferred per
-- Lit-Search task drop ross_selinger_arxiv_1403_2975_zomega_invsqrt2_synthesis.md.
import SKEFTHawking.FKLW.RossSelingerLightweight
-- Phase 6AN Wave 5 (2026-06-08): correct-by-construction Clifford+T gate compiler (CompCert-style).
import SKEFTHawking.FKLW.CliffordTCompiler
-- Phase 6x Tier-1 residual B-RR5 (2026-05-27): UNCONDITIONAL constructive
-- base finder + 3-conjunct strict headline for Read-Rezayi `SU(2)_5`.
-- Mirrors RossSelingerLightweight's T-S′ pattern (ConstructiveEpsilonNet
-- + rr5_density_unconditional + SU(2) compactness → finite Finset cover).
-- Closes retrospective failure mode #4 for RR5.
import SKEFTHawking.FKLW.ReadRezayiK5BaseFinder
-- Phase 6x Tier-1 residual B-RR7 (2026-05-27): UNCONDITIONAL constructive
-- base finder + 3-conjunct strict headline for Read-Rezayi `SU(2)_7`.
-- Mirrors RossSelingerLightweight + ReadRezayiK5BaseFinder. Closes
-- retrospective failure mode #4 for RR7.
import SKEFTHawking.FKLW.ReadRezayiK7BaseFinder
-- Phase 6x Tier-2 Item D (M1, 2026-05-27): ZOmega ring of integers of
-- ℚ(ζ₈) = ℚ(e^(iπ/4)), structure with four ℤ fields, CommRing instance,
-- Galois automorphisms (σ_3, σ_5, conj), algebraic field norm. Foundation
-- for the Phase 6x Ross-Selinger arc per Pre-Implementation DR.
-- native_decide-compatible runtime arithmetic. Clean-room rebuild from
-- arXiv:1206.5236 + arXiv:1403.2975; no newsynth GPL code copied.
import SKEFTHawking.FKLW.RossSelinger.ZOmega
-- Phase 6x Tier-2 Item E (M2; runtime upgrade 2026-05-29): ZOmegaSqrt2 :=
-- ℤ[ω][1/√2] as the COMPUTABLE runtime quotient Quotient Frac.setoid
-- (DR §1.7 rep B), replacing the noncomputable Localization.Away. Frac =
-- (num : ZOmega, den : ℕ) ~ num/√2^den; full CommRing + DecidableEq +
-- sqrt2/invSqrt2/units + Algebra ZOmega embedding (of/ofRingHom). The
-- native_decide-able substrate for KMM exact synthesis (Item F).
import SKEFTHawking.FKLW.RossSelinger.ZOmegaSqrt2
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — computable √2-adic valuation
-- + denominator-exponent substrate for sde. ZOmega.dividesSqrt2 (decidable
-- √2 ∣ z via parity), divSqrt2 (z/√2), lowestDenExp (structural-recursion
-- lowest-terms denominator exponent), and ZOmegaSqrt2.denExp (Quotient.lift,
-- well-defined via lowestDenExp_sqrt2_pow_mul). Feeds the matrix sde that
-- makes kmmReduce terminate.
import SKEFTHawking.FKLW.RossSelinger.Sde
-- Phase 6x Tier-2 Item F (M4, 2026-05-27) — CliffordTGate ADT and matrix
-- interpretation. Single-qubit Clifford+T gates {H, S, T, X, Y, Z, id,
-- omega} → 2x2 ZOmegaSqrt2 matrices. interp foldr of a List CliffordTGate
-- to its product matrix; interp_append distributes over multiplication.
import SKEFTHawking.FKLW.RossSelinger.CliffordTGate
-- Phase 6x Tier-2 Item F (M4, 2026-05-27) — KMM exact synthesis substrate
-- + algorithm specification. Defines sde_le relation, IsCliffordTRealizable,
-- KMMReduction structure (reduce + correct + length_bound fields per
-- KMM Corollary 1: n_g ≤ N₃ + 4·sde), and the tracked-Prop
-- KMMReductionExists (Nonempty KMMReduction). Concrete KMMReduction
-- instance construction (192-Clifford lookup + sde-decreasing proof) is
-- deferred multi-session work requiring the runtime ZOmegaSqrt2 (z, k)
-- representation per DR §1.7 option (B).
import SKEFTHawking.FKLW.RossSelinger.KMM
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — computable matrix sde + spec
-- bridge. KMM.sdeC (Finset.sup of per-entry denExp) + sde_le_sdeC
-- (achievability), sdeC_le_of_sde_le (minimality), sde_eq_sdeC (the
-- noncomputable Nat.find spec coincides with the computable sdeC). This
-- is the least-clearing-exponent fact kmmReduce recurses on.
import SKEFTHawking.FKLW.RossSelinger.SdeMatrix
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — KMM reduction-step algebraic
-- spine. gateMatrix_T_pow_eight (T^8=I via T^2=S/S^2=Z/Z^2=I), reconWord
-- (T^(8-j)++[H]) + interp_reconWord, reconWord_inv (left-inverts H·T^j),
-- interp_reconWord_mul (the reduction-step correctness identity
-- interp(reconWord j)·(H·T^j·M)=M, purely algebraic via H²=I/T⁸=I), and
-- realizability-preservation under the peel. The algebraic half of
-- kmmReduce_correct; the residue Lemma-3 (sde decrease) + sde≤3 coverage
-- remain for the full discharge.
import SKEFTHawking.FKLW.RossSelinger.KMMReduce
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — S/Z-compressed KMM reconstruction
-- syllable (the N₃+4·k length-bound fix). reconWordC k spells T^(8-k)·H with
-- the Clifford gates S=T², Z=T⁴ (T⁸=I↦[H], T⁷=Z·S·T, T⁶=Z·S, T⁵=Z·T) so the
-- syllable is ≤4 gates (reconWordC_length_le_four) vs reconWord's up-to-9;
-- interp_reconWordC_eq proves it interprets identically (=T^(8-k)·H), so
-- interp_reconWordC_mul inherits reconWord's reduction-step correctness. This
-- is the per-step gate budget behind the N₃+4·sde KMM Corollary-1 bound.
import SKEFTHawking.FKLW.RossSelinger.ReconWordCompressed
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — √2-residue map (KMM Lemma 3
-- substrate). ZOmega.resSqrt2 : ℤ[ω] → ZMod 2 × ZMod 2 coordinatizing
-- ℤ[ω]/(√2) ≅ 𝔽₂[ε]/(ε²) (local nilpotent; NOT 𝔽₄ — √2=𝔭² is not prime);
-- resSqrt2_eq_zero_iff_dividesSqrt2, additive structure (resSqrt2_add/zero/neg),
-- the multiplicative layer (resMul + resSqrt2_mul), and key residues
-- (sqrt2/2 ↦ 0, 1 ↦ (0,1), ω ↦ (1,0)). The coset layer KMM Lemma 3 reasons over.
import SKEFTHawking.FKLW.RossSelinger.ResidueSqrt2
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — conjugation + squared modulus
-- on ZOmegaSqrt2. ZOmegaSqrt2.conj (lifts ZOmega.conj through the quotient;
-- fixes √2 so descends to the localization) as a ring hom + involution;
-- normSq z := z * conj z (= |z|²) with conj_normSq (realness). KMM tracks
-- sde(|z|²) of the matrix entries (Lemmas 3 & 4).
import SKEFTHawking.FKLW.RossSelinger.Conj
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — greatest-dividing-exponent
-- substrate. ZOmega.dividesSqrt2_iff_dvd (dividesSqrt2 z ↔ √2 ∣ z),
-- dvdSqrt2Pow z m (decidable peel-based √2^m ∣ z predicate) +
-- dvdSqrt2Pow_iff (↔ √2^m ∣ z). The decidable gde machinery KMM Lemma 3 /
-- Prop 1 reason over.
import SKEFTHawking.FKLW.RossSelinger.GdeSqrt2
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — ℕ-valued gde(z,√2). gdePeel
-- (fuel-bounded √2-peel count), gdePeel_le_fuel, dvdSqrt2Pow_antitone,
-- dvdSqrt2Pow_gdePeel (√2^(gdePeel) ∣ z), and the predicate↔value bridge
-- dvdSqrt2Pow_iff_le_gdePeel (m ≤ fuel → (√2^m∣z ↔ m ≤ gdePeel z fuel)) +
-- gdePeel_mono_fuel. The gde VALUES KMM Lemma 5's ⌊(gde+gde)/2⌋ arithmetic
-- and Lemma 3's gde-difference case analysis reason over.
import SKEFTHawking.FKLW.RossSelinger.GdeValue
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — squared modulus on ZOmega + its gde
-- (KMM Lemma 5 substrate). ZOmega.normSq x := x·conj x (real ℤ[√2] element),
-- isReal_normSq, normSq_mul/add (cross-term)/pow, normSq_omega_pow_mul
-- (|ωᵏ·y|²=|y|²), and gdeNormSq x := gdePeel (normSq x) + the |x|² predicate↔
-- value bridge + gde modulus-invariance. The squared-modulus gde KMM Lemma 3/5
-- track (validated by scripts/kmm_zomega_reference_oracle.py: no mod-√2 shortcut).
import SKEFTHawking.FKLW.RossSelinger.NormSqGde
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — non-archimedean gde arithmetic
-- (KMM Lemma 5 toolkit). dvdSqrt2Pow_add (closed under +), dvdSqrt2Pow_min
-- (gde(p+q)≥min), dvdSqrt2Pow_mul_of (gde(zw)≥gde z+gde w), dvdSqrt2Pow_neg/
-- _zero_elt/_sqrt2_pow_self, + gde-value consequences gdePeel_add_ge/_mul_ge.
-- The non-archimedean toolkit assembling Lemma 5 from the cross-term estimate.
import SKEFTHawking.FKLW.RossSelinger.GdeArith
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — KMM Lemma 5 cross-term "+1" mechanism.
-- dividesSqrt2_add_conj (√2 ∣ (w+conj w) — the trace is always √2-divisible),
-- normSq_sqrt2 (|√2|²=2), dvdSqrt2Pow_add_conj (√2^m∣u ⟹ √2^(m+1)∣(u+conj u) —
-- the "+1" source, valuation-free). Validated by the ZOmega oracle.
import SKEFTHawking.FKLW.RossSelinger.CrossTermGde
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — computable reduction step +
-- chooseReduction search (re-point onto the runtime ring; native_decide-able).
-- reduceStep M k := H·Tᵏ·M, chooseReductionComp (first k∈{0,1,2,3} lowering
-- the computable sdeC), chooseReductionComp_reduces (by-construction sde
-- decrease), interp_reconWordC_reduceStep (step correctness via reconWordC).
-- Lemma-3-independent runtime KMM-reduction core (Lemma 3 = existence of such
-- a k when sdeC≥4, the one outstanding analytic input; DR-dispatched).
import SKEFTHawking.FKLW.RossSelinger.KMMCompute
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — kmmReduce fuel recursion + correctness.
-- kmmReduceFuel base n M (peel H·Tᵏ via chooseReductionComp up to n times,
-- prepend reconWordC k, emit base M at leaves) + interp_kmmReduceFuel: the
-- `correct` field of KMMReduction discharged NOW, Lemma-3-INDEPENDENT (needs only
-- step left-inversion + base-finder correctness, NOT sde decrease). Remaining for
-- discharge (DR-gated): Lemma 3 (termination+length) + cliffordLookup/N₃ base.
import SKEFTHawking.FKLW.RossSelinger.KMMReduceFuel
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — reduceStep column-0 transformation.
-- T_pow_diag (gateMatrix .T ^ k = diagonal ![1, ωᵏ]); reduceStep_zero_zero
-- ((H·Tᵏ·M) 0 0 = invSqrt2·(M₀₀ + ωᵏ·M₁₀)) + reduceStep_one_zero
-- ((H·Tᵏ·M) 1 0 = invSqrt2·(M₀₀ − ωᵏ·M₁₀)). The new top-left z'=(z+ωᵏw)/√2 is
-- KMM's s=−1 update; |z'|²=|z+ωᵏw|²/2 is the quantity kmm_lemma3_column controls.
-- Algebraic bridge from residue reduction-existence to matrix-sde decrease.
import SKEFTHawking.FKLW.RossSelinger.ReduceStepColumn
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — KMM Lemma 3 via Algorithm 2.
-- kmm_lemma3_alg2: the sde-reduction existence lemma proved by native_decide
-- over ℤ[ω]/(2³)=(ZMod 8)⁴ residues (Coord4) — KMM's actual proof (Algorithm 2,
-- "we implemented it and the result is true"), NOT a 𝔭-adic case split (none is
-- published). P/Q/gde/mulOmega oracle-validated in the ⟨a,b,c,d⟩ convention
-- (0 mismatches; Alg2 FAILS=0 over 393216 pairs). Carries Lean.ofReduceBool
-- (native_decide), the trust of running KMM's published C++ Algorithm 2.
import SKEFTHawking.FKLW.RossSelinger.KMMLemma3
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — bridge: KMM Algorithm 2 (residues)
-- ↔ ZOmega. coordOf (the mod-8 residue), normSq_d/normSq_c (|x|² coords =
-- P/Q polynomials), Pform_coordOf/Qform_coordOf (residue forms = normSq coords
-- mod 8), coordOf_omega_mul (residue ω-action = mod-8 of ZOmega ω-mult). The
-- foundational ring identities connecting kmm_lemma3_alg2 to actual elements;
-- the gde-value bridge (Prop 1) builds on top.
import SKEFTHawking.FKLW.RossSelinger.KMMLemma3Bridge
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — KMM Prop 1 step 1: gde of a real
-- element via the integer peel. peelN A B (peel √2 while A even, swap (A,B)↦
-- (B,A/2)) + gdePeel_real_eq_peelN (conj z=z ⟹ gdePeel z fuel = peelN z.d z.c
-- fuel). The integer shadow of gdePeel on the real subring; the closed form
-- (peelN = 2·min(v₂A,v₂B)+[v₂A>v₂B]) + mod-8 reduction to Coord4.gde build on it.
import SKEFTHawking.FKLW.RossSelinger.PropOne
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — the gde-value bridge (KMM Prop 1,
-- mod-8 form). coord4_gde_coordOf: KMM.Coord4.gde (coordOf x) = gdePeel (normSq x)
-- 4 — the residue-level gde of x's coordinates equals the genuine √2-gde of |x|²
-- (capped at 4). Proof: gdePeel of real |x|² = integer peelN of its ℤ[√2]-coords
-- (PropOne), peelN _ _ 4 periodic mod 8 + 64-representative kernel `decide` =
-- gdeFromPQ of residues, and Pform/Qform_coordOf identify those residues. The
-- connector applying kmm_lemma3_alg2 (over Coord4.gde) to actual ZOmega columns.
import SKEFTHawking.FKLW.RossSelinger.PropOneBridge
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — KMM Lemma 3 lifted to ZOmega columns.
-- coordOf_add / coordOf_omega_pow_mul (coordOf homomorphism), and
-- kmm_lemma3_column: for x,y with gde(|x|²)=gde(|y|²)=j∈{0,1} and unit-column
-- congruences (|x|²+|y|²).d ≡ (|x|²+|y|²).c ≡ 0 (mod 8), ∀ s+1∈{1,2,3} ∃k∈{0..3}:
-- gde(|x+ωᵏy|²)=(s+1)+j. The faithful ZOmega-image of kmm_lemma3_alg2 (via the
-- gde-value bridge); the s=2 case is the sde-reducing step. Fuel-sufficiency input.
import SKEFTHawking.FKLW.RossSelinger.KMMLemma3Column
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — clearing connection (ZOmegaSqrt2 sde ↔
-- ZOmega gde). lowestDenExp_add_gdePeel (lowestDenExp + gdePeel = fuel: residual +
-- peel-count = fuel); sqrt2_pow_normSq_clearing (√2^(2s)·|z|² = of |x|² for cleared
-- numerator x); denExp_normSq_clearing: ∃x, √2^(denExp z)·z = of x ∧ denExp(|z|²) =
-- 2·denExp z − gde(|x|²). The linchpin of plan B: bridges matrix-entry sde(|z|²) to
-- the ℤ[ω]-gde of the cleared numerator that kmm_lemma3_column controls.
import SKEFTHawking.FKLW.RossSelinger.ClearingConnection
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — KMM Lemma 4 value-form (gde(|x|²)≤1).
-- gdePeel_normSq_le_one_of_not_dividesSqrt2: a lowest-terms numerator (√2∤x) has
-- gde(|x|²)≤1 — contrapositive of dividesSqrt2_of_dvdSqrt2Pow_normSq_two (ZMod-2
-- parity decide: 2|P ∧ 2|Q ⟹ √2∣x). The j∈{0,1} hypothesis of kmm_lemma3_column
-- for cleared column numerators; the equal-sde half is denExp_normSq_col0_eq.
import SKEFTHawking.FKLW.RossSelinger.Lemma4Value
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — unit-column congruences (for
-- kmm_lemma3_column). sqrt2_pow_two_mul_coords (√2^(2s)=2^s: .c=0,.d=2^s);
-- clearedCol_normSq_sum (unit col |z|²+|w|²=1 cleared at common s ⟹ |x|²+|y|²=
-- √2^(2s)); unit_col_congruences (s≥3 ⟹ (|x|²+|y|²).d ≡ (|x|²+|y|²).c ≡ 0 mod 8) —
-- exactly the Pform-sum/Qform-sum hypotheses of kmm_lemma3_column.
import SKEFTHawking.FKLW.RossSelinger.UnitColumnCongruence
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — μ-decrease engine (per-entry cleared-form
-- layer). μ(M):=denExp(normSq(M₀₀))=sde(|z₀₀|²). of_sqrt2_eq; not_dividesSqrt2_clearedNum
-- (cleared num at denExp is √2∤, from denExp minimality); gdePeel_stabilizes (fuel
-- reconciliation 4↔2s); denExp_normSq_le (≤2·denExp z); entry_cleared_form (denExp z≥2 ⟹
-- gde(|x|²)≤1 ∧ denExp(|z|²)=2·denExp z−gde(|x|²)). Builds toward μ(reduceStep M k)<μ(M).
import SKEFTHawking.FKLW.RossSelinger.MuDecrease
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — real subring ℤ[√2] ⊂ ℤ[ω]
-- (KMM Prop 1 substrate). isReal_iff (conj z = z ↔ z.a=-z.c ∧ z.b=0;
-- real = a+√2 b with a=z.d, b=z.c), dividesSqrt2_of_isReal (√2∣real ↔
-- z.d even), divSqrt2_of_isReal (the √2-peel swap (a,b)↦(b,a/2) for even
-- z.d), isReal_divSqrt2 (peel stays in ℤ[√2]). The Euclidean-style peel
-- recursion underlying gde + Prop 1.
import SKEFTHawking.FKLW.RossSelinger.RealSubring
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — unitarity over ZOmegaSqrt2
-- (KMM Lemma 4 substrate). ZOmegaSqrt2.adjoint (conjugate transpose),
-- IsUnitaryT M := adjoint M * M = 1, and the column squared-norm
-- extraction unitary_col0_normSq / unitary_col1_normSq
-- (IsUnitaryT M ⟹ normSq(M i 0)+normSq(M i 1) = 1) — the orthonormal-column
-- identity Lemma 4 uses to force equal sde on both entries.
import SKEFTHawking.FKLW.RossSelinger.UnitaryT
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — Clifford+T-realizable ⟹ unitary.
-- adjoint_mul (conj-transpose anti-hom), adjoint_one, IsUnitaryT.one/.mul,
-- gateMatrix_isUnitaryT (per-gate decide), interp_isUnitaryT, and
-- isUnitaryT_of_isCliffordTRealizable — the fuel-sufficiency precondition for the
-- kmmReduce recursion (reduceStep preserves realizability ⟹ unitarity ⟹ mu_decrease
-- applies). Note: Mat2 `*` is heterogeneous HMul; IsUnitaryT.mul is term-mode.
import SKEFTHawking.FKLW.RossSelinger.UnitaryClosure
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — μ-tracking KMM recursion. kmmReduceMu
-- (peel H·Tᵏ via chooseReductionMu, prepend reconWordC, base at leaves) +
-- interp_kmmReduceMu (correctness WITH termination: μ(M)≤n + base correct on μ≤3 ⟹
-- interp = M; recursion bottoms at μ≤3 via chooseReductionMu_succeeds) +
-- length_kmmReduceMu (≤ N₃+4·n = honest KMM Cor 1 with n=μ(M)). Assembles toward
-- the Nonempty KMMReduction discharge (needs only cliffordLookup over 𝕊₃, N₃=9).
import SKEFTHawking.FKLW.RossSelinger.KMMReduceMu
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — Nonempty KMMReduction from the 𝕊₃ base
-- coverage. baseFinder9 (≤9-gate base word via Classical.choose; len≤9 always,
-- correct on μ≤3 given coverage) + kmmReduction_of_coverage: coverage ⟹ Nonempty
-- KMMReduction (concrete: reduce M = kmmReduceMu baseFinder9 (μ(M)) M; correct via
-- interp_kmmReduceMu; length_bound = N₃+4·sde(|z₀₀|²) KMM Cor 1). Reduces orphan #2
-- to the SOLE remaining fact: 𝕊₃ coverage (∀ realizable μ≤3 M, ∃ ≤9-word). NO axiom
-- (coverage is a hypothesis, Inv #15) — discharging it makes Nonempty unconditional.
import SKEFTHawking.FKLW.RossSelinger.KMMReductionDischarge
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — 𝕊₃ base-case coverage (toward unconditional
-- discharge). denExp_le_two_of_denExp_normSq_le_three (any entry; denExp(|z|²)≤3 ⟹ denExp z≤2)
-- + column0_cleared_bounded (μ≤3 unitary ⟹ cleared col-0 numerators x,y have (|x|²).d,(|y|²).d
-- ≤4 — finiteness seed: P=a²+b²+c²+d² sum-of-squares + P_x+P_y=2^s≤4 ⟹ coords bounded by 2,
-- NO real-order needed). Builds toward the coverage that makes Nonempty KMMReduction uncond.
import SKEFTHawking.FKLW.RossSelinger.KMMBaseCoverage
-- Phase 6x Tier-2 Item F (𝕊₃ coverage; 2026-05-29) — the Bloch / SO(3) map +
-- Matsumoto-Amano T-count measure kSO3. madjoint (Hermitian adjoint), pauliMat
-- (σ₁=X,σ₂=Y,σ₃=Z), blochEntry M i j = ½·Tr(σ_i M σ_j M†), and kSO3 M =
-- sup_{i,j} denExp(blochEntry M i j) — the SO(3) least-denominator exponent =
-- Giles-Selinger Lemma 4.10 T-count (validated kernel-pure: kSO3 I/H/S/X=0,
-- kSO3 T=1, kSO3 THT=2). The DR-validated recursion MEASURE for the MA
-- base-coverage route (replaces the dominated BFS-connectivity route).
import SKEFTHawking.FKLW.RossSelinger.BlochMap
-- Phase 6x Tier-2 Item F (𝕊₃ coverage; 2026-05-29) — the Bloch covering map is a
-- ring homomorphism SU(2)→SO(3) (substrate for relating kSO3 of a syllable strip
-- to kSO3 M). pauli_completeness (2•Y = Tr(Y)•I + Σₖ Tr(σₖY)•σₖ, the Pauli-basis
-- resolution; iS²=-1 per off-diagonal entry) + trace_conj_unitary (Tr(B·X·B†)=Tr X
-- for unitary B, term-mode calc via the HMul defeq bridge). The two ingredients of
-- R(A·B)=R(A)·R(B).
import SKEFTHawking.FKLW.RossSelinger.BlochHomomorphism
-- Phase 6x Tier-2 Item F (𝕊₃ coverage; 2026-05-29) — Matsumoto-Amano syllable
-- strip (the recursion step, algebraic half). IsCliffordTRealizable.adjoint
-- (realizability closed under Hermitian adjoint; per-gate short adjoint words
-- T†=Z·S·T etc.), Syllable {T,HT,SHT} + sylWord/sylMat, stripMat s M = (sylMat s)†·M,
-- interp_sylWord_stripMat (strip exactly invertible), stripMat_realizable, and the
-- computable kSO3-reducing selectSyllable (U(2)-residue-mod-2-determined per
-- kmm_ma_step_residue.py). The kSO3-decrease EXISTENCE (residue crux) ships next.
import SKEFTHawking.FKLW.RossSelinger.MAStep
-- Phase 6x Tier-2 Item F (𝕊₃ coverage; 2026-05-29) — the kSO3-decrease of a syllable
-- strip, mod-2 condition foundation. sylBlochNum (c^s := √2·R((sylMat s)†), concrete
-- cleared ZOmega 3×3) + sylBlochNum_clearing (of(c^s_ik) = √2·R((sylMat s)†)ᵢₖ, decide).
-- With bloch_stripMat: √2^(n-1)·R(stripMat s M)ᵢⱼ = (∑ₖ c^s_ik·b_kj)/2, so the kSO3
-- decrease ⟺ ∀ i,j: ∑ₖ c^s_ik·b_kj ≡ 0 (mod 2) — the 15-class Bloch parity native_decide.
import SKEFTHawking.FKLW.RossSelinger.MAStepDecrease
-- Phase 6x Tier-2 Item F (𝕊₃ coverage; 2026-05-29) — the Bloch image is orthogonal
-- (R(M)∈O(3), the ma_step achievability foundation). blochMat (R(M) as a 3×3 matrix),
-- blochMat_mul (R(A·B)=R(A)·R(B), bloch_hom lifted), blochMat_one (R(I)=I),
-- blochMat_transpose (R(M)ᵀ=R(M†), trace cyclicity), blochMat_transpose_mul
-- (R(M)ᵀ·R(M)=1 for unitary M). Forces bᵀ·b = 2^kSO3·I ⟹ bᵀ·b ≡ 0 (mod 2) — the
-- constraint cutting the Bloch parity residue to the 15 classes for ma_step ∃-s.
import SKEFTHawking.FKLW.RossSelinger.BlochOrthogonal
-- Phase 6x Tier-2 Item F (𝕊₃ coverage; 2026-05-29) — ma_step existence SUBSTRATE: REALITY of
-- the Bloch image of any realizable matrix (conj(R(M)ᵢⱼ)=R(M)ᵢⱼ): blochEntry_gate_real
-- (per-gate, decide) + blochEntry_interp_real (multiplicative via bloch_hom + conj ring-hom,
-- induction on the word) + blochEntry_realizable_real (B i j ∈ ⟨a,0,-a,d⟩). Plus the column/kill
-- vocabulary (Col, dvdTwo, colKills, someKills, notSqrt2Div, stripRow), blochNum orthogonality
-- ∑ᵢBᵢⱼBᵢₗ = 2^kSO3·δⱼₗ, and kSO3-exactness (some odd .d). [Phase 6AO 2026-06-10: the former
-- maStep_exists_core native_decide (~809k-tuple validCol³ sweep) was ELIMINATED — the existence
-- theorem now lives in MAStepStructural, proved by the Giles–Selinger §6 parity argument.]
import SKEFTHawking.FKLW.RossSelinger.MAStepExists
-- Phase 6AO Track 3 inc 3 (2026-06-10) — **MAStepStructural: maStep_exists_core ELIMINATED**.
-- The structural MA-step: killCond_engine (ONE 12-variable mod-2 parity lemma; the witness
-- column's pattern + F2 + the target's F1/F3/F4 ⟹ all three kill conditions; covers self AND
-- cross cases since F3(W,W)/F4(W,W) derive from F1(W)/commutativity) + per-syllable
-- colKills_{T,HT,SHT}_of + killsAll_{T,HT,SHT} + someKills_of_orthogonal (∀ even t — NO t ≤ 8
-- bound, NO box, NO enumeration) + the moved ma_step_exists (kSO3 ≤ 3 hypothesis DROPPED —
-- strictly stronger: the reducing syllable exists for EVERY kSO3 ≥ 1).
import SKEFTHawking.FKLW.RossSelinger.MAStepStructural
-- Phase 6AO Track 3 inc 4a (2026-06-10) — ZOmegaTorsion: the ℤ[ω] torsion classification
-- toward eliminating cliffordBase_box_core. |z|²=1 ⟹ z=ωʲ (Σcoord²=1, range bash);
-- |z|²=⟨0,0,0,2⟩ ⟹ z=√2·ωʲ (cross-coords kill non-adjacent ±1-pairs); |z|²=⟨0,0,0,4⟩ ⟹
-- z=2·ωʲ (mod-4 square parity: all-even halves to norm-1, all-odd ±1⁴ dies on cross-coords).
-- Aux-decomposed range bashes (Inv #10 budgets) closing by decide on the CLOSED substituted
-- normSq equation. Plus Galois positivity 2(|z|²).c² ≤ (|z|²).d² (= |z·σ₅z|².d ≥ 0) — the
-- engine pinning the √2-part in the inc-4b |x|² ∈ {0,2,4} quantization.
import SKEFTHawking.FKLW.RossSelinger.ZOmegaTorsion
-- Phase 6AO Track 3 inc 4b (2026-06-10) — CliffordBaseStructural: the kSO3 = 0 QUANTIZATION.
-- blochEntry_reconstruct_zz (R₂₂ = mk (2(|x|²−|y|²)) 6, k-free); kSO3=0 ⟹ 4 ∣ |x|²−|y|²
-- (√2⁶-clearing + 2-cancellation over the ZOmega domain); normSq_quantized trichotomy:
-- unit-column + 4∣Δ ⟹ (x=0 ∧ |y|²=4) ∨ (|x|²=|y|²=2) ∨ (|x|²=4 ∧ y=0) — Galois positivity
-- (ZOmegaTorsion) kills the √2-parts on BOTH coordinates. Composes with the torsion classes:
-- every kSO3=0 key is (0, 2ωᵇ), (√2ωᵃ, √2ωᵇ), or (2ωᵃ, 0) — substrate for the per-class
-- finite coverage checks replacing cliffordBase_box_core (inc 4c).
import SKEFTHawking.FKLW.RossSelinger.CliffordBaseStructural
-- Phase 6AO Track 3 site 4/4 (2026-06-10) — **KMMLemma3Structural: the T-pairing calculus**
-- toward eliminating kmm_lemma3_alg2. Bform pairing + gdePQ-factoring + update formulas
-- (P(x+z) = P+P+2B; Q(x+z) = Q+Q+(B(x,ωz)−B(x,ω³z))) + P/Q ω-invariance + B(x,ω⁴z) = −B +
-- the TWO norm-multiplicativity reachability identities (x·ȳ = ⟨T₃,T₂,T₁,T₀⟩ exactly:
-- P·P'+2Q·Q' = ΣTᵢ²; P·Q'+Q·P' = T₃T₂+T₂T₁+T₁T₀−T₃T₀) — all ring-proved. Plus the two
-- 262k-tuple kernel master sweeps kmm_master_a/b (decide +kernel, ~80 s each; the free-T
-- version is FALSE — the reachability constraints are load-bearing, validated 0/36864).
import SKEFTHawking.FKLW.RossSelinger.KMMLemma3Structural
-- Phase 6AO Track 3 site 4/4 (2026-06-10) — **KMMLemma3Alg2: kmm_lemma3_alg2 ELIMINATED**
-- (the LAST of the 4 KMM native_decide sites — formerly a ~16.7M-pair sweep). The statement
-- is re-proved VERBATIM (zero consumer changes): branch on P(x)+P(y) ∈ {0,4} (2u=0 dichotomy),
-- massage to the master's (P,Q,T)-data via the reachability identities, transport the
-- conclusion through gde_add_eq_of + the Bform index folds. Kernel-pure — the ENTIRE KMM
-- exact-synthesis arc (bridge, ma_step, cliffordBase, Lemma 3) is now native_decide-free.
import SKEFTHawking.FKLW.RossSelinger.KMMLemma3Alg2
-- Phase 6x Tier-2 Item F (𝕊₃ coverage; 2026-05-29) — the Matsumoto-Amano coverage recursion.
-- maCoverage (realizable M, kSO3 M≤3 ⟹ ∃ word ≤ 3·kSO3 M+6 ≤ 15) by strong induction on kSO3:
-- base = Clifford (cliffordBase hypothesis ≤6); step = strip ma_step syllable (kSO3 drops) +
-- prepend sylWord (interp_sylWord_stripMat reconstructs). coverage_fifteen adds bridge μ≤3⟹kSO3≤3
-- ⟹ the relaxed N₃=15 base coverage (DR: fits Item G L≤90<100). cliffordBase + bridge are
-- hypotheses, discharged separately; the recursion itself is unconditional.
import SKEFTHawking.FKLW.RossSelinger.MACoverage
-- Phase 6x Tier-2 Item F (𝕊₃ coverage; 2026-05-29) — determinant of a realizable matrix
-- (KMM Theorem 1 forward half). det_gateMatrix_eq_omega_pow (per-gate det = ωS^k, decide) +
-- det_realizable_eq_omega_pow (det multiplicative over the word ⟹ det M = ωS^k). Foundation
-- for the M-structure form M=[[x,-ωᵏȳ],[y,ωᵏx̄]]/√2^m feeding the μ≤3⟹kSO3≤3 bridge + Clifford base.
import SKEFTHawking.FKLW.RossSelinger.KMMDet
-- Phase 6x Tier-2 Item F (𝕊₃ coverage; 2026-05-29) — KMM Theorem 1 column structure.
-- realizable_col1: a Clifford+T-realizable M has column 1 determined by column 0 and the
-- determinant ωᵏ — M 1 1 = ωᵏ·conj(M 0 0), M 0 1 = -(ωᵏ·conj(M 1 0)) — via the uniform
-- det•M† = adjugate M identity (no case split on M 0 0 = 0). The foundation that turns the
-- ∀-over-realizable-M discharges (μ≤3⟹kSO3≤3 bridge, kSO3=0⟹Clifford base) into bounded
-- native_decide enumerations over a (x,y,k,m) integer tuple.
import SKEFTHawking.FKLW.RossSelinger.KMMForm
-- Phase 6x Tier-2 Item F (𝕊₃ coverage; 2026-05-29) — KMM reconstruction substrate for the
-- μ≤3⟹kSO3≤3 bridge. reconstruct (KMM Thm 1 form from column-0 numerators x,y + phase k) +
-- coordBox/zomBox (the [-2,2]⁴ ℤ[ω] box, still consumed by CliffordBase) + connecting lemmas
-- (eq_mk_of_sqrt2_pow_mul: √2-unit clearing; mem_zomBox; ωS^8=1 periodicity) + the μ≤kSO3+2
-- reverse bound. [Phase 6AO 2026-06-10: the former bridgeBoxOk/bridge_box_core native_decide
-- finite check was ELIMINATED — the bridge theorem itself now lives in BridgeStructural,
-- proved structurally with no box enumeration.]
import SKEFTHawking.FKLW.RossSelinger.KMMBridge
-- Phase 6x Tier-2 Item F (𝕊₃ coverage; 2026-05-29) — the Clifford base + CAPSTONE. cliffordBase:
-- realizable M, kSO3 M = 0 (Clifford up to phase) ⟹ ∃ ≤6-gate Clifford word, via the μ≤kSO3+2
-- reverse bound (kSO3=0⟹μ≤2≤3, KMMBridge) + 192-entry (x,y,k)→word lookup (cliffordTable).
-- [Phase 6AO Track 3 inc 4c (2026-06-10): cliffordBase_box_core native_decide ELIMINATED —
-- the kSO3=0 quantization (CliffordBaseStructural+ZOmegaTorsion) pins every key to a torsion
-- class ((0,2ωᵇ), (√2ωᵃ,√2ωᵇ), (2ωᵃ,0)); per-class kernel decide +kernel coverage checks
-- cliffordCover_{y2,mid_0..7,x2} (640 tuples, 64/chunk) verify the table words. cliffordBase
-- now KERNEL-PURE.] The SECOND of MACoverage's two hypotheses discharged ⟹
-- nonempty_kmmReduction : Nonempty KMMReduction — the exact-synthesis substrate closing
-- Phase 6x orphan #2 at the deterministic-branch level.
import SKEFTHawking.FKLW.RossSelinger.CliffordBase
-- Phase 6x Tier-2 Item G (2026-05-29) — the ℤ[ω] → ℂ ring embedding. ZOmega.toComplex : ZOmega →+* ℂ
-- (evaluation at ω = e^{iπ/4} = Complex.exp(π/4·I)), ⟨a,b,c,d⟩ ↦ a·ω³+b·ω²+c·ω+d; map_mul via the
-- ω⁴=-1 reduction (omegaC_pow_four) of the convolution product. Foundation for ZOmegaSqrt2 → ℂ and
-- the KMM(ZOmegaSqrt2)→SU(2,ℂ) operator-norm approximation bridge of Item G.
import SKEFTHawking.FKLW.RossSelinger.ComplexEmbedding
-- Phase 6x Tier-2 Item G (2026-05-29) — the ℤ[ω][1/√2] → ℂ ring embedding. ZOmegaSqrt2.toComplex :
-- ZOmegaSqrt2 →+* ℂ, mk z k ↦ ZOmega.toComplex z / s2C^k (s2C = toComplex √2, s2C²=2≠0), via the
-- Frac-quotient lift. The abstract↔analytic bridge: KMM exact synthesis (Mat2 over ZOmegaSqrt2) →
-- ℂ where Item G's cliffordTBaseFinder_kmm states its SU(2,ℂ) operator-norm approximation.
import SKEFTHawking.FKLW.RossSelinger.ComplexEmbeddingSqrt2
-- Phase 6x Tier-2 Item G (2026-05-29) — matrix-level ℤ[ω][1/√2] → ℂ embedding. toComplexMat :=
-- ZOmegaSqrt2.toComplex.mapMatrix + toComplexMat_interp (carries the KMM gate word interp gs to
-- ∏ toComplexMat(gateMatrix g)). The matrix abstract↔analytic bridge: KMM output (Mat2 over
-- ZOmegaSqrt2) → Matrix (Fin 2) ℂ. Docstring records the U(2)↔SU(2) global-phase caveat
-- (toComplexMat(gateMatrix T) = e^{iπ/8}·T_SU, phase ∉ ring) handled downstream in the finder.
import SKEFTHawking.FKLW.RossSelinger.ComplexEmbeddingMatrix
-- Phase 6x Tier-2 Item G (2026-05-29) — the KMM-gate → FreeGroup map (phase-bridge defs).
-- gateWord : CliffordTGate → FreeGroup (Fin 2) (H↦of0, T↦of1, S↦T², Z↦T⁴, X↦H·T⁴·H, Y↦X·Z-word,
-- id/ω↦1) + freeword (list lift, the map cliffordTBaseFinder_kmm uses) + gatePhase/phaseProd (the
-- per-gate global phase e^{iπk/8} relating U(2) gateMatrix to SU(2) ρ_CliffT; ∏=±1 for det-1 words).
-- Validated 0/2000 (scripts/phase_bridge_validation.py). Per-gate ρ_CliffT identities = next increment.
import SKEFTHawking.FKLW.RossSelinger.PhaseBridge
-- Phase 6x Tier-2 Items G/H (2026-05-29) — Ross-Selinger grid-problem solver foundation.
-- normSq_mk (normSq(mk z k) = mk (ZOmega.normSq z) (2k)) + assembleUnitary (step (d):
-- M=[[u,-t*],[t,u*]]/√2^k from a solved (u,t) pair). The (a) ε-region + (b) gridSolutions +
-- (c) ℤ[ω] Diophantine (the convex-geometry/number-theory analytic core) are the next
-- increment. (c)+(d) validated end-to-end in scripts/grid_stub_validation.py (exact det-1 SU(2)).
import SKEFTHawking.FKLW.RossSelinger.GridSynth
-- Phase 6x Tier-2 Item G (2026-05-29) — KMM Theorem 1 *converse* (completeness) descent
-- ingredients: reduceStep preserves unitarity + det=ωᵏ (isUnitaryT_reduceStep, det_reduceStep)
-- and reconstruct_box_data_unitary (box-data extraction realizability-free, via unitary_col1).
-- Toward `IsUnitaryT M → (∃k, det M = ωS^k) → IsCliffordTRealizable M`, the direction that makes
-- any constructed SU(2)-over-ℤ[ω][1/√2] unitary (GridSynth.assembleUnitary) synthesizable.
import SKEFTHawking.FKLW.RossSelinger.KMMCompleteness
-- Phase 6x Tier-2 Items H/I (2026-05-29) — deterministic grid-synthesis compiler (sound core):
-- diophantineSearch (bounded ℤ[ω], sound) + gridFindT (+realizable via completeness) +
-- gridSynthWord (kmmReduce) with gridSynthWord_correct (interp = assembleUnitary) + length bound.
-- Runnable end-to-end; the ε-region FINDER completeness (RS §5) is the remaining analytic core.
import SKEFTHawking.FKLW.RossSelinger.GridSolver
-- Phase 6x Tier-2 Item H (2026-05-30) — Ross-Selinger grid FINDER completeness, existence core
-- (DR-grounded, thesis arXiv:1510.02198 Ch.5): oneDim_grid_exists (1-D balanced center-rounding,
-- Lemma 5.2.7) + twoDim_grid_exists (ℤ[ω]=ℤ[√2][i] split, Prop 5.2.9). The existence keystone
-- the FINDER needs (no Step-operator/uprightness machinery — that's for efficient enumeration only).
import SKEFTHawking.FKLW.RossSelinger.GridProblem
-- Phase 6x Tier-2 Item H/I (2026-05-30) — §6 relative-norm foundation (Ross thesis §3.2.2,
-- primary-verified): toComplex_conj (toComplex is a *-hom) + star_omegaC + the total-positivity
-- necessary condition (thesis p.26). The §6 deterministic ∀-target existence (prime-density NT;
-- Selinger 1212.6253 randomized + prime-distribution hypothesis) is the remaining concrete-L≤90 gate.
import SKEFTHawking.FKLW.RossSelinger.RelativeNorm
-- Phase 6x Tier-2 Item G (2026-05-30) — ℤ[√2]=Zsqrtd 2 ring structure for the two-squares sub-arc
-- (Prop 3.2.7): two_ne_sq + IsDomain (via Mathlib Zsqrtd.toReal_injective). First ring-theoretic
-- brick toward two-squares-over-ℤ[√2] (GaussianInt template) → Prop 3.2.7 → unconditional Item G.
import SKEFTHawking.FKLW.RossSelinger.Zsqrt2
-- Phase 6x Tier-2 (2026-05-30) — EuclideanDomain (ℤ[√2]=Zsqrtd 2) via nearest-ℚ(√2)-rounding
-- division with the indefinite-norm Euclidean measure (norm·).natAbs and the rounding-error
-- descent zsqrt2_round_norm_lt. ⟹ ℤ[√2] is a PID/UFD — the two-squares-over-ℤ[√2] (Prop 3.2.7)
-- substrate feeding Item I's residual-t existence (unconditional compile_correct).
import SKEFTHawking.FKLW.RossSelinger.Zsqrt2EuclideanDomain
-- Phase 6x Tier-2 (2026-05-30) — ℤ[√2][i] = Gaussian integers over the ℤ[√2] ED base
-- (structure GaussInt2 + CommRing + multiplicative relative norm re²+im²). The degree-2
-- extension whose splitting gives two-squares-over-ℤ[√2] (Prop 3.2.7) → Item I residual-t.
import SKEFTHawking.FKLW.RossSelinger.Zsqrt2GaussianInt
-- Phase 6AO Track 1(b) (2026-06-09) — conjugation on ℤ[√2][i]=GaussInt2: conj(re+im·i)=re−im·i, a
-- ring hom (conj_add/conj_mul) with x·conj x = ⟨N x, 0⟩ (mul_conj) + norm_conj. Foundation for the
-- GaussInt2 EuclideanDomain division step (x/y = round(x·conj y / N y)).
import SKEFTHawking.FKLW.RossSelinger.Zsqrt2GaussInt2Conj
-- Phase 6AO Track 1(b) (2026-06-09) — ℤ[√2][i]=GaussInt2 is an INTEGRAL DOMAIN (instIsDomain), via
-- its positive-definite relative norm re²+im²: zsqrt2_sq_add_sq_eq_zero (a²+b²=0⟺a=b=0 over ℤ[√2], by
-- integer-coordinate non-negativity — no real embedding) + GaussInt2.norm_eq_zero + NoZeroDivisors.
-- The next brick toward the even-power two-squares-over-ℤ[√2] criterion (Prop 3.2.7).
import SKEFTHawking.FKLW.RossSelinger.Zsqrt2GaussInt2Domain
-- Phase 6AO Track 1(b) (2026-06-10) — ℤ[ω]=ℤ[ζ₈] is a EUCLIDEAN DOMAIN (Mathlib has none): ℤ[i]-pair
-- Gaussian rounding on the {1,ω}-grading (γ=d+bi, δ=c+ai; relative conj = σ5; norm = N_ℤ[i](t·σ5 t)
-- = sum of two squares ⟹ norm_nonneg) with the perpendicular-corner rescue
-- A²+B² = S²−2(e₁(f₁−f₂)+e₂(f₁+f₂))², all-corners value 1/2. Also IsDomain ZOmega, norm_eq_zero_iff
-- (ℤ[√2]-descent via Zsqrtd.norm_eq_zero). ⟹ PID/UFD/gcd for ℤ[ω] — the engine for the paper's
-- Appendix-C gcd arguments (Lemma C.20, t = gcd(ξ, u+i)): Track 1(c). NOTE ℤ[√2][i] (above) is an
-- index-2 NON-integrally-closed subring (paper Lemma 5.5) — never a UFD; the Euclidean layer lives
-- on the full ZOmega.
import SKEFTHawking.FKLW.RossSelinger.ZOmegaEuclideanDomain
-- Phase 6AO Track 1(c) inc 1 (2026-06-10) — ℤ[√2] unit theory (RS 1403.2975v3 Lemma C.2 =
-- Selinger 1212.6253 Lemma 10): zsqrt2_isSquare_of_unit_pos_pos — DOUBLY-POSITIVE UNITS ARE
-- SQUARES, by fundamental-unit descent (λ⁻²=3−2√2 multiplier shrinks im.natAbs; φ<1 branch flips
-- through star INSIDE the recursion at the smaller measure — no unit-group classification needed).
-- Real-embedding order zsqrt2ToReal (= paper's ξ ≥ 0). The unit input Lemma C.16 consumes.
import SKEFTHawking.FKLW.RossSelinger.Zsqrt2Units
-- Phase 6AO Track 1(c) inc 2 (2026-06-10) — RS 1403.2975v3 **Lemma C.16**:
-- relNorm_iff_doublyPositive_decomposable — t†t = ξ solvable in ℤ[ω] ⟺ ξ doubly positive ∧
-- †-decomposable (Defs C.1/C.15). Infrastructure: zsqrt2ToZOmega (ℤ[√2] →+* ℤ[ω], conj-fixed,
-- σ5∘embed = embed∘star, toComplex∘embed = ℝ-cast∘zsqrt2ToReal via s2C_eq), relNormZsqrt2 (the
-- ℤ[√2]-valued t†t) with the NORM TOWER N_ℤ[√2](relNorm t) = N_ℤ[ω](t) ⟹ strict positivity for
-- t ≠ 0 via norm_eq_zero_iff (NO toComplex-injectivity). Unit absorbed by Lemma C.2.
import SKEFTHawking.FKLW.RossSelinger.RelNormSolvability
-- Phase 6AO Track 1(d) (2026-06-10) — RS 1403.2975v3 **Lemma 4.4 SHARP (product form)**:
-- oneDim_grid_exists_product — δ·Δ ≥ (1+√2)² alone gives 1-D grid existence at EVERY position
-- (the asymmetric tiny-ε-region × huge-disk form that Lemma 5.23 / eq.(21)'s
-- k₂ ≤ 2+2log₂(1+√2)+2log₂(1/ε) consumes; center-rounding needed BOTH ≥ 1+√2). Selinger
-- 1212.6253 Lemmas 16–17 formalized: OneDimCoverage moves (mono/swap/λ-rescale via α↦λα,
-- λ•=−λ⁻¹ absorbed by ∀-position), explicit 3-candidate base (1+√2, √2), λ-power bracketing
-- with the swapped family at j+1 rescuing the √2-gap (λ ≥ 2).
import SKEFTHawking.FKLW.RossSelinger.GridExistenceSharp
-- Phase 6AO Track 1(c) inc 3 (2026-06-10) — RS 1403.2975v3 **Lemma C.19**:
-- daggerDecomposable_mul_iff — for coprime α, β ∈ ℤ[√2], αβ †-decomposable ⟺ both are.
-- BEZOUT-ONLY (no GCDMonoid/normalize): s := gcd(t, embed α) in the new EuclideanDomain ZOmega;
-- s·s† ∣ α² (conjHom dvd-transport) ∧ s·s† ∣ t·t† ~ αβ; IsCoprime.map transports Bezout through
-- the embedding ⟹ s·s† ∣ α = xα²+yαβ; conversely gcd_eq_gcd_ab expands s·s† = pp†(tt†)+α(…) ⟹
-- α ∣ s·s†; mutual dvd of CONJ-FIXED elements descends to an ℤ[√2]-unit (conj-fixed ⟺ embedded,
-- by coordinates). Also conjHom (bundled), relNormZsqrt2_mul.
import SKEFTHawking.FKLW.RossSelinger.RelNormMultiplicativity
-- Phase 6AO Track 1(c) inc 4 (2026-06-10) — the EVEN-POWER OBSTRUCTION (RS Lemmas C.20 p≡7(8)
-- case + C.21 odd half): not_daggerDecomposable_of_norm_pow_seven — N(ξ) = ±p^m, p≡7(8), m odd ⟹
-- NOT †-decomposable. Engine: exists_sq_add_sq_of_daggerDecomposable (N(ξ) = ±(a²+b²) via the
-- norm tower + the ℤ[i]-graded Gauss form norm_eq_gauss = the paper's t•t = a+bi) + sums of two
-- squares ≢ 7 (mod 8). Structural positives: daggerDecomposable_pow_even (ξ^{2k} = (ξ^k)²),
-- DaggerDecomposable.pow, relNormZsqrt2_embed.
import SKEFTHawking.FKLW.RossSelinger.RelNormEvenPowerObstruction
-- Phase 6AO Track 1(c) inc 5 (2026-06-10) — RS **Lemma C.20 ENGINE** (positive prime cases):
-- daggerDecomposable_of_prime_dvd_normSq — prime ξ ∣ w·w† with ξ ∤ (w − w†) ⟹ †-decomposable,
-- via t := gcd(embed ξ, w) + dvd_prime_pow three-possibilities (unit case ⟹ IsCoprime to w AND
-- w† (conjHom) ⟹ ξ ∣ normSq w forces ξ unit ✗; ξ²-case ⟹ embed ξ ∣ w ∧ ∣ w† ✗ the difference;
-- middle case = the decomposition). Plus zsqrt2_dvd_descent / zsqrt2_isUnit_descent (ℤ[ω]→ℤ[√2]
-- via conj-fixedness). Both the u²+1 (p≡1 mod 4) and u²+2 (p≡3 mod 8) paper cases are
-- instances (w = u+i, w = u+√2i are conj-pairs: u²+k = normSq w). Specializations next inc.
import SKEFTHawking.FKLW.RossSelinger.RelNormPrimeCase
-- Phase 6AO Track 1(c) inc 6 (2026-06-10) — **C.20 instances + C.21 criterion**:
-- daggerDecomposable_sqrt2 (p=2: √2 = λ⁻¹·δ†δ, δ=1+ω);
-- daggerDecomposable_of_dvd_prime_one_mod_four (w = u+i via ZMod.exists_sq_eq_neg_one_iff) and
-- _three_mod_eight (w = u+√2i via ZMod.exists_sq_eq_neg_two_iff; difference-kills 2ω²·ω² = −2,
-- 2√2i·√2(−i) = 4); not_dvd_two_of_dvd_odd_prime (Bezout 1 = p − 2m);
-- **daggerDecomposable_pow_iff_seven** — Lemma C.21 at the obstructed primes: N(ξ)=±p, p≡7(8):
-- ξ^m †-decomposable ⟺ m EVEN (the even-power criterion, iff form). zsqrtd_norm_pow.
import SKEFTHawking.FKLW.RossSelinger.RelNormPrimeCaseInstances
-- Phase 6AO Track 3 inc 1 (2026-06-10) — **BridgeParity: the structural-bridge core**
-- (toward eliminating bridge_box_core's native_decide): sqrt2_sq_dvd_sq_add_sub —
-- |x|²+|y|² = √2⁴ ∧ √2 ∣ |x|² ⟹ √2² ∣ (x²±y²). Parity toolkit: √2∣|z|² ⟺ √2∣z² ⟺
-- Σcoord even (residue arithmetic, t²≡t); δ = 1+ω with δ² = √2·⟨0,1,1,1⟩ and the explicit
-- divDelta split; equal-parity squares agree mod √2; the mixed case refuted via the halving
-- lemma. Plus dvdSqrt2Pow_sub_conj (the −-twin of the KMM-L5 +1 lemma) and ω-unit transport.
import SKEFTHawking.FKLW.RossSelinger.BridgeParity
-- Phase 6AO Track 3 inc 2 (2026-06-10) — **BridgeStructural: bridge_box_core ELIMINATED**
-- (native_decide 596 → 595). The nine per-entry denExp_bloch_{xx..zz} ≤ 3 bounds for
-- reconstruct x y k under |x|²+|y|² = √2⁴ ∧ √2 ∣ |x|² (each entry's cleared ℤ[ω] numerator
-- carries √2³ via the BridgeParity calculus; denExp_mk_le_three workhorse; per-declaration
-- budgets per Inv #10). Assembled: kSO3_reconstruct_le_three (∀ x y k — NO box, NO finite
-- check) + the moved structural `bridge` (μ ≤ 3 ⟹ kSO3 ≤ 3, Giles–Selinger Cor 7.11).
import SKEFTHawking.FKLW.RossSelinger.BridgeStructural
-- Phase 6x Tier-2 Item I (2026-05-30) — compile_correct approximation helpers:
-- linftyOpNorm_fin_two_le (entrywise ≤δ ⟹ ℓ∞-operator-norm ≤ 2δ for 2×2) + su2_entry_structure
-- (U∈SU(2) ⟹ U=[[a,−b̄],[b,ā]]). Propagate the grid first-column approximation to ‖·‖≤ε.
import SKEFTHawking.FKLW.RossSelinger.CompileApprox
-- Phase 6x Tier-2 Item I (2026-05-30) — compile_correct core: ZOmegaSqrt2.toComplex_conj
-- (toComplex is a *-hom) + linftyOpNorm_sub_le_of_su2_col (two SU(2)-form matrices agreeing on
-- the first column within ε ⟹ ‖·‖ ≤ 2ε). The soundness backbone of the Ross-Selinger compile.
import SKEFTHawking.FKLW.RossSelinger.GridCompileCorrect
-- Phase 6x Tier-2 Item H (2026-05-30) — the constructive Ross-Selinger grid SOLVER:
-- oneDimGridSolution / twoDimGridSolution (center-rounding witnesses of GridProblem's existence,
-- exposed as runnable functions) + correctness. Upright-case §5 grid solutions; composes with
-- gridFindT + assembleUnitary + kmmReduce (compile_correct_core) for the target-level compile.
import SKEFTHawking.FKLW.RossSelinger.GridSolutions
-- Phase 6x Tier-2 Item H (2026-05-30) — the Ross-Selinger §5 Thm-2 upright grid ENUMERATION:
-- gridSolutions1D lo hi lo' hi' = the finite set of all (m,n)∈ℤ² with m+n√2 ∈ [lo,hi] and its Galois
-- conjugate m−n√2 ∈ [lo',hi'] (m-scan ⌈(lo+lo')/2⌉..⌊(hi+hi')/2⌋, per-m n-scan), with
-- gridSolutions1D_mem_iff (correctness + completeness: membership ⇔ the four real bounds) +
-- gridSolutions1D_card_le (count bound). Cross-validated vs pygridsynth.odgp.solve_ODGP (180/180
-- boxes, 4851 solutions, exact set match) in scripts/grid_enum_pygridsynth_xval.py.
import SKEFTHawking.FKLW.RossSelinger.GridEnum
-- Phase 6x Tier-2 Item I (2026-05-30) — the runnable Ross-Selinger compile : SU(2)→(k,b)→
-- Option(Clifford+T word) (round first column via twoDimGridSolution → gridFindT residual →
-- gridCompile=kmmReduce∘assembleUnitary) + compile_correct SOUNDNESS (finder returns + columns
-- within ε ⟹ ‖toComplexMat(interp word)−U‖≤2ε), composing gridCompile_correct + approx_assembleUnitary.
import SKEFTHawking.FKLW.RossSelinger.Compile
-- Phase 6x Tier-2 Item G (2026-05-30) — the KMM-derived Clifford+T base finder in the ρ_CliffT/
-- FreeGroup headline picture: signCorrect (±1-sign-corrected freeword, killing the U(2)↔SU(2)
-- residual phase via H·H), the keystone coe_ρ_CliffT_signCorrect (det-1 word ⟹ ρ_CliffT image =
-- toComplexMat interp, UNCONDITIONAL), signCorrect_kmmReduce_resynth (KMM re-synthesis at honest
-- N₃+4·sde length, UNCONDITIONAL), and cliffordTBaseFinder_kmm + _approx/_headline (the ρ_CliffT-
-- picture SOUNDNESS lift of compile_correct). Composes nonempty_kmmReduction + the phase bridge.
import SKEFTHawking.FKLW.RossSelinger.CliffordTBaseFinderKMM
-- Phase 6AM W5 (2026-06-09): Ross–Selinger O(log 1/ε) word-length headline (exponent 1, vs SK log^3.97).
import SKEFTHawking.FKLW.RossSelinger.LogLengthHeadline
-- Phase 6AO Track 2 (2026-06-09): KMM ancilla mechanism — exists_two_relativeNorms_of_nat (every r:ℕ
-- is a sum of two ℤ[ω] relative norms, via Lagrange Nat.sum_four_squares) + ancilla_completion_of_nat_residual
-- (the (1+ancilla)-qubit unit column closes UNCONDITIONALLY — no relative-norm/prime-density hypothesis,
-- unlike the ancilla-free rossSelinger_synth_of_residual). The number-theoretic core that removes the W5 wall.
import SKEFTHawking.FKLW.RossSelinger.AncillaCompletion
-- Phase 6AO Track 2 (2026-06-09): two-qubit Clifford+T gate semantics (system + ancilla) — Gate2 ADT,
-- gateMatrix2/interp2 over Matrix (Fin 2 × Fin 2), kronecker embeddings embedFst/embedSnd (monoid homs),
-- realizability transport embedFst_interp (single-qubit kmmReduce word → 2-qubit word, SAME length) +
-- cnot involutions (kernel decide). Foundation for the ancilla-extended O(log 1/ε) Clifford+T circuit.
import SKEFTHawking.FKLW.RossSelinger.CliffordTGate2
-- Phase 6AO Track 2 (2026-06-09): unconditional normalized ancilla state column — ancillaColNormSq
-- (3-entry extension of KMM.colNormSq) + exists_ancilla_normalized_column (for an integer-residual
-- approximant u, the cleared column (u,t₁,t₂)/√2^k is a UNIT vector unconditionally — the KMM-ancilla
-- "existence" at the ℤ[ω][1/√2] amplitude level, no relative-norm hypothesis). Lifts the inc-1 keystone.
import SKEFTHawking.FKLW.RossSelinger.AncillaState
-- Phase 6AO Track 2 (increment 8; 2026-06-09): unconditional amplitude approximation (rounding → ε) —
-- exists_round_toward_zero + toComplex_gaussian_approx (the embedding sends the KMM Gaussian approximant
-- m₁+m₂·ω² at denominator 2k to its analytic amplitude (m₁+m₂·i)/2^k) + kmm_amplitude_approx
-- (‖u/2^k − e^{iφ}‖ ≤ √2/2^k, disk-bounded, UNCONDITIONAL) + kmm_ancilla_state_approx (the milestone:
-- the normalized KMM ancilla state approximating e^{iφ} exists for every (φ,k), no prime-density hypothesis).
import SKEFTHawking.FKLW.RossSelinger.AmplitudeApprox
-- Phase 6AO Track 2 (increment 9; 2026-06-09): the KMM leakage bound (dominant O(2^{−0.5k}) error) —
-- toComplex_normSq (ring norm → complex squared modulus) + kmm_ancilla_state_full (normalized +
-- amplitude within √2/2^k of e^{iφ} + total ancilla-|1⟩ leakage ≤ 2·√2/2^k, all UNCONDITIONAL via
-- inc-8 amplitude bound + reverse triangle). Completes the error-budget half of ‖W − Λ(e^{iφ})⊗I‖ ≤ ε.
import SKEFTHawking.FKLW.RossSelinger.AncillaLeakage
-- Phase 6AO Track 2 (increment 10; 2026-06-09): the dim-4 column-synthesis backbone — IsColRealizableWithin
-- (a column is M·e₀ of a Gate2 word of length ≤ L), IsColRealizableWithin.smul_left (the induction
-- backbone: G realizable + v col-realizable ⟹ G·v col-realizable, budgets add), isColRealizableWithin_e0
-- (base anchor |00⟩). The skeleton the dim-4 Column Lemma induction (on denominator exponent) is built on.
import SKEFTHawking.FKLW.RossSelinger.ColumnSynthesis
-- Phase 6AO Track 2 (increment 11; 2026-06-09): the dim-4 column-lemma base-case number theory —
-- normSq_eq_one_iff_omega_pow (|z|²=1 ⟺ z=ωᵏ, k<8: the modulus-1 elements of ℤ[ω] are exactly the
-- 8th roots of unity, via elementary sum-of-four-squares — no Galois/Kronecker) + normSq_eq_zero_iff
-- (|z|²=0 ⟺ z=0). The denExp-0 unit-column structure (one unit entry ⟹ ωᵏ·eᵢ realizable) builds on these.
import SKEFTHawking.FKLW.RossSelinger.ColumnBaseCase
-- Phase 6AO Track 2 (increment 14; 2026-06-09): the dim-4 column-lemma base case ASSEMBLED —
-- Gate2.base_case (a denExp-0 unit column v : Fin 2 × Fin 2 → ℤ[ω][1/√2] is column-realizable): the
-- denExp-0 entries are ℤ[ω]-valued (denExp_le_iff k=0), Σ|v i|²=1 transports to ℤ[ω] (normSq_of, of inj),
-- the structure gives ωᵏ·e_{i₀} (inc 11/12), realizable by inc 13. The column-lemma induction anchor.
import SKEFTHawking.FKLW.RossSelinger.ColumnBaseRealizable
-- Phase 6AO Track 2 (increment 16; 2026-06-09): the elementary matching-residue reduction engine —
-- dividesSqrt2_add_of_dividesSqrt2_sub (x≡y mod √2 ⟹ √2 ∣ x±y, since x+y=(x−y)+2y) +
-- denExp_mk_succ_le_of_dividesSqrt2 (√2-divisible numerator at level k+1 clears to denExp ≤ k). The
-- kernel-pure core of the dim-4 ReductionStep — NO kmm_lemma3/native_decide (that proves optimal T-count;
-- the column lemma needs only *some* reduction). ⟹ kernel-pure synthesis likely independent of Track 3.
import SKEFTHawking.FKLW.RossSelinger.MatchingResidue
-- Phase 6AO Track 2 (increment 18; 2026-06-09): Giles–Selinger residue-norm classification —
-- normSq_cd_not_both_odd (|z|² has residue norm mod 2 in {0000,0001,1010}, never 1011: (|z|².c,|z|².d)
-- never both odd, since Q≡(a+c)(b+d), P≡(a+c)+(b+d), so Q odd ⟹ P even). The number-theoretic entry
-- point to the Giles–Selinger column-lemma reduction (Lemma 5 parity); kernel decide over (ZMod 2)⁴.
import SKEFTHawking.FKLW.RossSelinger.GilesSelingerResidue
-- Phase 6AO Track 2 (increments 22–27; 2026-06-09): Giles–Selinger Lemma-4 row operation. inc 22
-- core_step; inc 23 exists_sqrt2_match (√2-match ∃m∈{0,1}); inc 24 exists_mod2_align_of_normSq_c_odd +
-- lemma4_1010 (the 1010 case in one H·Tᵐ); inc 25 normSq_c_mod4_all_odd + divSqrt2_normSq_c_odd (brick B′
-- mod-4 core: all-odd z ⟹ (normSq z).c ≡ 2 mod 4 ⟹ divSqrt2 z is 1010 — the cross-orbit step1's
-- 1111-sum lands both outputs in 1010 for lemma4_1010); inc 26 matched_active_dichotomy (the UNIFORM
-- case-split: matched-active pair ⟹ mod-2 ω-aligned [core_step] ∨ step1-able-to-all-odd [→ lemma4_1010];
-- one ZMod 2 decide + parity bridge — the decision ReductionStep consumes); inc 27 step1_combo_eq/_sub +
-- cross_orbit_drop (cross-orbit 2-step: H·Tᵐ on an all-odd combo keeps the level with 1010 numerators, then
-- lemma4_1010 — discharges BOTH dichotomy branches ⟹ full Lemma 4 at the pair level). Kernel decide only
-- (√2·√2=2 ; ZMod 2/ZMod 4), native_decide held at 596.
import SKEFTHawking.FKLW.RossSelinger.GilesSelingerRowOp
-- Phase 6AO Track 2 (inc 29, 2026-06-10): the controlled-gate block algebra + det-balanced row-op gadget —
-- ctrl P Q (fst-controlled blockdiag) with the ctrl_mul block algebra; CH = ctrl 1 H realized EXACTLY as an
-- 18-gate Gate2 word (conjugator V = S·H·T·H·S†·H with V·X·V⁻¹ = H; decide +kernel = pure kernel reduction,
-- same trust base as decide, no native_decide); rowOpGadget m = ctrl Tᵐ (H·Tᵐ) = CH·(I⊗Tᵐ) — the
-- det-balanced Lemma-4 row op (the bare two-level H·Tᵐ has det −ωᵐ ∉ ⟨ω²⟩ for odd m, NOT Gate2-realizable;
-- the unconditional I⊗Tᵐ phase balances it for all m) + realizability ≤ 18+m + inverse + the exact column
-- action (verbatim the core_step / cross_orbit_drop pair shapes; spectators get a harmless ωᵐ unit phase).
import SKEFTHawking.FKLW.RossSelinger.Gate2Control
-- Phase 6AO Track 2 (inc 30, 2026-06-10): basis-permutation words + the pair-alignment table — permMat f
-- (pullback convention: (permMat f).mulVec v = v ∘ f) + anti-composition permMat_mul; the 4 Gate2
-- permutation generators (cnot01/cnot10/X⊗I/I⊗X) identified as permMats of explicit involutions; and
-- exists_pair_alignment: EVERY ordered pair p ≠ q of column indices is pulled into the gadget's canonical
-- slots {(1,0),(1,1)} by mutually-inverse ≤5-gate perm words realizing permMat e / permMat e.symm
-- (12-case table, kernel decide). Conjugating the inc-29 gadget by these words = the row op at (p,q).
import SKEFTHawking.FKLW.RossSelinger.Gate2Perm
-- Phase 6AO Track 2 (inc 31, 2026-06-10): the single-pair column drop — exists_pair_drop: for a column at
-- level t+1 with a matched-active numerator pair p ≠ q, a realizable G (+ realizable inverse, Ginv·G = 1,
-- both ≤ 70 gates: alignment-conjugated row-op gadgets) drops BOTH pair entries to denExp ≤ t, leaves every
-- spectator's denExp unchanged (unit phases only), and preserves the unit-column normSq-sum. Dichotomy
-- branches: aligned = one gadget + core_step; cross-orbit = two gadgets + cross_orbit_drop. Helper layer:
-- ω⁸ = 1 + exponent capping (budget-bounded phases), denExp/normSq unit-phase invariance, the
-- √2-parallelogram law, mk-numerator extraction, denExp (mk z (k+1)) = k+1 ⟺ ¬dividesSqrt2 z.
import SKEFTHawking.FKLW.RossSelinger.GilesSelingerPairDrop
-- Phase 6AO Track 2 (inc 32–33, 2026-06-10): ReductionStep DISCHARGED + the UNCONDITIONAL dim-4
-- Giles–Selinger column lemma — reductionStep_holds : ReductionStep 280 (numerator-sum bridge
-- Σ|wᵢ|² = 2^{t+1} ⟹ Lemma-5 matched pair exists ⟹ exists_pair_drop removes it; active-set descent,
-- ≤4 rounds/level); column_lemma_bounded: EVERY unit ℤ[ω][1/√2] column is the first column of an exact
-- 2-qubit Clifford+T word of length ≤ 280·colDenExp + 9 (LINEAR in the denominator exponent = the
-- O(log 1/ε) count the KMM ≤2-ancilla headline consumes) + the existential form. Circuit C exact
-- synthesis complete. Kernel-pure {propext, Classical.choice, Quot.sound}.
import SKEFTHawking.FKLW.RossSelinger.GilesSelingerColumnLemma
-- Phase 6AO Track 2 (inc 34, 2026-06-10): three-qubit Clifford+T gate semantics (system + 2 ancillas) —
-- Gate3 ADT (single-qubit on each line + all 6 directed cnots), Mat8 = system × (anc₁ × anc₂) so the
-- ancilla pair carries the Mat4 index natively; embedAnc (M ↦ I₂⊗M) with the faithful length-preserving
-- transport embedAnc_interp2 (the column-lemma circuit C rides onto the register at no length cost);
-- embedSys; IsRealizable3Within + additive composition. The register the controlled-C lift lives on.
import SKEFTHawking.FKLW.RossSelinger.CliffordTGate3
-- Phase 6AO Track 2 (inc 35, 2026-06-10): the system-controlled lift — ctrl8 block algebra; Toffoli via the
-- CCZ phase-polynomial word 4sab = s+a+b−(s⊕a)−(a⊕b)−(s⊕b)+(s⊕a⊕b) (kernel-verified, decide +kernel at
-- top level where the kernel check is budget-free); ctrlLift per-gate rule (target-diagonal T/S/Z/id lift
-- UNCONTROLLED — their s=0 block fixes |00⟩, sidestepping the det-impossible controlled-T; X→CNOT, Y→S-conj,
-- H→V-conjugated CNOT, cnots→Toffoli, ω→T_sys); ctrlLift_word_spec: EVERY Gate2 word w lifts to a Gate3 word
-- ≤ 30·|w| with interp3 = ctrl8 D (interp2 w), D |00⟩-fixing — applied to the column-lemma word = KMM's
-- controlled-C. Kernel-pure.
import SKEFTHawking.FKLW.RossSelinger.Gate3Control
-- Phase 6AO Track 2 (inc 36, 2026-06-10): THE KMM Z-ROTATION HEADLINE WORD — kmm_z_rotation_word: ∀ φ k,
-- an explicit 3-qubit Clifford+T word W of length ≤ 16800·k + 270 (LINEAR in k = O(log 1/ε) exponent 1,
-- ε = √2/2^k) realizing controlled-C UNCONDITIONALLY (no prime-density hypothesis; only Lagrange
-- four-squares + the constructive column lemma): the |0,00⟩ column RING-EXACT (FixesE00), the |1,00⟩
-- column = |1⟩⊗|v⟩ with v a unit column, v(0,1)=0, |00⟩-amplitude within √2/2^k of e^{iφ}, ancilla
-- leakage ≤ 2√2/2^k. By linearity = the full KMM ≤2-ancilla guarantee on ancilla-initialized inputs.
import SKEFTHawking.FKLW.RossSelinger.KMMZRotationHeadline
-- Phase 6AO Track 2 (inc 37, 2026-06-10): unitarity of three-qubit words + the ℂ-norm transport —
-- adjoint8/IsUnitary8 (ring-level conj-transpose at dim 8); EVERY Gate3 generator unitary (ONE kernel
-- reduction over the 30-element Fintype, decide +kernel top-level); interp3_unitary (word induction);
-- toComplexMat8 intertwines adjoint8 with ᴴ (toComplex_conj *-hom) ⟹ embedded words ℂ-UNITARY;
-- sumNormSq (squared ℓ² on ℂ⁸) preserved by embedded words — the norm-preservation the ∀U error
-- composition consumes (intermediate states leave the initialized subspace).
import SKEFTHawking.FKLW.RossSelinger.Gate3Unitary
-- Phase 6AO Track 2 (inc 38, 2026-06-10): the OPERATIONAL KMM z-rotation bound on ℂ⁸ —
-- kmm_z_rotation_operational: ∀ φ k ∃ W (length ≤ 16800k+270), ∀ α β: the embedded word maps the
-- initialized state (α|0⟩+β|1⟩)⊗|00⟩ within SQUARED ℓ²-distance |β|²·(2/4^k + 2√2/2^k) of the ideal
-- α|000⟩ + β·e^{iφ}|100⟩ — KMM's |β(e^{iφ}−γ)|² + |β|²‖g‖² error, O(2^{-k}) in squared distance.
-- initState/targetState; mulVec_two_support collapse; 8-index difference computation.
import SKEFTHawking.FKLW.RossSelinger.KMMOperational
-- Phase 6AO Track 2 (inc 39 substrate, 2026-06-10): SU(2) Euler decomposition substrate — lamC (the
-- Λ(φ) = diag(1, e^{iφ}) target), hC (the ℂ-Hadamard matching toComplexMat_gateMatrix_H), the half-angle
-- identities 1 ± e^{iθ} = (2cos / −2i·sin)(θ/2)·e^{iθ/2}, and eulerProd_eq: the closed form of
-- Λ(φ₁)·H·Λ(φ₂)·H·Λ(φ₃) = ½[[1+e₂, (1−e₂)e₃],[e₁(1−e₂), e₁e₃(1+e₂)]]. Toward the ∀U∈SU(2)
-- up-to-global-phase decomposition (the LAST Track-2 piece).
import SKEFTHawking.FKLW.RossSelinger.SU2Euler
-- Phase 6AO Track 2 (inc 40 part 1, 2026-06-10): ∀U composition machinery — the ℓ²-bridge
-- (sumNormSq = ‖·‖² in EuclideanSpace) and step_triangle: one composition step's errors add through
-- a unitary word prefix (triangle + sumNormSq_mulVec_interp3 norm preservation).
import SKEFTHawking.FKLW.RossSelinger.KMMUniversal
-- Phase 6AO Track 2 (2026-06-09): system-line synthesis on the two-qubit register — embedFst_kmmReduce_interp
-- (interp2 ((kmmReduce M).map onFst) = embedFst M: the shipped single-qubit KMM synthesis realizes M⊗I on
-- the system line) + embedFst_kmmReduce_length (same KMM length bound N₃+4·denExp, no length cost). Connects
-- the 2-qubit semantics to the verified kmmReduce; building block for the ancilla circuit's system-line ops.
import SKEFTHawking.FKLW.RossSelinger.AncillaSynthesisBridge
-- Phase 6x Tier-2 Item F (M4; 2026-05-29) — denExp is non-archimedean +
-- KMM Lemma 4 core. denExp_neg, denExp_add_le (sub-additive),
-- denExp_add_eq_max_of_ne (valuation equality on distinct exponents), and
-- denExp_normSq_col0_eq (unitary M ⟹ denExp|M₀₀|² = denExp|M₁₀|²) — the
-- equal-column-sde fact KMM Lemma 4 supplies, proved from the |z|²+|w|²=1
-- column identity + non-archimedean valuation.
import SKEFTHawking.FKLW.RossSelinger.DenExpValuation
-- Phase 6x Track M.4 actual extraction (Mathlib-PR-quality ship,
-- 2026-05-26): re-exports the α-polymorphic FreeGroup length bound
-- (Track 2's GenericConcreteWordLengthBound) under the Mathlib-style
-- namespace Matrix.SolovayKitaev.LengthBound. Filename mirror
-- Mathlib.Analysis.MatrixGroups.SolovayKitaev.LengthBound.
import SKEFTHawking.SolovayKitaevLengthBoundMathlibPR
-- Phase 6x Track M.1 actual extraction (Mathlib-PR-quality ship,
-- 2026-05-26): order-2 Baker-Campbell-Hausdorff cubic estimate at
-- Matrix (Fin d) (Fin d) ℂ under Matrix.BCH namespace. Substantive
-- substrate: Matrix.linftyOpNorm_reindex (L∞ op norm invariant under
-- reindex). Filename mirror Mathlib.Analysis.Calculus.BCH.OrderTwo.
-- SU(2)/SU(4)/SU(8) examples shipped.
import SKEFTHawking.MatrixBCHCubicMathlibPR
-- Phase 6x Track M.2 actual extraction (Mathlib-PR-quality ship,
-- 2026-05-26): Cartan-final-step density-from-witness at SU(2) under
-- Matrix.SpecialUnitary.Cartan namespace, fully Mathlib-namespaced
-- predicate (no project-namespace references in finalStepV2). Bridge
-- to project's CartanFinalStep_SU2_v4 + UNCONDITIONAL discharge.
-- Filename mirror Mathlib.Analysis.MatrixGroups.SpecialUnitary.Cartan.
-- SU(d) → Phase 6y Track S.
import SKEFTHawking.CartanFinalStepSUdMathlibPR
-- Phase 6x Tier-1 residual Item C (Mathlib-PR-quality re-presentation,
-- 2026-05-27): SU(d) compactness substrate packaged for upstream
-- submission. Re-exports Matrix.{unitaryGroup,specialUnitaryGroup}
-- _{isClosed,isCompact} from Phase 6p Wave 2c.4a-substrate
-- (FKLW.SpecialUnitaryTopology) with worked SU(2)/SU(3) examples.
-- Closes orphan #6 from the 2026-05-27 audit addendum.
import SKEFTHawking.SU2CompactnessMathlibPR
-- Phase 6y Track S.1 (2026-05-27): generic SU(d) generating-set framework.
-- d-parametric lift of Phase 6u GenericSU2.GeneratingSet to arbitrary
-- matrix dimension d (carrier ρ_hom : W →* specialUnitaryGroup (Fin d) ℂ).
-- Substrate keystone for the Phase 6y SU(d) extension chain (S.2 Cartan
-- v4 at SU(d), S.3 Dawson-Nielsen at 𝔰𝔲(d), S.4 d-dependent Lipschitz,
-- S.5 generic discharge, S.6 generic bundled-strict headline). Bridge
-- ofGenericSU2 : GenericSU2.GeneratingSet → GeneratingSet 2 preserves
-- H_of_G definitionally.
import SKEFTHawking.FKLW.GenericSUdGeneratingSet
-- Phase 6y Track S.2a (2026-05-27): generic SU(d) Cartan-final-step v4
-- predicate definition. CartanFinalStep_SUd_v4 (d : ℕ) — the Cartan
-- closed-subgroup theorem specialized to SU(d): closed H ≤ SU(d) with
-- flow lines of spanning traceless skew-Hermitian tangents ⟹ H = ⊤.
-- Substantive discharge ships in GenericSUdCartanSubstrate (S.2b–d).
import SKEFTHawking.FKLW.GenericSUdCartanPredicate
-- Phase 6y Track S.2b (2026-05-27): d-generic matrix-exp local diffeomorphism
-- via Mathlib IFT (`HasStrictFDerivAt.toOpenPartialHomeomorph`). Ships
-- `expAmbient d`, `expAmbient_hasStrictFDerivAt_zero_equiv d`,
-- `expAmbientPartialHomeo d`, `matrixLog d`, round-trip identities, and
-- local injectivity. d-generic lift of Phase 6u `SU2LocalDiffeo`.
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo
-- Phase 6y Track S.2c (2026-05-27): matrix log of unitary near 1 is
-- skew-Hermitian. For h ∈ SU(d) close to 1, the local matrix log
-- `matrixLog d h` satisfies `(matrixLog d h).IsSkewHermitian`. Composes
-- `Matrix.exp_conjTranspose` + `Matrix.exp_neg` + S.2b's local exp
-- injectivity + the symmetric-source-nbhd topological argument. Half
-- of the substrate for S.2's discharge (traceless half ships separately).
import SKEFTHawking.FKLW.GenericSUdMatrixLogSkewHerm
-- Phase 6y Track M-S.2 (2026-05-27): Mathlib-PR-quality presentation of
-- the matrix exp local homeomorphism at 0. Ships under the Matrix
-- namespace: `Matrix.expOpenPartialHomeomorphAt_zero d`,
-- `Matrix.exp_isLocalHomeomorph_zero`, `Matrix.map_nhds_zero_exp`.
-- ACTUAL extraction (per Phase 6x failure mode #3): de-namespaced,
-- generic-typed, Mathlib-style docstrings + SU(2)/SU(4)/SU(8) examples.
-- Filename mirror Mathlib.Analysis.Normed.Algebra.MatrixExponential.
import SKEFTHawking.MatrixExpLocalHomeomorphMathlibPR
-- Phase 6y Track M-S.1 (2026-05-27): Mathlib-PR-quality d-generic
-- Cartan-final-step density-from-witness predicate at SU(d). Ships under
-- the Matrix.SpecialUnitary.Cartan namespace: `finalStepVd (d : ℕ)`.
-- ACTUAL extraction (de-namespaced, generic-typed). Bridges to project's
-- `CartanFinalStep_SUd_v4` via `finalStepVd_iff_project` (= rfl).
-- Discharge (the d-generic chain) ships in follow-on commits via
-- the S.2-d-e-f Lie-theory substrate. Filename mirror
-- Mathlib.Analysis.MatrixGroups.SpecialUnitary.Cartan.
import SKEFTHawking.CartanFinalStepSUdGenericMathlibPR
-- Phase 6y Track S.2d (2026-05-27): Jacobi formula `det(exp Y) = exp(tr Y)`
-- for skew-Hermitian Y. Foundational helpers + full composition via
-- spectral theorem on iY (Hermitian). Ships
-- `det_exp_skewHermitian Y hY` (substantive, SU(d) Jacobi). Mathlib
-- v4.29.1 has the general-A version as TODO; this skew-Hermitian
-- specialization unblocks Phase 6y's S.2g discharge chain.
import SKEFTHawking.FKLW.GenericSUdDetExpSkewHerm
-- Phase 6y Track S.2e (2026-05-27): exp(tr Y) = 1 when Y = matrixLog d h
-- for h ∈ SU(d) near 1. Composes S.2c (skew-Hermitian preservation) +
-- S.2d (Jacobi). Ships `exp_trace_matrixLog_eq_one_on_nhd_one d`.
-- Traceless conclusion `tr Y = 0` follows via small-norm exp-injectivity
-- on ℂ near 0, shipped in S.2g discharge.
import SKEFTHawking.FKLW.GenericSUdMatrixLogTraceless
-- Phase 6y Track S.2g-substrate (2026-05-27): trace norm bound
-- `|tr Y| ≤ d * ‖Y‖` for Y : Matrix (Fin d) (Fin d) ℂ in linftyOp norm.
-- Combined with S.2e exp(tr Y) = 1 and small-norm injectivity of
-- Complex.exp on a disk around 0, gives tr Y = 0 for matrixLog of
-- SU(d) elements near 1 (S.2g discharge).
import SKEFTHawking.FKLW.GenericSUdTraceNorm
-- Phase 6y Track T-A1′.1-substrate (2026-05-27): SU(4) trapped-ion gate
-- helpers via Kronecker product + reindex (Fin 2 × Fin 2 ≃ Fin 4).
-- Ships kronSU4 + H_SU_on_ion1, H_SU_on_ion2, T_SU_on_ion1, T_SU_on_ion2
-- (single-qubit-on-ion-i SU(4) gates). Substrate for trappedIonGenerating-
-- SetSU4 full instance (T-A1′.1 proper).
import SKEFTHawking.FKLW.TrappedIonSU4Substrate
-- Phase 6y Track T-A2′.1-substrate (2026-05-27): SU(8) Clifford+CCZ
-- Hadamard-on-qubit-i helpers via Kronecker products (Fin 4 × Fin 2 ≃ Fin 8
-- and Fin 2 × Fin 4 ≃ Fin 8). Ships kronSU4SU2, kronSU2SU4, plus the
-- three Hadamards H_SU_on_qubit{1,2,3} on the 3-qubit Hilbert space.
-- Combined with Phase 6x's CCZ_mat, forms the alphabet for
-- cliffordCCZGeneratingSetSU8 full instance (T-A2′.1 proper).
import SKEFTHawking.FKLW.CliffordCCZSU8Substrate
-- Phase 6y Track T-A1′.1-partial (2026-05-27): trapped-ion 1Q-only
-- GeneratingSet 4 instance using the 4 packaged SU(4) gates
-- {H_SU_on_ion1, T_SU_on_ion1, H_SU_on_ion2, T_SU_on_ion2}. Substantive
-- intermediate ship toward T-A1′.1 proper (which adds MS(θ) at
-- rational-π/N grid once MSGateMat SU(4) membership ships).
import SKEFTHawking.FKLW.TrappedIonGeneratingSetSU4Partial
-- Phase 6y Track T-A2′.1-partial (2026-05-27): Clifford-only 3-Hadamard
-- GeneratingSet 8 instance using the 3 packaged SU(8) Hadamards
-- {H_SU_on_qubit1, H_SU_on_qubit2, H_SU_on_qubit3}. Substantive
-- intermediate toward T-A2′.1 proper (adds CCZ_SU once
-- CCZ_SU_mem_specialUnitaryGroup ships).
import SKEFTHawking.FKLW.CliffordCCZGeneratingSetSU8Partial
-- Phase 6y Track T-A2′.1-substrate (2026-05-27): phase-corrected CCZ
-- for SU(8). Ships `CCZ_SU := ω • CCZ_mat` with ω = e^(iπ/8) so that
-- ω^8 · det(CCZ_mat) = -1 · -1 = 1 (CCZ_SU ∈ SU(8)).
-- `CCZ_SU_mem_specialUnitaryGroup` + `CCZ_SU_subtype` packaged.
import SKEFTHawking.FKLW.CCZ_SU
-- Phase 6y Track T-A2′.1 PROPER (2026-05-27): full
-- `cliffordCCZGeneratingSetSU8 : GeneratingSet 8` instance for the
-- 4-generator Clifford+CCZ alphabet {H_q1, H_q2, H_q3, CCZ_SU}.
-- Substantively closes T-A2′.1 — all 4 generators packaged as SU(8)
-- subtype elements; FreeGroup (Fin 4) word type.
import SKEFTHawking.FKLW.CliffordCCZGeneratingSetSU8Full
-- Phase 6y Track T-A2′.2 (D) witness (2026-05-28): the 63 tensor-Pauli tangents of 𝔰𝔲(8)
-- (kronSU8 + hX_in_sud; alphabet-agnostic, shared by any universal SU(8) gate set).
import SKEFTHawking.FKLW.CliffordCCZSU8Tangents
-- Phase 6y Track T-A2′.2 (D) witness (2026-05-28): the 63 tensor-Pauli tangents ℝ-span 𝔰𝔲(8)
-- (hX_spans via Hilbert-Schmidt completeness; alphabet-agnostic).
import SKEFTHawking.FKLW.CliffordCCZSU8TangentSpan
-- Phase 6y Track T-A2′.2 (D) witness (2026-05-28): per-qubit SU(2)→SU(8) embedding monoid homs
-- (qubit{1,2,3}Embed) + continuity; alphabet-agnostic substrate for the per-qubit flow lines.
import SKEFTHawking.FKLW.CliffordCCZSU8QubitEmbed
-- Phase 6y Track T-A2′.2 (D) witness (2026-05-28): exp commutes with the per-qubit SU(2)→SU(8)
-- embeddings (qubit{1,2,3}MatRingHom + NormedSpace.map_exp); alphabet-agnostic flow-line substrate.
import SKEFTHawking.FKLW.CliffordCCZSU8ExpCommute
-- Phase 6y Track T-A2′.1 (2026-05-28): universal Clifford+CCZ+T gate substrate — per-qubit
-- T-gates T_SU_on_qubit{1,2,3}_SU8 := qubit_iEmbed T_SU + Hadamard-embedding bridges.
import SKEFTHawking.FKLW.CliffordCCZSU8UniversalGates
-- Phase 6y Track T-A2′.1 (2026-05-28): CNOT₁₂/₁₃/₂₃ as SU(8) even-permutation matrices
-- (permMatrix; det = sign = 1) — cross-qubit Clifford generators for the universal alphabet.
import SKEFTHawking.FKLW.CliffordCCZSU8CNOT
-- Phase 6y Track T-A2′.2 (D) witness (2026-05-28): per-qubit containment
-- qubit_iEmbed(SU(2)) ⊆ H_of_G(universal alphabet) via the Clifford+T density factorization.
import SKEFTHawking.FKLW.CliffordCCZSU8PerQubitContainment
-- Phase 6y Track T-A2′.2 (D) witness (2026-05-28): the 9 per-qubit single-qubit tangent flow lines
-- exp(t·X_{a00/0b0/00c}) ∈ H_of_G via Clifford+T density through the per-qubit embeddings.
import SKEFTHawking.FKLW.CliffordCCZSU8PerQubitFlow
-- Phase 6y Track T-A2′.2 (D) witness (2026-05-28): entangler-spread foundation — CNOT involutions
-- + generic permMatrix conjugation = index relabel + validated base CNOT Pauli-conjugation.
import SKEFTHawking.FKLW.CliffordCCZSU8EntanglerSpread
-- Phase 6y Track T-A2′.2 (D) witness (2026-05-28): factor-wise conjugation — qubit_iEmbed(C) rotates
-- only tensor slot i (pure Kronecker mixed-product algebra + per-qubit inverse bridge).
import SKEFTHawking.FKLW.CliffordCCZSU8FactorConj
-- Phase 6y Track T-A2′.2 (D) witness (2026-05-28): the 54 entangling tangent flow lines — CNOT base
-- entanglers + per-qubit Clifford rotation spread (conjugation transport) → full suEightTangent_flow.
import SKEFTHawking.FKLW.CliffordCCZSU8EntanglerFlow
-- Phase 6y Track S.2-consumer (2026-05-27): generic SU(d) ClosureDenseWitness
-- structure for `GeneratingSet d`. Bundles n traceless skew-Hermitian
-- spanning tangents + flow-line containment in H_of_G gs. Conditional
-- dispatch into `H_of_G gs = ⊤` via S.2 CartanFinalStep_SUd_v4 predicate.
-- Consumer-facing substrate for T-A1′.2 and T-A2′.2 closure-density.
import SKEFTHawking.FKLW.GenericSUdClosureDenseWitness
-- Phase 6y Track S.4 (2026-05-27): matrix log Lipschitz-style smallness
-- bound on a nbhd of 1 in SU(d). For any ε > 0, ∃ δ > 0 such that
-- ‖h - 1‖ < δ ∧ h ∈ target ⟹ ‖matrixLog d h‖ < ε. Continuity-derived
-- form of the Y_h Lipschitz constant Phase 6u shipped for SU(2).
import SKEFTHawking.FKLW.GenericSUdMatrixLogLipschitz
-- Phase 6y Track S.6 statement (2026-05-27): predicate-form of the
-- generic SU(d) Solovay-Kitaev quantitative bundled-strict headline.
-- Captures BOTH the error bound `‖compile U ε - U‖ ≤ ε` AND the
-- concrete word-length conjunct `c · log(1/ε)^(log 5 / log 2)` per
-- the M.4 inheritance discipline (F#4 guardrail).
import SKEFTHawking.FKLW.GenericSUdHeadlineForm
-- Phase 6y Track S.2g-conditional (2026-05-27): Cartan v4 conditional
-- discharge at SU(d) — closed subgroup of SU(d) with `1 ∈ interior`
-- ⟹ H = ⊤, via Mathlib's Subgroup.eq_top_of_isOpen_of_connected +
-- project SU(d) connectedness instance. Ships
-- `subgroup_SUd_eq_top_of_one_mem_interior` + the predicate-level
-- conditional `CartanFinalStep_SUd_v4_holds_of_interior_witness`.
import SKEFTHawking.FKLW.GenericSUdCartanConditional
-- Phase 6y Track T-A2′.5 statement (2026-05-27): predicate-form of
-- the Clifford+CCZ SU(8) Solovay-Kitaev bundled-strict headline.
-- `cliffordCCZSU8Headline : Prop` captures BOTH error bound + concrete
-- word-length conjunct (FreeGroup (Fin 4).toWord.length) per M.4
-- inheritance discipline (F#4 guardrail).
import SKEFTHawking.FKLW.CliffordCCZSU8HeadlineForm
-- Phase 6y Track T-A1′.5 statement (2026-05-27): predicate-form of
-- the trapped-ion SU(4) 1Q sub-alphabet SK bundled-strict headline.
-- `trappedIonSU4_1QHeadline : Prop` captures BOTH error bound +
-- concrete word-length conjunct per M.4 inheritance.
import SKEFTHawking.FKLW.TrappedIonSU4HeadlineForm
-- Phase 6y Track T-A1′.1 (2026-05-27): MS gate via exp/Jacobi route.
-- Closes long-standing MSGate SU(4) membership gap (multiple prior
-- entry-wise verification attempts failed). Defines `MSGateExp θ :=
-- exp(-iθ/2 • (X⊗X))` and proves SU(4) membership via skew-Hermitian
-- exp is unitary + Phase 6y S.2d Jacobi formula det(exp Y) = exp(tr Y).
-- Ships `MSGate_SU4 (θ : ℝ) : ↥(specialUnitaryGroup (Fin 4) ℂ)`.
import SKEFTHawking.FKLW.MSGateExpForm
-- Phase 6y Track T-A1′.1 PROPER (2026-05-27): full trapped-ion alphabet
-- with MS at rational-π/N grid. N-parameterized `GeneratingSet 4`
-- instance with 4 single-qubit gates + 2N MS gates (4 + 2N total
-- generators, FreeGroup (Fin (4 + 2*N)) word type). Closure-density at
-- SU(4) ships in T-A1′.2 via Phase 6y S.2g.
import SKEFTHawking.FKLW.TrappedIonGeneratingSetSU4Full
-- Phase 6y Track T-A1′.2 (D)-witness substrate (2026-05-28): kronSU4 homomorphism
-- (kronSU4_mul / kronSU4_one + per-ion specializations) — foundation for the per-ion
-- SU(2)→SU(4) embedding monoid homs in the Brylinski-Brylinski ClosureDenseWitness.
import SKEFTHawking.FKLW.TrappedIonSU4KronHom
-- Phase 6y Track T-A1′.2 (D)-witness substrate (2026-05-28): per-ion SU(2)→SU(4)
-- embeddings as continuous monoid homs (ion1Embed/ion2Embed) — the maps through which
-- SU(2) Clifford+T density lifts to per-ion flow-line containment in H_of_G.
import SKEFTHawking.FKLW.TrappedIonSU4IonEmbed
-- Phase 6y Track T-A1′.2 (D)-witness substrate (2026-05-28): per-ion embedding ↔ alphabet
-- generator identities (ion{1,2}Embed of H_SU/T_SU = the per-ion SU(4) gates) — the bridge
-- carrying SU(2) Clifford+T density into H_of_G(trappedIon).
import SKEFTHawking.FKLW.TrappedIonSU4PerIonBridge
-- Phase 6y Track T-A1′.2 (D)-witness substrate (2026-05-28): per-ion representation
-- factorization (trappedIonRho_full ∘ FreeGroup.map incl{1,2} = ion{1,2}Embed ∘ ρ_CliffT) —
-- puts the embedded Clifford+T range inside the trapped-ion range (density-transfer core).
import SKEFTHawking.FKLW.TrappedIonSU4PerIonFactorization
-- Phase 6y Track T-A1′.2 (D)-witness substrate (2026-05-28): per-ion containment
-- ion{1,2}Embed(SU(2)) ⊆ H_of_G(trappedIon) — density transfer culmination carrying SU(2)
-- Clifford+T density into the trapped-ion closed subgroup (per-ion half of the (D) witness).
import SKEFTHawking.FKLW.TrappedIonSU4PerIonContainment
-- Phase 6y Track T-A1′.2 (D)-witness substrate (2026-05-28): exp commutes with the per-ion
-- embedding (kronSU4 (exp X) 1 = exp (kronSU4 X 1)) via map_exp on the embedding RingHom —
-- gives the per-ion 𝔰𝔲(2) tangent one-parameter subgroups as embedded SU(2) flow lines.
import SKEFTHawking.FKLW.TrappedIonSU4ExpCommute
-- Phase 6y Track T-A1′.2 (D) witness (2026-05-28): tensor-Pauli tangent set + hX_in_sud
import SKEFTHawking.FKLW.TrappedIonSU4Tangents
-- Phase 6y Track T-A1′.2 (D) witness (2026-05-28): 6 per-ion tangent flow lines
import SKEFTHawking.FKLW.TrappedIonSU4PerIonFlow
-- Phase 6y (D) witness (2026-05-28): generic conjugation transports flow lines
import SKEFTHawking.FKLW.GenericSUdFlowConj
-- Phase 6y Track T-A1′.2 (D) witness (2026-05-28): MS gate = X₁₁ flow (grid points in H_of_G)
import SKEFTHawking.FKLW.TrappedIonSU4MSFlowGrid
-- Phase 6y Track T-A1′.2 (D) witness (2026-05-28): 15 tensor-Pauli tangents span 𝔰𝔲(4) (hX_spans)
import SKEFTHawking.FKLW.TrappedIonSU4TangentSpan
-- Phase 6y (D) witness (2026-05-28): exp of idempotent/involution closed forms (Banach algebra)
import SKEFTHawking.FKLW.GenericExpInvolution
-- Phase 6y Track T-A1′.2 (D) witness (2026-05-28): entangler conjugation cores (X₃₀·i·xKronX = −X₂₁)
import SKEFTHawking.FKLW.TrappedIonSU4EntanglerConj
-- Phase 6y Track T-A1′.2 (D) witness (2026-05-28): first entangling flow exp(t·X₂₁) ∈ H_of_G
import SKEFTHawking.FKLW.TrappedIonSU4EntanglerFlow
-- Phase 6y Track T-A1′.2 (D) witness (2026-05-28): per-ion conjugation spreads entangling flow
import SKEFTHawking.FKLW.TrappedIonSU4PerIonConjFlow
-- Phase 6y Track T-A1′.2 (D) witness (2026-05-28): single-qubit Cliffords spread X₂₁ to all 9 entanglers
import SKEFTHawking.FKLW.TrappedIonSU4EntanglerSpread
-- Phase 6y Track T-A1′.2/.5 (D) witness (2026-05-28): SU(4) ClosureDenseWitness + UNCONDITIONAL headline
import SKEFTHawking.FKLW.TrappedIonSU4WitnessFull
-- Phase 6y Track S.2g-substrate (2026-05-27): local diffeo restriction
-- `𝔰𝔲(d) ↔ SU(d)` near (0, 1). Forward: exp of 𝔰𝔲(d) ∩ source ⊆ SU(d) ∩ target
-- (via skew-Hermitian-exp-is-unitary + S.2d Jacobi det = exp(tr) = 1).
-- Backward: matrixLog of SU(d) ∩ small_nbhd lands in 𝔰𝔲(d) (re-export of
-- S.2e PROPER combined). Substrate consumed by S.2g unconditional + T-A1′.2 +
-- T-A2′.2 + S.5 + S.6 UNCONDITIONAL.
import SKEFTHawking.FKLW.GenericSUdLocalDiffeoRestriction
-- Phase 6y Track S.2g-substrate (2026-05-27): n-parameter exp product
-- structural foundation. Definition `multiDirExpProduct X t :=
-- exp(t_0 • X_0) · … · exp(t_{n-1} • X_{n-1})` (via List.prod over
-- List.finRange n; non-commutative-monoid-friendly). Ships base properties
-- (zero ↦ 1, SU(d)-image preservation, H-image preservation given per-direction
-- flow witnesses). Structural foundation for the multi-parameter IFT route
-- to S.2g unconditional discharge.
import SKEFTHawking.FKLW.GenericSUdMultiParamExpProduct
-- Phase 6y Track T-A1′.5 PROPER (2026-05-27): full-alphabet headline form
-- at the trappedIonGeneratingSetSU4 N hN GeneratingSet (MS at rational-π/N
-- grid + 1Q rotations, both compiled per the Phase 6y T-A1′ roadmap).
-- Predicate `trappedIonSU4FullHeadline N hN : Prop` captures BOTH error
-- bound AND concrete `FreeGroup (Fin (4 + 2*N)).toWord.length` conjunct
-- per M.4 inheritance (F#4 guardrail). Supersedes the 1Q-only partial
-- `trappedIonSU4_1QHeadline`.
import SKEFTHawking.FKLW.TrappedIonSU4FullHeadlineForm
-- Phase 6y Track T-X′.3-substrate (2026-05-27): d-generic ε₀-net
-- `epsilonNet_findNearest_SUd gs h_dense U ε₀` that takes an
-- IsDenseInSUd_gs density witness and returns a word approximating any
-- target U ∈ SU(d) to within ε₀. Mirrors Phase 6u's SU(2) version.
-- Existential (Classical.choose); per-alphabet algorithmic forms ship
-- in T-A1′.3 (Ross-Selinger-style for trapped-ion) and T-A2′.3
-- (Aaronson-Gottesman-style for Clifford+CCZ).
import SKEFTHawking.FKLW.GenericSUdEpsilonNet
-- Phase 6y Track T-A1′.2-substrate (2026-05-27): conditional SU(4) density
-- for full trapped-ion alphabet via Phase 6y S.2g + closure-density witness.
-- Ships `trappedIonGeneratingSetSU4_isDense_conditional N hN w h_cartan`
-- plus the consumer ε₀-net `trappedIonEpsilonNet_findNearest_conditional`
-- with correctness lemma.
import SKEFTHawking.FKLW.TrappedIonSU4DensityConditional
-- Phase 6y Track T-A2′.2-substrate (2026-05-27): conditional SU(8) density
-- for full Clifford+CCZ alphabet (parallel to T-A1′.2-substrate at d = 8).
-- Ships `cliffordCCZGeneratingSetSU8_isDense_conditional w h_cartan` + consumer
-- ε₀-net `cliffordCCZEpsilonNet_findNearest_conditional` + correctness.
import SKEFTHawking.FKLW.CliffordCCZSU8DensityConditional
-- Phase 6y Track S.2g (2026-05-27): UNCONDITIONAL n-parameter exp product
-- strict F-derivative at 0 (HasStrictFDerivAt multiDirExpProduct
-- multiDirDerivCLM 0). Ports SU(2) Phase 6u/6p substrate to d-generic +
-- composes via Mathlib's HasStrictFDerivAt.list_prod' (non-commutative
-- product rule), with NormedAlgebra.complexToReal + IsScalarTower.left ℝ
-- supplying the scalar-tower instances. Background-explore-agent-aided
-- breakthrough on the multi-parameter IFT bottleneck.
import SKEFTHawking.FKLW.GenericSUdMultiParamExpProductDeriv
-- Phase 6y Track S.2g-substrate (2026-05-27): d-generic tsProj_d
-- continuous linear projection `Matrix _ _ ℂ →L[ℝ] ↥(𝔰𝔲(d))` via
-- `Submodule.exists_isCompl` complement + linearProjOfIsCompl. d-generic
-- lift of SU(2)-specific tsProj. Consumed by the IFT-on-subspace
-- composition for S.2g UNCONDITIONAL discharge.
import SKEFTHawking.FKLW.GenericSUdTsProj
-- Phase 6y Track S.2g-substrate (2026-05-27): composite strict F-derivative
-- substrate. Ships `matrixLog_hasStrictFDerivAt_one`, the composed
-- `matrixLog ∘ multiDirExpProduct` strict derivative at 0, and the full
-- `tsProj_d ∘ matrixLog ∘ multiDirExpProduct` composite landing in
-- ↥(tracelessSkewHermitian (Fin d)). Load-bearing for the IFT-on-subspace
-- step of the S.2g UNCONDITIONAL discharge. Also ships composite-derivative
-- range-top-when-spans (input to Mathlib's map_nhds_eq_of_surj).
import SKEFTHawking.FKLW.GenericSUdMultiParamCompositeDeriv
-- Phase 6y Track S.2g-substrate (2026-05-27): substrate value lemma for the
-- IFT-on-subspace step. `composite_map_value_zero`: the composite
-- `tsProj_d ∘ matrixLog ∘ multiDirExpProduct X` evaluates to 0 at the
-- zero parameter vector. The final map_nhds_eq_of_surj application
-- (requiring CompleteSpace ↥(𝔰𝔲(d)) typeclass synthesis) ships in
-- a follow-on commit.
import SKEFTHawking.FKLW.GenericSUdCartanUnconditional
-- Phase 6y Track S.5 — UNCONDITIONAL generic SU(d) discharge.
-- Composes the conditional `H_of_G_eq_top_of_witness_conditional` +
-- `densityFromWitness_conditional` (from S.1+S.2 chain) with the
-- UNCONDITIONAL `CartanFinalStep_SUd_v4_holds` (from S.2g) to ship
-- the UNCONDITIONAL forms taking only a `ClosureDenseWitness gs`.
import SKEFTHawking.FKLW.GenericSUdDischargeUnconditional
-- Phase 6y Track T-A1′.2 + T-A2′.2 (cascade-closing): UNCONDITIONAL closure-density
-- + ε₀-net findNearest at SU(4) trapped-ion and SU(8) Clifford+CCZ, taking ONLY a
-- substantive `ClosureDenseWitness gs` (the prior `h_cartan : CartanFinalStep_SUd_v4 d`
-- hypothesis is auto-discharged via S.2g UNCONDITIONAL).
import SKEFTHawking.FKLW.TrappedIonSU4DensityFromWitness
import SKEFTHawking.FKLW.CliffordCCZSU8DensityFromWitness
-- Phase 6y Tracks T-A1′.2 + T-A2′.2 tracked-Prop witness framework. Defines
-- `trappedIonSU4_v4_witness_tracked` + `cliffordCCZSU8_v4_witness_tracked`
-- (existential Lie-algebra spanning + flow-line predicates) + extraction to
-- `ClosureDenseWitness` + UNCONDITIONAL density/ε₀-net from tracked Prop.
-- Mirrors Phase 6u CliffordT pattern (`cliffordT_v4_witness_tracked`).
import SKEFTHawking.FKLW.TrappedIonSU4WitnessTracked
import SKEFTHawking.FKLW.CliffordCCZSU8WitnessTracked
-- Phase 6y Track T-A2′.2/.5 (D) witness (2026-05-28): UNCONDITIONAL SU(8) Clifford+CCZ(+T) closure-
-- density witness assembly + UNCONDITIONAL SolovayKitaevHeadline_FreeGroup_SUd. Ships Clifford+T at
-- SU(8) (CCZ over-complete); literal CCZ-essential is a tracked strengthening (DR seed spike).
import SKEFTHawking.FKLW.CliffordCCZSU8WitnessFull
-- Phase 6y literal Clifford+CCZ strengthening, Phase A.1 (2026-05-28): the irrational-angle seed
-- g = CCZ·(H⊗H⊗H) with tr(g) = 1/√2 (the obstruction to finite order — Kronecker/algebraic-integer).
-- Foundation for the faithful (CCZ-essential, no-T) literal headline; Phases B (irrationality) + C
-- (closure→1-param-subgroup Kronecker-Weyl lift) pending.
import SKEFTHawking.FKLW.CliffordCCZSU8LiteralSeed
-- Phase 6z Wave 1 (2026-05-28): the algebraic-integer / root-of-unity obstruction.
-- `not_rootOfUnity_of_not_isIntegral` (reusable) + the Gate-1-corrected seed eigenvalue
-- λ=(−3+i√7)/4 is not an algebraic integer (λ+λ̄=−3/2∉ℤ) ⟹ not a root of unity.
import SKEFTHawking.FKLW.CliffordCCZSU8Irrationality
-- Phase 6z Wave 1 (2026-05-28): the literal Clifford+CCZ (no-T) generating set
-- ⟨H,S,CNOT,CCZ⟩ on SU(8) — GeneratingSet 8 instance + the genuinely T-free Clifford S-gate.
import SKEFTHawking.FKLW.CliffordCCZSU8LiteralGeneratingSet
-- Phase 6z Wave 1 (2026-05-28): the seed group element CCZ·H_q1·H_q2·H_q3 ∈ ⟨H,S,CNOT,CCZ⟩ has
-- INFINITE order (matrix bridge to litSeed + tr = u·(1/√2) not an algebraic integer + the spectral
-- meta-lemma). The Kronecker seed for the Wave-2 first flow.
import SKEFTHawking.FKLW.CliffordCCZSU8SeedNotFiniteOrder
-- Phase 6z Wave 2b (2026-05-28): SU(d) von-Neumann 1-parameter-subgroup construction (generalizing
-- OneParameterSubgroupSU2). Increment 1: von-Neumann sequence extraction from an accumulation point.
import SKEFTHawking.FKLW.GenericSUdOneParameterSubgroup
-- Phase 6z Wave 2a (2026-05-28): the infinite-order seed gives 1 as an accumulation point of H_of_G
-- (infinite closed subgroup of compact SU(8)) — the precondition for the SU(d) von-Neumann
-- 1-parameter-subgroup theorem (Wave 2b → the first seed flow).
import SKEFTHawking.FKLW.CliffordCCZSU8SeedFlow
import SKEFTHawking.FKLW.CliffordCCZSU8OrbitSpan
import SKEFTHawking.FKLW.CliffordCCZSU8PauliConj
import SKEFTHawking.FKLW.CliffordCCZSU8PauliConjTensor
import SKEFTHawking.FKLW.CliffordCCZSU8CharOrth
import SKEFTHawking.FKLW.CliffordCCZSU8PauliTwirl
import SKEFTHawking.FKLW.CliffordCCZSU8LabelTransitivity
import SKEFTHawking.FKLW.CliffordCCZSU8GenConjValues
import SKEFTHawking.FKLW.CliffordCCZSU8GenLift
import SKEFTHawking.FKLW.CliffordCCZSU8CNOTConj
import SKEFTHawking.FKLW.CliffordCCZSU8LineTransport
import SKEFTHawking.FKLW.CliffordCCZSU8Transport
import SKEFTHawking.FKLW.CliffordCCZSU8ConjClosure
import SKEFTHawking.FKLW.CliffordCCZSU8PauliWords
import SKEFTHawking.FKLW.CliffordCCZSU8KronK8Closure
import SKEFTHawking.FKLW.CliffordCCZSU8Irreducible
import SKEFTHawking.FKLW.CliffordCCZSU8OrbitWitness
import SKEFTHawking.FKLW.CliffordCCZSU8OrbitProps
import SKEFTHawking.FKLW.CliffordCCZSU8Density
-- (4) synth_CCZ_correct MVP: IsExactlyCliffordCCZ U := ∃gs, interp gs = U is a submonoid containing
-- every gate (isExactlyCliffordCCZ_one/_mul/_gate/_ccz); synth extracts a witnessing word and
-- synth_CCZ_correct : interp (synth U h) = U is the kernel-routine exact-synthesis correctness for any
-- exactly-representable U (the minimal/Toffoli-optimal meet-in-the-middle search is the optional stretch).
-- Phase 6x Item L increments 1–4 (2026-05-30): Mukhopadhyay exact Clifford+CCZ synthesis (public
-- math layer). (1) Generating-element grounding mukGen_Z = CCZ — the canonical Mukhopadhyay Eq.12
-- generator G_{Z₁,Z₂,Z₃} = (3/4)I+(1/4)(Z₁+Z₂+Z₃−Z₁Z₂−Z₂Z₃−Z₃Z₁+Z₁Z₂Z₃) equals the project's
-- CCZ_mat. (2) CliffordCCZGate ADT + interp (over the shipped SU(8) literal generators + CCZ_mat) +
-- composition soundness interp_append + the synth_CCZ_correct MVP at the canonical generator
-- (mukGen_Z exactly representable by the single-CCZ word) + the order-2 relation interp[CCZ,CCZ]=I.
-- (3) The GENERAL generating element mukGen p q r + the reflection structure mukGen_sq (G²=I for any
-- pairwise-commuting involutions — Mukhopadhyay's defining property), instantiated as mukGen_Z_sq
-- (CCZ²=I via the generating-element structure; pauliZ_mul_self/pauliZ_comm).
import SKEFTHawking.FKLW.MukhopadhyayCCZ
-- Phase 6x Item L.A continuation (2026-05-30): Mukhopadhyay channel (Heisenberg/Pauli-conjugation)
-- representation Û (Eq.27) over the shipped 64-Pauli basis — monoid homomorphism (channelRep_mul),
-- orthogonality of the channel rep of a unitary, the conjugation-action characterization
-- (channelRep_mulVec_repr), and the structural re-base of IsExactlyCliffordCCZ onto channelGenMonoid.
import SKEFTHawking.FKLW.MukhopadhyayChannelRep
-- Phase 6x Item L.B (2026-05-30): the dyadic sde₂ invariant (Definition 3.13, the √2→2 analog of the
-- shipped √2-sde T-count) + Fact 3.14 half-sum monotonicity (the +1 core of Lemma 3.16).
import SKEFTHawking.FKLW.MukhopadhyaySde2
-- Phase 6x Item L.C (2026-05-30): the Toffoli-count lower bound — toffoliCount/toffoliCost + the
-- telescoping mechanism toffoliCount_ge_measure / toffoliCost_ge_measure giving T^of(U) ≥ sde₂(Û)
-- (reading μ = sde₂∘channelRep). Not proved tight (full minimality = MITM/Conjecture 4.8, residual).
import SKEFTHawking.FKLW.MukhopadhyayToffoliBound
-- Phase 6x′ B (2026-05-30): Fact 3.9 (⟹) — channelRep of each literal Clifford generator
-- (H_qi/S_qi/CNOT_ij) is a signed permutation, via the shipped 6z conjugation tables + the L.A
-- channel rep. The substrate for the hC bridge + the 6z CCZ-essentiality converse.
import SKEFTHawking.FKLW.MukhopadhyayChannelRepClifford
-- Phase 6x′ capstone inc 1 (2026-05-30): the abstract algebra of signed permutation matrices —
-- IsSignedPerm closed under one/mul/inverse and a finite set. The finite target into which the
-- channel-rep homomorphism carries the Clifford-only group ⟨H,S,CNOT⟩ (Fact 3.9), the combinatorial
-- input to the 6z CCZ-essentiality converse (cliffordOnly_not_dense).
import SKEFTHawking.FKLW.MukhopadhyaySignedPerm
-- Phase 6x′ capstone inc 2 (2026-05-30): the Clifford-only generating set ⟨H,S,CNOT⟩ (no CCZ) +
-- Fact 3.9 (⟹) lifted across the free group — every word in ⟨H,S,CNOT⟩ has a signed-permutation
-- channel rep (cliffordWord_channelRep_signedPerm). The "lands in a finite set" half of the converse.
import SKEFTHawking.FKLW.MukhopadhyayCliffordConverse
-- Phase 6x′ capstone inc 3+4 (2026-05-30): the 6z CCZ-essentiality converse —
-- `cliffordOnly_not_dense`: ⟨H,S,CNOT⟩ (no CCZ) is NOT dense in SU(8). channelRep is a continuous
-- monoid hom carrying ⟨H,S,CNOT⟩ into the finite signed-permutation set, while the infinite-order seed
-- forces channelRep(SU(8)) infinite — so the Clifford-only set cannot be dense. CCZ is essential.
import SKEFTHawking.FKLW.MukhopadhyayCliffordNotDense
-- Phase 6x′ Phase 2 (C.1) (2026-05-30): the CCZ diagonal-conjugation identity
-- (CCZ·M·CCZ)_ij = ccz_i·ccz_j·M_ij + CCZ commutes with diagonal operators — the structural engine
-- behind Theorem 3.8. Off-ramp ship: the full off-diagonal Theorem-3.8 structure + hCCZ + Lemma 3.10 +
-- unconditional T^of remain documented residuals (see file docstring + Phase6x_prime_Roadmap).
import SKEFTHawking.FKLW.MukhopadhyayCCZConjugation
-- Phase 6x′ Phase 2 (A) (2026-05-30): the sde₂-valued measure on ℂ-matrices — sde2ℂ (dyadic exponent
-- via the rational value) + matrixSde2 (max over entries, porting KMM.sdeC) + channelSde2 = matrixSde2 ∘
-- channelRep + channelSde2 1 = 0. The rationality-conditional Fact-3.14 lift (sde2ℂ_half_sum_le) is the
-- crux infra for the unconditional T^of bound. Non-vacuous (sde2ℂ (1/2) = 1).
import SKEFTHawking.FKLW.MukhopadhyayMatrixSde2
-- Phase 6x′ Phase 2 (B) (2026-05-30): the hC bridge — Cliffords leave the channelSde2 measure unchanged
-- (channelSde2_clifford_le), via matrixSde2_signedPerm_mul_le (left-mult by a signed perm permutes/
-- sign-flips entries) + the gateMatrix↔cliffordOnlyGenMap bridge. Toward the unconditional T^of bound.
import SKEFTHawking.FKLW.MukhopadhyayToffoliUnconditional
-- Phase 6x′ Phase 2 (C foundation) (2026-05-30): the entry-factorization substrate for the channelRep CCZ
-- structure (Theorem 3.8) — kronSU8_bitIso8_apply (general), index 7 = bitIso8(1,1,1), the per-qubit
-- factorizations (kronK8 v)₇₇ = ∏(σ_vᵢ)₁₁ and (P_r P_s)₇₇ = ∏(σ_rᵢ σ_sᵢ)₁₁, and the Hermitian
-- conjugate-swap (σ_b σ_a)₁₁ = conj((σ_a σ_b)₁₁). The half-integer headline follows.
import SKEFTHawking.FKLW.MukhopadhyayCCZChannelRep
-- Phase 6x′ Phase 2 (D) (2026-05-30): hCCZ — channelSde2_ccz_le: one CCZ raises the channel-rep sde₂
-- by ≤1 (dyadic-conditional), via the sde2ℂ arithmetic layer (integer-scaling/addition/÷2/finite-sum)
-- + Theorem 3.8's half-integer entries. Toward the unconditional T^of bound.
import SKEFTHawking.FKLW.MukhopadhyayHCCZ
-- Phase 6y Track S.6 substrate (2026-05-27): SK compile-with-polylog-length-bound
-- data structure for SU(d). Defines `SKCompileWithBounds_FreeGroup` +
-- `SKCompileWithBounds_SUd` structures bundling (ε₀, c, compile, error, length)
-- predicate hypotheses, with generic discharges of
-- `SolovayKitaevHeadline_FreeGroup_SUd` + `SolovayKitaevHeadline_SUd` predicates.
-- This is the substrate hypothesis that Phase 6y headlines (T-A1′.5, T-A2′.5)
-- discharge through, decoupling structural F#4-compliant headlines from the
-- substantive SK-at-SU(d) implementation (the latter ships in Phase 6z+).
import SKEFTHawking.FKLW.GenericSUdSKCompileBounds
-- Phase 6y Track T-A1′.5 PROPER discharge (2026-05-27): F#4-compliant
-- `trappedIonSU4FullHeadline N hN` discharge given a SKCompileWithBounds data
-- hypothesis for the full trapped-ion SU(4) alphabet.
import SKEFTHawking.FKLW.TrappedIonSU4HeadlineDischarge
-- Phase 6y Track T-A2′.5 PROPER discharge (2026-05-27): F#4-compliant
-- `cliffordCCZSU8Headline` discharge given a SKCompileWithBounds data
-- hypothesis for the Clifford+CCZ SU(8) alphabet.
import SKEFTHawking.FKLW.CliffordCCZSU8HeadlineDischarge
-- Phase 6y Track S.4 PROPER (2026-05-27): EXPLICIT d-generic Lipschitz constant
-- K = 2 for matrixLog d near 1. Composes `matrixLog_hasStrictFDerivAt_one` with
-- the strict-F-derivative ε-δ characterization, yielding the substantive
-- explicit-constant form refining the existential `matrixLog_smallness_on_nhd_one`.
-- The Phase 6u SU(2)-specific `Y_h_norm_le_four_norm_sub_one` (K=4) is now matched
-- by the d-generic ship with the TIGHTER K=2 (via IFT derivative inverse).
import SKEFTHawking.FKLW.GenericSUdMatrixLogLipschitzExplicit
-- Phase 6y Track T-X′.3 (2026-05-27): d-generic constructive/algorithmic
-- (finite-Finset) ε₀-net. Composes `IsDenseInSUd_gs` density witness +
-- UNCONDITIONAL `Matrix.specialUnitaryGroup_isCompact` to produce the
-- finite-Finset ε-cover of SU(d) + algorithmic per-`U` findNearestInCover.
-- F#5-compliant ALGORITHMIC ε₀-net substrate at SU(d).
import SKEFTHawking.FKLW.GenericSUdConstructiveEpsilonNet
-- Phase 6y Track T-A1′.3 PROPER (2026-05-27): F#5-compliant ALGORITHMIC
-- ε₀-net for trapped-ion SU(4). Composes `GenericSUdConstructiveEpsilonNet`
-- with the tracked-Prop discharge to produce per-`U` algorithmic word
-- extraction via finite-Finset minimization (NOT existential per query).
import SKEFTHawking.FKLW.TrappedIonSU4ConstructiveEpsilonNet
-- Phase 6y Track T-A2′.3 PROPER (2026-05-27): F#5-compliant ALGORITHMIC
-- ε₀-net for Clifford+CCZ SU(8). Mirrors T-A1′.3 pattern at d=8.
import SKEFTHawking.FKLW.CliffordCCZSU8ConstructiveEpsilonNet
-- Phase 6y Track S.3 (2026-05-27): d-generic balanced commutator predicate
-- `BalancedCommutator_SUd d : Prop`. Substantively discharged at d ≤ 2 via
-- direct mechanical lift of `balanced_commutator_general_axis_lie_traceless`
-- (Phase 6t SU(2) Pauli decomposition with Bloch-sphere K = √(1/2)).
import SKEFTHawking.FKLW.GenericSUdBalancedCommutator
-- Phase 6y Track S.3 substrate (Session 3, 2026-05-27): d-generic 2-block
-- Pauli analogs `sigmaYBlock`, `sigmaXBlock`, `sigmaZBlock` ∈ Matrix (Fin d) (Fin d) ℂ
-- supported on the 2×2 block at distinct indices (i, j). Substantive primitive
-- for the Aharonov-Arad SU(d) spectral construction (rank-2 case + spectral
-- sum). Ships Hermiticity + tracelessness lemmas; commutator + rank-2
-- BalancedCommutator_SUd discharge in Session 4+.
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock
-- Phase 6y Track S.3 substrate (Session 13, 2026-05-27): unitary conjugation
-- invariance lemmas — commutator equivariance, Hermitian preservation, trace
-- preservation, composite balanced-commutator-structure invariance. Substrate
-- for the "spectral-pair + conjugate" approach to Aharonov-Arad d≥3. Norm-
-- bridging (linftyOp vs spectral) deferred to follow-on commit.
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorConjugation
-- Phase 6y Track S.3 substrate (Session 14, 2026-05-27): rank-2 unitary-image
-- balanced commutator at SU(d) — composes Session 11 σ_z-pattern + Session 13
-- conjugation invariance. Ships F·G − G·F = −iθ·H for H = U·σ_z(i,j)·U* under
-- arbitrary U ∈ SU(d). Algebraic conjuncts only (norm-bridging caveat documented).
import SKEFTHawking.FKLW.GenericSUdDiagonalTracelessDecomp
-- Phase 6y Track S.3 substrate (Session 15, 2026-05-27): diagonal-traceless H
-- decomposition into σ_z-pair basis. For diagonal H = diag(a) over Fin (n+2)
-- with ∑ a = 0, ships H = ∑_{k : Fin (n+1)} b_k · σ_z(k.castSucc, k.succ)
-- where b_k = ∑_{j ≤ k} a_j are the partial sums. Algebraic substrate for
-- the Aharonov-Arad SU(d) construction (per-pair F, G + cross-term counterterms
-- ship in follow-on substrate).
import SKEFTHawking.FKLW.GenericSUdDiagonalDecomp
-- Phase 6y Track S.3 substrate (Session 17, 2026-05-27): cross-term commutator
-- for σ_y/σ_x adjacent-block pairs. Ships the keystone identity
-- [σ_y(a, b), σ_x(b, c)] = -i · σ_x(a, c) for distinct a, b, c ∈ Fin d.
-- This is the off-diagonal obstruction in the naive σ_y/σ_x sum construction;
-- counterterm cancellation (Aharonov-Arad 2014) ships separately.
import SKEFTHawking.FKLW.GenericSUdSigmaCrossTerm
-- Phase 6y Track S.3 substrate (Session 18, 2026-05-27): complete 2-block
-- commutator classification — disjoint supports ⟹ commutator = 0; shared-first
-- cross-term `[σ_y(a, b), σ_x(a, c)] = +i · σ_x(b, c)` for distinct a, b, c.
-- Exhausts all 2-block commutator cases (together with Session 11 same-pair
-- and Session 17 shared-middle), giving the complete cross-term substrate
-- for Aharonov-Arad SU(d) counterterm construction.
import SKEFTHawking.FKLW.GenericSUdSigmaClassification
-- Phase 6y Track S.3 substrate (Session 19, 2026-05-27): cross-term pair-swap
-- cancellation lemma. For p ≠ q ∈ Fin (n+1):
--   [σ_y(p), σ_x(q)] + [σ_y(q), σ_x(p)] = 0
-- This is the algebraic key to the cross-term-free symmetric construction:
-- with F = Σ α_p σ_y(p), G = Σ α_p σ_x(p), the cross-terms pair up and cancel.
-- No counterterms needed for the symmetric α-coefficient case.
import SKEFTHawking.FKLW.GenericSUdSigmaPairSwap
-- Phase 6y Track S.3 substrate (Session 20, 2026-05-27): γ-weighted cross-term
-- pair-swap cancellation lemmas. Lifts Session 19's pair-swap to γ-weighted
-- form `(γ_p γ_q) • [σ_y(p), σ_x(q)] + (γ_q γ_p) • [σ_y(q), σ_x(p)] = 0`
-- + same-pair γ-weighted formula `(γ_p²) • [σ_y(p), σ_x(p)] = (γ_p²·-2i) • σ_z(p)`
-- + same-pair-at-target-coeff `(θ·b_p/2 · -2i) = -iθ·b_p`. Bridges Session 19
-- to the full F·G − G·F discharge in Session 21+.
import SKEFTHawking.FKLW.GenericSUdSymmetricCommReduction
-- Phase 6y Track S.3 substrate (Session 21, 2026-05-27): antisymmetric off-diag
-- sum vanishing. Generic Mathlib-PR-quality fact: for `f : Fin n → Fin n → M`
-- (M a ℂ-module) with f p q + f q p = 0 for all p ≠ q, the off-diagonal sum
--   ∑ p, ∑ q ∈ univ.erase p, f p q = 0
-- via the doubling trick (Fubini + diagonal cancellation + ℂ-module 2-invertibility).
-- Substrate for the F·G − G·F = ∑_p γ_p² · [σ_y(p), σ_x(p)] reduction (S22+).
import SKEFTHawking.FKLW.GenericSUdAntisymOffDiag
-- Phase 6y Track S.3 substrate (Session 22, 2026-05-27): MAIN F·G − G·F reduction.
-- For symmetric F = Σ γ_p · σ_y(p), G = Σ γ_p · σ_x(p):
--   F·G − G·F = Σ_p (γ_p)² · [σ_y(p), σ_x(p)]
-- Combines S20 (γ-weighted pair-swap) + S21 (antisym off-diag vanishing) +
-- Finset.sum_mul_sum double-sum expansion + Fubini. Core algebraic theorem
-- that powers the symmetric F=αG balanced commutator construction at SU(d).
import SKEFTHawking.FKLW.GenericSUdSymmetricCommFGreduction
-- Phase 6y Track S.3 substrate (Session 23, 2026-05-27): MAIN algebraic identity.
-- For symmetric F = Σ_p γ_p · σ_y(p), G = Σ_p γ_p · σ_x(p) with γ_p² = θ·b_p/2
-- and traceless `a`:
--   F·G − G·F = -(θ·i) • Matrix.diagonal a
-- Composes S22 (F·G − G·F same-pair reduction) + S11 ([σ_y,σ_x]=-2i·σ_z) +
-- S15 (diagonal-traceless decomposition). The algebraic heart of the symmetric
-- F=αG Aharonov-Arad balanced commutator construction at SU(d).
import SKEFTHawking.FKLW.GenericSUdSymmetricFGEqIdentity
-- Phase 6y Track S.3 substrate (Session 24, 2026-05-27): symmetric F=αG discharge
-- with Hermitian + trace conjuncts packaged into ∃-existence theorem. Combines
-- S23 algebraic identity with the Hermitian/traceless lemmas for real-coefficient
-- σ-block sums. Discharge of symmetric balanced commutator for diagonal real-
-- valued traceless a with non-negative partial sums.
import SKEFTHawking.FKLW.GenericSUdSymmetricDischarge
-- Phase 6y Track S.3 substrate (Session 25, 2026-05-27): partial sums non-negativity
-- for decreasing-sorted traceless sequences. For `a : Fin (n + 1) → ℝ` that is
-- non-increasing and traceless:
--   ∀ k, 0 ≤ ∑_{j ≤ k} a j
-- Eigenvalue-sort substrate: any traceless `a` sorted decreasingly satisfies the
-- non-negativity hypothesis required by Session 24's symmetric discharge.
import SKEFTHawking.FKLW.GenericSUdDecreasingSortPartialSums
-- Phase 6y Track S.3 substrate (Session 26, 2026-05-27): U(d) (unitary-group)
-- conjugation invariance lemmas. Generalizes Session 13's `specialUnitaryGroup`
-- forms to broader `unitaryGroup` (allowing permutation matrices with det = ±1).
-- Proofs are IDENTICAL — the conjugation invariance only uses star U · U = 1,
-- not the SU(d) determinant constraint. Enables permutation-matrix conjugation
-- for the eigenvalue-sort lift of S24 to arbitrary diagonal H.
import SKEFTHawking.FKLW.GenericSUdUnitaryConjugationInvariance
-- Phase 6y Track S.3 substrate (Session 27, 2026-05-27): permutation matrices
-- are unitary. For any σ : Equiv.Perm (Fin n), permMatrix ℂ σ ∈ unitaryGroup
-- via Matrix.conjTranspose_permMatrix + permMatrix_mul + inverse cancellation.
-- Ships permMatrixAsUnitary bundle + star_form. Substrate for eigenvalue-sort
-- lift (combine with S25 + S24 + S26 in Session 28+).
import SKEFTHawking.FKLW.GenericSUdPermutationConjugation
-- Phase 6y Track S.3 substrate (Session 28, 2026-05-27): diagonal conjugation
-- by permutation matrix. For σ : Equiv.Perm (Fin n) and a : Fin n → ℂ:
--   permMatrix σ · diagonal a · permMatrix σ⁻¹ = diagonal (a ∘ σ)
-- This is the key identity that combines with S25/S26/S27 to lift discharge
-- for diag(a ∘ σ) (sorted) to discharge for diag(a) (arbitrary).
import SKEFTHawking.FKLW.GenericSUdPermutationDiagonal
-- Phase 6y Track S.3 substrate (Session 29, 2026-05-27): partial sum bridge
-- lemmas for real-coerced sequences:
--   (partialSumCoeff (a ·) p).im = 0
--   (partialSumCoeff (a ·) p).re = ∑ j ∈ range (p.val + 1), if-then-else a ⟨j, _⟩
-- Bridges the ℂ-valued partialSumCoeff (used by S24) to real partial sums
-- (used by S25's decreasing-sort non-negativity).
import SKEFTHawking.FKLW.GenericSUdPartialSumBridge
-- Phase 6y Track S.3 substrate (Session 30, 2026-05-27): range/filter sum
-- equivalence for partial sums. For real `a : Fin (n + 1) → ℝ` and `p : Fin n`:
--   ∑ j ∈ range (p.val + 1), (if h : j < n + 1 then a ⟨j, h⟩ else 0)
--   = ∑ j ∈ univ.filter (· ≤ p.castSucc), a j
-- Bijection via Finset.sum_bij maps j ↦ ⟨j, _⟩ : Fin (n + 1). Last piece for
-- combining S29 partial sum bridge with S25's filter-form non-negativity.
import SKEFTHawking.FKLW.GenericSUdRangeFilterBridge
-- Phase 6y Track S.3 substrate (Session 31, 2026-05-27): FULL DIAGONAL DISCHARGE.
-- For ARBITRARY traceless real `a : Fin (n + 2) → ℝ` (no partial-sums hypothesis):
--   ∃ F G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ,
--     F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
--     F · G − G · F = -((θ : ℂ) · Complex.I) • Matrix.diagonal (a coerced to ℂ)
-- Composes S24 + S25 + S26 + S27 + S28 + S29 + S30 via eigenvalue sort
-- (Tuple.sort) + permutation matrix conjugation. The full diagonal case of
-- S.3 d≥3 PROPER. Spectral theorem lift to arbitrary Hermitian H follows.
import SKEFTHawking.FKLW.GenericSUdSymmetricDiagonalDischargeFull
-- Phase 6y Track S.3 substrate (Session 32, 2026-05-27): SPECTRAL LIFT —
-- discharge for ANY Hermitian-traceless H with spectral decomposition. Lifts
-- S31's diagonal discharge to arbitrary Hermitian H via the user-supplied
-- (U, a) spectral data (Mathlib's IsHermitian.spectralTheorem provides this).
-- Conjugates F_D, G_D for diag(a) by U via S26 → F, G for H.
import SKEFTHawking.FKLW.GenericSUdSpectralLift
-- Phase 6y Track S.3 d≥3 PROPER (Session 33, 2026-05-27): UNCONDITIONAL DISCHARGE.
-- For ANY Hermitian-traceless H ∈ Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ:
--   ∃ F G Hermitian-traceless, F · G − G · F = -((θ : ℂ) · Complex.I) • H
-- Combines S32's spectral-lift form with Mathlib's `IsHermitian.spectral_theorem`
-- (which extracts eigenvectorUnitary + eigenvalues from any Hermitian H).
-- THE SUBSTANTIVE FULL S.3 d≥3 PROPER DISCHARGE.
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeFull
-- Phase 6y Track S.3 d≥3 PROPER (Session 34, 2026-05-27): predicate-form lift.
-- For any d ≥ 2: `BalancedCommutator_SUd_unbounded d` (same as project's
-- `BalancedCommutator_SUd` but without linftyOp norm bounds) is UNCONDITIONALLY
-- discharged via S33. Worked examples at d ∈ {2, 3, 4, 8}. Predicate-form
-- substrate for downstream SK recursion consumers.
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorUnbounded
-- Phase 6y Track S.3 d≥3 PROPER (Session 35, 2026-05-27): all-d discharge.
-- Extends S34 to ALL `d : ℕ` (no `2 ≤ d` assumption). d ∈ {0, 1} via vacuous
-- F = G = 0 (H = 0 in those dimensions). d ≥ 2 via S34. Clean unconditional form.
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorUnboundedAllD
-- Phase 6y Track S.3 substrate (Session 36, 2026-05-27): NORM BRIDGE for unitary
-- conjugation (loose d² bound). For U ∈ unitaryGroup (Fin n) ℂ and any A:
--   ‖U · A · star U‖_linftyOp ≤ n² · ‖A‖_linftyOp
-- Via `Matrix.linfty_opNorm_mul` (submultiplicativity) + entry_norm_bound_of_unitary
-- (each entry of unitary has norm ≤ 1) → ‖U‖_linftyOp ≤ n. Combined with S26
-- conjugation invariance, gives a quantitative bound on the linftyOp norm after
-- spectral-then-conjugate. The tighter `n` bound (via Cauchy-Schwarz) ships in
-- a follow-on commit.
import SKEFTHawking.FKLW.GenericSUdNormBridgeUnitaryConjugation
-- Phase 6y Track S.3 substrate (Session 37, 2026-05-27): BOUNDED-FORM Hermitian
-- discharge. Composes S32 spectral-lift discharge with S36 norm bridge to give
-- the discharge with EXPLICIT linftyOp bounds on F, G:
--   ‖F‖_linftyOp ≤ (n+2)² · ‖F_inner‖_linftyOp
-- where F_inner is the inner diagonal-case witness. Concrete bound for downstream
-- consumers requiring explicit norm structure (e.g., SK recursion calibration).
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeBounded
-- Phase 6y Track S.3 substrate (Session 38, 2026-05-27): KEYSTONE INDEX —
-- aliases for the three load-bearing S.3 d≥3 PROPER theorems:
--   phase6y_S3_balancedCommutator_dischargeAlgebraic (direct)
--   phase6y_S3_balancedCommutator_dischargePredicate (all-d)
--   phase6y_S3_balancedCommutator_dischargeBounded (with linftyOp bound)
-- Single import point for downstream consumers. Docstring summarizes the
-- entire Sessions 14-37 substrate composition chain.
import SKEFTHawking.FKLW.GenericSUdPhase6yKeystoneIndex
-- Phase 6y Track S.3 substrate (Session 39, 2026-05-27): USAGE EXAMPLES at
-- Phase 6y target d values. Worked examples at SU(4) (T-A1′ trapped-ion)
-- and SU(8) (T-A2′ Clifford+CCZ) demonstrating downstream consumer pattern
-- + consumer obtain-pattern idiom for SK recursion contexts.
import SKEFTHawking.FKLW.GenericSUdPhase6yUsageExamples
-- Phase 6y Track S.3 substrate (Session 40, 2026-05-27): LOOSE BOUNDED PREDICATE.
-- Ships `BalancedCommutator_SUd_loose (d : ℕ) (K_d : ℝ) : Prop` — predicate
-- with explicit norm bound `‖F‖, ‖G‖ ≤ K_d · √(θ/2)` parameterized by K_d.
-- For S37+S36 composition: K_d = d² captures the spectral-then-conjugate
-- looseness. Plus `BalancedCommutator_SUd_loose_extends_unbounded` showing the
-- loose form implies the unbounded form (norm conjuncts droppable).
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorLoose
-- Phase 6y Track S (Session 41, 2026-05-27): SU(d) Dawson-Nielsen step
-- composing the keystone Session 33 `symmetric_balanced_commutator_hermitian_unconditional`
-- with project's matrix log substrate. Ships `DNStepData_SUd (d : ℕ)` structure +
-- `dnStepFG_sud {n : ℕ} (V_n U : ↥SU(n+2)) : DNStepData_SUd (n+2)` extracting
-- (F, G) for one DN step at SU(d) via the keystone. Substrate for SU(d) SK
-- recursion lift (Sessions 42+ — analog of Phase 6u Wave 4 `skApproxC_generic`).
import SKEFTHawking.FKLW.GenericSUdDnStepFG
-- Phase 6y Track S (Session 42, 2026-05-27): SU(d) matrix exponential coercion
-- to specialUnitaryGroup. SU(d) analog of `expIsu2` (Phase 6t Path A) conditional
-- on a det = 1 hypothesis (decouples from SU(2)-specific `DetExpZeroOnSu2_SU2`
-- ~2300 LoC substrate). Ships `I_smul_isHermitian_mem_skewAdjoint`,
-- `expAmbient_I_smul_mem_unitaryGroup`, `expIsud_conditional`,
-- `expIsud_of_det_predicate`, `ExpIsud_det_eq_one_predicate`. Substrate for
-- Sessions 43+ SK recursion lift (skApproxC_generic_sud + bounds + discharge).
import SKEFTHawking.FKLW.GenericSUdExpIsuD
-- Phase 6y Track S (Session 43, 2026-05-27): SU(d) Solovay-Kitaev recursion
-- engine. SU(d) analog of `skApproxC_generic` (Phase 6u Wave 4 SU(2)) composing
-- `dnStepFG_sud` (Session 41) + `expIsud_of_det_predicate` (Session 42). Ships
-- the structural recursion + level-0/(n+1) unfolding lemmas +
-- `BaseFinder_approximates_within_sud` predicate. Takes the det-predicate
-- hypothesis as a parameter (decouples from substantive det = 1 discharge).
-- Substrate for Sessions 44+ (super-quadratic bound + per-alphabet
-- instantiations + headline cascade unblock).
import SKEFTHawking.FKLW.GenericSUdSkApproxC
-- Phase 6y Track S (Session 44, 2026-05-27): SU(d) super-quadratic bound
-- predicate. SU(d) analog of `SkApproxCSuperQuadraticBound_generic` (Phase 6u
-- Wave 4 SU(2)). Captures the shape `‖ρ_hom (skApproxC_generic_sud n U) - U‖
-- ≤ ε_seq K (2·ε₀_sud) n`. Structural predicate; substantive discharge ships
-- in Session 45+ (analog of Phase 6u Wave 4b ~981-LoC discharge).
import SKEFTHawking.FKLW.GenericSUdSkApproxCBound
-- Phase 6y Track S (Session 45, 2026-05-27): SU(d) SK headline CASCADE
-- composition. Composes Sessions 41-44 substrate (dnStepFG_sud, expIsud_conditional,
-- skApproxC_generic_sud, super-quadratic bound predicate) into the F#4-compliant
-- SU(d) headline shape. Takes the 4 substantive ingredients as named hypotheses:
-- (1) det predicate, (2) bound discharge, (3) level chooser, (4) length-polylog
-- bound. Ships `skApproxC_generic_sud_error_cascade` + `skHeadline_FreeGroup_SUd_cascade`.
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascade
-- Phase 6y Track S (Session 46, 2026-05-27): SU(d) generic polylog-level
-- chooser. SU(d) analog of `skLevel_polylog` (Phase 6u SU(2)). Ships definition
-- `skLevel_polylog_sud K ε := ⌈log(log(1/(K²·ε))/log 4)/log(3/2)⌉₊` + spec
-- predicate `SkLevelPolylog_sud_spec K ε₀_sud`. Substantive discharge ships
-- in Session 47+ (analog of ~110-LoC SU(2) spec proof).
import SKEFTHawking.FKLW.GenericSUdSkLevelPolylog
-- Phase 6y Track S (Session 47, 2026-05-27): SU(d) SK cascade INDEX
-- documenting Sessions 41-46 substrate chain. Provides documented aliases for
-- the cascade entry points + summarizes the 4 substantive ingredients reduction.
import SKEFTHawking.FKLW.GenericSUdSkCascadeIndex
-- Phase 6y Track S (Session 48, 2026-05-27): SUBSTANTIVE DISCHARGE of
-- SkLevelPolylog_sud_spec at SU(d). Generic in K with calibration condition
-- K² · 2·ε₀_sud ≤ 1/4. Lifts the SU(2) ~110-LoC `skLevel_polylog_spec` proof
-- to K-parametric form. Discharges the 3rd of 4 substantive ingredients
-- enumerated by Session 47's cascade index.
import SKEFTHawking.FKLW.GenericSUdSkLevelPolylogSpec
-- Phase 6y Track S (Session 49, 2026-05-27): SUBSTANTIVE discharge of
-- `ExpIsud_det_eq_one_predicate` at SU(d) for d ≥ 2. For any Hermitian-traceless
-- F : Matrix (Fin (n+2)) (Fin (n+2)) ℂ, proves det(exp(I·F)) = 1 via spectral
-- decomposition + Matrix.exp_conj + Matrix.exp_diagonal + Matrix.det_diagonal +
-- Pi.exp_def + Complex.exp_sum. Discharges the 1st of 4 substantive ingredients
-- enumerated by Session 47's cascade index. Composes with Session 42's
-- expIsud_of_det_predicate to give UNCONDITIONAL SU(d) exp coercion.
import SKEFTHawking.FKLW.GenericSUdExpIsuDDetDischarge
-- Phase 6y Track S (Session 50, 2026-05-27): REFINED 2-INGREDIENT cascade.
-- Composes Session 45's full cascade with Sessions 48 + 49 substantive discharges
-- (polylog level spec + det predicate) to reduce SU(d) SK headline cascade to
-- only 2 remaining ingredients: super-quad bound + length bound. Ships
-- `skHeadline_FreeGroup_SUd_cascade_2ingredient` + `_with_calibration`.
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascade2Ingredient
-- Phase 6y Track S (Session 51, 2026-05-27): SU(d) word-length closed-form
-- upper bound. SU(d) analog of Phase 6u SU(2) `skLength`. Ships
-- `skLength_sud baseCase decompCost n := baseCase·5^n + decompCost·(5^n-1)/4`
-- (parametric in per-alphabet constants) + nonneg/monotone helpers +
-- recursive form + `SkLengthPolylogBound_sud` predicate. Alphabet-agnostic
-- 5-fold branching closed-form. Substrate for the length-bound ingredient
-- (4th of 4 enumerated by Session 47 cascade index).
import SKEFTHawking.FKLW.GenericSUdSkLength
-- Phase 6y Track S (2026-05-28): canonical single-source SK length exponent
-- `skLengthExponent_sud := log 5 / log (3/2)` (Dawson-Nielsen). De-duplicates the
-- exponent across all SU(d) headline/cascade/calibration modules.
import SKEFTHawking.FKLW.GenericSUdSkLengthExponent
-- Phase 6y Track S (2026-05-28): UNCONDITIONAL discharge of SkLengthPolylogBound_sud
-- at the canonical exponent log 5/log(3/2) (lifts the SU(2) skLength_at_skLevel_polylog_le).
import SKEFTHawking.FKLW.GenericSUdSkLengthPolylogDischarge
-- Phase 6y Track S (2026-05-28): F#4 length conjunct discharged + headline-from-density.
-- Composes the asymptotic + S141 closed-form + S55 base-finder bound → cascade h_length_polylog;
-- reduces SU(d) headline to ONLY the (D) density witness + word-length bundle.
import SKEFTHawking.FKLW.GenericSUdConcreteLengthPolylog
-- Phase 6y Tracks T-A1′.5 / T-A2′.5 (2026-05-28): per-alphabet headline reduced to the (D)
-- ClosureDenseWitness ALONE (composes from_density + densityFromWitness). Sole remaining
-- substantive ingredient is the witness (Brylinski-Brylinski SU(4) / Aaronson-Gottesman SU(8)).
import SKEFTHawking.FKLW.GenericSUdPerAlphabetHeadlineFromWitness
-- Phase 6z.5 closeout (2026-05-29): literal no-`T` Clifford+CCZ SU(8) Solovay–Kitaev headline
-- `cliffordCCZLiteral_solovayKitaev_headline_unconditional` — wraps the shipped
-- `cliffordCCZLiteral_dense` (CCZ-essential, T-free) into the named compilation headline.
import SKEFTHawking.FKLW.CliffordCCZSU8LiteralHeadline
-- Phase 6y Track S.6 (2026-05-28): canonical-named generic SU(d) bundled-strict headline
-- `solovayKitaev_dawson_nielsen_quantitative_generic_sud_strict_constructive_tight`.
import SKEFTHawking.FKLW.GenericSUdQuantitative
-- Phase 6y Track S (Session 52, 2026-05-27): UNCONDITIONAL `expIsud` at SU(d≥2).
-- Composes Session 42's `expIsud_of_det_predicate` with Session 49's substantive
-- `expIsud_det_eq_one_predicate_holds` — removes the det-hypothesis from
-- downstream consumers. SU(d) analog of Phase 6t SU(2)'s `expIsu2`. Ships
-- `expIsud` + value extraction + worked examples at SU(2)/SU(4)/SU(8).
import SKEFTHawking.FKLW.GenericSUdExpIsuDUnconditional
-- Phase 6y Track S (Session 53, 2026-05-27): SUBSTANTIVE length-bound recursion
-- discharge at SU(d) (parametric in wordLength function). Lifts Phase 6x
-- `skApproxC_generic_freeGroup_length_le_skLength` from SU(2) to SU(d).
-- Ships `BaseFinder_length_bounded_sud_param`, `WordLengthFreeGroupLike`
-- bundle, `skApproxC_generic_sud_length_succ_param` per-step recurrence,
-- and `skApproxC_generic_sud_length_le_skLength_sud_param` strong induction
-- bound. Composes with Session 51's closed-form skLength_sud for the
-- length-bound substantive ingredient.
import SKEFTHawking.FKLW.GenericSUdConcreteWordLengthBound
-- Phase 6y Track S (Session 54, 2026-05-27): per-alphabet length-bound
-- specializations at SU(4) trapped-ion + SU(8) Clifford+CCZ. Applies Session
-- 53's parametric framework via FreeGroup.norm_mul_le + FreeGroup.norm_inv_eq.
-- Ships `freeGroup_wordLength_su4`/`_su8` + their submultiplicativity bundles
-- + per-alphabet wrapper theorems `trappedIonSU4_length_le_skLength_sud` +
-- `cliffordCCZSU8_length_le_skLength_sud`.
import SKEFTHawking.FKLW.GenericSUdLengthBoundPerAlphabet
-- Phase 6y Track S (Session 55, 2026-05-27): length-bounded baseFinder discharge
-- from constructive ε-net. Shows `findNearestInCover_SUd` output length ≤
-- max word length over cover Finset, discharging `BaseFinder_length_bounded_sud_param`
-- (Session 53 predicate). Substrate for T-A1′.5/T-A2′.5 cascade unblock via
-- per-alphabet ε-net consumer.
import SKEFTHawking.FKLW.GenericSUdBaseFinderLengthBound
-- Phase 6y Track S (Session 56, 2026-05-27): END-TO-END SU(d) cascade reducing
-- F#4-compliant SU(d) headline to JUST 2 substantive ingredients: (D) density
-- witness + (B) super-quad bound discharge. Composes Sessions 41-55 substrate
-- internally. Ships `skHeadline_FreeGroup_SUd_cascade_final`.
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascade2IngredientFinal
-- Phase 6y Track T-A1′.5 (Session 57, 2026-05-27): per-alphabet cascade-final
-- discharge of `trappedIonSU4FullHeadline` (T-A1′.5 F#4-compliant headline).
-- Instantiates Session 56's end-to-end cascade at SU(4) trapped-ion. Reduces
-- T-A1′.5 to ONLY 2 remaining substantive ingredients: (D) density witness
-- at SU(4) + (B) super-quad bound at SU(4).
import SKEFTHawking.FKLW.TrappedIonSU4HeadlineCascadeFinal
-- Phase 6y Track T-A2′.5 (Session 58, 2026-05-27): per-alphabet cascade-final
-- discharge of `cliffordCCZSU8Headline` (T-A2′.5 F#4-compliant headline).
-- Mirror of Session 57 at SU(8) Clifford+CCZ. Reduces T-A2′.5 to ONLY 2
-- remaining substantive ingredients: (D) density witness at SU(8) + (B)
-- super-quad bound at SU(8).
import SKEFTHawking.FKLW.CliffordCCZSU8HeadlineCascadeFinal
-- Phase 6y (Session 59, 2026-05-27): Phase 6y CASCADE CLOSURE STATUS INDEX.
-- Documentation module crystallizing the cascade state. Documents:
-- (1) Tracks S.1-S.5 UNCONDITIONAL; (2) Track S.6 cascade substrate + 3 of 4
-- substantive ingredients discharged; (3) Tracks M-S/T-A1′/T-A2′ shipped;
-- (4) Sessions 56-58 cascade-final compositions reducing headlines to
-- 2 remaining ingredients (D) + (B). Useful for downstream consumers +
-- Stage-13 review prep.
import SKEFTHawking.FKLW.Phase6yClosureStatusIndex
-- Phase 6y Track S (Session 60, 2026-05-27): super-quad bound SUBSTRATE
-- lift — first lemma of ~10 from SU(2). Ships `residual_norm_le_d_mul` at
-- SU(d) (SU(d) analog of SU(2)'s `residual_norm_le_sqrt_two_mul` using
-- `linftyOpNorm_unitary_le` Session 36 substrate). Substrate for full
-- SU(d) super-quad bound discharge.
import SKEFTHawking.FKLW.GenericSUdSuperQuadSubstrate
-- Phase 6y Track S (Session 69, 2026-05-27): bounded-form (F,G) existence at
-- dnStep level. Composes Session 33 spectral extraction + Session 37 bounded
-- form to give `balanced_commutator_bounded_of_hermitian` — UNCONDITIONAL-in-H
-- existence of F,G,F_inner,G_inner with `‖F‖ ≤ (n+2)²·‖F_inner‖` + commutator
-- identity. Super-quad bound F/G-norm substrate (remaining gap: ‖F_inner‖ bound).
import SKEFTHawking.FKLW.GenericSUdDnStepFGBounded
-- Phase 6y Track S (Session 70, 2026-05-27): σ_y/σ_x-block sum linftyOp norm
-- bound. Triangle inequality + per-block norm ≤ 1 (Session 10) gives
-- `‖∑ p ∈ s, γ p • σ_y(a p)(b p)‖ ≤ ∑ p ∈ s, |γ p|`. F_inner norm bound
-- substrate for the super-quad bound F/G-norm ingredient.
import SKEFTHawking.FKLW.GenericSUdSigmaYSumNormBound
-- Phase 6y Track S (Session 71, 2026-05-27): permutation-conjugation preserves
-- linftyOp norm. `‖permMatrix σ · A · permMatrix σ⁻¹‖ = ‖A‖` via the entry-wise
-- identity `= Matrix.reindex σ⁻¹ σ⁻¹ A` + Phase 6x M.1 `Matrix.linftyOpNorm_reindex`.
-- Bridges the eigenvalue-sort permMatrix conjugation (Session 28/31) to the
-- σ_y-sum norm bound (Session 70) for the F_inner norm bound.
import SKEFTHawking.FKLW.GenericSUdPermConjNormPreserve
-- Phase 6y Track S (Session 72, 2026-05-27): γ-sum algebraic decomposition.
-- For γ_p = √(θ·b_p/2), ships `∑ √(θ·b_p/2) = √(θ/2)·∑√b_p` + `∑√b_p ≤ card·√B`
-- + `gamma_sum_bound` giving `∑|γ_p| ≤ √(θ/2)·card·√B`. F_inner norm bound
-- with K_inner = card·√B (B = max partial sum bound from Gershgorin).
import SKEFTHawking.FKLW.GenericSUdGammaSumDecomp
-- Phase 6y Track S (Session 73, 2026-05-27): Hermitian eigenvalue bounded by
-- linftyOp norm (Gershgorin). `|hA.eigenvalues i| ≤ ‖A‖` via charpoly root →
-- HasEigenvalue (toLin' A) → `eigenvalue_mem_ball` (Mathlib Gershgorin) →
-- |μ| ≤ row-k sum ≤ max row sum = ‖A‖_linftyOp. Last mathematical ingredient
-- for the F_inner partial-sum bound B = d·‖H‖.
import SKEFTHawking.FKLW.GenericSUdEigenvalueLinftyBound
-- Phase 6y Track S (Session 77, 2026-05-27): bounded symmetric diagonal discharge.
-- Strengthens Session 24 to ALSO return `‖F‖,‖G‖ ≤ ∑_p √(θ·(b_p).re/2)` — the
-- explicit-witness norm bound via Session 70 applied to F = ∑γ·σ_y. The re-thread
-- exposing the inner-witness norm bound for the super-quad F/G-norm ingredient.
import SKEFTHawking.FKLW.GenericSUdSymmetricDischargeBounded
-- Phase 6y Track S (Session 79, 2026-05-27): bounded full diagonal discharge.
-- Session 31's eigenvalue-sort full diagonal discharge for ANY traceless real H,
-- strengthened to ALSO return `‖F‖, ‖G‖ ≤ ∑_p √(θ·(sorted partial sum).re/2)`.
-- Threads Session 77 (bounded discharge) at the sorted diagonal + Session 78
-- (permMatrixAsUnitary conjugation norm preservation) through the sort conjugation.
import SKEFTHawking.FKLW.GenericSUdSymmetricDiagonalDischargeFullBounded
-- Phase 6y Track S (Session 80, 2026-05-27): explicit-∑√ bounded Hermitian discharge.
-- Re-threads Session 37 with Session 79's bounded diagonal discharge so the inner
-- witness norm is replaced by the explicit spectral partial-sum bound
-- `‖F‖ ≤ (n+2)²·∑_p √(θ·(sorted partial sum of eigenvalues).re/2)`.
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeBoundedExplicit
-- Phase 6y Track S (Session 81, 2026-05-27): concrete K_F·√(θ/2) bounded keystone.
-- Composes Session 80 with the spectral partial-sum analysis (Gershgorin
-- eigenvalue bound + partial-sum bound + γ-sum decomposition) to give the
-- concrete `‖F‖ ≤ (n+2)²·(n+1)·√(n+2)·√(θ/2)` form needed by the F-norm predicate.
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeKeystoneBounded
-- Phase 6y Track S (Session 82, 2026-05-27): dnStepFG_sud F/G-norm bound discharge.
-- dnStepFG_sud re-wired to extract (F,G) from the bounded keystone (Session 81),
-- so the chosen witnesses carry the concrete bound; discharges
-- DnStepFG_sud_F/G_norm_bound_predicate at K_F = (n+2)²·(n+1)·√(n+2).
import SKEFTHawking.FKLW.GenericSUdDnStepFGNormBound
-- Phase 6y Track S (Session 83, 2026-05-27): dnStepFG_sud structural extraction.
-- Commutator identity (valid branch) `[F,G] = -matrixLog (n+2) Δ.val` + invalid-branch
-- F=G=0, mirroring the SU(2) structural lemmas for the super-quad main induction.
import SKEFTHawking.FKLW.GenericSUdDnStepFGCommutator
-- Phase 6y Track S (Session 84, 2026-05-27): dnStepFG_sud exp(-[F,G]) = Δ identity.
-- Composes Session 83's commutator identity with the matrix exp/log right-inverse
-- expAmbient_matrixLog (valid regime Δ.val ∈ target). Super-quad induction substrate.
import SKEFTHawking.FKLW.GenericSUdDnStepFGExpDelta
-- Phase 6y Track S (Session 85, 2026-05-27): expIsud near-identity norm bounds.
-- `‖(expIsud n F).val − 1‖ ≤ δ·exp δ` (forward + matrix-inverse), via the
-- dimension-generic MatrixBCH.norm_exp_pm_I_smul_sub_one_le_delta. Super-quad substrate.
import SKEFTHawking.FKLW.GenericSUdExpIsuDNormBound
-- Phase 6y Track S (Session 86, 2026-05-27): dnStepFG_sud group-commutator cubic remainder.
-- `‖gC(expIsud F, expIsud G) − Δ‖ ≤ 320·δ³` via the dimension-generic BCH cubic remainder
-- + Session 84's exp(−[F,G]) = Δ. The recursion's super-quadratic error-contraction step.
import SKEFTHawking.FKLW.GenericSUdDnStepFGCubic
-- Phase 6y Track S (Session 129, 2026-05-28): log-agnostic Dawson-Nielsen step dnStepFG_fromLog
-- (re-point R4 foundation). Factors dnStepFG_sud over its generator matrix M (dnStepFG_sud =
-- dnStepFG_fromLog (matrixLog …) by rfl); ships [F,G]=-M + invalid-branch + round-trip-conditional
-- exp(-[F,G])=Δ generic in M, so the concrete log matrixMercatorLog(Δ−1) (S118/S120-128) can be
-- substituted without duplicating the super-quad chain.
import SKEFTHawking.FKLW.GenericSUdDnStepFGFromLog
-- Phase 6y Track S (Session 130, 2026-05-28): concrete-radius DN step dnStepFG_sud_concrete
-- (re-point R4). Instantiates dnStepFG_fromLog at matrixMercatorLog(Δ−1); ships exp(-[F,G])=Δ
-- UNCONDITIONALLY on the named ball (n+2)²·‖V_n−U‖≤1/8 (existential Δ∈target eliminated) via
-- exp_matrixMercatorLog + concrete regime conjuncts S122/S127/S128.
import SKEFTHawking.FKLW.GenericSUdDnStepFGConcrete
-- Phase 6y Track S (Session 131, 2026-05-28): log-agnostic + concrete DN step F/G-norm bound.
-- dnStepFG_fromLog_{F,G}_norm_le (‖F‖,‖G‖ ≤ K_F·√(θ/2), θ=‖(-i)•M‖, generic in M) +
-- dnStepFG_sud_concrete_{F,G}_norm_le (re-pointed at matrixMercatorLog). Re-point R4 norm ingredient.
import SKEFTHawking.FKLW.GenericSUdDnStepFGFromLogNormBound
-- Phase 6y Track S (Session 132, 2026-05-28): concrete dnStep group-commutator cubic remainder.
-- dnStepFG_sud_concrete_gC_minus_Delta_norm_le_cubic — ‖gC(expIsud F,expIsud G)−Δ‖≤320·δ³ on the
-- named ball (n+2)²·‖V_n−U‖≤1/8 (existential h_regime3 + Δ∈target ELIMINATED via S130 exp-delta).
import SKEFTHawking.FKLW.GenericSUdDnStepFGConcreteCubic
-- Phase 6y Track S (Session 133, 2026-05-28): concrete-radius SK recursion skApproxC_generic_sud_concrete.
-- Re-pointed skApproxC_generic_sud extracting each level's (F,G) via dnStepFG_sud_concrete (S130);
-- foundation for the UNCONDITIONAL concrete (B) bound. + zero/succ unfolding lemmas.
import SKEFTHawking.FKLW.GenericSUdSkApproxCConcrete
-- Phase 6y Track S (Session 139, 2026-05-28): UNCONDITIONAL concrete (B) super-quad bound (re-point R4
-- FINAL). SkApproxCSuperQuadraticBound_generic_sud_concrete_holds — NO h_regime hypothesis (per-level
-- regime discharged internally via S120 θ-bound + calibration two_ε₀_sud_mul_le_half / sq_*_eighth).
import SKEFTHawking.FKLW.GenericSUdSkApproxCBoundConcrete
-- Phase 6y Track S (Session 140, 2026-05-28): UNCONDITIONAL SU(d) SK headline via the concrete
-- re-point (R4 capstone). skHeadline_FreeGroup_SUd_cascade_B_discharged_concrete — produces
-- SolovayKitaevHeadline_FreeGroup_SUd from (D) density + length-polylog with NO h_regime hypothesis
-- (compile witness = skApproxC_generic_sud_concrete; error from S139 unconditional (B) bound).
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascadeConcrete
-- Phase 6y Track S (Session 141, 2026-05-28): concrete-recursion word-length bound (R4 length ingredient).
-- skApproxC_generic_sud_concrete_length_{succ,le_skLength_sud}_param — word length is log-independent
-- (identical group-word shape), so the IFT S53 per-step + closed-form skLength_sud bounds transfer.
import SKEFTHawking.FKLW.GenericSUdSkApproxCConcreteLength
-- Phase 6y Track S (Session 134, 2026-05-28): concrete super-quad induction substrate (base case +
-- polynomial F/G-norm bounds). skApproxC_generic_sud_concrete_zero_error_bound (base, log-agnostic) +
-- dnStepFG_sud_concrete_{F,G}_norm_le_poly ((n+2)⁴·√(θ/2) form, composes S131 + S90).
import SKEFTHawking.FKLW.GenericSUdSuperQuadInductionConcrete
-- Phase 6y Track S (Session 87, 2026-05-27): SU(d) ρ_hom MonoidHom abstraction lemmas.
-- ρ_hom_sud_mul_val / _inv_val / _groupCommutator_val (+ SUd_subtype_inv_val_eq_matrix_inv):
-- push gs.ρ_hom : W →* SU(d) to the matrix level. Super-quad main-induction MonoidHom substrate.
import SKEFTHawking.FKLW.GenericSUdRhomAbstraction
-- Phase 6y Track S (Session 89, 2026-05-27): super-quad main-induction assembly (base case).
-- skApproxC_generic_sud_zero_error_bound — level-0 error ≤ ε_seq K (2·ε₀) 0 = 2·ε₀.
-- First component of the SkApproxCSuperQuadraticBound_generic_sud (B) discharge.
import SKEFTHawking.FKLW.GenericSUdSuperQuadInduction
-- Phase 6y Track S.6 (Session 103, 2026-05-28): headline cascade with (B) discharged.
-- Feeds Session 102's (B) super-quad discharge into the Session 56 cascade, reducing
-- the SU(d) headline to (D) density witness + regime hypothesis + length-polylog.
import SKEFTHawking.FKLW.GenericSUdSkHeadlineCascadeBDischarged
-- Phase 6y Track S (Session 104, 2026-05-28): regime guards. H = (-i)·matrixLog Δ is
-- Hermitian + traceless on a nbhd of 1 (from matrixLog-in-su-d substrate); the
-- Hermitian/traceless component of the h_regime hypothesis discharge.
import SKEFTHawking.FKLW.GenericSUdRegimeGuards
-- Phase 6y Track S (Session 109, 2026-05-28): concrete-radius Mercator power-series
-- matrix log (brick 1). matrixMercatorLog converges on the NAMED ball ‖X‖<1 with
-- ‖·‖ ≤ ‖X‖/(1−‖X‖) (≤ 2‖X‖ for ‖X‖≤1/2), the concrete-radius replacement for the
-- existential IFT matrixLog — toward the unconditional regime discharge.
import SKEFTHawking.FKLW.GenericSUdMatrixMercatorLog
-- Phase 6y Track S (Session 120, 2026-05-28): concrete-radius regime substrate (re-point
-- R0/R1). regime_thetabound_concrete — the θ-bound conjunct on a NAMED ball, composing the
-- K=2 Mercator bound (S109) + SU(d) residual bound (S60). First brick of re-pointing the
-- regime from the existential IFT matrixLog to matrixLogConcrete := matrixMercatorLog(·−1).
import SKEFTHawking.FKLW.GenericSUdRegimeConcrete
-- Phase 6y Track T-A2′.4 (2026-05-27): Clifford+CCZ SU(8) calibration constants
-- (mirror of TrappedIonSU4Calibration at d=8).
import SKEFTHawking.FKLW.CliffordCCZSU8Calibration
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
-- Phase 6q Wave 1a.2 (2026-05-23): Drude–Kadanoff–Martin (DKM) transport
-- bootstrap predicate substrate. Chowdhury–Hartnoll–Hebbar–Khondaker
-- (arXiv:2509.18255) is purely analytic — sidesteps the three Phase 6o
-- Wave 1c NO-GO obstructions (unitarity→KMS, crossing, complex-contour
-- SDP) by design. Ships DKMParameters 5-real positivity capsule,
-- explicit CHHK eq. (15) Im G^R form, 6 axiom-family Props (F1–F6)
-- bundled into IsDKMAxiomSet, Drude metal (τ→0) closed form as
-- substantive textbook example, plus zero-correlator witness for the 4
-- testable axiom families.
import SKEFTHawking.DKMBootstrap.Predicates
-- Phase 6q Wave 1b.1 (2026-05-23): CHHK ↔ CGL six-axiom-set bridge.
-- Action-correlator link predicate `IsDKMSpectralFunction`; F4 / F5 / F6
-- bridges from `SKEFTAxioms` to CHHK axiom families; F1 strictly-stronger
-- structural statement; substantive F2 / F3 orthogonality theorems (CHHK
-- microscopic axioms NOT implied by CGL `SKEFTAxioms`); trivial-link
-- well-posedness witness.
import SKEFTHawking.DKMBootstrap.AxiomSet
-- Phase 6q Wave 1b.2 (2026-05-23): KMS-replaces-unitarity structural
-- lemma — Phase 6o Obstruction (I) fully resolved at the 2-pt-function
-- level. KMSReplacesUnitarity predicate + kms_replaces_unitarity_thm
-- substantive theorem + zero-substrate witnesses.
import SKEFTHawking.DKMBootstrap.KMSConsistency
-- Phase 6q Wave 1b.3 (2026-05-23): no-crossing structural finding —
-- Phase 6o Obstruction (II) fully resolved. IsVerticalBootstrap
-- predicate + vertical_bootstrap_bypasses_crossing structural theorem
-- + dkm_axiom_set_iff_vertical_plus_f4f5f6 equivalence.
import SKEFTHawking.DKMBootstrap.NoCrossing
-- Phase 6q Wave 1c.1 (2026-05-23): SDP-bypass structural finding —
-- Phase 6o Obstruction (III) fully resolved. IsAnalyticBootstrap
-- predicate + analytic_iff_vertical_plus_f4f5f6 equivalence + forward-
-- deferred IsDKMFeasibleSDPCandidate scaffold.
import SKEFTHawking.DKMBootstrap.SDPStructure
-- Phase 6q Wave 1c.2 (2026-05-23): linear-functional convex cone.
-- IsDKMCompatibleFunctional predicate + three convex-cone closure
-- theorems (zero / nonneg-scaling / sum) + evalAt point-evaluation
-- non-vacuity witnesses.
import SKEFTHawking.DKMBootstrap.LinearFunctionals
-- Phase 6q Wave 1c.3 (2026-05-23): LDP cross-bridge — highest-leverage
-- cross-bridge of the phase. DKMToLDPData construction with FDT-pinned
-- variance σ²:= χ·D; dkm_rate_function_is_LDPRateFunction substantive
-- theorem instantiating the Phase 6n abstract LDP class on Phase 6q
-- DKM substrate; chhk_positivity_yields_LDP_rate_function cross-bridge.
import SKEFTHawking.DKMBootstrap.LDPBridge
-- Phase 6q Wave 2a.2 (2026-05-23): SK-EFT-Hawking specialization of the
-- DKM bootstrap. IsCHHKBootstrapBound + IsMIRBound predicates;
-- IsDKMCompatibleSKEFT Wilson-coefficient bridge to FirstOrderCoeffs;
-- IsGaussianFluctuationRegime DR §6 condition; IsLDPCompatibleCorrelator
-- bundled predicate + forward-direction chhk_positivity_yields_LDP_compatible.
import SKEFTHawking.DKMBootstrap.SKEFTSpecialization
-- Phase 6q Wave 2a.3 (2026-05-23): E1/E2 platform cross-bridge.
-- PlatformKMSQuality 3-way classifier (Strong/Approximate/EffectiveOnly);
-- per-platform DKMParameters witnesses (graphene/BEC/polariton);
-- LDP-compatibility + MIR-bound per-platform theorems;
-- platform_kms_qualities_pairwise_distinct substantive structural finding.
import SKEFTHawking.DKMBootstrap.E1E2CrossBridge
-- Phase 6q Wave 2b (2026-05-23): horizon-transport bootstrap, BIMODAL OUTCOME.
-- POSITIVE-UNIQUENESS HALF: HorizonTransportUniquenessBound predicate +
-- horizon_transport_uniqueness_thm substantive theorem + graphene witnesses
-- at mirConst=0 (trivial) and mirConst=1/2 (substantively-nontrivial).
-- SHARPENED-NO-GO HALF: IsSuperFactorialUnbounded predicate + sharpened_no_go
-- _super_factorial substantive theorem (Yin-Lucas/Kuwahara-Saito Lieb-Robinson
-- -for-bosons substrate). PlatformBimodalOutcome explicit disjunction + graphene
-- witness for the positive-uniqueness half. Both halves shipped substantively.
import SKEFTHawking.DKMBootstrap.HorizonTransportBootstrap
-- Phase 6q Wave 2b.4 (2026-05-25): substantive BEC Bogoliubov-bosonic
-- unbounded-norm lift. becBogoliubovCommutatorNorm := (2κ)! concrete
-- substrate-level stand-in for the bosonic ‖[H,[H,…,[H,n_x]]]_κ‖ sequence;
-- becBogoliubovCommutatorNorm_isSuperFactorialUnbounded substantively
-- instantiates the predicate; bec_falls_under_sharpened_no_go closes the
-- second-NO-GO half at concrete-substrate-instance level via Mathlib's
-- FloorSemiring.tendsto_pow_div_factorial_atTop + central-binomial
-- (κ!)² ≤ (2κ)!.
import SKEFTHawking.DKMBootstrap.BECBogoliubovBosonicGrowth
-- Phase 6v Wave 6v.3 (2026-05-26): polariton DKM F3 bound + bimodal-branch
-- resolution. Closes the Phase 6q open question: polariton, under a finite
-- pump-energy operating constraint (Penn TMD 4 fJ → 1.44×10⁴ photons/mode
-- ≪ n_threshold ≈ 10⁶), takes the POSITIVE-uniqueness branch of
-- PlatformBimodalOutcome — inheriting the graphene witness at substrate
-- normalized mirConst = 1/2. polariton_dkm_f3_holds_at_pump_below_threshold
-- is the substantive contrapositive of sharpened_no_go_super_factorial.
import SKEFTHawking.DKMBootstrap.PolaritonF3Bound
-- Phase 6v Wave 6v.1 (2026-05-26): Williamson-Yoder gauging-QEC overhead
-- bound (arXiv:2410.02213). Substrate-level encoding of the "qubit overhead
-- linear in the weight of the operator being measured up to a polylogarithmic
-- factor" headline. gaugingQEC_auxQubit_overhead_le ships the bound with C=1
-- via williamsonYoderAuxQubits W := W * (Nat.log 2 W + 1); the substantive
-- contrast quadraticOverhead_not_linear establishes that the polylog factor
-- is unavoidable for ANY scheme that includes the quadratic baseline.
-- FIRST kernel-verified declaration under D6 ("Formally Verified
-- Fault-Tolerant Quantum Computation Substrate") publication bundle.
import SKEFTHawking.FaultTolerance.GaugingQEC
-- Phase 6v Wave 6v.2 (2026-05-26): Shor ECC-256 T-gate-count upper bound
-- (arXiv:2603.28846 Babbush-Gidney-et-al. 2026 + Bravyi-Kitaev 2005 exact
-- 7-factor decomposition). googleShorECC256TGateBound config1200 = 630M,
-- config1450 = 490M; both fit inside the 1-G T-gate FT-QC budget envelope
-- with substantive headroom (370M / 510M respectively). FIRST kernel-
-- verified end-to-end ECC-256 Shor T-gate-count bound in any proof
-- assistant. Lifts into D6 §5.
import SKEFTHawking.FaultTolerance.ShorTGateCount
-- Phase 6v Wave 6v.5 (2026-05-26): APM-LDPC code substrate + Shannon-
-- capacity hashing-bound predicate (Komoto-Kasai 2025 npj QI 11, 154).
-- QuEra/Harvard/MIT [[1152, 580, ≤12]] reference code: rate 580/1152 ≈
-- 0.5035 > 1/2 (`IsRateAboveHalf` substantive ship); the rate-exactly-1/2
-- `[[2k, k]]` code is the substantive falsifier-class instance.
-- `IsHashingBoundAchievable` predicate with substrate-level witness at
-- the representative Komoto-Kasai threshold 53/100. Lifts into D6 §4.
import SKEFTHawking.FaultTolerance.APMLdpcHashingBound
-- Phase 6v Wave 6v.6 (2026-05-26): W-state QFT decomposition in Q(ζ_N)
-- substrate. Substrate-level encoding of the cyclic-shift QFT
-- decomposition: n-qubit W-state has Z_n cyclic-shift symmetry, so
-- single-shot projective measurement yields n outcomes (vs full 2^n
-- Hilbert space). Concrete exponential-vs-polynomial separations at
-- n = 5 (QCyc5), n = 8 (QCyc16), n = 40 (QCyc40) project-substrate
-- sizes. Lifts into D6 §6.
import SKEFTHawking.FaultTolerance.WStateQFT
-- Phase 6AA (2026-06-01): Verified Quantum-Network Substrate (bundle D6 §6).
-- The import DAG is a tree rooted at Basic with leaves Envelope (→EndToEnd→Swapping),
-- NumericalBounds (→Channels), Distillation, WStateRate — import all leaves to cover
-- all 8 modules.
import SKEFTHawking.QuantumNetwork.Envelope
import SKEFTHawking.QuantumNetwork.NumericalBounds
import SKEFTHawking.QuantumNetwork.Distillation
import SKEFTHawking.QuantumNetwork.WStateRate
-- Phase 6AB (2026-06-01): decay-inclusive envelope + general Bell-diagonal swap (new leaf modules).
import SKEFTHawking.QuantumNetwork.DecayEnvelope
import SKEFTHawking.QuantumNetwork.BellDiagonalSwap
import SKEFTHawking.QuantumNetwork.RepeaterChain
-- Phase 6AC (2026-06-01): BB84 secret-key rate (Shor–Preskill, crossover proven not hardcoded).
import SKEFTHawking.QuantumNetwork.SecretKeyRate
-- Phase 6AC (2026-06-01): multipartite W₃-vs-GHZ₃ randomization-advantage comparison.
import SKEFTHawking.QuantumNetwork.MultipartiteComparison
-- Phase 6AC (2026-06-01): Horodecki teleportation fidelity (Haar value = tracked hypothesis).
import SKEFTHawking.QuantumNetwork.Teleportation
-- Bucket 3.1 (2026-06-01): Haar–Pauli integral discharged → teleportation unconditional.
import SKEFTHawking.QuantumNetwork.HaarPauli
-- Bucket 3.2 (2026-06-01): W1′ Tier-1 anchors (linear-optics BSM bound + physics link rate).
import SKEFTHawking.QuantumNetwork.Rate
-- Bucket 3.3 (2026-06-01): DEJMPS general-Bell-diagonal map structure + sub-basin convergence.
import SKEFTHawking.QuantumNetwork.DEJMPSConvergence
-- Phase 6AE-A (2026-06-01): general mixed-state certification layer (trace norm/distance) — foundation.
import SKEFTHawking.QuantumNetwork.MixedState
-- Phase 6AE-B (2026-06-01): channel structure for the diamond norm (partial trace, Choi matrix).
import SKEFTHawking.QuantumNetwork.DiamondNorm
-- Phase 6AF-4 (2026-06-01): CPTP Kraus channel + trace-distance contractivity (data processing).
import SKEFTHawking.QuantumNetwork.CPTPChannel
-- Phase 6AM W2 (2026-06-09): Kraus↔MState/CPTPMap bridge to PhysLib + sandwiched-Rényi DPI transfer witness.
import SKEFTHawking.QuantumNetwork.PhyslibBridge
-- Phase 6AM W3 (2026-06-09): consume PhysLib — SSA on the repo representation + operational relative entropy of entanglement.
import SKEFTHawking.QuantumNetwork.PhyslibConsequences
-- Phase 6AF-6 (2026-06-01): the diamond distance ½‖Φ₁−Φ₂‖_◇ (tensor channel + bounded sSup).
import SKEFTHawking.QuantumNetwork.DiamondNormSup
-- Phase 6AF-7 (2026-06-01): fidelity bounds (F≤1 / Fuchs–van de Graaf) — entry point + blueprint.
import SKEFTHawking.QuantumNetwork.FidelityBounds
-- Phase 6AF-8 (2026-06-02): diamond-distance attainment — trace-norm continuity (Frobenius Lipschitz).
import SKEFTHawking.QuantumNetwork.DiamondNormAttainment
-- Phase 6AF-9 (2026-06-02): diamond-norm Choi/maximally-entangled primal (one-sided) bound.
import SKEFTHawking.QuantumNetwork.DiamondNormChoi
-- Phase 6AF-10 (2026-06-02): Fuchs–van de Graaf UPPER bound (Helstrom + classical-FvdG foundation).
import SKEFTHawking.QuantumNetwork.FidelityUpperBound
-- Phase 6AF-10 (2026-06-02): Schatten-2 Cauchy–Schwarz (traceNorm(A·B) ≤ ‖A‖_F·‖B‖_F).
import SKEFTHawking.QuantumNetwork.TraceNormCauchySchwarz
-- Phase 6AF-11 (2026-06-02): diamond-norm Choi operator-norm UPPER bound (Watrous sandwich).
import SKEFTHawking.QuantumNetwork.DiamondNormChoiUpper
-- Phase 6AG (2026-06-02): operational QN layer — general-state network data-processing monotonicity.
import SKEFTHawking.QuantumNetwork.GeneralStateNetwork
-- Phase 6AG (2026-06-02): named single-qubit noise channels (depolarizing/dephasing/amp-damp).
import SKEFTHawking.QuantumNetwork.NamedChannels
-- Phase 6AG (2026-06-02): fidelity ↔ diamond-distance bridges (Fuchs–van de Graaf ∘ diamond LUB).
import SKEFTHawking.QuantumNetwork.GateFidelityBridge
-- Phase 6AG (2026-06-02): Watrous weak-dual upper bound on the diamond distance (tight, Ask 2).
import SKEFTHawking.QuantumNetwork.DiamondNormDual
-- Phase 6AG (2026-06-02): exact named-channel diamond distance via the optimal dual witness.
import SKEFTHawking.QuantumNetwork.NamedChannelDiamondExact
-- Phase 6AG (2026-06-02): standard Gaussian moments — foundation for the Haar-twirl avg-gate-fidelity.
import SKEFTHawking.QuantumNetwork.GaussianMoments
import SKEFTHawking.QuantumNetwork.GaussianWick
import SKEFTHawking.QuantumNetwork.GaussianPolar
import SKEFTHawking.QuantumNetwork.GaussianSphere
import SKEFTHawking.QuantumNetwork.GaussianComplexMoment
import SKEFTHawking.QuantumNetwork.GaussianComplexTensor
import SKEFTHawking.QuantumNetwork.GateFidelity
import SKEFTHawking.QuantumNetwork.PauliChannel
import SKEFTHawking.QuantumNetwork.RBCertificate
import SKEFTHawking.QuantumNetwork.DiamondBudget
import SKEFTHawking.QuantumNetwork.DiamondNormWitness
import SKEFTHawking.QuantumNetwork.FidelityDataProcessing
import SKEFTHawking.QuantumNetwork.FidelityBlockForm
import SKEFTHawking.QuantumNetwork.OpNormHolder
import SKEFTHawking.QuantumNetwork.FidelityForwardBound
import SKEFTHawking.QuantumNetwork.FidelityForwardBoundPSD
import SKEFTHawking.QuantumNetwork.FidelityAttainmentPSD
import SKEFTHawking.QuantumNetwork.FidelityKrausDP
import SKEFTHawking.QuantumNetwork.SelfAdjointInnerProduct
import SKEFTHawking.QuantumNetwork.HermitianCarrier
import SKEFTHawking.QuantumNetwork.DiamondSDPCone
import SKEFTHawking.QuantumNetwork.DiamondSDP
import SKEFTHawking.QuantumNetwork.DiamondSDPAttainment
import SKEFTHawking.QuantumNetwork.DiamondSDPDuality
-- Phase 6AK Wave 6AK.1 (2026-06-03): coherence-limited average-gate-fidelity ceiling.
import SKEFTHawking.QuantumNetwork.CoherenceFidelity
-- Phase 6AN Wave 3 (2026-06-08): composed coherence ⊕ control gate error budget (diamond + fidelity).
import SKEFTHawking.QuantumNetwork.ComposedGateFidelity
-- Phase 6AN Wave 2 (2026-06-08): multipath network capacity (flow/cut weak duality + path bottleneck).
import SKEFTHawking.QuantumNetwork.NetworkCapacity
-- Phase 6AN Wave 2 strengthening (2026-06-08): MFMC strong-duality progress — max-flow attained
-- (compactness) + conditional strong duality (reduces full MFMC to the augmenting-path lemma).
import SKEFTHawking.QuantumNetwork.NetworkCapacityStrongDuality
-- Phase 6AN Wave 4 (2026-06-08): FDT (Johnson–Nyquist) noise floor + LDP rare-event tail (devices).
import SKEFTHawking.QuantumNetwork.FDTNoiseFloor
-- Phase 6AM W4 (2026-06-09): quantum (Callen–Welton) coth floor — QHO CanonicalEnsemble meanEnergy from PhysLib.
import SKEFTHawking.QuantumNetwork.QuantumFDTFloor
-- Phase 6AK Wave 6AK.3 (2026-06-03): unitary-error-basis exact diamond distance (two-qubit Pauli).
import SKEFTHawking.QuantumNetwork.ErrorBasisDiamond
-- Phase 6AK Wave 6AK.6 (2026-06-03): SPAM bit-flip diamond distance + process fidelity.
import SKEFTHawking.QuantumNetwork.SpamProcessFidelity
-- Phase 6AK Wave 6AK.5 (2026-06-03): code-distance error-suppression / threshold theorem (abstract QEC).
import SKEFTHawking.QuantumNetwork.QECSuppression
-- Phase 6AK Wave 6AK.2 (2026-06-03): repeaterless (PLOB) rate-bound function + loss-penalty properties.
import SKEFTHawking.QuantumNetwork.PLOBRateBound
-- Phase 6AK Wave 6AK.4 (2026-06-03): generalized (thermal) amplitude-damping two-sided diamond bracket.
import SKEFTHawking.QuantumNetwork.GeneralizedAmpDamp
-- Phase 6AK Wave FU-1 (2026-06-03): qutrit Weyl–Heisenberg leakage channel exact diamond distance
-- (n = 3 instance of the unitary-error-basis theorem).
import SKEFTHawking.QuantumNetwork.QutritWeyl
-- Phase 6AK Wave FU-2 (2026-06-03): two-qubit Bell-diagonal negativity + PPT criterion
-- (partial transpose on the Bell-block substrate; Werner threshold at F = ½).
import SKEFTHawking.QuantumNetwork.BellNegativity
-- Phase 6AK Wave FU-3 (2026-06-04): negativity is an entanglement monotone under local operations
-- (partial transpose commutes with a local channel; trace-norm contractivity) + one-shot no-go.
import SKEFTHawking.QuantumNetwork.NegativityMonotone
-- Phase 6AK Wave FU-4 (2026-06-04): log-negativity + trace-norm multiplicativity under Kronecker
-- (E_N = log₂‖ρ^Γ‖₁ additive; the reusable ‖A⊗B‖₁ = ‖A‖₁·‖B‖₁ brick).
import SKEFTHawking.QuantumNetwork.LogNegativity
-- Phase 6AK Wave FU-5 (2026-06-04): negativity is 2-Lipschitz in trace distance
-- (partial transpose is trace-norm-bounded: ‖X^Γ‖₁ ≤ 2‖X‖₁ via Frobenius preservation).
import SKEFTHawking.QuantumNetwork.NegativityContinuity
-- Phase 6AK Wave FU-6 substrate (2026-06-04): general-dimensional partial transpose on Fin dA × Fin dB
-- (‖ρ^Γ‖_F preserved, ‖ρ^Γ‖₁ ≤ √(dA·dB)·‖ρ‖₁) — foundation for the n-copy rate + Choi-state bounds.
import SKEFTHawking.QuantumNetwork.PartialTransposeGeneral
-- Phase 6AK Wave FU-6 brick 1 (2026-06-04): negativity monotone under local ops, general bipartite dim
-- (ptB commutes with a local A-channel; trace-norm contractivity) — generalizes FU-3.
import SKEFTHawking.QuantumNetwork.NegativityMonotoneGeneral
-- Phase 6AK Wave FU-6 brick 2 (2026-06-04): log-negativity at general bipartite dim — monotone + additive
-- (logNegB monotone under local ops, logNegB_add over tensor products).
import SKEFTHawking.QuantumNetwork.LogNegativityGeneral
-- Phase 6AK Wave FU-6 brick 3 (2026-06-04): Kronecker power A^⊗n + n-fold log-negativity additivity
-- (traceNorm_kronPow ‖A^⊗n‖₁=‖A‖₁ⁿ; logNegB_kronPow E_N(ρ^⊗n)=n·E_N(ρ)) — the n-copy step of E_D ≤ E_N.
import SKEFTHawking.QuantumNetwork.KroneckerPower
-- Phase 6AK Wave FU-6 brick 4 (2026-06-04): log-negativity of the maximally entangled state
-- (swapMat SWAP permutation, |SWAP|=1 ⟹ ‖SWAP‖₁=d²; logNegB_maxEntState E_N(Φ_d)=log₂d) — distillation target.
import SKEFTHawking.QuantumNetwork.MaxEntNegativity
-- Phase 6AK Wave FU-6 brick 5 (2026-06-04): single-copy distillation rate bound
-- (distillation_single_copy_bound: local op → Φ_k ⟹ log₂k ≤ E_N(ρ); brick-1 monotone ∘ brick-4 target).
import SKEFTHawking.QuantumNetwork.DistillationRateBound
-- Phase 6AK Wave FU-6 brick 6b (2026-06-04): regularized n-copy distillation rate bound
-- (ncopy grouped n-copy on KronIdx parties; logNegB_ncopy E_N(ρ^⊗n)=n·E_N(ρ) on the ACTUAL grouped
--  state; logNegB_ncopy_localKraus_le E_N(Λ(ρ^⊗n))≤n·E_N(ρ) — the regularized E_D ≤ E_N rate).
import SKEFTHawking.QuantumNetwork.NCopyRateBound
-- Phase 6AK Wave FU-8 (2026-06-04): von Neumann entropy S(ρ)=∑negMulLog(λᵢ) (eigenvalue sum, no matrix log)
-- with 0 ≤ S(ρ) ≤ log(dim) (nonnegativity + max-entropy bound via negMulLog concavity).
import SKEFTHawking.QuantumNetwork.VonNeumannEntropy
-- Phase 6AK Wave FU-8 (2026-06-04): matrix log (cfc Real.log), Re tr(ρ log ρ)=−S(ρ) bridge,
-- and the quantum relative entropy S(ρ‖σ) = Re tr(ρ(log ρ − log σ)) with S(ρ‖ρ)=0.
import SKEFTHawking.QuantumNetwork.QuantumRelativeEntropy
-- Phase 6AK Wave FU-7 (2026-06-04): Pauli-channel entanglement-generating capacity — the normalised
-- Choi state ½J(Φ_p)=bellDiagState p, its negativity/log-negativity closed form, dephasing instance ½|2γ−1|.
import SKEFTHawking.QuantumNetwork.PauliChoiNegativity
-- Phase 6AK Wave FU-8 (2026-06-04): eigenvalues of a Kronecker product = products {λᵢμⱼ} (missing
-- Mathlib infra, via charpoly matching) ⟹ von Neumann entropy additivity S(ρ⊗σ)=S(ρ)+S(σ).
import SKEFTHawking.QuantumNetwork.KroneckerEntropy
-- Phase 6AK Wave FU-8 (2026-06-04): Klein's inequality S(ρ‖σ)≥0 (quantum relative-entropy
-- nonnegativity) via two-eigenbasis spectral expansion + doubly-stochastic overlap + Jensen + Gibbs.
import SKEFTHawking.QuantumNetwork.QuantumKlein
-- Phase 6AL Wave 1 (2026-06-04): concavity of von Neumann entropy S(∑pᵢρᵢ)≥∑pᵢS(ρᵢ) (A)
-- and the Gibbs variational principle / free-energy bound (D) — both Klein corollaries.
import SKEFTHawking.QuantumNetwork.EntropyConcavity
import SKEFTHawking.QuantumNetwork.GibbsVariational
-- Phase 6AL Wave 2 (2026-06-04): negativity convexity N(∑pᵢρᵢ)≤∑pᵢN(ρᵢ) (B) + general-density
-- strengthening (E): ‖A‖₁≥|tr A|, general negativity≥0, logNegativity_add without the ≠0 side-condition.
import SKEFTHawking.QuantumNetwork.NegativityGeneral
-- Phase 6AL Wave 3 (2026-06-04): subadditivity S(ρ_AB)≤S(ρ_A)+S(ρ_B) + mutual information I(A:B)≥0 (C),
-- via the operator-log tensor identity log(ρ_A⊗ρ_B)=log ρ_A⊗1+1⊗log ρ_B (cfc_diagonal built here,
-- cfc_kronecker absent from Mathlib) + Klein's inequality on the product reference.
import SKEFTHawking.QuantumNetwork.EntropySubadditivity
-- Phase 6AL Wave 4 (2026-06-04): spectral-majorization infrastructure toward Fannes–Audenaert
-- continuity (F). `sum_mul_le_sum_top` — the rearrangement/fractional-knapsack inequality
-- (∑μᵢpᵢ ≤ ∑_{i<k}μᵢ for antitone μ, weights pᵢ∈[0,1] summing to k), heart of the Ky Fan maximum
-- principle. Mathlib has no Ky Fan/Lidskii/Mirsky/majorization machinery — built from scratch.
import SKEFTHawking.QuantumNetwork.SpectralMajorization
-- Phase 6AL Wave 4 (2026-06-04): Fannes–Audenaert assembly module. So far the trace-norm ↔ sorted-
-- eigenvalue bridge ‖A‖₁ = ∑ₖ|λ↓ₖ(A)|. Mirsky ℓ¹ + classical FA remain (Phase6AL roadmap Wave-4).
import SKEFTHawking.QuantumNetwork.FannesAudenaert
-- Phase 6AL Wave 4 (2026-06-04): Mirsky UNCONDITIONAL (no hB3/Wielandt). mirsky_unconditional —
-- ∑ₖ|λ↓ₖ(A)−λ↓ₖ(B)| ≤ ‖A−B‖₁ via Weyl monotonicity + positive/negative-part split; discharges hMirsky,
-- making quantum_fannes_audenaert (trace-distance form) rest only on the separate classical-Audenaert residual.
import SKEFTHawking.QuantumNetwork.MirskyUnconditional
-- Phase 6AM Wave 6 (2026-06-09): sharp Fannes–Audenaert log(d−1) — discharges hAud. sharp_fannes_classical
-- (|H(p)−H(q)| ≤ qaryEntropy d T via the maximal coupling + per-column spreading + binEntropy-concavity)
-- and quantum_fannes_audenaert_sharp (FULLY UNCONDITIONAL trace-distance bound for density operators:
-- |S(ρ)−S(σ)| ≤ qaryEntropy d (½‖ρ−σ‖₁), no hB3, no hAud residual). Closes Phase 6AL Gap 1.
import SKEFTHawking.QuantumNetwork.SharpFannesAudenaert
-- Phase 6AL Wave 4 (2026-06-04): toward Lidskii–Wielandt. diag_conj_eq_sum_normSq — the diagonal of a
-- Hermitian conjugated into another eigenbasis is a doubly-stochastic combination of its eigenvalues
-- (∑ⱼ|Mᵢⱼ|²λⱼ); the operator core of the sorted-difference majorization (the sole remaining Mirsky brick).
import SKEFTHawking.QuantumNetwork.LidskiiWielandt
-- Phase 6AL Wave 4 (2026-06-04): vector-majorization layer (route (b) Lidskii-via-Schur–Horn).
-- subset_sum_le_sorted_prefix — subset sum ≤ sum of the |S| largest entries (sortDesc); foundational
-- for weak majorization. Mathlib lacks the majorization predicate (Birkhoff.lean TODO).
import SKEFTHawking.QuantumNetwork.VectorMajorization
-- Phase 6AL Wave 4 (2026-06-04): Wielandt min-max toward arbitrary-index Lidskii (F1b core ∃P).
-- exists_mem_inf_ne_zero — subspace-intersection dim lemma (two subspaces summing past ambient dim
-- meet nonzero); the counting step of Courant–Fischer min-max + the Wielandt frame construction.
import SKEFTHawking.QuantumNetwork.WielandtLidskii
-- Phase 6v Wave 6v.8 (2026-05-26): NbRe noncentrosymmetric triplet
-- superconductor substrate (Colangelo et al. PRL 135, 226002 (2025)).
-- DIII-class topological-superconductor predicate + substantive contrast
-- against elemental-Nb canonical s-wave singlet baseline. Cross-bridge to
-- D2 SPT classification + D4 topological-qubit substrate. Lifts into
-- D2 + D4 (NOT D6).
--
-- Sub-wave 8.C (2026-05-26): the original tracked Prop
-- `H_NbReWindingNumberIdentity` is now **substantively discharged**
-- via the Fu–Kane / Sato–Fujimoto TRIM-product Pfaffian Z₂ invariant
-- (Pathway A per the 2026-05-26 decomposition-pathways DR dossier).
-- Body strengthened from `True` to `fuKaneInvariant sc = -1` for any
-- DIII-topological `sc`, with proof
-- `H_NbReWindingNumberIdentity_holds` kernel-only. Project-local
-- axiom count UNCHANGED at 0.
import SKEFTHawking.NbReTripletSPT
-- Phase 6v Sub-wave 8.D (2026-05-26 PM): general project-local Pfaffian
-- substrate in Mathlib-style namespace. `Matrix.IsSkewSymmetric`
-- predicate + `Matrix.pfaffianFin4` 4×4 closed form + algebraic
-- properties. Upstreamable to Mathlib at a later date per project's
-- typical vendoring-before-upstreaming posture. The 4×4 closed form
-- is what the NbRe Sub-wave 8.C discharge uses; the general
-- `Matrix.pfaffian` for arbitrary `Fin (2*n)` is documented as a
-- follow-up requiring the combinatorial perfect-matching
-- infrastructure not currently in Mathlib.
import SKEFTHawking.MathlibAux.Pfaffian
-- Phase 6v Sub-wave 8.E (2026-05-26 PM): Hamiltonian bridge — closes
-- the "encoded vs derived" gap from the Sub-wave 8.C adversarial
-- review. Defines a concrete 4×4 BdG Hamiltonian `H_BdG_NbRe_at_gamma`
-- consuming `SCParameters`, the TRS involution `Θ = iσ_y ⊗ σ_0` with
-- algebraic properties (`Θᵀ = -Θ`, `Θ² = -I`), and the canonical
-- TR-conjugated sewing matrix `Θ · H · Θ`. The (0,2) entry of the
-- derived sewing matrix evaluates to `-1` for NbRe and `+1` for Nb,
-- structurally consistent with the substrate-level `sewingCoeffsAt`
-- `f`-coefficient sign. Zero new project-local axioms.
import SKEFTHawking.BdGHamiltonianNbRe
-- Phase 6v Sub-wave 8.F (2026-05-26 PM): Z₁₆ Rokhlin cross-bridge.
-- Lifts the documentation-only Phase-6r-Pin⁺/ℤ₁₆ connection in
-- `NbReTripletSPT.lean §6` to a Lean theorem-level map. Defines
-- `diiiBdGToZ16 : SCParameters → ZMod 16`; ships theorems
-- `nbRe_diiiBdGToZ16 = 1`, `elementalNb_diiiBdGToZ16 = 0`, and
-- the bridge `diiiBdGToOmega4PinPlus` via Phase 6r-prime W1.2's
-- substantive `omega4PinPlusBordismEquivZMod16` iso. Unifies NbRe's
-- Pfaffian-Z₂ substrate (Sub-waves 8.C / 8.E) with the project's
-- existing ~9,910 LoC Phase 6r Pin⁺/ℤ₁₆ infrastructure.
import SKEFTHawking.CrossBridges.NbReDIIIToPinPlusZ16
-- Phase 6v Sub-wave 8.G (2026-05-26 PM): 3D winding-number formal
-- connection. Closes the original Sub-wave 8.C spec gap (the wave was
-- named "3D winding-number identity"). Defines `windingNumber :
-- SCParameters → ℤ` as the substrate-level integer 3D winding number
-- (Schnyder-Ryu-Furusaki-Ludwig PRB 78, 195125 (2008)); ships the
-- canonical Pfaffian-Z₂ ↔ integer-winding-mod-2 reduction theorem
-- (Sato-Fujimoto PRB 79, 094504 (2009)). NbRe winding = -1
-- (DIII-topological); Nb winding = 0 (DIII-trivial); parity
-- correspondence `(1 - fuKane)/2 = winding mod 2` shipped at both
-- material instances.
import SKEFTHawking.NbReWindingNumber
-- Phase 6v Sub-wave 8.H (2026-05-26 PM): TRIM parameterization polish.
-- Closes ADV-1 hardcoded `Fin 4` scope-limitation from the Sub-wave
-- 8.C adversarial review. Ships `genericFuKaneInvariant` over any
-- `[Fintype T]` TRIM enumeration; hexagonal-Fin-4 case recovers the
-- existing NbReTripletSPT.lean §7.D `fuKaneInvariant`; orthorhombic
-- Fin-8 case ships substantive non-vacuity witnesses (topological → -1,
-- trivial → +1). Demonstrates the substrate generalizes cleanly to
-- orthorhombic NbReSi/Ima2 variants without structural redesign.
-- Additive (non-breaking) ship — does not modify existing hexagonal
-- substrate.
import SKEFTHawking.TRIMParameterization
-- Phase 6v Sub-waves 8.D-8.H cumulative substantive closure (2026-05-26 PM):
-- single aggregated witness for the architectural coherence of the
-- strengthening pass. Per ADV-3 of the final adversarial review,
-- visible at the Lean theorem level.
import SKEFTHawking.Phase6vSubwaves8DHClose

-- Phase 6v Wave 6v.9 cumulative substantive-closure theorem aggregating
-- sub-waves 9.A-9.E (post 2026-05-26 PM unfinished-business audit
-- finish-strengthening pass).
import SKEFTHawking.Phase6vWave9Close

-- Phase 6w Wave 6w.1 foundation: Kibble-Zurek-Unruh correspondence between
-- the SK-EFT surface gravity kappa and the KZM defect-density scaling
-- exponent (Tindall, Mello, Fishman, Stoudenmire, Sels, Science 392, 868
-- (2026), DOI 10.1126/science.adx2728; arXiv:2503.05693). Headline:
-- surface_gravity_bounds_kzm_exponent.
import SKEFTHawking.KibbleZurekUnruh

-- Phase 6w Wave 6w.2 Mathlib-PR-quality substrate: belief propagation on
-- factor graphs (Yedidia-Freeman-Weiss 2003). FactorGraph + BPMessages
-- + bpVariableUpdate + bpFactorUpdate + bpUpdate + IsBPFixedPoint;
-- substantive theorems for normalization, positivity propagation,
-- factorization, fixed-point stability. Consumed by Wave 6w.3 LDP-
-- controlled simulability headline.
import SKEFTHawking.BeliefPropagation

-- Phase 6w Wave 6w.3 LDP-controlled classical-simulability headline
-- (A1a follow-up; review-2026-06-05 D7-EV3 continuous-rate upgrade).
-- fourCycles + loopDensity + bernoulliLoopMgf + loopCorrectionRate
-- (Cramér/Legendre transform of the Bernoulli loop-presence log-MGF at
-- zero deviation; closed form -log(1-p) proven via IsLUB) +
-- bernoulliCramerRate KL bridge to SKEFTHawking.LDP.IsCramerIIDUpperBound +
-- IsBPConvergenceFavorable + HEADLINE bp_convergence_iff_ldp_rate_zero.
-- Substantive biconditional combining BP-on-TN substrate (Wave 6w.2) with
-- the loop-correction rate-function characterization (Tindall-Sels
-- Science 392, 868 (2026) classical-simulation regime).
import SKEFTHawking.BPLDPSimulability

-- Phase 6w Wave 6w.4 substrate (Antão-Sun-Fumega-Lado, PRL 136, 156601
-- (2026); DOI 10.1103/hhdf-xpwg; arXiv:2506.05230). First-kind Chebyshev
-- polynomials with canonical recurrence + truncated expansion + boundary-
-- value identities (T_n(1)=1, T_n(-1)=(-1)^n, etc.); aperiodic-lattice
-- predicate substrate (Lattice2D + IsPeriodic2D + IsAperiodic2D +
-- IsTranslationInvariant + boundary cases). Consumed by Wave 6w.5
-- categorical-Chern ↔ real-space-Chern bridge.
import SKEFTHawking.ChebyshevTN
import SKEFTHawking.AperiodicLattice

-- Phase 6w Wave 6w.5 categorical-Chern ↔ real-space-Chern bridge (A1b).
-- categoricalChernExpansion + realSpaceChernAt + two distinct headline
-- theorems for crystalline (band-edge x=1: c0 + c1) and quasicrystalline
-- (band-edge x=-1: c0 - c1) limits + substantive 2c1 difference identity.
import SKEFTHawking.ChernBridge

-- Phase 6w Wave 6w.6 combined classical-simulability demarcation (A1c).
-- HEADLINE analog_hawking_quantum_advantage_demarcation biconditional
-- combining Wave 6w.3 BP-LDP simulability with Wave 6w.5 Chern bridge:
-- a system is classically simulable iff BP-LDP-favorable AND c_1 = 0.
-- Contrapositive yields quantum-advantage regime explicitly. D7
-- spin-out decision deferred to user authorization (default: NO,
-- absorb into D1 + E1 + E2 via Wave 6w.7).
import SKEFTHawking.AnalogHawkingDemarcation
-- Phase 6AP (2026-06-10): QuantumNetwork substrate completions — textbook-math
-- origination + the diamond AKN chain. W1 general exp-enclosure landed in-place in
-- NumericalBounds (already imported). W2 Kronecker-with-identity opnorm bound; W3 the
-- unitary opnorm→diamond AKN bound + trace-norm Hölder transfer from PhysLib (with the
-- global-phase non-sharpness caveat AS a theorem); W3b row-sum→L2-opnorm bridge + the
-- END-TO-END compiled-gate diamond certificate diamondDist_cliffordTCompile_le
-- (compiler contract → row sums → norm bridge → AKN, every link kernel-checked);
-- W4 erasure two-way rate-bound formula (two-layer posture mirroring PLOBRateBound).
import SKEFTHawking.QuantumNetwork.KroneckerOpNorm
import SKEFTHawking.QuantumNetwork.UnitaryDiamond
import SKEFTHawking.QuantumNetwork.MatrixNormBridge
import SKEFTHawking.QuantumNetwork.ErasureRateBound
import SKEFTHawking.FKLW.CompiledGateDiamond
-- Phase 6AQ (2026-06-10): device-characterization envelope completion — readout-window
-- bounds from the same universally-stated coherence/thermal parameters that bound gates.
-- W1 readout-window relaxation envelope: p_decay = 1 − e^{−t/T₁} (range/strict-mono/antitone/
-- endpoints incl. Tendsto-to-1, rational enclosure via expNeg_enclosure, averaged-assignment
-- floor with uniform-prior prefactor ½; identification with device assignment error stays
-- literature-cited, two-layer posture). W2 thermal-population assignment floor: p_th =
-- 1/(1+e^{βℏω}) DERIVED from PhysLib CanonicalEnsemble.twoState (tanh↔logistic bridge),
-- StrictAnti + Temperature/frequency-indexed monotonicity via the Temperature.β bridge,
-- endpoints (T→0⁺ ⇒ 0; high-T ⇒ ½), rational enclosures, combined max-floor capstone.
import SKEFTHawking.QuantumNetwork.ReadoutRelaxationBound
import SKEFTHawking.QuantumNetwork.ThermalAssignmentFloor

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
