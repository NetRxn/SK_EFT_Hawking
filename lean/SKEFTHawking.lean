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
-- (A1a follow-up). loopCorrectionRate + ldpSimulabilityThreshold +
-- IsBPConvergenceFavorable + HEADLINE bp_convergence_iff_ldp_below_threshold.
-- Substantive biconditional combining BP-on-TN substrate (Wave 6w.2) with
-- LDP rate function characterization (Tindall-Sels Science 392, 868
-- (2026) classical-simulation regime).
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
