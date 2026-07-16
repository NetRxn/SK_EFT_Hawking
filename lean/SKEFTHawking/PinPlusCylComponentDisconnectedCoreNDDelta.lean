import Mathlib
import SKEFTHawking.PinPlusCylComponentDisconnectedCoreND
import SKEFTHawking.PinPlusCylDataDischargeWuLeafSuspDelta

/-!
# Phase 5q.H close-out — THE DISCONNECTED TWINS from the class identity (δ-route, connectedness-free)

The disconnected residual `disconnectedCylCoreND_of_named` (`PinPlusCylComponentDisconnectedCoreND`)
threads three named leaves against the k-component datum `discD`:
`DiscCylV1Desuspend`, `DiscCylV2Desuspend`, and `DisconnectedCylSuspIntertwineData`. This module
discharges all three from ONE linchpin — the class identity

  `hcls : discD.cls = cylFundClassCandidate M = crossH [M]`   (the k-component `[W,∂W] = [M] × [I,∂I]`)

— by MIRRORING the connected δ-route (`PinPlusCylDataDischargeWuLeafSuspDelta`) and the connected
cap-cross Fubini (`…CylinderSuspDual`/`…CylinderCapCrossProj`) VERBATIM, all of whose lemmas are
connectedness-free (they reference the datum only through its `.mu`, and `fundamentalFunctional`/
`fundamentalClass`/`cylCrossH_bijective`/`rhsReduce`/`wu_relation`/`prismProjKillsHomology_holds` carry
no `[PreconnectedSpace]`). The single connectedness entry — the datum-class identification
`cylinderDatum_mu_eq_funct` — is replaced by the hypothesis `hcls`, whose disconnected discharge (the
per-component crossHloc transport) is the sole remaining crux.

With all three leaves supplied from `hcls`, `disconnectedCylCoreND_of_named` fires and
`nonempty_provider_of_disconnectedCoreND` yields the provider from `hcls` alone
(`nonempty_provider_of_disconnectedClsIdent`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open scoped Manifold
open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeCohomDelta
open SKEFTHawking.SingularBockstein SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.SingularClosedHomologyFinite
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.PoincareDualityWu
open SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspDual
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspBij
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapProj
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapCrossProj
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapPrism
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNondeg
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine
open SKEFTHawking.SingularNormalizationPInfty
open SKEFTHawking.PinPlusCylDataDischargeDisconnected
open SKEFTHawking.PinPlusCylDataDischargeDisconnectedComponents
open SKEFTHawking.PinPlusCylComponentExcisionBridgeFinite
open SKEFTHawking.PinPlusCylDataDischargeWuLeaf
open SKEFTHawking.PinPlusCylDataDischargeWuLeafSusp
open SKEFTHawking.PinPlusCylDataDischargeWuLeafSuspDelta
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusCylComponentDisconnectedCoreND

namespace SKEFTHawking.PinPlusCylComponentDisconnectedCoreNDDelta

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [T1Space (cylW M)]

/-! ## §1. The linchpin functional form and `discD.mu` on δ-images. -/

/-- **The disconnected datum functional as the explicit pairing against `[M] × [I,∂I]`.** From the
class identity `hcls`, `discD.mu = ⟨·, crossH [M]⟩` — the disconnected twin of `cylinderDatum_mu_eq_funct`
(the `Classical.choose` opacity of `discD.cls` collapsed to the explicit product candidate). -/
theorem disc_mu_eq_funct (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2)) :
    (discD (M := M)).mu = relFundFunctional (cylBdW (M := M)) (cylFundClassCandidate (M := M) (m' := 2)) :=
  congrArg (relFundFunctional (cylBdW (M := M))) hcls

/-- **`discD.mu` on δ-images** — the disconnected twin of `cylinderDatum_mu_deltaRelH`, connectedness-free
via the class identity `hcls`: `μ_W [δy] = ⟨[e₁* y], [M]⟩ + ⟨[e₀* y], [M]⟩`, the end evaluation at
`x := [M]` through `[W,∂W] = crossH [M]`. -/
theorem disc_mu_deltaRelH (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2))
    (y : SingularCochain (cyl (TopCat.of M)) 4)
    (h : coboundaryₗ (cyl (TopCat.of M)) 4 y ∈ relCochains (cylBd (M := M)) 5) :
    (discD (M := M)).mu (deltaRelH y h)
      = fundamentalFunctional (m := 2) (M := M)
          (endClass 1 (slice_one_mapsTo (M := M) (m' := 2)) y h)
        + fundamentalFunctional (m := 2) (M := M)
            (endClass 0 (slice_zero_mapsTo (M := M) (m' := 2)) y h) := by
  rw [disc_mu_eq_funct hcls]
  show relKroneckerH (cylBdW (M := M)) (deltaRelH y h) (cylFundClassCandidate (M := M) (m' := 2)) = _
  rw [cylFundClassCandidate_eq_cylCrossH]
  exact relKroneckerH_deltaRelH_crossH 3 y h (fundamentalClass (m := 2) (M := M))

/-! ## §2. The disconnected Sq-suspension stability atoms (δ-route, from `hcls`). -/

/-- **`disc_cyl_sqSusp23`** — the disconnected twin of `cyl_sqSusp23`: `μ_W(relSq² b) = ⟨(β b)², [M]⟩`
against the k-component datum `discD`, via the δ-image calculus and the class identity `hcls`. -/
theorem disc_cyl_sqSusp23 (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2))
    (hbij : Function.Bijective (cylCrossH (M := M) 1))
    (b : RelativeCohomology (cylBd (M := M)) 3) :
    (discD (M := M)).mu (relSq2 (S := cylBd (M := M)) b)
      = fundamentalFunctional (m := 2) (M := M) (cupSquare2 (cylBeta (M := M) 1 hbij b)) := by
  obtain ⟨z, h, rfl⟩ := exists_deltaRelH_of_relToAbs_eq_zero b
    (relToAbs_eq_zero_of_cyl (M := M) (n := 2) b)
  rw [relSq2_deltaRelH z h]
  refine (disc_mu_deltaRelH hcls (cup z z) (coboundary_cup_self_mem_relCochains z h)).trans ?_
  rw [cylBeta_deltaRelH₂ hbij z h, cupSquare2_add, map_add, endClass_cup_self, endClass_cup_self]

/-- **`disc_cyl_sqSusp14`** — the disconnected twin of `cyl_sqSusp14`: `μ_W(relSq¹ b) = ⟨Sq¹(β b), [M]⟩`
against `discD`. -/
theorem disc_cyl_sqSusp14 (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2))
    (hbij : Function.Bijective (cylCrossH (M := M) 2))
    (b : RelativeCohomology (cylBd (M := M)) 4) :
    (discD (M := M)).mu (relSq1 (S := cylBd (M := M)) (n := 3) b)
      = fundamentalFunctional (m := 2) (M := M) (Sq1 (n := 2) (cylBeta (M := M) 2 hbij b)) := by
  obtain ⟨z, h, rfl⟩ := exists_deltaRelH_of_relToAbs_eq_zero b
    (relToAbs_eq_zero_of_cyl (M := M) (n := 3) b)
  rw [relSq1_deltaRelH_three z h]
  refine (disc_mu_deltaRelH hcls (sq1Defect z) (coboundary_sq1Defect_mem_relCochains z h)).trans ?_
  rw [cylBeta_deltaRelH₃ hbij z h, map_add, map_add, endClass_sq1Defect, endClass_sq1Defect]

/-! ## §2b. `discD.mu` on relative cups (the explicit pairing) and the cap-cross `hproj` values. -/

/-- **`discD.mu` on a `(2,3)` cup** — the explicit relative-Kronecker pairing against `[M] × [I,∂I]`
(disconnected twin of `cylinderDatum_mu_relCup23`), from `hcls`. -/
theorem disc_mu_relCup23 (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2))
    (a : Cohomology (TopCat.of (cylW M)) 2)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) :
    (discD (M := M)).mu (relCupH23 a b)
      = relKroneckerH (cylBdW (M := M)) (relCupH23 a b) (cylFundClassCandidate (M := M) (m' := 2)) := by
  rw [disc_mu_eq_funct hcls]; rfl

/-- **`discD.mu` on a `(1,4)` cup** — the `(1,4)` mirror. -/
theorem disc_mu_relCup14 (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2))
    (a : Cohomology (TopCat.of (cylW M)) 1)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) :
    (discD (M := M)).mu (relCupH14 a b)
      = relKroneckerH (cylBdW (M := M)) (relCupH14 a b) (cylFundClassCandidate (M := M) (m' := 2)) := by
  rw [disc_mu_eq_funct hcls]; rfl

/-- **The `(2,3)` cap-cross `hproj` value against `discD`** — the disconnected twin of `hproj23`, the
explicit cap-cross projection residual supplied internally from `prismProjKillsHomology_holds`. -/
theorem disc_hproj23 (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2))
    (a : Cohomology (TopCat.of (cylW M)) 2)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) :
    (discD (M := M)).mu (relCupH23 a b)
      = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 1 (capH 2 1 (cylCollapse2 a) (fundamentalClass (m := 2) (M := M)))) :=
  (disc_mu_relCup23 hcls a b).trans
    (capCrossProjPairing23_of_homologyProj a
      (capCrossHomologyProj23_of_pullback a
        (capCrossPullbackProj23_of_kills (prismProjKillsHomology_holds (TopCat.of M))
          (cylCollapse2 a))) b)

/-- **The `(1,4)` cap-cross `hproj` value against `discD`** — the `(1,4)` mirror. -/
theorem disc_hproj14 (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2))
    (a : Cohomology (TopCat.of (cylW M)) 1)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) :
    (discD (M := M)).mu (relCupH14 a b)
      = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 2 (capH 1 2 (cylCollapse1 a) (fundamentalClass (m := 2) (M := M)))) :=
  (disc_mu_relCup14 hcls a b).trans
    (capCrossProjPairing14_of_homologyProj a
      (capCrossHomologyProj14_of_pullback a
        (capCrossPullbackProj14_of_kills (prismProjKillsHomology_holds (TopCat.of M))
          (cylCollapse1 a))) b)

/-! ## §3. The disconnected desuspension leaves from the pairing form. -/

/-- **`DiscCylV2Desuspend` from the pairing form** — the disconnected twin of `CylV2Desuspend_of_pairing`.
The suspension-Fubini identity `⟨(π* v₂M) ∪ b, [W,∂W]⟩ = ⟨relSq² b, [W,∂W]⟩` on `H³(W,∂W)` against `discD`
pins `v₂(W) = π* v₂(M)` (pairing-uniqueness `wuClass_eq_of_pairing`). -/
theorem DiscCylV2Desuspend_of_pairing
    (h : ∀ (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
        (discD (M := M)).mu
            (relCupH23 (cylCollapse2.symm (wuClass2 (poincareDual4Mid_of_closed (M := M)))) b)
          = (discD (M := M)).mu (relSq2 b)) :
    DiscCylV2Desuspend (M := M) := by
  intro nd23
  rw [← LinearEquiv.eq_symm_apply]
  refine wuClass_eq_of_pairing _ _ ?_
  ext b
  exact h b

/-- **`DiscCylV1Desuspend` from the pairing form** — the disconnected twin of `CylV1Desuspend_of_pairing`. -/
theorem DiscCylV1Desuspend_of_pairing
    (h : ∀ (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
        (discD (M := M)).mu
            (relCupH14 (cylCollapse1.symm (wuClass1 (poincareDual4Lo_of_closed (M := M)))) b)
          = (discD (M := M)).mu (relSq1 (n := 3) b)) :
    DiscCylV1Desuspend (M := M) := by
  intro nd14
  rw [← LinearEquiv.eq_symm_apply]
  refine wuClass_eq_of_pairing _ _ ?_
  ext b
  exact h b

/-! ## §4. The two disconnected Wu-desuspension leaves, discharged from `hcls`. -/

/-- **`DiscCylV2Desuspend` HOLDS from `hcls`** — the disconnected `(2,3)` Wu-desuspension leaf. The
`hproj23`/`hbij23` cap-cross inputs are supplied internally (`prismProjKillsHomology_holds` +
`cylCrossH_bijective`); the LHS dissolves via `rhsReduce23` + the base Wu relation `wu_relation`, and the
RHS is the disconnected Sq-suspension atom `disc_cyl_sqSusp23`. -/
theorem DiscCylV2Desuspend_of_clsIdent
    (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2)) :
    DiscCylV2Desuspend (M := M) := by
  have hM2 := (finiteDimensional_homology_of_closed (M := M)).2.1
  have hM3 := (finiteDimensional_homology_of_closed (M := M)).2.2.1
  set hbij := cylCrossH_bijective (M := M) 1 hM2 (cylinder_findimRelHom23_of_base hM3 hM2) with hbij_def
  refine DiscCylV2Desuspend_of_pairing (fun b => ?_)
  calc (discD (M := M)).mu
          (relCupH23 (cylCollapse2.symm (wuClass2 (poincareDual4Mid_of_closed (M := M)))) b)
      = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 1 (capH 2 1
            (cylCollapse2 (cylCollapse2.symm (wuClass2 (poincareDual4Mid_of_closed (M := M)))))
            (fundamentalClass (m := 2) (M := M)))) :=
        disc_hproj23 hcls _ b
    _ = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 1 (capH 2 1 (wuClass2 (poincareDual4Mid_of_closed (M := M)))
            (fundamentalClass (m := 2) (M := M)))) := by
        rw [cylCollapse2.apply_symm_apply]
    _ = fundamentalFunctional (m := 2) (M := M)
          (cupH24 (wuClass2 (poincareDual4Mid_of_closed (M := M))) (cylBeta (M := M) 1 hbij b)) :=
        (rhsReduce23 hbij (wuClass2 (poincareDual4Mid_of_closed (M := M))) b).symm
    _ = fundamentalFunctional (m := 2) (M := M)
          (cupSquare2 (cylBeta (M := M) 1 hbij b)) :=
        wu_relation (poincareDual4Mid_of_closed (M := M)) (cylBeta (M := M) 1 hbij b)
    _ = (discD (M := M)).mu (relSq2 b) := (disc_cyl_sqSusp23 hcls hbij b).symm

/-- **`DiscCylV1Desuspend` HOLDS from `hcls`** — the disconnected `(1,4)` Wu-desuspension leaf; the
`(1,4)` mirror, with `hM4` supplied by `topHomology_finite` (connectedness-free). -/
theorem DiscCylV1Desuspend_of_clsIdent
    (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2)) :
    DiscCylV1Desuspend (M := M) := by
  have hM3 := (finiteDimensional_homology_of_closed (M := M)).2.2.1
  have hM4 := topHomology_finite M
  set hbij := cylCrossH_bijective (M := M) 2 hM3 (cylinder_findimRelHom14_of_base hM4 hM3) with hbij_def
  refine DiscCylV1Desuspend_of_pairing (fun b => ?_)
  calc (discD (M := M)).mu
          (relCupH14 (cylCollapse1.symm (wuClass1 (poincareDual4Lo_of_closed (M := M)))) b)
      = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 2 (capH 1 2
            (cylCollapse1 (cylCollapse1.symm (wuClass1 (poincareDual4Lo_of_closed (M := M)))))
            (fundamentalClass (m := 2) (M := M)))) :=
        disc_hproj14 hcls _ b
    _ = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 2 (capH 1 2 (wuClass1 (poincareDual4Lo_of_closed (M := M)))
            (fundamentalClass (m := 2) (M := M)))) := by
        rw [cylCollapse1.apply_symm_apply]
    _ = fundamentalFunctional (m := 2) (M := M)
          (cupH13 (wuClass1 (poincareDual4Lo_of_closed (M := M))) (cylBeta (M := M) 2 hbij b)) :=
        (rhsReduce14 hbij (wuClass1 (poincareDual4Lo_of_closed (M := M))) b).symm
    _ = fundamentalFunctional (m := 2) (M := M)
          (Sq1 (n := 2) (cylBeta (M := M) 2 hbij b)) :=
        wu_relation_v1 (poincareDual4Lo_of_closed (M := M)) (cylBeta (M := M) 2 hbij b)
    _ = (discD (M := M)).mu (relSq1 (n := 3) b) := (disc_cyl_sqSusp14 hcls hbij b).symm

/-! ## §5. The disconnected cup-suspension intertwining data, discharged from `hcls`. -/

/-- **`DisconnectedCylSuspIntertwineData` from `hcls`** — the disconnected cup-suspension intertwining
(β pinned to `cylBeta`; the two Fubini `hcompat` legs are `disc_hproj{23,14}` composed with the
Fubini-RHS reduction `rhsReduce{23,14}`). This supplies the `nd14`/`nd23` non-degeneracies of the
disconnected core. -/
def disconnectedCylSuspIntertwineData_of_clsIdent
    (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2)) :
    DisconnectedCylSuspIntertwineData M := by
  have hM2 := (finiteDimensional_homology_of_closed (M := M)).2.1
  have hM3 := (finiteDimensional_homology_of_closed (M := M)).2.2.1
  have hM4 := topHomology_finite M
  set hbij23 := cylCrossH_bijective (M := M) 1 hM2 (cylinder_findimRelHom23_of_base hM3 hM2)
    with h23_def
  set hbij14 := cylCrossH_bijective (M := M) 2 hM3 (cylinder_findimRelHom14_of_base hM4 hM3)
    with h14_def
  exact
    { β23 := cylBeta (M := M) 1 hbij23
      hcompat23 := fun a b =>
        (disc_hproj23 hcls a b).trans (rhsReduce23 hbij23 (cylCollapse2 a) b).symm
      β14 := cylBeta (M := M) 2 hbij14
      hcompat14 := fun a b =>
        (disc_hproj14 hcls a b).trans (rhsReduce14 hbij14 (cylCollapse1 a) b).symm }

/-- **The disconnected core from `hcls`** — `disconnectedCylCoreND_of_named` fed the three named leaves,
all now supplied from the single class identity `hcls` + `σ.cert`. -/
def disconnectedCylCoreND_of_clsIdent
    (hcls : (discD (M := M)).cls = cylFundClassCandidate (M := M) (m' := 2))
    (hcert : PoincareDualityWuFormula.wuW2 (poincareDual4Mid_of_closed (M := M))
      (poincareDual4Lo_of_closed (M := M)) = 0) :
    DisconnectedCylCoreND M :=
  disconnectedCylCoreND_of_named (disconnectedCylSuspIntertwineData_of_clsIdent hcls) hcert
    (DiscCylV2Desuspend_of_clsIdent hcls) (DiscCylV1Desuspend_of_clsIdent hcls)

end

/-! ## §6. The provider from the class identity alone. -/

/-- **THE PROVIDER FROM THE CLASS IDENTITY.** With the two connected Wu-leaf atoms already theorems
(`CylV2Desuspend_holds`/`CylV1Desuspend_holds`, `nonempty_provider_of_disconnectedCoreND`), the
char-pair `W`-provider inhabitation reduces to the SINGLE disconnected class identity
`discD.cls = crossH [M]` per disconnected carrier: the three named disconnected leaves
(`DisconnectedCylSuspIntertwineData`, `DiscCylV{1,2}Desuspend`) are all supplied from it via `σ.cert`.
This is the honest sharpened provider row — the disconnected residual collapsed to the one k-component
`[W,∂W] = [M] × [I,∂I]` identity. -/
theorem nonempty_provider_of_disconnectedClsIdent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {k : WithTop ℕ∞} {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
    (hcls : ∀ {s : SingularManifold.{0} PUnit.{1} k I} (_σ : CharPairStrBundled I s)
      [T2Space s.M] [Nonempty s.M] [T1Space (cylW s.M)],
      ¬ PreconnectedSpace s.M →
        (discD (M := s.M)).cls = cylFundClassCandidate (M := s.M) (m' := 2)) :
    Nonempty (CharPairWProviderPerOp I k) := by
  refine nonempty_provider_of_disconnectedCoreND ?_
  intro s σ _ _ hpc
  haveI : T1Space (cylW s.M) := inferInstance
  exact disconnectedCylCoreND_of_clsIdent (hcls σ hpc) σ.cert

end SKEFTHawking.PinPlusCylComponentDisconnectedCoreNDDelta
