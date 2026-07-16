/-
# Phase 5q.H close-out (Lane A2) — the WU LEAF sharpened to the canonical Sq-SUSPENSION STABILITY

`PinPlusCylDataDischargeWuLeaf` reduced the two desuspension atoms `CylV2Desuspend`/`CylV1Desuspend`
to the honest pairing hypotheses (`CylV2Desuspend_of_pairing`,
`μ_W(relCupH23 (π* v₂M) b) = μ_W(relSq2 b)`). This module TIGHTENS those pairing residuals: the
LHS `μ_W(relCupH23 (π* v₂M) b)` is dissolved — through the now-discharged cap-cross **Fubini**
(the prism `PrismProjKillsHomology` route, `hproj23`/`rhsReduce23`) and the base **Wu relation**
(`PoincareDualityWu.wu_relation`, `⟨v₂ ∪ x, [M]⟩ = ⟨x ∪ x, [M]⟩` for `x ∈ H²`) — so the sole
surviving content is the sharp **Sq-suspension stability** identity in the pairing form:

  `(hsusp23)  μ_W(relSq2 b) = ⟨(β b) ∪ (β b), [M]⟩`   (`β = cylBeta`, `β b ∈ H²(M)`)

i.e. the suspension iso `β` intertwines the relative `Sq²` (`= relSq2`, a genuine cup-1 on `H³`)
with the base cup-**square** (`Sq²` on `H²`). Equivalently `crossHDual (relSq2 b) = (β b) ∪ (β b)`
in `H⁴(M)` (the fundamental pairing is an iso on `H⁴` of a connected closed 4-manifold). The `(1,4)`
mirror carries the relative `Sq¹` (`relSq1`) to the base `Sq¹` on `H¹` — `hsusp14`.

This is the honest `#99` residual, cleanly isolated: the cup-i / Eilenberg–Zilber Cartan of the
cross product (`SphereProdCrossInt` slice-6). The prism cap-cross projection discharges the LHS
(one factor is the pullback `π* v₂M`) but structurally CANNOT reach `relSq2 b = cupOne33(b',b')`
(neither factor a pullback), which is exactly what these atoms isolate.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusCylDataDischargeWuLeaf
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspBij
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapPrism
import SKEFTHawking.PoincareDualityWu

open scoped Manifold
open SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PoincareDualityWu
open SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.SingularBockstein
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspDual
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspBij
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapCrossProj
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapProj
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapPrism
open SKEFTHawking.SingularNormalizationPInfty
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PinPlusCylDataDischargeWuLeaf

namespace SKEFTHawking.PinPlusCylDataDischargeWuLeafSusp

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [PreconnectedSpace M] [T1Space (cylW M)]

/-- **The `(2,3)` desuspension atom from the sharp Sq-suspension stability.** With the cap-cross
Fubini value `hproj23` (discharged elsewhere from `PrismProjKillsHomology`) and the pair-suspension
iso witness `hbij23`, the LHS of the pairing atom dissolves via `rhsReduce23` + the base Wu relation,
leaving the sole residual `hsusp23`: `μ_W(relSq2 b) = ⟨(β b) ∪ (β b), [M]⟩`. -/
theorem CylV2Desuspend_of_sqSusp
    (hbij23 : Function.Bijective (cylCrossH (M := M) 1))
    (hproj23 : ∀ (a : Cohomology (TopCat.of (cylW M)) 2)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
            (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = relKroneckerH (cylBd (M := M)) b
              (cylCrossH (M := M) 1 (capH 2 1 (cylCollapse2 a) (fundamentalClass (m := 2) (M := M)))))
    (hsusp23 : ∀ (b : RelativeCohomology (X := TopCat.of (cylW M))
        ((cylModel 2).boundary (cylW M)) 3),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu (relSq2 b)
          = fundamentalFunctional (m := 2) (M := M)
              (cupSquare2 (cylBeta (M := M) 1 hbij23 b))) :
    CylV2Desuspend (M := M) := by
  refine CylV2Desuspend_of_pairing ?_
  intro b
  calc (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
          (relCupH23 (cylCollapse2.symm (wuClass2 (poincareDual4Mid_of_closed (M := M)))) b)
      = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 1 (capH 2 1
            (cylCollapse2 (cylCollapse2.symm (wuClass2 (poincareDual4Mid_of_closed (M := M)))))
            (fundamentalClass (m := 2) (M := M)))) :=
        hproj23 _ b
    _ = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 1 (capH 2 1 (wuClass2 (poincareDual4Mid_of_closed (M := M)))
            (fundamentalClass (m := 2) (M := M)))) := by
        rw [cylCollapse2.apply_symm_apply]
    _ = fundamentalFunctional (m := 2) (M := M)
          (cupH24 (wuClass2 (poincareDual4Mid_of_closed (M := M))) (cylBeta (M := M) 1 hbij23 b)) :=
        (rhsReduce23 hbij23 (wuClass2 (poincareDual4Mid_of_closed (M := M))) b).symm
    _ = fundamentalFunctional (m := 2) (M := M)
          (cupSquare2 (cylBeta (M := M) 1 hbij23 b)) :=
        wu_relation (poincareDual4Mid_of_closed (M := M)) (cylBeta (M := M) 1 hbij23 b)
    _ = (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu (relSq2 b) :=
        (hsusp23 b).symm

/-- **The `(1,4)` desuspension atom from the sharp Sq-suspension stability.** The `(1,4)` mirror of
`CylV2Desuspend_of_sqSusp`: the LHS `μ_W(relCupH14 (π* v₁M) b)` dissolves via `rhsReduce14` + the base
`(1,3)` Wu relation (`wu_relation_v1`, `⟨v₁ ∪ x, [M]⟩ = ⟨Sq¹ x, [M]⟩` for `x ∈ H³`), leaving the sole
residual `hsusp14`: `μ_W(relSq1 b) = ⟨Sq¹ (β b), [M]⟩` (`β b ∈ H³(M)`) — the suspension iso carries the
relative `Sq¹` to the base `Sq¹`. -/
theorem CylV1Desuspend_of_sqSusp
    (hbij14 : Function.Bijective (cylCrossH (M := M) 2))
    (hproj14 : ∀ (a : Cohomology (TopCat.of (cylW M)) 1)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
            (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = relKroneckerH (cylBd (M := M)) b
              (cylCrossH (M := M) 2 (capH 1 2 (cylCollapse1 a) (fundamentalClass (m := 2) (M := M)))))
    (hsusp14 : ∀ (b : RelativeCohomology (X := TopCat.of (cylW M))
        ((cylModel 2).boundary (cylW M)) 4),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu (relSq1 (n := 3) b)
          = fundamentalFunctional (m := 2) (M := M)
              (Sq1 (n := 2) (cylBeta (M := M) 2 hbij14 b))) :
    CylV1Desuspend (M := M) := by
  refine CylV1Desuspend_of_pairing ?_
  intro b
  calc (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
          (relCupH14 (cylCollapse1.symm (wuClass1 (poincareDual4Lo_of_closed (M := M)))) b)
      = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 2 (capH 1 2
            (cylCollapse1 (cylCollapse1.symm (wuClass1 (poincareDual4Lo_of_closed (M := M)))))
            (fundamentalClass (m := 2) (M := M)))) :=
        hproj14 _ b
    _ = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 2 (capH 1 2 (wuClass1 (poincareDual4Lo_of_closed (M := M)))
            (fundamentalClass (m := 2) (M := M)))) := by
        rw [cylCollapse1.apply_symm_apply]
    _ = fundamentalFunctional (m := 2) (M := M)
          (cupH13 (wuClass1 (poincareDual4Lo_of_closed (M := M))) (cylBeta (M := M) 2 hbij14 b)) :=
        (rhsReduce14 hbij14 (wuClass1 (poincareDual4Lo_of_closed (M := M))) b).symm
    _ = fundamentalFunctional (m := 2) (M := M)
          (Sq1 (n := 2) (cylBeta (M := M) 2 hbij14 b)) :=
        wu_relation_v1 (poincareDual4Lo_of_closed (M := M)) (cylBeta (M := M) 2 hbij14 b)
    _ = (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu (relSq1 (n := 3) b) :=
        (hsusp14 b).symm

/-! ## §2. The prism-discharged form — `hproj`/`hbij` dissolved, sole residual = the Sq-suspension atom -/

/-- **The `(2,3)` atom, fully discharged bar the Sq-suspension.** The cap-cross Fubini value `hproj23`
and the pair-suspension iso witness `hbij23` are supplied INTERNALLY from `PrismProjKillsHomology`
(`prismProjKillsHomology_holds`, the singular-normalization identity — holds unconditionally) and
`cylCrossH_bijective` (injective + the pair-suspension finrank count), so the SOLE residual of
`CylV2Desuspend` is the sharp Sq-suspension stability `hsusp23`. This is the honest provider-row shape:
per closed `M`, the middle Wu-leaf reduces to exactly `μ_W(relSq2 b) = ⟨(β b) ∪ (β b), [M]⟩`. -/
theorem CylV2Desuspend_of_sqSusp_prism
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hsusp23 : ∀ (b : RelativeCohomology (X := TopCat.of (cylW M))
        ((cylModel 2).boundary (cylW M)) 3),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu (relSq2 b)
          = fundamentalFunctional (m := 2) (M := M)
              (cupSquare2 (cylBeta (M := M) 1
                (cylCrossH_bijective (M := M) 1 hM2 (cylinder_findimRelHom23_of_base hM3 hM2)) b))) :
    CylV2Desuspend (M := M) :=
  CylV2Desuspend_of_sqSusp
    (cylCrossH_bijective (M := M) 1 hM2 (cylinder_findimRelHom23_of_base hM3 hM2))
    (fun a b => hproj23_of_pairing
      (fun a' b' => capCrossProjPairing23_of_homologyProj a'
        (capCrossHomologyProj23_of_pullback a'
          (capCrossPullbackProj23_of_kills (prismProjKillsHomology_holds (TopCat.of M))
            (cylCollapse2 a'))) b') a b)
    hsusp23

/-- **The `(1,4)` atom, fully discharged bar the Sq-suspension.** The `(1,4)` mirror of
`CylV2Desuspend_of_sqSusp_prism`: `hproj14`/`hbij14` supplied internally from `PrismProjKillsHomology`
+ `cylCrossH_bijective`, so the sole residual of `CylV1Desuspend` is the sharp `hsusp14`:
`μ_W(relSq1 b) = ⟨Sq¹ (β b), [M]⟩`. -/
theorem CylV1Desuspend_of_sqSusp_prism
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (hsusp14 : ∀ (b : RelativeCohomology (X := TopCat.of (cylW M))
        ((cylModel 2).boundary (cylW M)) 4),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu (relSq1 (n := 3) b)
          = fundamentalFunctional (m := 2) (M := M)
              (Sq1 (n := 2) (cylBeta (M := M) 2
                (cylCrossH_bijective (M := M) 2 hM3 (cylinder_findimRelHom14_of_base hM4 hM3)) b))) :
    CylV1Desuspend (M := M) :=
  CylV1Desuspend_of_sqSusp
    (cylCrossH_bijective (M := M) 2 hM3 (cylinder_findimRelHom14_of_base hM4 hM3))
    (fun a b => hproj14_of_pairing
      (fun a' b' => capCrossProjPairing14_of_homologyProj a'
        (capCrossHomologyProj14_of_pullback a'
          (capCrossPullbackProj14_of_kills (prismProjKillsHomology_holds (TopCat.of M))
            (cylCollapse1 a'))) b') a b)
    hsusp14

end

end SKEFTHawking.PinPlusCylDataDischargeWuLeafSusp
