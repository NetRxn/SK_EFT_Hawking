/-
# Phase 5q.H close-out (Lane A2) — the WU LEAF: `CylinderWuResidual` wired to `σ.cert` via the
# α-collapse desuspension of the cylinder Lefschetz–Wu classes

The provider inhabitation `nonempty_provider_of_wuLeaf_and_disconnectedCoreND`
(`PinPlusCylDataDischargeDisconnectedComponents`) is live modulo two leaves: the disconnected core
(closed in a parallel lane) and THIS one — the per-`M` `CylinderWuResidual`, honestly
`wuW2(cylinderP14, cylinderP23) = 0`, i.e. `w₂(M × I) = 0` in the cylinder's relative-pairing form.

## What this module banks (the σ.cert wiring, α-collapse ring-naturality)

The cylinder Lefschetz–Wu classes `v₁(W), v₂(W)` live in the ABSOLUTE cohomology `H¹(W), H²(W)`, and the
homotopy collapse `Hᵏ(W) ≅ Hᵏ(M)` (`cylCollapse1`/`cylCollapse2`, the `.symm` of the projection
pullback `π* : Hᵏ(M) ≅ Hᵏ(W)`) is a RING iso. So the whole `wuW2` transports through the collapse:

  `cylCollapse2 (wuW2 P₁₄ P₂₃) = wuClass2 (pd4Mid M) + (wuClass1 (pd4Lo M))²`   (`cylinderWu_desuspend_image`)

*provided* the two sharp desuspension class-identities hold:

  `(hA)  cylCollapse2 (v₂(W)) = v₂(M)`   and   `(hB)  cylCollapse1 (v₁(W)) = v₁(M)`.

The RHS is exactly the base `PoincareDualityWuFormula.wuW2 (pd4Mid M) (pd4Lo M)`, so `σ.cert`
(`= 0`, `PinPlusCertK`) forces `cylCollapse2 (wuW2 P₁₄ P₂₃) = 0`, hence — `cylCollapse2` an iso —
`wuW2 P₁₄ P₂₃ = 0`. This is `cylinderWu_of_desuspend`: it wires the residual to `{hA, hB}` +
`σ.cert`, discharging the finiteness/pairing scaffolding entirely.

`(hA)`/`(hB)` are the genuine sharp atoms — the Steenrod-square SUSPENSION naturality of the
cylinder's Lefschetz–Wu classes — carried here as named hypotheses (the `#99` wall, now attacked with
the matured cap-cross EZ layer). This module isolates them AS the residual and discharges everything
else kernel-purely.

### Supporting lemma — the cup-naturality of the α-collapse (`cylCollapse2_cupH`)

`cylCollapse2 (a ∪ b) = cylCollapse1 a ∪ cylCollapse1 b` for `a, b ∈ H¹(W)`: the α-collapse is the
inverse of the ring map `π*`, so it respects cup (`cohomologyPullback_cupH`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusCylDataDischarge
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine

open scoped Manifold
open SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularCohomologyHomotopy
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareDualityWu
open SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.SingularClosedHomologyFinite
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCylDataDischarge

namespace SKEFTHawking.PinPlusCylDataDischargeWuLeaf

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-! ## §1. Cup-naturality of the α-collapse `Hᵏ(W) ≅ Hᵏ(M)`. -/

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] in
/-- **The α-collapse respects the cup product.** `cylCollapse2 (a ∪ b) = cylCollapse1 a ∪ cylCollapse1 b`
for `a, b ∈ H¹(W)`. The collapse is the inverse of the projection pullback `π*` (a ring map,
`cohomologyPullback_cupH`), so it too respects cup. -/
theorem cylCollapse2_cupH (a b : Cohomology (TopCat.of (cylW M)) 1) :
    cylCollapse2 (cupH a b) = cupH (cylCollapse1 a) (cylCollapse1 b) := by
  apply cylCollapse2.symm.injective
  rw [cylCollapse2.symm_apply_apply]
  show _ = cohomologyPullback (prodFst (TopCat.of M) (TopCat.of unitInterval)) 2
    (cupH (cylCollapse1 a) (cylCollapse1 b))
  rw [cohomologyPullback_cupH]
  show _ = cupH (cylCollapse1.symm (cylCollapse1 a)) (cylCollapse1.symm (cylCollapse1 b))
  rw [cylCollapse1.symm_apply_apply, cylCollapse1.symm_apply_apply]

/-! ## §2. The abstract desuspension wiring — `wuW2(W) = 0` from `{hA, hB}` + `σ.cert`. -/

/-- **THE WU LEAF, abstractly.** For ANY two cylinder Lefschetz–Wu data `P₁₄`, `P₂₃`, if the two sharp
desuspension identities hold — `cylCollapse2 (v₂(W)) = v₂(M)` and `cylCollapse1 (v₁(W)) = v₁(M)` — then
the cylinder Wu obstruction `wuW2 P₁₄ P₂₃ = 0` follows from the base certificate `σ.cert`
(`wuW2 (pd4Mid M) (pd4Lo M) = 0`). The α-collapse (a ring iso) carries the whole `wuW2` to the base's,
which `σ.cert` kills; injectivity of the collapse pulls the vanishing back. -/
theorem cylinderWu_of_desuspend
    (P₁₄ : LefschetzWuDatum (TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 1 4 5)
    (P₂₃ : LefschetzWuDatum (TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 2 3 5)
    (hcert : PoincareDualityWuFormula.wuW2 (poincareDual4Mid_of_closed (M := M))
      (poincareDual4Lo_of_closed (M := M)) = 0)
    (hA : cylCollapse2 (wuClassW2 P₂₃) = wuClass2 (poincareDual4Mid_of_closed (M := M)))
    (hB : cylCollapse1 (wuClassW1 P₁₄) = wuClass1 (poincareDual4Lo_of_closed (M := M))) :
    PoincareLefschetzWu5.wuW2 P₁₄ P₂₃ = 0 := by
  apply cylCollapse2.injective
  rw [map_zero, PoincareLefschetzWu5.wuW2_eq, map_add, hA, cylCollapse2_cupH, hB,
    ← PoincareDualityWuFormula.wuW2_eq, hcert]

/-! ## §3. The two sharp named atoms (the Steenrod suspension-naturality leaves) and the σ.cert wiring. -/

section Leaf

variable [PreconnectedSpace M] [T1Space (cylW M)]

/-- **The `(2,3)` desuspension atom** — `v₂(W)` desuspends (along the α-collapse) to `v₂(M)`. The sharp
Steenrod-`Sq²` suspension content of the cylinder Wu leaf: the cylinder's `(2,3)` Lefschetz–Wu class,
collapsed to `H²(M)`, is `M`'s own middle Wu class `wuClass2 (pd4Mid M)`. Honestly the pair-suspension
naturality `Sq² ∘ β = β' ∘ relSq²` in the `⟨·,[W,∂W]⟩ = ⟨·,[M]⟩` Fubini form (the `#99` residual). -/
def CylV2Desuspend : Prop :=
  ∀ (nd23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu)),
    cylCollapse2 (wuClassW2 (cylinderP23 (hasRelFundClass_cylGen (m' := 2) (M := M))
      (cylinder_findimAbs23 (finiteDimensional_cohomology_of_closed (M := M)).2.1)
      (cylinder_findimRel23 (cylinder_findimRelHom23_of_base
        (finiteDimensional_homology_of_closed (M := M)).2.2.1
        (finiteDimensional_homology_of_closed (M := M)).2.1))
      nd23
      (cylinder_dimeq23_holds (finiteDimensional_homology_of_closed (M := M)).2.1)))
      = wuClass2 (poincareDual4Mid_of_closed (M := M))

/-- **The `(1,4)` desuspension atom** — `v₁(W)` desuspends (along the α-collapse) to `v₁(M)`. The sharp
Steenrod-`Sq¹` suspension content: the cylinder's `(1,4)` Lefschetz–Wu class, collapsed to `H¹(M)`, is
`M`'s own first Wu class `wuClass1 (pd4Lo M)`. -/
def CylV1Desuspend : Prop :=
  ∀ (nd14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu)),
    cylCollapse1 (wuClassW1 (cylinderP14 (hasRelFundClass_cylGen (m' := 2) (M := M))
      (cylinder_findimAbs14 (finiteDimensional_cohomology_of_closed (M := M)).1)
      (cylinder_findimRel14 (cylinder_findimRelHom14_of_base
        (finiteDimensional_topHomology_of_closed_connected (M := M))
        (finiteDimensional_homology_of_closed (M := M)).2.2.1))
      nd14
      (cylinder_dimeq14_of_basePD (finiteDimensional_homology_of_closed (M := M)).2.2.1
        (finiteDimensional_homology_of_closed (M := M)).2.2.2)))
      = wuClass1 (poincareDual4Lo_of_closed (M := M))

/-- **The Wu leaf reduced to the two sharp desuspension atoms + `σ.cert`.** `CylinderWuResidual M`
(honestly `wuW2(cylinderP14, cylinderP23) = 0`) follows from the two class-desuspension atoms
`CylV2Desuspend`/`CylV1Desuspend` and the base `w₂ = 0` certificate. All the finiteness/duality
scaffolding of the residual is dissolved; the sole remaining content is the Steenrod suspension
naturality packaged in the two atoms. -/
theorem cylinderWuResidual_of_desuspendLeaves
    (hcert : PoincareDualityWuFormula.wuW2 (poincareDual4Mid_of_closed (M := M))
      (poincareDual4Lo_of_closed (M := M)) = 0)
    (hA : CylV2Desuspend (M := M)) (hB : CylV1Desuspend (M := M)) :
    CylinderWuResidual M := by
  intro nd14 nd23
  exact cylinderWu_of_desuspend _ _ hcert (hA nd23) (hB nd14)

/-- **The bundled σ.cert wiring.** For a bundled characteristic-pair carrier `σ : CharPairStrBundled I s`
the base `w₂ = 0` certificate is `σ.cert` (`PinPlusCertK`), so the Wu leaf reduces to exactly the two
desuspension atoms on `s.M`. This is the honest provider-row shape: the `hwu` hypothesis of
`nonempty_provider_of_wuLeaf_and_disconnectedCoreND` is supplied, per `σ`, by
`{CylV2Desuspend s.M, CylV1Desuspend s.M}` (the pure Steenrod-suspension leaves) via `σ.cert`. -/
theorem cylinderWuResidual_of_bundled_desuspend
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {k : WithTop ℕ∞}
    {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
    {s : SingularManifold.{0} PUnit.{1} k I} (σ : CharPairStrBundled I s)
    [T2Space s.M] [Nonempty s.M] [PreconnectedSpace s.M] [T1Space (cylW s.M)]
    (hA : CylV2Desuspend (M := s.M)) (hB : CylV1Desuspend (M := s.M)) :
    CylinderWuResidual s.M :=
  cylinderWuResidual_of_desuspendLeaves σ.cert hA hB

end Leaf

end

end SKEFTHawking.PinPlusCylDataDischargeWuLeaf
