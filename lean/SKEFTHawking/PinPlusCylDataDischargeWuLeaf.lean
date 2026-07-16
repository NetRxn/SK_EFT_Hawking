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

end

end SKEFTHawking.PinPlusCylDataDischargeWuLeaf
