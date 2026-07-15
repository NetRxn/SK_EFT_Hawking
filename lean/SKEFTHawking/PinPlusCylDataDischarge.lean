import Mathlib
import SKEFTHawking.SingularClosedHomologyFinite
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapNorm
import SKEFTHawking.PinPlusCharPairWProviderTransport
import SKEFTHawking.PinPlusKTLeafGate

/-!
# Phase 5q.H — THE `cylData` DISCHARGE (M-finiteness + basePD discharged; the sharp per-M Wu leaf)

Track-2's terminal engine `CylinderWAdmPinned.ofClosedPDSuspIntertwineNorm` consumes, on the base `M`,
the row `{findimM1, findimM2, hM2, hM3, hM4, basePD, hwu}`. This module discharges the six
finiteness/duality inputs FROM the closed-manifold stock and isolates the ONE genuine residual, `hwu`.

## The six discharged inputs (`SingularClosedHomologyFinite` + `SingularPD4Instances`)

* `findimM1/findimM2` = `finiteDimensional_cohomology_of_closed` (5q.G, degrees 1,2);
* `hM2/hM3` = `finiteDimensional_homology_of_closed` (the `P₄`-window transport of the cohomology
  findims onto the homology side);
* `hM4` = `finiteDimensional_topHomology_of_closed_connected` (the single-point-restriction injectivity
  into local homology `≅ ℤ/2`, connected `M`);
* `basePD` (`finrank H₁ = finrank H₃`) = the homology-side Poincaré duality of
  `finiteDimensional_homology_of_closed` (the window transports `dimeq_of_closed`).

## The one residual (`CylinderWuResidual`): the cylinder Wu obstruction

After the six are discharged, the ONLY remaining input is the cylinder Wu obstruction
`wuW2 (cylinderP14 …) (cylinderP23 …) = 0` — honestly `w₂(M × I) = 0` in the cylinder's relative-pairing
form. Connecting it to `M`'s own `w₂ = 0` (the bundle certificate `σ.cert`,
`wuW2 (poincareDual4Mid_of_closed M) (poincareDual4Lo_of_closed M) = 0`) is the **Steenrod-square
SUSPENSION naturality** `Sq ∘ susp = susp ∘ Sq` (`Hᵏ(W,∂W) ≅ Hᵏ⁻¹(M)`), the sharp missing brick named
(not faked) by `…CylinderWAdmPinnedTriage`: `SingularRelativeSteenrodSq2` provides only the
pair-restriction naturality `relToAbs_relSq2`, NOT the product/suspension naturality. This module
packages that residual as the per-M leaf `CylinderWuResidual` (the nondeg legs are `Prop`-quantified —
proof-irrelevant, so the leaf unifies against the engine's internally-built intertwine data).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCylinderWAdmPinned
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapNorm
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairWProviderTransport
open SKEFTHawking.SingularClosedHomologyFinite
open SKEFTHawking.SingularPD4Instances

namespace SKEFTHawking.PinPlusCylDataDischarge

noncomputable section

/-! ## §1. The sharp per-M cylinder-Wu residual. -/

variable (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [PreconnectedSpace M] [T1Space (cylW M)]

/-- **The sharp per-M cylinder Wu residual** — the ONLY input to Track-2's terminal engine that is
NOT discharged from the closed-manifold stock. Its honest content is `w₂(M × I) = 0` in the cylinder's
relative-pairing form; the missing brick that would derive it from `M`'s own `w₂ = 0` (`σ.cert`) is the
Steenrod-square suspension naturality (`…Triage`). The two non-degeneracy legs are `Prop`-quantified so
the leaf unifies (proof-irrelevantly) against the intertwine data the engine builds internally. -/
def CylinderWuResidual : Prop :=
  ∀ (nd14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu))
    (nd23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu)),
    wuW2
      (cylinderP14 (hasRelFundClass_cylGen (m' := 2) (M := M))
        (cylinder_findimAbs14 (finiteDimensional_cohomology_of_closed (M := M)).1)
        (cylinder_findimRel14 (cylinder_findimRelHom14_of_base
          (finiteDimensional_topHomology_of_closed_connected (M := M))
          (finiteDimensional_homology_of_closed (M := M)).2.2.1))
        nd14
        (cylinder_dimeq14_of_basePD (finiteDimensional_homology_of_closed (M := M)).2.2.1
          (finiteDimensional_homology_of_closed (M := M)).2.2.2))
      (cylinderP23 (hasRelFundClass_cylGen (m' := 2) (M := M))
        (cylinder_findimAbs23 (finiteDimensional_cohomology_of_closed (M := M)).2.1)
        (cylinder_findimRel23 (cylinder_findimRelHom23_of_base
          (finiteDimensional_homology_of_closed (M := M)).2.2.1
          (finiteDimensional_homology_of_closed (M := M)).2.1))
        nd23
        (cylinder_dimeq23_holds (finiteDimensional_homology_of_closed (M := M)).2.1)) = 0

/-! ## §2. The nonempty-connected assembler — M-finiteness and basePD discharged. -/

/-- **THE DISCHARGE**: for a closed CONNECTED charted 4-manifold `M`, `CylinderWAdmPinned M` follows
from the single sharp residual `CylinderWuResidual M` — every finiteness/duality input of the terminal
engine is discharged from the closed-manifold stock (`SingularClosedHomologyFinite` +
`finiteDimensional_cohomology_of_closed`). The residual's nondeg legs unify against the engine's
internal intertwine data (proof-irrelevance). -/
def cylinderWAdmPinned_of_wuResidual (hRes : CylinderWuResidual M) : CylinderWAdmPinned M :=
  CylinderWAdmPinned.ofClosedPDSuspIntertwineNorm
    (finiteDimensional_cohomology_of_closed (M := M)).1
    (finiteDimensional_cohomology_of_closed (M := M)).2.1
    (finiteDimensional_homology_of_closed (M := M)).2.1
    (finiteDimensional_homology_of_closed (M := M)).2.2.1
    (finiteDimensional_topHomology_of_closed_connected (M := M))
    (finiteDimensional_homology_of_closed (M := M)).2.2.2
    (hRes _ _)

end

end SKEFTHawking.PinPlusCylDataDischarge
