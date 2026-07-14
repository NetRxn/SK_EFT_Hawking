/-
# Phase 5q.H (W-A arm 4) — the cylinder Lefschetz `nondeg` residual: reduced to `M`'s own PD pairing

The last deep cylinder-numerics residual. `CylinderWAdmPinned.nondeg14`/`nondeg23` (for the reflexive
cylinder `W = M × [0,1]` over a **closed 4-manifold** `M`) are the LEFT non-degeneracy of the
Poincaré–Lefschetz pairing `H^k(W) × H^{5-k}(W,∂W) → ℤ/2`, `(a,b) ↦ ⟨a ∪ b, [W,∂W]⟩` — injectivity of
`(relCupH1k).compr₂ μ_W`. This module lands the honest reduction of that residual.

## The reduction (iso-transport, `PoincareLefschetzWuPairingCriterion.injective_of_pairing_congr`)

Under the cylinder's homotopy structure the two Lefschetz-dual degree pairs match `M`'s own
Poincaré-duality pairs:
* `(2,3)`: `H^2(W) × H^3(W,∂W)` corresponds — `H^2(W) ≅ H^2(M)` (contractible collapse), `H^3(W,∂W) ≅
  H^2(M)` (suspension) — to `M`'s MIDDLE pairing `H^2(M) × H^2(M) → ℤ/2` (`cupH24.compr₂
  fundamentalFunctional`), whose perfectness is the in-tree theorem `SingularPD4Instances.nondeg_of_closed`;
* `(1,4)`: `H^1(W) × H^4(W,∂W)` corresponds — `H^1(W) ≅ H^1(M)`, `H^4(W,∂W) ≅ H^3(M)` — to `M`'s
  `(1,3)` pairing `H^1(M) × H^3(M) → ℤ/2` (`cupH13.compr₂ fundamentalFunctional`), whose perfectness is
  `SingularPD4Instances.nondeg13_of_closed`.

`cylinder_nondeg23_of_intertwining` / `cylinder_nondeg14_of_intertwining` PROVE the cylinder `nondeg`
from ONE remaining named input each — the **intertwining datum** `(α, β, hcompat)`: cohomology
equivalences on the two pairing arguments plus the cup-compatibility `⟨a ∪ b, [W,∂W]⟩ = ⟨α a ∪ β b,
[M]⟩`. `M`'s own Poincaré-duality perfectness is consumed IN-TREE (`nondeg_of_closed` /
`nondeg13_of_closed`), so the residual isolates to exactly the intertwining — the cohomology
suspension iso composed with the cup/cross-product compatibility of `[W,∂W] = [M] × [I,∂I]`, i.e. the
`hcls` cross-product arc. It is NOT re-derived here; it is named as the single honest residual.

## `ofClosedPD` — the closed-manifold constructor (`basePD` + the `M`-side findims discharged)

`CylinderWAdmPinned.ofClosedPD` improves on `ofBasePD`: for a genuine closed charted 4-manifold the
degree-1↔3 Betti equality `basePD` is PROVEN from `M`'s own Poincaré duality (`dimeq_of_closed`,
Kronecker-transported to homology), and the `M`-side absolute findims `b_1(M), b_2(M) < ∞` are PROVEN
from the Erdős–Kaplansky window (`finiteDimensional_cohomology_of_closed`). The residual-set collapses
to exactly the four DEEP inputs — existence `hcls`, the two `nondeg`, Wall-2 `hdet`, the Wu vanishing
`hwu` — plus the soft `M`-side homology finiteness `b_2, b_3, b_4(M) < ∞`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCylinderWAdmPinned
import SKEFTHawking.PoincareLefschetzWuPairingCriterion
import SKEFTHawking.SingularPD4Instances

open scoped Manifold
open SKEFTHawking.PoincareLefschetzWuPairingCriterion
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.PinPlusCylinderWAdmPinned
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.SingularPD4Instances

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderNondeg

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-! ## §1. The `nondeg` reduction via the intertwining, `M`'s PD pairing consumed in-tree -/

/-- **The cylinder `(2,3)` Lefschetz non-degeneracy, reduced to the named intertwining.** Given
cohomology equivalences `α : H^2(W) ≅ H^2(M)`, `β : H^3(W,∂W) ≅ H^2(M)` intertwining the cylinder
pairing with `M`'s MIDDLE pairing (`⟨a ∪ b, [W,∂W]⟩ = ⟨α a ∪ β b, [M]⟩`), the cylinder pairing is
left-non-degenerate. `M`'s own middle-pairing perfectness is consumed in-tree
(`nondeg_of_closed`); the sole residual is the intertwining `(α, β, hcompat)` (the cohomology
suspension iso + cup-compatibility of `[W,∂W] = [M] × [I,∂I]`). -/
theorem cylinder_nondeg23_of_intertwining
    (hcls : HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))
      (cylGen (M := M) (m' := 2)))
    (α : Cohomology (TopCat.of (cylW M)) 2 ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 2)
    (β : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3
      ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 2)
    (hcompat : ∀ (a : Cohomology (TopCat.of (cylW M)) 2)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
        (cylinderDatum hcls).mu
            (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = fundamentalFunctional (m := 2) (M := M) (cupH24 (α a) (β b))) :
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum hcls).mu) :=
  lefschetzPairing_injective_of_congr (cylinderDatum hcls).mu
    (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)))
    (cupH24.compr₂ (fundamentalFunctional (m := 2) (M := M))) α β hcompat
    (nondeg_of_closed (M := M))

/-- **The cylinder `(1,4)` Lefschetz non-degeneracy, reduced to the named intertwining.** Given
cohomology equivalences `α : H^1(W) ≅ H^1(M)`, `β : H^4(W,∂W) ≅ H^3(M)` intertwining the cylinder
pairing with `M`'s `(1,3)` pairing (`⟨a ∪ b, [W,∂W]⟩ = ⟨α a ∪ β b, [M]⟩`), the cylinder pairing is
left-non-degenerate. `M`'s `(1,3)` perfectness is consumed in-tree (`nondeg13_of_closed`); the sole
residual is the intertwining. -/
theorem cylinder_nondeg14_of_intertwining
    (hcls : HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))
      (cylGen (M := M) (m' := 2)))
    (α : Cohomology (TopCat.of (cylW M)) 1 ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 1)
    (β : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4
      ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 3)
    (hcompat : ∀ (a : Cohomology (TopCat.of (cylW M)) 1)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
        (cylinderDatum hcls).mu
            (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = fundamentalFunctional (m := 2) (M := M) (cupH13 (α a) (β b))) :
    Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum hcls).mu) :=
  lefschetzPairing_injective_of_congr (cylinderDatum hcls).mu
    (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)))
    (cupH13.compr₂ (fundamentalFunctional (m := 2) (M := M))) α β hcompat
    (nondeg13_of_closed (M := M))

/-! ## §2. `basePD` from closedness, and the closed-manifold constructor `ofClosedPD` -/

/-- **The degree-1↔3 homology Betti equality `b_1(M) = b_3(M)` from `M`'s own Poincaré duality.** The
`ofBasePD` input `basePD`, discharged for a closed charted 4-manifold: Kronecker-transport both sides
to cohomology, apply `dimeq_of_closed` (`dim H^1(M) = dim H^3(M)`). -/
theorem basePD_of_closed :
    Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3) := by
  calc Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Cohomology (TopCat.of M) 1) :=
        (finrank_cohomology_eq_homology (X := TopCat.of M) 0).symm
    _ = Module.finrank (ZMod 2) (Cohomology (TopCat.of M) 3) := dimeq_of_closed (M := M)
    _ = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3) :=
        finrank_cohomology_eq_homology (X := TopCat.of M) 2

/-- **The closed-manifold residual-set constructor.** For a genuine closed charted 4-manifold `M`,
`ofClosedPD` assembles the whole `CylinderWAdmPinned` residual-set with the Betti equality `basePD` and
the `M`-side absolute findims `b_1(M), b_2(M) < ∞` DISCHARGED from `M`'s Poincaré duality
(`basePD_of_closed`) and the Erdős–Kaplansky window (`finiteDimensional_cohomology_of_closed`). The
residual-set is exactly the four deep inputs — existence `hcls`, the two `nondeg`, Wall-2 `hdet`, the
Wu vanishing `hwu` — plus the soft homology finiteness `b_2, b_3, b_4(M) < ∞`. -/
def CylinderWAdmPinned.ofClosedPD
    (hcls : HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))
      (cylGen (M := M) (m' := 2)))
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (nondeg14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum hcls).mu))
    (nondeg23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum hcls).mu))
    (hdet : determinedByPoints (X := TopCat.of (cylW M)) (2 + 1 + 2) (interiorSlab M))
    (hwu : wuW2
      (cylinderP14 hcls (cylinder_findimAbs14 (finiteDimensional_cohomology_of_closed (M := M)).1)
        (cylinder_findimRel14 (cylinder_findimRelHom14_of_base hM4 hM3)) nondeg14
        (cylinder_dimeq14_of_basePD hM3 (basePD_of_closed (M := M))))
      (cylinderP23 hcls
        (cylinder_findimAbs23 (finiteDimensional_cohomology_of_closed (M := M)).2.1)
        (cylinder_findimRel23 (cylinder_findimRelHom23_of_base hM3 hM2)) nondeg23
        (cylinder_dimeq23_holds hM2)) = 0) :
    CylinderWAdmPinned M :=
  CylinderWAdmPinned.ofBasePD hcls
    (finiteDimensional_cohomology_of_closed (M := M)).1
    (finiteDimensional_cohomology_of_closed (M := M)).2.1
    hM2 hM3 hM4 nondeg14 nondeg23 (basePD_of_closed (M := M)) hdet hwu

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderNondeg
