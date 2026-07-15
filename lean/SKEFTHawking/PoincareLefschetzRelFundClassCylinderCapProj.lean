/-
# Phase 5q.H Track 2 Part 3 — the cap–cup adjunction layer discharged: the residual is now the
# honest cap-cross HOMOLOGY projection (the EZ layer, isolated)

Part 2 (`…CylinderCapCrossProj`) landed the residual pairing, `.mu`/`.cls`-opacity-free:

  `CapCrossProjPairing23 a b : ⟨a ∪ b, [M] × [I,∂I]⟩ = ⟨b, ((α a) ⌢ [M]) × [I,∂I]⟩`   (pairing form).

This module discharges the **cap–cup adjunction + relative-Kronecker pairing layer** using the generic
relative cap product on homology `SingularRelativeCapHomology.capRelH` and its descended adjunction
`relKroneckerH_relCupRightGeneralH` (`⟨a ∪ b, z⟩ = ⟨b, a ⌢ z⟩`, relative both sides). Applying the
adjunction to the LHS collapses the pairing residual to a single **homology-class** identity per leg —
the honest Eilenberg–Zilber cap-cross projection, with NO cup, NO `b`-quantification, NO Kronecker
pairing:

  **`CapCrossHomologyProj23 a : a ⌢ ([M] × [I,∂I]) = ((α a) ⌢ [M]) × [I,∂I]`**   (`capRelH` on the left,
  `cylCrossH` on the right; `α = cylCollapse2`).

`capCrossProjPairing23_of_homologyProj` derives the Part-2 pairing residual from this class identity, and
`CylinderWAdmPinned.ofClosedPDSuspIntertwineCapProj` (`§3`) is the FIRE constructor consuming the two
class-level projections `CapCrossHomologyProj{23,14}` in place of the pairing residuals — so Track-2's
nondeg residual is now exactly the pure cap-cross homology projection per leg (the missing EZ layer),
plus `{hwu, basePD, M-finiteness}`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapCrossProj
import SKEFTHawking.SingularRelativeCapHomology

open scoped Manifold
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspDual
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspBij
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapCrossProj
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PinPlusCylinderWAdmPinned
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularRelativeCapHomology
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapProj

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [T1Space (cylW M)]

/-! ## §1. The honest cap-cross HOMOLOGY projection residuals (the isolated EZ layer) -/

/-- **The `(2,3)` cap-cross homology projection — the isolated EZ residual.**
`a ⌢ ([M] × [I,∂I]) = ((α a) ⌢ [M]) × [I,∂I]` as an equality of relative homology classes in
`H₃(W, ∂W)`, with `⌢` the relative cap `capRelH`, `[M] × [I,∂I] = cylFundClassCandidate`, `× [I,∂I]` the
homology cross `cylCrossH`, and `α = cylCollapse2`. This is the pure Eilenberg–Zilber cap-cross
projection — no cup, no `b`, no Kronecker pairing; the sharpest single named residual of the `(2,3)`
Track-2 nondeg leg. -/
def CapCrossHomologyProj23 (a : Cohomology (TopCat.of (cylW M)) 2) : Prop :=
  capRelH 2 2 a (cylFundClassCandidate (M := M) (m' := 2))
    = cylCrossH (M := M) 1 (capH 2 1 (cylCollapse2 a) (fundamentalClass (m := 2) (M := M)))

/-- **The `(1,4)` cap-cross homology projection — the isolated EZ residual.** The `(1,4)`-degree mirror
of `CapCrossHomologyProj23`: `a ⌢ ([M] × [I,∂I]) = ((α a) ⌢ [M]) × [I,∂I]` in `H₄(W, ∂W)`,
`α = cylCollapse1`. -/
def CapCrossHomologyProj14 (a : Cohomology (TopCat.of (cylW M)) 1) : Prop :=
  capRelH 1 3 a (cylFundClassCandidate (M := M) (m' := 2))
    = cylCrossH (M := M) 2 (capH 1 2 (cylCollapse1 a) (fundamentalClass (m := 2) (M := M)))

/-! ## §1b. The pulled-back form of the residual — the standard cap-cross projection formula

`cylCollapse2 = (prodContractibleCohomologyEquiv)⁻¹`, so `cylCollapse2.symm` is the projection pullback
`π* : Hᵏ(M) → Hᵏ(W)` (`= cohomologyPullback (prodFst)`, the contractible-interval collapse's inverse).
Restating the residual with the left cohomology factor as a **pulled-back** class `π* u` turns
`CapCrossHomologyProj` into the textbook Eilenberg–Zilber projection formula
`(π* u) ⌢ (z × [I,∂I]) = (u ⌢ z) × [I,∂I]` — the maximally-clean final target for the EZ layer. -/

/-- **The `(2,3)` cap-cross projection, pulled-back form.** `(π* u) ⌢ ([M] × [I,∂I]) = (u ⌢ [M]) × [I,∂I]`
for `u ∈ H²(M)`, `π* = cylCollapse2.symm` the projection pullback. The classical cap-cross projection
formula for pulled-back classes; equivalent to `CapCrossHomologyProj23` at `a = π* u` since
`cylCollapse2` is a bijection. -/
def CapCrossPullbackProj23 (u : Cohomology (TopCat.of M) 2) : Prop :=
  capRelH 2 2 (cylCollapse2.symm u) (cylFundClassCandidate (M := M) (m' := 2))
    = cylCrossH (M := M) 1 (capH 2 1 u (fundamentalClass (m := 2) (M := M)))

/-- **The `(1,4)` cap-cross projection, pulled-back form.** `(π* u) ⌢ ([M] × [I,∂I]) = (u ⌢ [M]) × [I,∂I]`
for `u ∈ H¹(M)`, `π* = cylCollapse1.symm`. -/
def CapCrossPullbackProj14 (u : Cohomology (TopCat.of M) 1) : Prop :=
  capRelH 1 3 (cylCollapse1.symm u) (cylFundClassCandidate (M := M) (m' := 2))
    = cylCrossH (M := M) 2 (capH 1 2 u (fundamentalClass (m := 2) (M := M)))

omit [PreconnectedSpace M] [T1Space (cylW M)] in
/-- **The general `(2,3)` residual follows from the pulled-back form.** Every `a ∈ H²(W)` is
`π* (α a) = cylCollapse2.symm (cylCollapse2 a)` (`cylCollapse2` a bijection), so the pulled-back
projection at `u = α a` IS the general projection at `a`. -/
theorem capCrossHomologyProj23_of_pullback (a : Cohomology (TopCat.of (cylW M)) 2)
    (h : CapCrossPullbackProj23 (cylCollapse2 a)) : CapCrossHomologyProj23 a := by
  unfold CapCrossPullbackProj23 at h
  rw [cylCollapse2.symm_apply_apply] at h
  exact h

omit [PreconnectedSpace M] [T1Space (cylW M)] in
/-- **The general `(1,4)` residual follows from the pulled-back form.** -/
theorem capCrossHomologyProj14_of_pullback (a : Cohomology (TopCat.of (cylW M)) 1)
    (h : CapCrossPullbackProj14 (cylCollapse1 a)) : CapCrossHomologyProj14 a := by
  unfold CapCrossPullbackProj14 at h
  rw [cylCollapse1.symm_apply_apply] at h
  exact h

/-! ## §2. Deriving the Part-2 pairing residual from the cap-cross homology projection (adjunction) -/

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] [T1Space (cylW M)] in
/-- **The `(2,3)` cap–cup adjunction bridge.** `relCupH23` on a representative left class is
`relCupRightGeneralH` (both descend `relCupLeftₗ`), so the descended relative adjunction
`relKroneckerH_relCupRightGeneralH` applies with the left factor as the class `a`:
`⟨a ∪ b, z⟩ = ⟨b, a ⌢ z⟩` (relative Kronecker both sides, `⌢ = capRelH 2 2`). -/
theorem relKroneckerH_relCupH23_eq
    (a : Cohomology (TopCat.of (cylW M)) 2)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3)
    (z : RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 5) :
    relKroneckerH (cylBdW (M := M))
        (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b) z
      = relKroneckerH (cylBdW (M := M)) b (capRelH 2 2 a z) := by
  obtain ⟨â, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  exact relKroneckerH_relCupRightGeneralH (S := cylBdW (M := M)) (k := 2) (m := 2) â b z

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] [T1Space (cylW M)] in
/-- **The `(1,4)` cap–cup adjunction bridge.** The `(1,4)`-degree mirror of
`relKroneckerH_relCupH23_eq`, `⌢ = capRelH 1 3`. -/
theorem relKroneckerH_relCupH14_eq
    (a : Cohomology (TopCat.of (cylW M)) 1)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4)
    (z : RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 5) :
    relKroneckerH (cylBdW (M := M))
        (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b) z
      = relKroneckerH (cylBdW (M := M)) b (capRelH 1 3 a z) := by
  obtain ⟨â, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  exact relKroneckerH_relCupRightGeneralH (S := cylBdW (M := M)) (k := 1) (m := 3) â b z

omit [PreconnectedSpace M] [T1Space (cylW M)] in
/-- **The `(2,3)` pairing residual follows from the cap-cross homology projection.** Applies the
adjunction bridge (`§2`) to the LHS of `CapCrossProjPairing23`, then rewrites the resulting
`⟨b, a ⌢ [M]×[I,∂I]⟩` by the honest cap-cross projection `CapCrossHomologyProj23`. -/
theorem capCrossProjPairing23_of_homologyProj
    (a : Cohomology (TopCat.of (cylW M)) 2)
    (hproj : CapCrossHomologyProj23 a)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) :
    CapCrossProjPairing23 (M := M) a b := by
  unfold CapCrossProjPairing23
  rw [relKroneckerH_relCupH23_eq a b (cylFundClassCandidate (M := M) (m' := 2))]
  exact congrArg (relKroneckerH (cylBdW (M := M)) b) hproj

omit [PreconnectedSpace M] [T1Space (cylW M)] in
/-- **The `(1,4)` pairing residual follows from the cap-cross homology projection.** -/
theorem capCrossProjPairing14_of_homologyProj
    (a : Cohomology (TopCat.of (cylW M)) 1)
    (hproj : CapCrossHomologyProj14 a)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) :
    CapCrossProjPairing14 (M := M) a b := by
  unfold CapCrossProjPairing14
  rw [relKroneckerH_relCupH14_eq a b (cylFundClassCandidate (M := M) (m' := 2))]
  exact congrArg (relKroneckerH (cylBdW (M := M)) b) hproj

/-! ## §3. The FIRE constructor — residual = the two cap-cross HOMOLOGY projections -/

/-- **The FIRE opener from the cap-cross homology projections.** Successor to
`…CylinderCapCrossProj.CylinderWAdmPinned.ofClosedPDSuspIntertwinePairing`: the two pairing residuals
`CapCrossProjPairing{23,14}` are replaced by the two class-level cap-cross homology projections
`CapCrossHomologyProj{23,14}` (which discharge to the pairings via the descended cap–cup adjunction, `§2`).
The Track-2 nondeg residual is now exactly the honest Eilenberg–Zilber cap-cross homology projection per
leg — `a ⌢ ([M]×[I,∂I]) = ((α a) ⌢ [M]) × [I,∂I]` — plus `{hwu, basePD, M-finiteness}`. -/
def CylinderWAdmPinned.ofClosedPDSuspIntertwineCapProj
    (findimM1 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 1))
    (findimM2 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 2))
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (basePD : Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3))
    (hcap23 : ∀ (a : Cohomology (TopCat.of (cylW M)) 2), CapCrossHomologyProj23 (M := M) a)
    (hcap14 : ∀ (a : Cohomology (TopCat.of (cylW M)) 1), CapCrossHomologyProj14 (M := M) a)
    (hwu : wuW2
      (cylinderP14 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs14 findimM1)
        (cylinder_findimRel14 (cylinder_findimRelHom14_of_base hM4 hM3))
        (CylinderSuspIntertwineData.ofCapCrossPairing hM2 hM3 hM4
          (fun a b => capCrossProjPairing23_of_homologyProj a (hcap23 a) b)
          (fun a b => capCrossProjPairing14_of_homologyProj a (hcap14 a) b)).nondeg14
        (cylinder_dimeq14_of_basePD hM3 basePD))
      (cylinderP23 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs23 findimM2)
        (cylinder_findimRel23 (cylinder_findimRelHom23_of_base hM3 hM2))
        (CylinderSuspIntertwineData.ofCapCrossPairing hM2 hM3 hM4
          (fun a b => capCrossProjPairing23_of_homologyProj a (hcap23 a) b)
          (fun a b => capCrossProjPairing14_of_homologyProj a (hcap14 a) b)).nondeg23
        (cylinder_dimeq23_holds hM2)) = 0) :
    CylinderWAdmPinned M :=
  CylinderWAdmPinned.ofClosedPDSuspIntertwinePairing findimM1 findimM2 hM2 hM3 hM4 basePD
    (fun a b => capCrossProjPairing23_of_homologyProj a (hcap23 a) b)
    (fun a b => capCrossProjPairing14_of_homologyProj a (hcap14 a) b) hwu

/-- **The FIRE opener from the pulled-back cap-cross projections — the sharpest firing shape.**
Consumes the two textbook cap-cross projection formulas `CapCrossPullbackProj{23,14}` (`(π* u) ⌢
([M]×[I,∂I]) = (u ⌢ [M]) × [I,∂I]`, quantified over the base classes `u ∈ H^{1,2}(M)`), reducing to
`ofClosedPDSuspIntertwineCapProj` via `capCrossHomologyProj{23,14}_of_pullback`. This is the Track-2
nondeg residual in its final, maximally-clean form: the classical Eilenberg–Zilber projection formula
for pulled-back classes, per leg, plus `{hwu, basePD, M-finiteness}`. -/
def CylinderWAdmPinned.ofClosedPDSuspIntertwinePullbackProj
    (findimM1 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 1))
    (findimM2 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 2))
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (basePD : Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3))
    (hpb23 : ∀ (u : Cohomology (TopCat.of M) 2), CapCrossPullbackProj23 (M := M) u)
    (hpb14 : ∀ (u : Cohomology (TopCat.of M) 1), CapCrossPullbackProj14 (M := M) u)
    (hwu : wuW2
      (cylinderP14 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs14 findimM1)
        (cylinder_findimRel14 (cylinder_findimRelHom14_of_base hM4 hM3))
        (CylinderSuspIntertwineData.ofCapCrossPairing hM2 hM3 hM4
          (fun a b => capCrossProjPairing23_of_homologyProj a
            (capCrossHomologyProj23_of_pullback a (hpb23 (cylCollapse2 a))) b)
          (fun a b => capCrossProjPairing14_of_homologyProj a
            (capCrossHomologyProj14_of_pullback a (hpb14 (cylCollapse1 a))) b)).nondeg14
        (cylinder_dimeq14_of_basePD hM3 basePD))
      (cylinderP23 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs23 findimM2)
        (cylinder_findimRel23 (cylinder_findimRelHom23_of_base hM3 hM2))
        (CylinderSuspIntertwineData.ofCapCrossPairing hM2 hM3 hM4
          (fun a b => capCrossProjPairing23_of_homologyProj a
            (capCrossHomologyProj23_of_pullback a (hpb23 (cylCollapse2 a))) b)
          (fun a b => capCrossProjPairing14_of_homologyProj a
            (capCrossHomologyProj14_of_pullback a (hpb14 (cylCollapse1 a))) b)).nondeg23
        (cylinder_dimeq23_holds hM2)) = 0) :
    CylinderWAdmPinned M :=
  CylinderWAdmPinned.ofClosedPDSuspIntertwineCapProj findimM1 findimM2 hM2 hM3 hM4 basePD
    (fun a => capCrossHomologyProj23_of_pullback a (hpb23 (cylCollapse2 a)))
    (fun a => capCrossHomologyProj14_of_pullback a (hpb14 (cylCollapse1 a))) hwu

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapProj
