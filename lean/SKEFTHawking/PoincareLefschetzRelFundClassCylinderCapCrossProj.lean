/-
# Phase 5q.H Track 2 Part 2 — the cap-cross projection OPENER (residual now fully explicit)

Part 1 (`…CylinderClsIdent.cylinderDatum_cls_eq_crossH`) killed the `Classical.choose` opacity of the
cylinder Poincaré–Lefschetz datum class: `(cylinderDatum (hasRelFundClass_cylGen)).cls =
cylFundClassCandidate = [M] × [I,∂I] = crossH [M]`. This module cashes that in on the **cap-cross
projection residual** the FIRE constructors (`…CylinderSuspBij.ofCapCrossProj` /
`ofClosedPDSuspIntertwineProj`) consume — the two projection values

  `hproj{23,14} : (cylinderDatum hcls).mu (relCup{23,14} a b) = ⟨b, cylCrossH ((α a) ⌢ [M])⟩`.

The LHS `(cylinderDatum hcls).mu (…)` still pairs the cup class against the OPAQUE datum functional. This
module rewrites it, via Part 1, into the EXPLICIT relative-Kronecker pairing against the honest cross
class `[M] × [I,∂I]`, landing the residual as a fully explicit, `.mu`/`.cls`-opacity-free identity:

  **`⟨a ∪ b, [M] × [I,∂I]⟩ = ⟨b, ((α a) ⌢ [M]) × [I,∂I]⟩`**   (`hpair{23,14}`, `§3`).

That IS the cap-cross projection formula at the pairing level — the next honest arc (its discharge needs
the relative descended cap-cup adjunction plus the Eilenberg–Zilber cap-cross projection, the missing
EZ layer this substrate does not yet build; see the module tail). The successor constructors
`CylinderSuspIntertwineData.ofCapCrossPairing` / `CylinderWAdmPinned.ofClosedPDSuspIntertwinePairing`
(`§4`) consume this explicit-pairing residual in place of the `.mu`-wrapped `hproj{23,14}`.

## Spelling discipline (why `cylBdW`)

Writing `relKroneckerH ((cylModel 2).boundary (cylW M)) _ _` or `relFundFunctional ((cylModel 2)…) _`
over the UNFOLDED cylinder boundary triggers a heartbeat-scale `isDefEq` blowup (the datum machinery
keeps that construction sealed). `cylBdW` seals the boundary in the `cylW` ambient once — every pairing
below carries the sealed spelling, dodging the blowup — exactly the `cylBd` discipline
`…CylinderSuspDual` uses in the `cyl (TopCat.of M)` ambient.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspBij
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderClsIdent

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
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderClsIdent
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PinPlusCylinderWAdmPinned
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapCrossProj

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [T1Space (cylW M)]

/-! ## §1. Bridging the datum class into the SuspDual cylinder-cross machinery -/

omit [PreconnectedSpace M] [T1Space (cylW M)] in
/-- **The explicit candidate IS the SuspDual cylinder cross of `[M]`.** `cylFundClassCandidate =
crossH (∂W) 3 [M]` and `cylCrossH 3 [M]` are the same `crossH` at `p = 3`, `S = (cylModel 2).boundary`
— definitionally equal. Bridges Part 1's `.cls = cylFundClassCandidate` into the `cylCrossH` handle the
`hproj` right-hand sides use. -/
theorem cylFundClassCandidate_eq_cylCrossH :
    cylFundClassCandidate (M := M) (m' := 2)
      = cylCrossH (M := M) 3
          (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M)) :=
  rfl

/-- **The datum class is the SuspDual cylinder cross of `[M]`.** Part 1's `cylinderDatum_cls_eq_crossH`
composed with the spelling bridge: `(cylinderDatum hcls).cls = cylCrossH 3 [M]`. -/
theorem cylinderDatum_cls_eq_cylCrossH :
    (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).cls
      = cylCrossH (M := M) 3
          (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M)) :=
  cylinderDatum_cls_eq_crossH.trans cylFundClassCandidate_eq_cylCrossH

/-! ## §2. The datum functional as the EXPLICIT pairing against `crossH [M]` (sealed spelling) -/

/-- **The cylinder boundary `∂W`, sealed in the `cylW` ambient.** Keeping the boundary folded here
dodges the `isDefEq` blowup that writing `relKroneckerH`/`relFundFunctional` over the unfolded boundary
would trigger (the datum machinery keeps it sealed). Mirror of `…CylinderSuspDual.cylBd` in the
`TopCat.of (cylW M)` (rather than `cyl (TopCat.of M)`) spelling. -/
def cylBdW : Set ↑(TopCat.of (cylW M)) := (cylModel 2).boundary (cylW M)

/-- **The datum functional is the pairing-against-`[M]×[I,∂I]` functional.** With the datum class
identified (Part 1), `(cylinderDatum hcls).mu = ⟨·, [M] × [I,∂I]⟩` — the `Classical.choose`-opacity is
gone from the functional itself. Sealed via `cylBdW`. -/
theorem cylinderDatum_mu_eq_funct :
    (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
      = relFundFunctional (cylBdW (M := M)) (cylFundClassCandidate (M := M) (m' := 2)) :=
  congrArg (relFundFunctional (cylBdW (M := M))) cylinderDatum_cls_eq_crossH

/-- **The explicit `(2,3)` cup-pairing.** `(cylinderDatum hcls).mu (a ∪ b) = ⟨a ∪ b, [M] × [I,∂I]⟩` —
the honest relative-Kronecker pairing of the cup class against the explicit cross class, no `.mu`/`.cls`
opacity. -/
theorem cylinderDatum_mu_relCup23
    (a : Cohomology (TopCat.of (cylW M)) 2)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) :
    (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
        (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
      = relKroneckerH (cylBdW (M := M))
          (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          (cylFundClassCandidate (M := M) (m' := 2)) := by
  rw [cylinderDatum_mu_eq_funct]; rfl

/-- **The explicit `(1,4)` cup-pairing.** The `(1,4)`-degree mirror of `cylinderDatum_mu_relCup23`. -/
theorem cylinderDatum_mu_relCup14
    (a : Cohomology (TopCat.of (cylW M)) 1)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) :
    (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
        (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
      = relKroneckerH (cylBdW (M := M))
          (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          (cylFundClassCandidate (M := M) (m' := 2)) := by
  rw [cylinderDatum_mu_eq_funct]; rfl

/-! ## §3. The honest, fully explicit cap-cross projection residual (`.mu`/`.cls`-opacity-free)

The two `hproj{23,14}` the FIRE constructors consume, with the LHS `.mu`-wrapping rewritten by `§2`
into the explicit relative-Kronecker pairing against `[M] × [I,∂I]`. This is the fully explicit
chain-level statement the cap-cross projection arc discharges. -/

/-- **The `(2,3)` cap-cross projection residual — fully explicit.** `⟨a ∪ b, [M] × [I,∂I]⟩ =
⟨b, ((α a) ⌢ [M]) × [I,∂I]⟩`, `α = cylCollapse2` the contractible-collapse `H²(W) ≅ H²(M)`. The honest
form of `hproj23` after the Part-1 identification: no `.mu`, no `.cls`, no `Classical.choose`. -/
def CapCrossProjPairing23 (a : Cohomology (TopCat.of (cylW M)) 2)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) : Prop :=
  relKroneckerH (cylBdW (M := M))
      (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
      (cylFundClassCandidate (M := M) (m' := 2))
    = relKroneckerH (cylBd (M := M)) b
        (cylCrossH (M := M) 1 (capH 2 1 (cylCollapse2 a) (fundamentalClass (m := 2) (M := M))))

/-- **The `(1,4)` cap-cross projection residual — fully explicit.** The `(1,4)`-degree mirror of
`CapCrossProjPairing23`. -/
def CapCrossProjPairing14 (a : Cohomology (TopCat.of (cylW M)) 1)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) : Prop :=
  relKroneckerH (cylBdW (M := M))
      (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
      (cylFundClassCandidate (M := M) (m' := 2))
    = relKroneckerH (cylBd (M := M)) b
        (cylCrossH (M := M) 2 (capH 1 2 (cylCollapse1 a) (fundamentalClass (m := 2) (M := M))))

/-- **The `(2,3)` `hproj` value, DERIVED from the explicit cap-cross projection residual.** Chains the
`§2` datum-functional landing with the explicit residual: the `.mu`-wrapped `hproj23` the FIRE
constructors consume follows from the opacity-free `CapCrossProjPairing23`. -/
theorem hproj23_of_pairing
    (hpair : ∀ (a : Cohomology (TopCat.of (cylW M)) 2)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
        CapCrossProjPairing23 a b)
    (a : Cohomology (TopCat.of (cylW M)) 2)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) :
    (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
        (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
      = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 1 (capH 2 1 (cylCollapse2 a) (fundamentalClass (m := 2) (M := M)))) :=
  (cylinderDatum_mu_relCup23 a b).trans (hpair a b)

/-- **The `(1,4)` `hproj` value, DERIVED from the explicit cap-cross projection residual.** -/
theorem hproj14_of_pairing
    (hpair : ∀ (a : Cohomology (TopCat.of (cylW M)) 1)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
        CapCrossProjPairing14 a b)
    (a : Cohomology (TopCat.of (cylW M)) 1)
    (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) :
    (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
        (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
      = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 2 (capH 1 2 (cylCollapse1 a) (fundamentalClass (m := 2) (M := M)))) :=
  (cylinderDatum_mu_relCup14 a b).trans (hpair a b)

/-! ## §4. The opener constructors — residual = the two explicit cap-cross projection pairings -/

/-- **The `CylinderSuspIntertwineData` builder from the explicit cap-cross projection residual.**
Successor to `…CylinderSuspBij.CylinderSuspIntertwineData.ofCapCrossProj`: the two `.mu`-wrapped
projection values `hproj{23,14}` are replaced by the two `.mu`/`.cls`-opacity-free explicit pairings
`CapCrossProjPairing{23,14}` (derived back to `hproj` via `§3`). The residual is now the honest
cap-cross projection identity `⟨a ∪ b, [M] × [I,∂I]⟩ = ⟨b, ((α a) ⌢ [M]) × [I,∂I]⟩`. -/
def CylinderSuspIntertwineData.ofCapCrossPairing
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (hpair23 : ∀ (a : Cohomology (TopCat.of (cylW M)) 2)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
        CapCrossProjPairing23 a b)
    (hpair14 : ∀ (a : Cohomology (TopCat.of (cylW M)) 1)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
        CapCrossProjPairing14 a b) :
    CylinderSuspIntertwineData M :=
  CylinderSuspIntertwineData.ofCapCrossProj hM2 hM3 hM4
    (hproj23_of_pairing hpair23) (hproj14_of_pairing hpair14)

/-- **The FIRE opener — `CylinderWAdmPinned` from the explicit cap-cross projection residual.**
Successor to `…CylinderSuspBij.CylinderWAdmPinned.ofClosedPDSuspIntertwineProj` with the two
projection values replaced by the opacity-free explicit pairings. The Track-2 nondeg residual now reads
as the honest, chain-level cap-cross projection identity per leg (plus `hwu`, `basePD`, and `M`-side
finiteness). -/
def CylinderWAdmPinned.ofClosedPDSuspIntertwinePairing
    (findimM1 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 1))
    (findimM2 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 2))
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (basePD : Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3))
    (hpair23 : ∀ (a : Cohomology (TopCat.of (cylW M)) 2)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
        CapCrossProjPairing23 a b)
    (hpair14 : ∀ (a : Cohomology (TopCat.of (cylW M)) 1)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
        CapCrossProjPairing14 a b)
    (hwu : wuW2
      (cylinderP14 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs14 findimM1)
        (cylinder_findimRel14 (cylinder_findimRelHom14_of_base hM4 hM3))
        (CylinderSuspIntertwineData.ofCapCrossPairing hM2 hM3 hM4 hpair23 hpair14).nondeg14
        (cylinder_dimeq14_of_basePD hM3 basePD))
      (cylinderP23 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs23 findimM2)
        (cylinder_findimRel23 (cylinder_findimRelHom23_of_base hM3 hM2))
        (CylinderSuspIntertwineData.ofCapCrossPairing hM2 hM3 hM4 hpair23 hpair14).nondeg23
        (cylinder_dimeq23_holds hM2)) = 0) :
    CylinderWAdmPinned M :=
  CylinderWAdmPinned.ofClosedPDSuspIntertwine findimM1 findimM2 hM2 hM3 hM4
    (CylinderSuspIntertwineData.ofCapCrossPairing hM2 hM3 hM4 hpair23 hpair14) basePD hwu

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapCrossProj
