/-
# Phase 5q.H Track 2 — the cup-suspension intertwining with the α-side DISCHARGED, and the
# `nondeg`-free constructor `ofClosedPDSuspIntertwine`

The `CylinderWAdmPinned` residual-set (post `ofClosedPDNoDet`, `…InteriorChart`) is
`{nondeg14, nondeg23, hwu}` + `M`-intrinsic inputs. `PoincareLefschetzRelFundClassCylinderNondeg`
reduced each `nondeg` leg to ONE named **intertwining datum** `(α, β, hcompat)` — cohomology
equivalences on the two Poincaré–Lefschetz pairing arguments plus the cup-compatibility
`⟨a ∪ b, [W,∂W]⟩ = ⟨α a ∪ β b, [M]⟩` — consuming `M`'s own PD perfectness in-tree
(`nondeg_of_closed`/`nondeg13_of_closed`). This module TIGHTENS that reduction on the **α side** and
re-packages the residual honestly.

## What this module discharges: the α-side collapse equivalences (`§1`, `§2`)

For the reflexive cylinder `W = M × [0,1]` the FIRST pairing argument lives in the ABSOLUTE
cohomology `Hᵏ(W)`, and the collapse `Hᵏ(W) ≅ Hᵏ(M)` is the plain homotopy-equivalence pullback
(`W ≃ M`, contractible interval factor). This is NOT a wall: `SingularCohomologyHomotopy`'s
`prodContractibleCohomologyEquiv` (the cohomology mirror of `prodContractibleHomologyEquiv`) supplies
it explicitly. `cylCollapse2`/`cylCollapse1` are those equivalences (`.symm` of the `π*`-pullback,
`W → M`), and the reduced criteria `cylinder_nondeg{23,14}_of_suspIntertwine` PIN `α` to them — so the
`(α, β, hcompat)` intertwining datum loses its `α` free input: the residual per leg drops from
`{α-equiv, β-equiv, hcompat}` to `{β-equiv, hcompat}`.

## What remains — the SHARPEST residual: the β-suspension + cup-cross Fubini evaluation

The SECOND pairing argument lives in the RELATIVE cohomology `H^{5-k}(W,∂W)`; its identification with
`Hᵏ(M)` is the **suspension** iso `β` (cup with the `H¹(I,∂I)` generator), and the cup-compatibility
`hcompat` — with `[W,∂W] = [M] × [I,∂I]` now explicit (`hasRelFundClass_cylGen`, `crossH [M]`) — is the
evaluation of a product cup cochain against the prism/cross fundamental chain, i.e. the
**Eilenberg–Zilber / Künneth cross-product (Fubini) value** `⟨(π*u) ∪ (π*v ∪ e), [M]×[I,∂I]⟩ =
⟨u ∪ v, [M]⟩·⟨e,[I,∂I]⟩`. This substrate builds its cup/cap products FROM SCRATCH on the custom
`TopCat.toSSet` cochain model and, at the pinned Mathlib (`5e932f97`, v4.29.1), has NO cross-product /
Eilenberg–Zilber shuffle map, NO Künneth theorem, and NO cap-product projection-formula naturality —
this is the project's own recorded, kernel-checked recon (`SphereProdCrossInt`, slice-6: "a
multi-hundred-line new combinatorial development"; confirmed here by the absence of any relative
cup-pullback / cap-projection lemma in `SingularCohomologyFunctoriality` / `IntCapProductInt`). The
`αU ≠ 0` opacity mechanics that closed `hcls` are a *detection* argument (crossH nonvanishing via the
pair connecting map), NOT a multiplicative cup evaluation, so they do not transfer. **The sharpest
single named residual per leg is therefore `hcompat` (the β-suspended cup-cross Fubini identity); the
α side is discharged here.**

## The constructor (`§3`)

`CylinderSuspIntertwineData M` bundles the two residual legs `(β23, hcompat23)`, `(β14, hcompat14)`
(α already pinned); `CylinderWAdmPinned.ofClosedPDSuspIntertwine` is the `ofClosedPDNoDet` successor
consuming that bundle in place of the two raw `nondeg` injectivities. The residual-set VISIBLY shrinks:
`nondeg14`/`nondeg23` no longer appear; the geometrically-transparent suspension-intertwining data
(with the α-collapse discharged) + `hwu` + `M`-intrinsic inputs remain.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderNondeg
import SKEFTHawking.PinPlusCylinderInteriorChart
import SKEFTHawking.SingularCohomologyHomotopy

open scoped Manifold
open SKEFTHawking.PoincareLefschetzWuPairingCriterion
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNondeg
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCylinderWAdmPinned
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.SingularCohomologyHomotopy

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-! ## §1. The α-side collapse equivalences `Hᵏ(W) ≃ Hᵏ(M)` (the homotopy-equivalence pullback) -/

/-- **The degree-2 α-collapse** `H²(W) ≃ₗ[ZMod 2] H²(M)`. The `.symm` of the projection pullback
`π* : H²(M) ≃ H²(W)` (`prodContractibleCohomologyEquiv`, contractible `[0,1]` factor). This is the
first-argument identification of the cylinder `(2,3)` intertwining — discharged, not a free input. -/
def cylCollapse2 :
    Cohomology (TopCat.of (cylW M)) 2 ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 2 :=
  (prodContractibleCohomologyEquiv (TopCat.of M) (TopCat.of unitInterval) ⊥ iccContraction
    slice_iccContraction_zero slice_iccContraction_one 1).symm

/-- **The degree-1 α-collapse** `H¹(W) ≃ₗ[ZMod 2] H¹(M)`. The `.symm` of the projection pullback
`π* : H¹(M) ≃ H¹(W)`. First-argument identification of the cylinder `(1,4)` intertwining. -/
def cylCollapse1 :
    Cohomology (TopCat.of (cylW M)) 1 ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 1 :=
  (prodContractibleCohomologyEquiv (TopCat.of M) (TopCat.of unitInterval) ⊥ iccContraction
    slice_iccContraction_zero slice_iccContraction_one 0).symm

/-! ## §2. The `nondeg` criteria with the α-side pinned (residual per leg = `(β, hcompat)`) -/

/-- **The cylinder `(2,3)` non-degeneracy, α discharged.** Same as
`cylinder_nondeg23_of_intertwining` but with `α` PINNED to the collapse `cylCollapse2` — so the sole
residual is `(β, hcompat)`: the suspension iso `β : H³(W,∂W) ≃ H²(M)` and the cup-suspension
compatibility (the β-suspended Fubini identity for `[W,∂W] = [M]×[I,∂I]`). `M`'s middle-pairing
perfectness is consumed in-tree (`nondeg_of_closed`). -/
theorem cylinder_nondeg23_of_suspIntertwine [PreconnectedSpace M]
    (β : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3
      ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 2)
    (hcompat : ∀ (a : Cohomology (TopCat.of (cylW M)) 2)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
            (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = fundamentalFunctional (m := 2) (M := M) (cupH24 (cylCollapse2 a) (β b))) :
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu) :=
  cylinder_nondeg23_of_intertwining (hasRelFundClass_cylGen (m' := 2) (M := M))
    cylCollapse2 β hcompat

/-- **The cylinder `(1,4)` non-degeneracy, α discharged.** Same as
`cylinder_nondeg14_of_intertwining` but with `α` PINNED to the collapse `cylCollapse1` — sole residual
`(β, hcompat)` (suspension iso `β : H⁴(W,∂W) ≃ H³(M)` + the `(1,3)` cup-suspension compatibility).
`M`'s `(1,3)` perfectness is consumed in-tree (`nondeg13_of_closed`). -/
theorem cylinder_nondeg14_of_suspIntertwine [PreconnectedSpace M]
    (β : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4
      ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 3)
    (hcompat : ∀ (a : Cohomology (TopCat.of (cylW M)) 1)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
            (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = fundamentalFunctional (m := 2) (M := M) (cupH13 (cylCollapse1 a) (β b))) :
    Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu) :=
  cylinder_nondeg14_of_intertwining (hasRelFundClass_cylGen (m' := 2) (M := M))
    cylCollapse1 β hcompat

/-! ## §3. The bundled residual and the `nondeg`-free constructor `ofClosedPDSuspIntertwine` -/

variable [PreconnectedSpace M]

/-- **The bundled cup-suspension intertwining residual** (α discharged). The two residual legs of the
cylinder Poincaré–Lefschetz non-degeneracy, each a suspension iso `β` plus the cup-suspension
compatibility `hcompat` (with the α-collapse already pinned to `cylCollapse2`/`cylCollapse1`). This is
the sharpest honest residual isolated by this module: the `β`-suspension identification of the relative
pairing argument and the cup-cross **Fubini** evaluation `⟨a ∪ b, [M]×[I,∂I]⟩ = ⟨α a ∪ β b, [M]⟩` — the
missing Eilenberg–Zilber cross-product layer this substrate does not yet build. -/
structure CylinderSuspIntertwineData (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [PreconnectedSpace M] where
  /-- The `(2,3)` suspension iso `β : H³(W,∂W) ≃ H²(M)`. -/
  β23 : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3
      ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 2
  /-- The `(2,3)` cup-suspension compatibility (α pinned to `cylCollapse2`). -/
  hcompat23 : ∀ (a : Cohomology (TopCat.of (cylW M)) 2)
      (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
      (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
          (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
        = fundamentalFunctional (m := 2) (M := M) (cupH24 (cylCollapse2 a) (β23 b))
  /-- The `(1,4)` suspension iso `β : H⁴(W,∂W) ≃ H³(M)`. -/
  β14 : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4
      ≃ₗ[ZMod 2] Cohomology (TopCat.of M) 3
  /-- The `(1,4)` cup-suspension compatibility (α pinned to `cylCollapse1`). -/
  hcompat14 : ∀ (a : Cohomology (TopCat.of (cylW M)) 1)
      (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
      (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
          (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
        = fundamentalFunctional (m := 2) (M := M) (cupH13 (cylCollapse1 a) (β14 b))

/-- The `(2,3)` non-degeneracy derived from the bundled residual. -/
theorem CylinderSuspIntertwineData.nondeg23 (D : CylinderSuspIntertwineData M) :
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu) :=
  cylinder_nondeg23_of_suspIntertwine D.β23 D.hcompat23

/-- The `(1,4)` non-degeneracy derived from the bundled residual. -/
theorem CylinderSuspIntertwineData.nondeg14 (D : CylinderSuspIntertwineData M) :
    Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu) :=
  cylinder_nondeg14_of_suspIntertwine D.β14 D.hcompat14

/-- **The closed-manifold constructor, `nondeg`-FREE.** Identical to
`CylinderWAdmPinned.ofClosedPDNoDet` except the two raw `nondeg14`/`nondeg23` injectivity inputs are
replaced by ONE bundled `CylinderSuspIntertwineData M` (from which they are derived), with the α-side
collapse equivalences already discharged. The residual-set VISIBLY shrinks: `nondeg14`/`nondeg23` no
longer appear; the suspension-intertwining data (β + cup-suspension Fubini compat, α pinned) + `hwu` +
`M`-intrinsic inputs remain. -/
def CylinderWAdmPinned.ofClosedPDSuspIntertwine
    (findimM1 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 1))
    (findimM2 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 2))
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (D : CylinderSuspIntertwineData M)
    (basePD : Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3))
    (hwu : wuW2
      (cylinderP14 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs14 findimM1)
        (cylinder_findimRel14 (cylinder_findimRelHom14_of_base hM4 hM3)) D.nondeg14
        (cylinder_dimeq14_of_basePD hM3 basePD))
      (cylinderP23 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs23 findimM2)
        (cylinder_findimRel23 (cylinder_findimRelHom23_of_base hM3 hM2)) D.nondeg23
        (cylinder_dimeq23_holds hM2)) = 0) :
    CylinderWAdmPinned M :=
  CylinderWAdmPinned.ofClosedPDNoDet findimM1 findimM2 hM2 hM3 hM4 D.nondeg14 D.nondeg23 basePD hwu

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine
