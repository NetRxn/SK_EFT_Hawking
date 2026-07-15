/-
# Phase 5q.H W-A arm 4 — the `hdet`/`hwu` residual TRIAGE for `CylinderWAdmPinned`

Two of the residual fields of `CylinderWAdmPinned M` (`…/PinPlusCylinderWAdmPinned.lean`) are triaged
here — honest reductions of the manifold-with-boundary `hdet`, and the honest-content statement of
`hwu` — using the two general Hatcher-3.27 bricks of `SingularGoodCompactCompactExcision`.

## `hdet` — REDUCED to the boundaryless interior (`cylinder_hdet_of_interior`, `ofClosedPDInterior`)

`hdet : determinedByPoints 5 (interiorSlab M)` lives in `W = M × [0,1]`, a manifold-WITH-boundary, to
which NO in-tree good-compact machinery applies. §2 reduces it — via
`SingularGoodCompactCompactExcision.determinedByPoints_of_open_excision` (excise the boundary `∂W`,
which is disjoint from the interior slab) — to the SAME determination on the boundaryless open interior
`cylInterior M = M × (0,1)`:

    `cylinder_hdet_of_interior : determinedByPoints 5 (Subtype.val ⁻¹' interiorSlab) (in ↥(M×(0,1)))
                                   → hdet`.

The reduced target is strictly more tractable: the interior is a boundaryLESS `5`-manifold, so
`SingularGoodCompactCompactExcision.goodCompact_compact` (arbitrary compact good-compact) discharges it
outright ONCE the interior carries a boundaryless Euclidean charted structure — the sole remaining
residual (the `E⁵`-charted-interior instance, a standard `ModelProd`→`E⁵` transport). The constructor
`CylinderWAdmPinned.ofClosedPDInterior` swaps the `hdet` field for this interior determination, so the
residual-set VISIBLY replaces a boundary-manifold determination with a boundaryless-interior one.

## `hwu` — its honest content is the cylinder Wu formula (`wuFormula`)

`hwu : wuW2 P14 P23 = 0` is, over the substrate-pinned cylinder data, a genuine `w₂(W) = 0`. §3
extracts its honest equivalent via `PoincareLefschetzWu5.wuW2_eq_zero_iff`:

    `wuFormula : wuClassW2 P23 = wuClassW1 P14 ∪ wuClassW1 P14`   (i.e. `v₂(W) = v₁(W)²`).

The FULL `M`-intrinsic reduction (`v₂(W), v₁(W)²` ← `M`'s own Wu/`w₂` classes) additionally needs a
Steenrod-square SUSPENSION naturality — `Sq` commuting with the pair-suspension isos
`Hᵏ(W,∂W) ≅ Hᵏ⁻¹(M)` — which is NOT in the tree (`SingularRelativeSteenrodSq2` provides only the
pair-restriction naturality `relToAbs_relSq2`, not product/suspension naturality). That sharp missing
brick is named, not faked.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusCylinderWAdmPinned
import SKEFTHawking.SingularGoodCompactCompactExcision

open scoped Manifold
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCylinderWAdmPinned
open SKEFTHawking.SingularGoodCompactCompactExcision

namespace SKEFTHawking.PinPlusCylinderWAdmPinned

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-! ## §1. The open interior `cylInterior M = M × (0,1)` and its geometry -/

/-- **The cylinder's open interior** `M × (0,1)` — the boundaryless open set carrying the interior
slab, and the excision target for `hdet`. -/
def cylInterior (M : Type) [TopologicalSpace M] : Set (cylW M) :=
  {p | (0 : ℝ) < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}

/-- The interior as a `TopCat` (the ambient of the reduced determination), with the carrier `X`
pinned to `TopCat.of (cylW M)` so `sub` does not leave a carrier metavariable. -/
abbrev cylInteriorTop (M : Type) [TopologicalSpace M] : TopCat :=
  sub (X := TopCat.of (cylW M)) (cylInterior M)

/-- The interior slab, viewed inside the interior subtype `↥(cylInterior M)` — the reduced
determination target `Subtype.val ⁻¹' (interiorSlab M)`, with its type pinned to avoid a carrier
metavariable. -/
def slabInInterior (M : Type) [TopologicalSpace M] : Set ↑(cylInteriorTop M) :=
  Subtype.val ⁻¹' (interiorSlab M)

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] in
/-- The interior is open (preimage of `(0,1)` under the continuous interval coordinate). -/
theorem cylInterior_open : IsOpen (cylInterior M) := by
  have hc : Continuous (fun p : cylW M => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] in
/-- The interior slab `M × [¼,¾]` lies inside the open interior `M × (0,1)`. -/
theorem interiorSlab_subset_cylInterior : interiorSlab M ⊆ cylInterior M := by
  intro p hp
  simp only [interiorSlab, Set.mem_setOf_eq] at hp
  exact ⟨by linarith [hp.1], by linarith [hp.2]⟩

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] in
/-- The interior slab is closed in the cylinder. -/
theorem isClosed_interiorSlab : IsClosed (interiorSlab M) := by
  have hc : Continuous (fun p : cylW M => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

/-! ## §2. `hdet` reduced to the boundaryless-interior determination -/

omit [T2Space M] [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] in
/-- **`hdet` reduces to the interior determination.** The Wall-2 slab determinedness `hdet`
(`determinedByPoints 5 (interiorSlab M)` in `W = M × [0,1]`) follows from the SAME degree-5
determination on the boundaryless open interior `cylInterior M = M × (0,1)`, via
`determinedByPoints_of_open_excision` (excise `∂W`, disjoint from the slab). The reduced hypothesis is
on a boundaryless `5`-manifold, where `goodCompact_compact` applies once the interior carries a
Euclidean charted structure. -/
theorem cylinder_hdet_of_interior [T1Space (cylW M)]
    (hdetU : determinedByPoints (X := cylInteriorTop M) (2 + 1 + 2)
      (slabInInterior M)) :
    determinedByPoints (X := TopCat.of (cylW M)) (2 + 1 + 2) (interiorSlab M) :=
  determinedByPoints_of_open_excision (X := TopCat.of (cylW M))
    isClosed_interiorSlab cylInterior_open interiorSlab_subset_cylInterior hdetU

/-- **The closed-manifold + Poincaré-duality + INTERIOR-determination constructor.** Identical to
`CylinderWAdmPinned.ofClosedPD` except the Wall-2 residual is supplied as the boundaryless-interior
determination `hdetU` (discharged into the boundary-manifold `hdet` by `cylinder_hdet_of_interior`).
This visibly shrinks the residual-set: the manifold-with-boundary determination `hdet` is replaced by
the strictly-more-tractable boundaryless-interior determination, to which `goodCompact_compact`
applies. -/
def CylinderWAdmPinned.ofClosedPDInterior [PreconnectedSpace M]
    (findimM1 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 1))
    (findimM2 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 2))
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (nondeg14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu))
    (nondeg23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu))
    (basePD : Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3))
    (hdetU : determinedByPoints (X := cylInteriorTop M) (2 + 1 + 2)
      (slabInInterior M))
    (hwu : wuW2
      (cylinderP14 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs14 findimM1)
        (cylinder_findimRel14 (cylinder_findimRelHom14_of_base hM4 hM3)) nondeg14
        (cylinder_dimeq14_of_basePD hM3 basePD))
      (cylinderP23 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs23 findimM2)
        (cylinder_findimRel23 (cylinder_findimRelHom23_of_base hM3 hM2)) nondeg23
        (cylinder_dimeq23_holds hM2)) = 0) :
    CylinderWAdmPinned M :=
  CylinderWAdmPinned.ofClosedPD findimM1 findimM2 hM2 hM3 hM4 nondeg14 nondeg23 basePD
    (cylinder_hdet_of_interior hdetU) hwu

/-! ## §3. `hwu` — the honest cylinder Wu formula `v₂(W) = v₁(W)²` -/

variable (W : CylinderWAdmPinned M)

/-- **The cylinder satisfies the Wu formula** `v₂(W) = v₁(W)²`. The honest content of the admissibility
field `hwu : wuW2 P14 P23 = 0`, extracted via `PoincareLefschetzWu5.wuW2_eq_zero_iff`: since the data
are substrate-pinned (`W.pin14`/`W.pin23`), `v₂ = wuClassW2 P23` and `v₁ = wuClassW1 P14` are the honest
Lefschetz duals of `⟨relSq² ·, [W,∂W]⟩` / `⟨relSq¹ ·, [W,∂W]⟩`, and their equality `v₂ = v₁²` is a
genuine relation between two independently-defined classes — NOT a free-`sqOp` artefact. -/
theorem CylinderWAdmPinned.wuFormula :
    wuClassW2 W.P23 = cupH (wuClassW1 W.P14) (wuClassW1 W.P14) :=
  (wuW2_eq_zero_iff W.P14 W.P23).mp W.hwu'

/-- **`hwu` is EQUIVALENT to the cylinder Wu formula** `v₂(W) = v₁(W)²` (`wuW2_eq_zero_iff`
instantiated at the derived cylinder data). Documents the honest content of the `hwu` residual: it is
exactly the degree-`(2,3)`↔`(1,4)` Wu equation for the cylinder pair, the shape the eventual
spin/empty-Σ consumers supply. -/
theorem CylinderWAdmPinned.hwu_iff_wuFormula :
    wuW2 W.P14 W.P23 = 0 ↔ wuClassW2 W.P23 = cupH (wuClassW1 W.P14) (wuClassW1 W.P14) :=
  wuW2_eq_zero_iff W.P14 W.P23

end

end SKEFTHawking.PinPlusCylinderWAdmPinned
