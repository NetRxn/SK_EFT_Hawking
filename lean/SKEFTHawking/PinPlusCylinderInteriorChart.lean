/-
# Phase 5q.H Track 2 — the `E⁵`-charted-interior instance (the `hdet` CLOSER)

The triage module (`PinPlusCylinderWAdmPinnedTriage`) reduced the manifold-with-boundary
`hdet : determinedByPoints 5 (interiorSlab M)` to the SAME determination on the boundaryless open
interior `cylInterior M = M × (0,1)`, named as the single residual hypothesis `hdetU` of
`cylinder_hdet_of_interior` / `CylinderWAdmPinned.ofClosedPDInterior`. This module discharges that
residual outright:

* **§1** — a generic single-global-chart transport `chartedSpaceOfHomeomorph`: a homeomorphism
  `e : X ≃ₜ H` gives `X` a `ChartedSpace H` structure (mirrors `SphereDiskJ5.chartedSpaceHB_HA`, but
  for a plain `ChartedSpace` — no `IsManifold`/groupoid compatibility is needed here).
* **§2** — the open interval `(0,1)` is `E¹`-charted: `Opens.instChartedSpace` gives it `ℝ`-charted
  (open subset of `ℝ` self-charted), then `ChartedSpace.comp` re-models along the canonical linear
  equiv `ℝ ≃L E¹` (`EuclideanSpace.equiv` + `ContinuousLinearEquiv.funUnique`).
* **§3** — `M × (0,1)` is `E⁵`-charted: `Prod.chartedSpace` (`ModelProd E⁴ E¹`), then `ChartedSpace.comp`
  re-associates along the project's OWN cylinder interior-chart equiv `εcyl 2 : E⁴×E¹ ≃L E⁵`
  (`PoincareLefschetzRelFundClassCylinder.εcyl`, reused verbatim — no new linear-equiv content).
* **§4** — the interior `↥(cylInterior M)` is literally `M × (0,1)` up to bookkeeping (forget/restore
  the `Set.Icc` membership half of the interval coordinate): the homeomorphism
  `cylInteriorProdEquiv` transports the `E⁵` charted structure onto it.
* **§5** — `slabInInterior M` is compact: `interiorSlab M` is compact in `cylW M`
  (`isCompact_interiorSlab`) and sits inside `cylInterior M`
  (`interiorSlab_subset_cylInterior`), so its preimage under the embedding
  `Subtype.val : ↥(cylInterior M) → cylW M` is compact
  (`Topology.IsEmbedding.isCompact_iff` + `Set.image_preimage_eq_of_subset`).
* **§6** — **`hdet` fully discharged, unconditionally**: `goodCompact_compact` (any compact subset of a
  boundaryless `E⁵`-charted manifold is `goodCompact`) applied to `slabInInterior M`, `.2`-projected to
  `determinedByPoints`, composed with `cylinder_hdet_of_interior`. The residual-set of
  `CylinderWAdmPinned` is refined accordingly: `ofClosedPDNoDet` drops the `hdetU` hypothesis entirely,
  leaving exactly `{nondeg14, nondeg23, hwu}` + the `M`-intrinsic named inputs.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusCylinderWAdmPinnedTriage

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

/-! ## §1. A generic single-global-chart `ChartedSpace` transport -/

/-- **A homeomorphism transports a `ChartedSpace` structure.** `e : X ≃ₜ H` gives `X` a
`ChartedSpace H` structure by the single global chart `e` (atlas a singleton). Mirrors
`SphereDiskJ5.chartedSpaceHB_HA` — no `IsManifold`/groupoid compatibility needed for plain
`ChartedSpace`. -/
@[reducible] def chartedSpaceOfHomeomorph {X H : Type*} [TopologicalSpace X] [TopologicalSpace H]
    (e : X ≃ₜ H) : ChartedSpace H X where
  atlas := {e.toOpenPartialHomeomorph}
  chartAt _ := e.toOpenPartialHomeomorph
  mem_chart_source _ := by simp [Homeomorph.toOpenPartialHomeomorph]
  chart_mem_atlas _ := rfl

/-! ## §2. The open interval `(0,1)` is `E¹`-charted -/

/-- `E¹` — the euclidean model factor of the interval coordinate. -/
abbrev E1 := EuclideanSpace ℝ (Fin 1)

/-- `ℝ ≃L[ℝ] E¹` — the canonical 1-dimensional linear equivalence. -/
def RtoE1 : ℝ ≃L[ℝ] E1 :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- `ℝ` is `E¹`-charted via the global linear-equiv chart. -/
instance instChartedSpaceE1R : ChartedSpace E1 ℝ :=
  chartedSpaceOfHomeomorph RtoE1.toHomeomorph

/-- The open interval `(0,1)` is `ℝ`-charted (an open subset of `ℝ`, self-charted). -/
instance instChartedSpaceROpenInterval : ChartedSpace ℝ ↥(Set.Ioo (0 : ℝ) 1) :=
  TopologicalSpace.Opens.instChartedSpace ⟨Set.Ioo (0 : ℝ) 1, isOpen_Ioo⟩

/-- The open interval `(0,1)` is `E¹`-charted (compose the two structures above). -/
instance instChartedSpaceE1OpenInterval : ChartedSpace E1 ↥(Set.Ioo (0 : ℝ) 1) :=
  ChartedSpace.comp E1 ℝ ↥(Set.Ioo (0 : ℝ) 1)

/-! ## §3. `M × (0,1)` is `E⁵`-charted -/

/-- `M × (0,1)` is `ModelProd E⁴ E¹`-charted (the product charted-space instance). -/
instance instChartedSpaceProdMIoo :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (2 + 2))) E1) (M × ↥(Set.Ioo (0 : ℝ) 1)) :=
  inferInstance

/-- `E⁴×E¹ ≃L E⁵` charts `ModelProd E⁴ E¹` over `E⁵` — reusing the project's OWN cylinder
interior-chart equiv `εcyl 2` (`PoincareLefschetzRelFundClassCylinder`), no new linear-equiv content. -/
instance instChartedSpaceE5ModelProd :
    ChartedSpace (EuclideanSpace ℝ (Fin 5)) (ModelProd (EuclideanSpace ℝ (Fin (2 + 2))) E1) :=
  chartedSpaceOfHomeomorph (εcyl 2).toHomeomorph

/-- `M × (0,1)` is `E⁵`-charted (associate via `ChartedSpace.comp`). -/
instance instChartedSpaceE5ProdMIoo :
    ChartedSpace (EuclideanSpace ℝ (Fin 5)) (M × ↥(Set.Ioo (0 : ℝ) 1)) :=
  ChartedSpace.comp (EuclideanSpace ℝ (Fin 5))
    (ModelProd (EuclideanSpace ℝ (Fin (2 + 2))) E1) (M × ↥(Set.Ioo (0 : ℝ) 1))

/-! ## §4. `↥(cylInterior M)` reassociated as `M × (0,1)`, and its `E⁵` chart -/

/-- **The interior reassociated**: `↥(cylInterior M) ≃ₜ M × (0,1)` — forgetting/restoring the
`Set.Icc 0 1` membership half of the interval coordinate (its value already lies in `(0,1)` by
`cylInterior`'s defining inequality, so the two subtype bookkeepings carry the same information). -/
def cylInteriorProdEquiv : ↥(cylInterior M) ≃ₜ (M × ↥(Set.Ioo (0 : ℝ) 1)) where
  toFun p := (p.1.1, ⟨(p.1.2 : ℝ), p.2.1, p.2.2⟩)
  invFun q := ⟨(q.1, ⟨q.2.1, le_of_lt q.2.2.1, le_of_lt q.2.2.2⟩), q.2.2.1, q.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
      (Continuous.subtype_mk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)) _)
  continuous_invFun :=
    Continuous.subtype_mk
      (Continuous.prodMk continuous_fst
        (Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _)) _

/-- `↥(cylInterior M)` is `(M × (0,1))`-charted (the reassociation homeomorphism, as a chart). -/
instance instChartedSpaceProdMIooCylInterior :
    ChartedSpace (M × ↥(Set.Ioo (0 : ℝ) 1)) ↥(cylInterior M) :=
  chartedSpaceOfHomeomorph cylInteriorProdEquiv

/-- **The `E⁵`-charted-interior instance** — the sole residual named by the triage module's
`hdetU`/`ofClosedPDInterior`, discharged: `↥(cylInterior M)` is a boundaryless `E⁵`-charted space,
composing `instChartedSpaceProdMIooCylInterior` with `instChartedSpaceE5ProdMIoo`. -/
instance instChartedSpaceE5CylInterior : ChartedSpace (EuclideanSpace ℝ (Fin 5)) ↥(cylInterior M) :=
  ChartedSpace.comp (EuclideanSpace ℝ (Fin 5)) (M × ↥(Set.Ioo (0 : ℝ) 1)) ↥(cylInterior M)

/-! ## §5. `slabInInterior M` is compact -/

omit [T2Space M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] in
/-- **`slabInInterior M` is compact.** `interiorSlab M` is compact in `cylW M`
(`isCompact_interiorSlab`) and lies inside `cylInterior M`
(`interiorSlab_subset_cylInterior`); pulling back along the (topological) embedding
`Subtype.val : ↥(cylInterior M) → cylW M` preserves compactness
(`Topology.IsEmbedding.isCompact_iff`), since the image of the preimage recovers `interiorSlab M`
exactly (`Set.image_preimage_eq_of_subset`, as `interiorSlab M ⊆ range Subtype.val = cylInterior M`). -/
theorem isCompact_slabInInterior : IsCompact (slabInInterior M) := by
  have hsub : interiorSlab M ⊆ Set.range (Subtype.val : ↥(cylInterior M) → cylW M) := by
    rw [Subtype.range_val]
    exact interiorSlab_subset_cylInterior
  have himg : (Subtype.val : ↥(cylInterior M) → cylW M) '' (slabInInterior M) = interiorSlab M :=
    Set.image_preimage_eq_of_subset hsub
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]
  exact isCompact_interiorSlab

/-! ## §6. `hdet` fully discharged (unconditionally), and the constructor refinement -/

omit [Nonempty M] in
/-- **`hdetU` discharged.** `slabInInterior M` is a compact subset of the boundaryless `E⁵`-charted
interior `↥(cylInterior M)`, so `goodCompact_compact` applies; its `determinedByPoints` half is
exactly the residual the triage module named `hdetU`. -/
theorem cylinder_hdetU :
    determinedByPoints (X := cylInteriorTop M) (2 + 1 + 2) (slabInInterior M) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (3 + 2))) ↥(cylInterior M) :=
    instChartedSpaceE5CylInterior
  exact (goodCompact_compact (m := 3) isCompact_slabInInterior).2

omit [Nonempty M] in
/-- **`hdet` fully discharged, unconditionally** — the `hdet` CLOSER. Combines
`cylinder_hdetU` (the interior determination, now a theorem, not a hypothesis) with
`cylinder_hdet_of_interior` (the excision transport back to the manifold-with-boundary `W`). -/
theorem cylinder_hdet [T1Space (cylW M)] :
    determinedByPoints (X := TopCat.of (cylW M)) (2 + 1 + 2) (interiorSlab M) :=
  cylinder_hdet_of_interior cylinder_hdetU

/-- **The closed-manifold + Poincaré-duality constructor, `hdet`-FREE.** Identical to
`CylinderWAdmPinned.ofClosedPDInterior` except the `hdetU` hypothesis is dropped entirely — it is
now supplied unconditionally by `cylinder_hdetU`. The residual-set VISIBLY shrinks to exactly
`{nondeg14, nondeg23, hwu}` plus the `M`-intrinsic named inputs; `hdet` no longer appears. -/
def CylinderWAdmPinned.ofClosedPDNoDet [PreconnectedSpace M]
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
    (hwu : wuW2
      (cylinderP14 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs14 findimM1)
        (cylinder_findimRel14 (cylinder_findimRelHom14_of_base hM4 hM3)) nondeg14
        (cylinder_dimeq14_of_basePD hM3 basePD))
      (cylinderP23 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs23 findimM2)
        (cylinder_findimRel23 (cylinder_findimRelHom23_of_base hM3 hM2)) nondeg23
        (cylinder_dimeq23_holds hM2)) = 0) :
    CylinderWAdmPinned M :=
  CylinderWAdmPinned.ofClosedPDInterior findimM1 findimM2 hM2 hM3 hM4 nondeg14 nondeg23 basePD
    cylinder_hdetU hwu

end

end SKEFTHawking.PinPlusCylinderWAdmPinned
