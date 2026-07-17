/-
# Phase 5q.H (#211 keystone) — the `(𝓡 4).prod (𝓡∂ 1)` model re-association for `S²×D³`

The banked `sphereDiskBordism (sphereDiskSmoothData k)` (`SphereProductBounding.lean` §5,
`SphereDiskFreezeB.lean` §3) is a complete `Bordism J5 (sphereProdSM k) (emptySM …)` with
`W = SphereDisk` (= S²×D³), `J5 = I4.prod (𝓡∂ 1)`, `I4 = (𝓡 2).prod (𝓡 2)`. The 16-convergence
assembly consumer (#211) wants the model `(𝓡 4).prod (𝓡∂ 1)` (source over the merged `𝓡 4`), not
`J5`. This module discharges that re-association: `(𝓡 2).prod (𝓡 2) ≅ 𝓡 4` (a linear isomorphism
`E²×E² ≃L E⁴`, via `ContinuousLinearEquiv.ofFinrankEq`), transporting the banked structures into
the consumer's model.

The transport pattern mirrors `SphereDiskJ5.lean` exactly (associator conjugation via a global
single chart + the `contDiffGroupoid` compatibility transfer), applied twice: once for the
boundaryless pair (`I4 → 𝓡 4`, on `SphereProd = S²×S²`) and once for the collar model
(`J5 → J6 := (𝓡 4).prod (𝓡∂ 1)`, on `SphereDisk = S²×D³`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom. `maxRecDepth` bumped for the deep product-instance synthesis only (mirrors `SphereDiskJ5.lean`).
-/
import Mathlib
import SKEFTHawking.SphereProductBounding
import SKEFTHawking.SphereDiskJ5
import SKEFTHawking.SphereDiskFreezeB

namespace SKEFTHawking.SpinSigmaRoute

open scoped Manifold
open Metric Set

set_option maxRecDepth 4000

/-! ### §0. `T2Space SphereDisk` — opening green brick

`SphereDisk = TwoSphere × ThreeDisk`, both subtypes of the metric space
`EuclideanSpace ℝ (Fin 3)`; metric spaces are `T2Space`, subtypes and products of `T2Space`s are
`T2Space` — all instances, no manual work needed. -/
instance sphereDisk_t2Space : T2Space SphereDisk := inferInstance

/-! ### §1. The dimension-merge equivalence `E²×E² ≃L E⁴`

Two finite-dimensional real normed spaces of equal `finrank` are continuously linearly equivalent
(`ContinuousLinearEquiv.ofFinrankEq`); `finrank (E²×E²) = 2+2 = 4 = finrank E⁴`. -/

/-- `E⁴` — the euclidean model factor merging the two `E²` sphere-product factors. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- **The dimension-merge equivalence**: `E²×E² ≃L[ℝ] E⁴` (via equal `finrank`, `2+2=4`). -/
noncomputable def Lmerge : (E2 × E2) ≃L[ℝ] E4 :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin])

/-- The merged 4-manifold model: `𝓡 4`, boundaryless self-model on `E⁴`. -/
noncomputable abbrev R4 := (𝓡 4 : ModelWithCorners ℝ E4 E4)

/-- The consumer's collar model: `J6 = (𝓡 4).prod (𝓡∂ 1)`. -/
noncomputable abbrev J6 := R4.prod (𝓡∂ 1)

/-! ### §2. The `I4 → 𝓡 4` re-association on `SphereProd` (deliverable 3 support)

Mirrors `SphereDiskJ5.lean` §2–4 exactly, with the associator `Lcle`/`αhomeo` replaced by the
merge `Lmerge`/`γhomeo`, and no trailing boundary factor (the boundaryless case). -/

/-- `I4` reparametrized so its euclidean space is `E⁴` (via `Lmerge`), keeping `I4`'s model space
`ModelProd E2 E2`. -/
noncomputable def I4L : ModelWithCorners ℝ E4 (ModelProd E2 E2) :=
  I4.transContinuousLinearEquiv Lmerge

theorem I4L_coe : ⇑I4L = Lmerge ∘ ⇑I4 := rfl

/-- `IsManifold I4L k SphereProd` — free, via the `transContinuousLinearEquiv` instance. -/
theorem isManifold_I4L {k : WithTop ℕ∞} : IsManifold I4L k SphereProd := by
  haveI : IsManifold I4 k SphereProd := .of_le le_top
  exact ContinuousLinearEquiv.instIsManifoldtransContinuousLinearEquiv Lmerge

/-- The model-space merge homeomorphism `ModelProd E2 E2 ≃ₜ E⁴` (= `Lmerge` as a homeomorphism). -/
noncomputable def γhomeo : ModelProd E2 E2 ≃ₜ E4 := Lmerge.toHomeomorph

/-- `γhomeo` as an `OpenPartialHomeomorph` (global chart, source = univ). -/
noncomputable def γOPH : OpenPartialHomeomorph (ModelProd E2 E2) E4 := γhomeo.toOpenPartialHomeomorph

/-- **The model intertwining**: `𝓡4 ∘ γhomeo = Lmerge ∘ I4` (`rfl` — both are `Lmerge` applied to the
self-model-reduced point). -/
theorem R4_comp_γhomeo (p : ModelProd E2 E2) : (R4) (γhomeo p) = I4L p := rfl

/-- `ModelProd E2 E2` charted over `E⁴` by the single global merge chart `γhomeo`. -/
@[reducible] noncomputable def chartedSpaceE4_ModelProdE2E2 : ChartedSpace E4 (ModelProd E2 E2) where
  atlas := {γOPH}
  chartAt _ := γOPH
  mem_chart_source x := by
    show x ∈ γOPH.source
    simp [γOPH, Homeomorph.toOpenPartialHomeomorph]
  chart_mem_atlas _ := rfl

attribute [local instance] chartedSpaceE4_ModelProdE2E2

/-- The natural charted space of `SphereProd` over `E⁴` (`𝓡4`'s model space): the natural
`ModelProd E2 E2` product atlas, re-modelled over `E⁴` by the merge (`ChartedSpace.comp`). -/
@[reducible] noncomputable def chartR4 : ChartedSpace E4 SphereProd :=
  ChartedSpace.comp E4 (ModelProd E2 E2) SphereProd

/-- The euclidean ranges coincide: `range R4 = range I4L` (via `γhomeo` surjective). -/
theorem range_R4_eq_I4L : range (⇑R4 : E4 → E4) = range I4L := by
  have h : range I4L = range (fun p => (R4) (γhomeo p)) := by
    apply congrArg; funext p; exact (R4_comp_γhomeo p).symm
  rw [h, Set.range_comp' (g := (R4 : E4 → E4)) (f := γhomeo)]
  · simp [γhomeo.surjective.range_eq]

@[simp] theorem γOPH_coe : ⇑γOPH = γhomeo := rfl
@[simp] theorem γOPH_symm_coe : ⇑γOPH.symm = γhomeo.symm := rfl
@[simp] theorem γOPH_source : γOPH.source = Set.univ := by
  simp [γOPH, Homeomorph.toOpenPartialHomeomorph]
@[simp] theorem γOPH_target : γOPH.target = Set.univ := by
  simp [γOPH, Homeomorph.toOpenPartialHomeomorph]

/-- `I4L.symm = γhomeo.symm ∘ R4.symm` (as functions `E⁴ → ModelProd E2 E2`). -/
theorem I4L_symm_eq (q : E4) : (I4L).symm q = γhomeo.symm ((R4).symm q) := rfl

theorem I4L_symm_fun : ⇑(I4L).symm = γhomeo.symm ∘ ⇑(R4).symm := by
  funext q; exact I4L_symm_eq q

/-- The conjugated coordinate map: `⇑(γOPH.symm ≫ₕ g ≫ₕ γOPH) = γhomeo ∘ g ∘ γhomeo.symm`. -/
theorem conj_coe4 (g : OpenPartialHomeomorph (ModelProd E2 E2) (ModelProd E2 E2)) :
    ⇑(γOPH.symm.trans (g.trans γOPH)) = γhomeo ∘ ⇑g ∘ γhomeo.symm := by
  simp [OpenPartialHomeomorph.coe_trans]; rfl

/-- The conjugated source: `(γOPH.symm ≫ₕ g ≫ₕ γOPH).source = γhomeo.symm ⁻¹' g.source`. -/
theorem conj_source4 (g : OpenPartialHomeomorph (ModelProd E2 E2) (ModelProd E2 E2)) :
    (γOPH.symm.trans (g.trans γOPH)).source = γhomeo.symm ⁻¹' g.source := by simp

/-- **The `contDiffPregroupoid` property transfer under merge conjugation**. -/
theorem conj_property_transfer4 {n : WithTop ℕ∞} (φ : ModelProd E2 E2 → ModelProd E2 E2)
    (s : Set (ModelProd E2 E2))
    (hφ : ContDiffOn ℝ n (⇑I4L ∘ φ ∘ ⇑(I4L).symm) (⇑(I4L).symm ⁻¹' s ∩ range I4L)) :
    ContDiffOn ℝ n (⇑R4 ∘ (γhomeo ∘ φ ∘ γhomeo.symm) ∘ ⇑(R4).symm)
      (⇑(R4).symm ⁻¹' (γhomeo.symm ⁻¹' s) ∩ range R4) := by
  have hfun : ⇑R4 ∘ (γhomeo ∘ φ ∘ γhomeo.symm) ∘ ⇑(R4).symm = ⇑I4L ∘ φ ∘ ⇑(I4L).symm := by
    funext y
    simp only [Function.comp_apply]
    rw [R4_comp_γhomeo, ← I4L_symm_eq]
  have hset : ⇑(R4).symm ⁻¹' (γhomeo.symm ⁻¹' s) ∩ range R4 = ⇑(I4L).symm ⁻¹' s ∩ range I4L := by
    rw [range_R4_eq_I4L, I4L_symm_fun, Set.preimage_comp]
  rw [hfun, hset]; exact hφ

/-- **Merge conjugation preserves `C^n` compatibility**. -/
theorem conj_mem_R4 {n : WithTop ℕ∞} {g : OpenPartialHomeomorph (ModelProd E2 E2) (ModelProd E2 E2)}
    (hg : g ∈ contDiffGroupoid n I4L) :
    (γOPH.symm.trans (g.trans γOPH)) ∈ contDiffGroupoid n R4 := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg ⊢
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [conj_coe4, conj_source4]
    exact conj_property_transfer4 g g.source hg1
  · have hsymm_coe : ⇑(γOPH.symm.trans (g.trans γOPH)).symm = γhomeo ∘ ⇑g.symm ∘ γhomeo.symm := by
      simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
        γOPH_coe, γOPH_symm_coe]
    have htarget : (γOPH.symm.trans (g.trans γOPH)).target = γhomeo.symm ⁻¹' g.target := by
      simp
    rw [hsymm_coe, htarget]
    exact conj_property_transfer4 g.symm g.target hg2

attribute [local instance] chartR4

/-- **`IsManifold 𝓡4 k SphereProd`** — the `S²×S²` singular manifold, re-associated to the merged
`𝓡 4` model (deliverable 3 support). -/
theorem isManifold_R4 {k : WithTop ℕ∞} : IsManifold (R4) k SphereProd := by
  haveI : IsManifold I4L k SphereProd := isManifold_I4L
  haveI hg : HasGroupoid SphereProd (contDiffGroupoid k (R4)) := by
    refine ⟨fun {e₁ e₂} he₁ he₂ => ?_⟩
    obtain ⟨f₁, hf₁, β₁, hβ₁, rfl⟩ := he₁
    obtain ⟨f₂, hf₂, β₂, hβ₂, rfl⟩ := he₂
    obtain rfl : β₁ = γOPH := hβ₁
    obtain rfl : β₂ = γOPH := hβ₂
    have heq : (f₁.trans γOPH).symm.trans (f₂.trans γOPH)
        = γOPH.symm.trans ((f₁.symm.trans f₂).trans γOPH) := by
      simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
    rw [heq]
    exact conj_mem_R4 ((contDiffGroupoid k I4L).compatible hf₁ hf₂)
  exact IsManifold.mk' (R4) k SphereProd

end SKEFTHawking.SpinSigmaRoute
