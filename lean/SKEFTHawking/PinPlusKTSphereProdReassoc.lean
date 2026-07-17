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
open Metric Set SKEFTHawking.BordismTheory

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

/-! ### §3. `sphereProdSM4` — the `S²×S²` source re-associated to `𝓡 4` (deliverable 3) -/

/-- **`S²×S²` as an absolute singular manifold over the merged `𝓡 4` model** (the consumer's source
model, `X = PUnit`). Transport of `sphereProdSM k` along `Lmerge`. -/
noncomputable def sphereProdSM4 (k : WithTop ℕ∞) : SingularManifold PUnit k (R4) :=
  haveI : IsManifold (R4) k SphereProd := isManifold_R4
  ⟨SphereProd, fun _ => PUnit.unit, continuous_const⟩

/-! ### §4. The `J5 → J6` re-association on `SphereDisk` (deliverable 2)

Same pattern as §2, threaded through the trailing boundary factor `𝓡∂ 1`: the euclidean-space
merge `Lcle2 = Lmerge.prodCongr (refl E1)` and the model-space merge
`βhomeo = γhomeo.prodCongr (refl HH)`, both acting only on the first (`E²×E²`/`ModelProd E2 E2`)
factor and fixing the boundary factor. -/

/-- `J5`'s euclidean space `(E²×E²)×E¹` merged to `J6`'s euclidean space `E⁴×E¹` (first factor
only). -/
noncomputable def Lcle2 : ((E2 × E2) × E1) ≃L[ℝ] (E4 × E1) :=
  Lmerge.prodCongr (ContinuousLinearEquiv.refl ℝ E1)

/-- `J5` reparametrized so its euclidean space is `J6`'s (`E⁴×E¹`), keeping `J5`'s model space
`HB = ModelProd (ModelProd E2 E2) HH`. -/
noncomputable def J6L : ModelWithCorners ℝ (E4 × E1) HB :=
  J5.transContinuousLinearEquiv Lcle2

theorem J6L_coe : ⇑J6L = Lcle2 ∘ ⇑J5 := rfl

attribute [local instance] SKEFTHawking.SpinSigmaRoute.chartW

/-- `IsManifold J6L k SphereDisk` — free, via the `transContinuousLinearEquiv` instance and the
banked `isManifold_J5`. -/
theorem isManifold_J6L {k : WithTop ℕ∞} : IsManifold J6L k SphereDisk := by
  haveI : IsManifold J5 k SphereDisk := isManifold_J5
  exact ContinuousLinearEquiv.instIsManifoldtransContinuousLinearEquiv Lcle2

/-- `J6`'s model space `HC = ModelProd E4 HH` (`= E⁴×HH`). -/
abbrev HC := ModelProd E4 HH

/-- The model-space merge homeomorphism `HB ≃ₜ HC` (merge on the first factor, identity on the
boundary factor). -/
noncomputable def βhomeo : HB ≃ₜ HC := γhomeo.prodCongr (Homeomorph.refl HH)

/-- `βhomeo` as an `OpenPartialHomeomorph` (global chart, source = univ). -/
noncomputable def βOPH : OpenPartialHomeomorph HB HC := βhomeo.toOpenPartialHomeomorph

/-- **The model intertwining**: `J6 ∘ βhomeo = J6L` (`rfl`). -/
theorem J6_comp_βhomeo (p : HB) : (J6) (βhomeo p) = J6L p := rfl

/-- `HB` charted over `HC` by the single global merge chart `βhomeo`. -/
@[reducible] noncomputable def chartedSpaceHC_HB : ChartedSpace HC HB where
  atlas := {βOPH}
  chartAt _ := βOPH
  mem_chart_source x := by
    show x ∈ βOPH.source
    simp [βOPH, Homeomorph.toOpenPartialHomeomorph]
  chart_mem_atlas _ := rfl

attribute [local instance] chartedSpaceHC_HB

/-- The natural charted space of `SphereDisk` over `HC` (`J6`'s model space): `J5`'s `HB`-atlas
(`chartW`, `SphereDiskJ5.lean`), re-modelled over `HC` by the merge (`ChartedSpace.comp`). -/
@[reducible] noncomputable def chartW6 : ChartedSpace HC SphereDisk :=
  ChartedSpace.comp HC HB SphereDisk

/-- The euclidean ranges coincide: `range J6 = range J6L` (via `βhomeo` surjective). -/
theorem range_J6_eq_J6L : range (⇑J6) = range J6L := by
  have h : range J6L = range (fun p => (J6) (βhomeo p)) := by
    apply congrArg; funext p; exact (J6_comp_βhomeo p).symm
  rw [h, Set.range_comp' (g := (J6)) (f := βhomeo)]
  · simp [βhomeo.surjective.range_eq]

@[simp] theorem βOPH_coe : ⇑βOPH = βhomeo := rfl
@[simp] theorem βOPH_symm_coe : ⇑βOPH.symm = βhomeo.symm := rfl
@[simp] theorem βOPH_source : βOPH.source = Set.univ := by
  simp [βOPH, Homeomorph.toOpenPartialHomeomorph]
@[simp] theorem βOPH_target : βOPH.target = Set.univ := by
  simp [βOPH, Homeomorph.toOpenPartialHomeomorph]

/-- `J6L.symm = βhomeo.symm ∘ J6.symm` (as functions `E⁴×E¹ → HB`). -/
theorem J6L_symm_eq (q : E4 × E1) : (J6L).symm q = βhomeo.symm ((J6).symm q) := rfl

theorem J6L_symm_fun : ⇑(J6L).symm = βhomeo.symm ∘ ⇑(J6).symm := by
  funext q; exact J6L_symm_eq q

/-- The conjugated coordinate map: `⇑(βOPH.symm ≫ₕ g ≫ₕ βOPH) = βhomeo ∘ g ∘ βhomeo.symm`. -/
theorem conj_coe6 (g : OpenPartialHomeomorph HB HB) :
    ⇑(βOPH.symm.trans (g.trans βOPH)) = βhomeo ∘ ⇑g ∘ βhomeo.symm := by
  simp [OpenPartialHomeomorph.coe_trans]; rfl

/-- The conjugated source: `(βOPH.symm ≫ₕ g ≫ₕ βOPH).source = βhomeo.symm ⁻¹' g.source`. -/
theorem conj_source6 (g : OpenPartialHomeomorph HB HB) :
    (βOPH.symm.trans (g.trans βOPH)).source = βhomeo.symm ⁻¹' g.source := by simp

/-- **The `contDiffPregroupoid` property transfer under merge conjugation**. -/
theorem conj_property_transfer6 {n : WithTop ℕ∞} (φ : HB → HB) (s : Set HB)
    (hφ : ContDiffOn ℝ n (⇑J6L ∘ φ ∘ ⇑(J6L).symm) (⇑(J6L).symm ⁻¹' s ∩ range J6L)) :
    ContDiffOn ℝ n (⇑J6 ∘ (βhomeo ∘ φ ∘ βhomeo.symm) ∘ ⇑(J6).symm)
      (⇑(J6).symm ⁻¹' (βhomeo.symm ⁻¹' s) ∩ range J6) := by
  have hfun : ⇑J6 ∘ (βhomeo ∘ φ ∘ βhomeo.symm) ∘ ⇑(J6).symm = ⇑J6L ∘ φ ∘ ⇑(J6L).symm := by
    funext y
    simp only [Function.comp_apply]
    rw [J6_comp_βhomeo, ← J6L_symm_eq]
  have hset : ⇑(J6).symm ⁻¹' (βhomeo.symm ⁻¹' s) ∩ range J6 = ⇑(J6L).symm ⁻¹' s ∩ range J6L := by
    rw [range_J6_eq_J6L, J6L_symm_fun, Set.preimage_comp]
  rw [hfun, hset]; exact hφ

/-- **Merge conjugation preserves `C^n` compatibility**. -/
theorem conj_mem_J6 {n : WithTop ℕ∞} {g : OpenPartialHomeomorph HB HB}
    (hg : g ∈ contDiffGroupoid n J6L) :
    (βOPH.symm.trans (g.trans βOPH)) ∈ contDiffGroupoid n J6 := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg ⊢
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [conj_coe6, conj_source6]
    exact conj_property_transfer6 g g.source hg1
  · have hsymm_coe : ⇑(βOPH.symm.trans (g.trans βOPH)).symm = βhomeo ∘ ⇑g.symm ∘ βhomeo.symm := by
      simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
        βOPH_coe, βOPH_symm_coe]
    have htarget : (βOPH.symm.trans (g.trans βOPH)).target = βhomeo.symm ⁻¹' g.target := by
      simp
    rw [hsymm_coe, htarget]
    exact conj_property_transfer6 g.symm g.target hg2

attribute [local instance] chartW6

/-- **`IsManifold J6 k SphereDisk`** — `S²×D³`'s manifold structure, re-associated from the banked
`J5` structure to the consumer's `J6 = (𝓡 4).prod (𝓡∂ 1)` model (deliverable 2). -/
theorem isManifold_J6 {k : WithTop ℕ∞} : IsManifold (J6) k SphereDisk := by
  haveI : IsManifold J6L k SphereDisk := isManifold_J6L
  haveI hg : HasGroupoid SphereDisk (contDiffGroupoid k (J6)) := by
    refine ⟨fun {e₁ e₂} he₁ he₂ => ?_⟩
    obtain ⟨f₁, hf₁, β₁, hβ₁, rfl⟩ := he₁
    obtain ⟨f₂, hf₂, β₂, hβ₂, rfl⟩ := he₂
    obtain rfl : β₁ = βOPH := hβ₁
    obtain rfl : β₂ = βOPH := hβ₂
    have heq : (f₁.trans βOPH).symm.trans (f₂.trans βOPH)
        = βOPH.symm.trans ((f₁.symm.trans f₂).trans βOPH) := by
      simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
    rw [heq]
    exact conj_mem_J6 ((contDiffGroupoid k J6L).compatible hf₁ hf₂)
  exact IsManifold.mk' (J6) k SphereDisk

/-! ### §5. Transporting `sphereDiskIncl`'s smoothness to `(𝓡 4, J6)` (deliverable 4 support) -/

/-- The extended chart of the merged `R4` atlas is the natural `I4` extended chart post-composed
with `Lmerge` (pointwise, mirrors `extChartAt_J5_apply`). -/
theorem extChartAt_R4_apply (q z : SphereProd) :
    (extChartAt (R4) q) z = Lmerge ((extChartAt I4 q) z) := by
  rw [extChartAt_coe, Function.comp_apply, extChartAt_coe, Function.comp_apply]
  exact R4_comp_γhomeo _

/-- The merged and natural extended charts of `SphereProd` share the same source. -/
theorem extChartAt_R4_source (q : SphereProd) :
    (extChartAt (R4) q).source = (extChartAt I4 q).source := by
  rw [extChartAt_source, extChartAt_source]
  show ((chartAt (ModelProd E2 E2) q).trans γOPH).source = (chartAt (ModelProd E2 E2) q).source
  rw [OpenPartialHomeomorph.trans_source, γOPH_source, Set.preimage_univ, Set.inter_univ]

/-- The extended chart of the merged `J6` atlas is the banked `J5` extended chart post-composed
with `Lcle2` (pointwise, mirrors `extChartAt_J5_apply`). -/
theorem extChartAt_J6_apply (q z : SphereDisk) :
    (extChartAt (J6) q) z = Lcle2 ((extChartAt J5 q) z) := by
  rw [extChartAt_coe, Function.comp_apply, extChartAt_coe, Function.comp_apply]
  exact J6_comp_βhomeo _

/-- The merged and `J5` extended charts of `SphereDisk` share the same source. -/
theorem extChartAt_J6_source (q : SphereDisk) :
    (extChartAt (J6) q).source = (extChartAt J5 q).source := by
  rw [extChartAt_source, extChartAt_source]
  show ((chartAt HB q).trans βOPH).source = (chartAt HB q).source
  rw [OpenPartialHomeomorph.trans_source, βOPH_source, Set.preimage_univ, Set.inter_univ]

/-- **Step A — target-only re-association**: `sphereDiskIncl` is `C^k` for `(I4, J6)` (the banked
`(I4, J5)` smoothness, post-composed with the `J5 → J6` merge `Lcle2`). -/
theorem smooth_incl_I4_J6 {k : WithTop ℕ∞} : ContMDiff I4 (J6) k sphereDiskIncl := by
  haveI : IsManifold J5 k SphereDisk := isManifold_J5
  haveI : IsManifold (J6) k SphereDisk := isManifold_J6
  have hnat := smooth_incl_J5 (k := k)
  rw [contMDiff_iff] at hnat ⊢
  obtain ⟨hcont, hnat2⟩ := hnat
  refine ⟨hcont, fun p q => ?_⟩
  rw [show (extChartAt (J6) q).source = (extChartAt J5 q).source from extChartAt_J6_source q]
  refine ((Lcle2.contDiff.of_le le_top).comp_contDiffOn (hnat2 p q)).congr ?_
  intro z _
  simp only [Function.comp_apply]
  exact (extChartAt_J6_apply q _).symm

/-- The merged extended chart's target is the `Lmerge`-image of the natural target (via
`PartialEquiv.image_source_eq_target` + the shared source `extChartAt_R4_source`). -/
theorem extChartAt_R4_target (p : SphereProd) :
    (extChartAt (R4) p).target = Lmerge '' (extChartAt I4 p).target := by
  have hfun : (⇑(extChartAt (R4) p) : SphereProd → E4) = ⇑Lmerge ∘ ⇑(extChartAt I4 p) := by
    funext z; exact extChartAt_R4_apply p z
  rw [← PartialEquiv.image_source_eq_target, ← PartialEquiv.image_source_eq_target,
    extChartAt_R4_source, hfun, Set.image_comp]

/-- The merged extended chart's inverse reads as the natural inverse pre-composed with
`Lmerge.symm` (on the merged target). -/
theorem extChartAt_R4_symm_apply {p : SphereProd} {w : E4} (hw : w ∈ (extChartAt (R4) p).target) :
    (extChartAt (R4) p).symm w = (extChartAt I4 p).symm (Lmerge.symm w) := by
  have hmem : Lmerge.symm w ∈ (extChartAt I4 p).target := by
    rw [extChartAt_R4_target] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rwa [Lmerge.symm_apply_apply]
  have hsrc : (extChartAt I4 p).symm (Lmerge.symm w) ∈ (extChartAt (R4) p).source := by
    rw [extChartAt_R4_source]
    exact (extChartAt I4 p).map_target hmem
  have heq : (extChartAt (R4) p) ((extChartAt I4 p).symm (Lmerge.symm w)) = w := by
    rw [extChartAt_R4_apply, (extChartAt I4 p).right_inv hmem, Lmerge.apply_symm_apply]
  have hleft := (extChartAt (R4) p).left_inv hsrc
  rwa [heq] at hleft

/-- **Step B — source-only re-association**: `sphereDiskIncl` is `C^k` for `(𝓡4, J6)` (Step A's
`(I4, J6)` smoothness, pre-composed with the `I4 → 𝓡4` merge `Lmerge`). -/
theorem smooth_incl_R4_J6 {k : WithTop ℕ∞} : ContMDiff (R4) (J6) k sphereDiskIncl := by
  haveI : IsManifold (R4) k SphereProd := isManifold_R4
  haveI : IsManifold (J6) k SphereDisk := isManifold_J6
  have hnat := smooth_incl_I4_J6 (k := k)
  rw [contMDiff_iff] at hnat ⊢
  obtain ⟨hcont, hnat2⟩ := hnat
  refine ⟨hcont, fun p q => ?_⟩
  have hmapsto : Set.MapsTo (⇑Lmerge.symm)
      ((extChartAt (R4) p).target ∩
        ↑(extChartAt (R4) p).symm ⁻¹' (sphereDiskIncl ⁻¹' (extChartAt (J6) q).source))
      ((extChartAt I4 p).target ∩
        ↑(extChartAt I4 p).symm ⁻¹' (sphereDiskIncl ⁻¹' (extChartAt (J6) q).source)) := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨?_, ?_⟩
    · rw [extChartAt_R4_target] at hz1
      obtain ⟨v, hv, rfl⟩ := hz1
      rwa [Lmerge.symm_apply_apply]
    · simp only [Set.mem_preimage] at hz2 ⊢
      rwa [← extChartAt_R4_symm_apply hz1]
  have hcongr : ∀ z ∈ (extChartAt (R4) p).target ∩
      ↑(extChartAt (R4) p).symm ⁻¹' (sphereDiskIncl ⁻¹' (extChartAt (J6) q).source),
      (↑(extChartAt (J6) q) ∘ sphereDiskIncl ∘ ↑(extChartAt I4 p).symm) (Lmerge.symm z)
        = (↑(extChartAt (J6) q) ∘ sphereDiskIncl ∘ ↑(extChartAt (R4) p).symm) z := by
    rintro z ⟨hz1, -⟩
    simp only [Function.comp_apply]
    rw [extChartAt_R4_symm_apply hz1]
  exact ((hnat2 p q).comp (Lmerge.symm.contDiff.of_le le_top).contDiffOn hmapsto).congr hcongr

/-! ### §6. Boundary transport (deliverable 5) -/

/-- The `J6` euclidean range is the `Lcle2`-image of the `J5` range (mirrors
`range_J5_eq_Lcle_image`). -/
theorem range_J6_eq_Lcle2_image : range ⇑(J6) = ⇑Lcle2 '' range ⇑J5 := by
  rw [range_J6_eq_J6L, J6L_coe, Set.range_comp]

/-- **Associator invariance of the boundary** (`J6` vs `J5`, mirrors
`boundary_J5_eq_boundary_J5'`): the re-associated `J6` atlas has the same manifold boundary as
the banked `J5` atlas — the boundary set is a homeomorphism invariant. -/
theorem boundary_J6_eq_boundary_J5 :
    (J6).boundary SphereDisk = J5.boundary SphereDisk := by
  ext x
  simp only [ModelWithCorners.boundary, ModelWithCorners.IsBoundaryPoint, Set.mem_setOf_eq]
  rw [extChartAt_J6_apply, range_J6_eq_Lcle2_image]
  simp only [← ContinuousLinearEquiv.coe_toHomeomorph]
  rw [← Homeomorph.image_frontier]
  exact Lcle2.toHomeomorph.injective.mem_set_image

/-- **Deliverable 5** — the consumer's `J6` manifold boundary of `SphereDisk` equals
`sphereDiskBoundarySet` (the genuine topological frontier slice `S² × ∂D³`,
`sphereDiskBoundarySet_eq_frontier`): transports the banked `boundary_J5_eq`
(`SphereDiskFreezeB.lean`) across the `J5 → J6` merge. -/
theorem sphereDisk_boundary_eq : (J6).boundary SphereDisk = sphereDiskBoundarySet := by
  rw [boundary_J6_eq_boundary_J5, boundary_J5_eq]

/-! ### §7. The assembled `Bordism` in the consumer's model (deliverable 4) -/

/-- **`sphereProdCoboundaryBordism`** — the banked `S²×D³` coboundary `Bordism`, re-associated
into the 16-convergence assembly consumer's model `J6 = (𝓡 4).prod (𝓡∂ 1)`: `W = SphereDisk`
(definitionally), the boundary inclusion `e := sphereDiskIncl ⊔ isEmptyElim` is `C^k` for
`(𝓡4, J6)` (`smooth_incl_R4_J6`) with range the `J6`-boundary (`sphereDisk_boundary_eq`). -/
noncomputable def sphereProdCoboundaryBordism (k : WithTop ℕ∞) :
    Bordism (J6) (sphereProdSM4 k) (emptySM (X := PUnit) (k := k) (I := R4)) :=
  haveI : IsManifold (R4) k SphereProd := isManifold_R4
  haveI : IsManifold (J6) k SphereDisk := isManifold_J6
  { W := SphereDisk
    e := Sum.elim sphereDiskIncl (fun z => isEmptyElim z)
    he_smooth := ContMDiff.sumElim smooth_incl_R4_J6 (fun z => isEmptyElim z)
    he_inj := by
      rintro (a | a) (b | b) hab
      · exact congrArg Sum.inl (sphereDiskIncl_injective hab)
      · exact isEmptyElim b
      · exact isEmptyElim a
      · exact isEmptyElim a
    he_boundary := by
      rw [Set.Sum.elim_range]
      simp only [Set.range_eq_empty, Set.union_empty]
      exact range_sphereDiskIncl.trans sphereDisk_boundary_eq.symm
    g := fun _ => PUnit.unit
    hg := continuous_const
    hg_restrict := by
      funext x
      rcases x with a | z
      · rfl
      · exact isEmptyElim z }

end SKEFTHawking.SpinSigmaRoute
