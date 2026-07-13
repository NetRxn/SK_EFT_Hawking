/-
# Phase 5q.H (N1a, gap 2) — the collar-model re-association transport for `S²×D³`

Freeze-B's `SphereDiskSmoothData` (`SphereProductBounding.lean` §4) states its frozen `chartW`/`mfdW`
fields on the **project `Bordism` model** `J5 = I4.prod (𝓡∂ 1)` with model space
`(E²×E²)×H`. But `S²×D³ = TwoSphere × ThreeDisk` charts *naturally* over `E²×(E²×H)`
(`S²` over `𝓡 2`, `D³` over the collar model `(𝓡 2).prod (𝓡∂ 1)` of `DiskChart`/`DiskManifoldSmooth`).
The two differ only by **product associativity of the model** — the manifold `S²×D³` is UNCHANGED.

This module discharges that re-association: it transports the natural `ChartedSpace`/`IsManifold`
structure of `S²×D³` along the model prod-associator, giving a genuine
`ChartedSpace ((E²×E²)×H) SphereDisk` (= `J5`'s model space) and `IsManifold J5 k SphereDisk`.
The transport is via the euclidean associator `Lcle : E²×(E²×E¹) ≃L (E²×E²)×E¹`
(`ContinuousLinearEquiv.prodAssoc`) intertwining the two models — `J5 ∘ α = Lcle ∘ J5'` (`rfl`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom. `maxRecDepth` bumped for the deep product-instance synthesis only.
-/
import Mathlib
import SKEFTHawking.SphereProductBounding
import SKEFTHawking.DiskManifoldSmooth

namespace SKEFTHawking.SpinSigmaRoute

open scoped Manifold
open Metric Set

set_option maxRecDepth 4000

/-! ### §1. The two models and the associator intertwining -/

/-- `E²` — the euclidean model factor of a sphere / disk-boundary chart. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)
/-- `E¹` — the euclidean space of the half-space model factor. -/
abbrev E1 := EuclideanSpace ℝ (Fin 1)
/-- `H` — the half-space model factor of the disk's collar chart. -/
abbrev HH := EuclideanHalfSpace 1

/-- `HA = E²×(E²×H)` — the natural model space of `S²×D³` (`S²` × collar-disk grouping). -/
abbrev HA := ModelProd E2 (ModelProd E2 HH)
/-- `HB = (E²×E²)×H` — `J5`'s model space (the project `Bordism` collar grouping `I4.prod (𝓡∂ 1)`). -/
abbrev HB := ModelProd (ModelProd E2 E2) HH

/-- `J5' = (𝓡 2).prod ((𝓡 2).prod (𝓡∂ 1))` — the NATURAL model of `S²×D³`
(`S²` boundaryless × the collar-disk model). -/
noncomputable abbrev J5' : ModelWithCorners ℝ (E2 × (E2 × E1)) HA :=
  (𝓡 2).prod ((𝓡 2).prod (𝓡∂ 1))

/-- The euclidean product-associator `E²×(E²×E¹) ≃L (E²×E²)×E¹`, intertwining `J5'` and `J5`. -/
noncomputable def Lcle : (E2 × (E2 × E1)) ≃L[ℝ] ((E2 × E2) × E1) :=
  (ContinuousLinearEquiv.prodAssoc ℝ E2 E2 E1).symm

/-- The model-space associator homeomorphism `E²×(E²×H) ≃ₜ (E²×E²)×H`. -/
noncomputable def αhomeo : HA ≃ₜ HB :=
  (Homeomorph.prodAssoc E2 E2 HH).symm

/-- `αhomeo` as an `OpenPartialHomeomorph` (global chart, source = univ). -/
noncomputable def αOPH : OpenPartialHomeomorph HA HB := αhomeo.toOpenPartialHomeomorph

@[simp] theorem αhomeo_apply (p : HA) : αhomeo p = ((p.1, p.2.1), p.2.2) := rfl
@[simp] theorem αhomeo_symm_apply (q : HB) : αhomeo.symm q = (q.1.1, (q.1.2, q.2)) := rfl

/-- **The model intertwining**: `J5 ∘ αhomeo = Lcle ∘ J5'` (holds by `rfl` — both re-bracket the
`E²` factors and apply the half-space inclusion `𝓡∂ 1` to the last factor). -/
theorem J5_comp_αhomeo (p : HA) : (J5) (αhomeo p) = Lcle (J5' p) := rfl

/-- **The inverse intertwining**: `J5'.symm ∘ Lcle.symm = αhomeo.symm ∘ J5.symm` (`rfl`). -/
theorem J5'symm_comp_Lclesymm (q : (E2 × E2) × E1) :
    (J5').symm (Lcle.symm q) = αhomeo.symm ((J5).symm q) := rfl

/-! ### §2. The re-associated charted space of `S²×D³` -/

/-- `HA` charted over `HB` by the single global associator chart `αhomeo`. -/
@[reducible] noncomputable def chartedSpaceHB_HA : ChartedSpace HB HA where
  atlas := {αOPH}
  chartAt _ := αOPH
  mem_chart_source x := by
    show x ∈ αOPH.source
    simp [αOPH, Homeomorph.toOpenPartialHomeomorph]
  chart_mem_atlas _ := rfl

attribute [local instance] chartedSpaceHB_HA

/-- The natural charted space of `S²×D³` over `HB = (E²×E²)×H` (`J5`'s model space): the natural
`E²×(E²×H)` product atlas, re-modelled over `HB` by the associator (`ChartedSpace.comp`). -/
@[reducible] noncomputable def chartW : ChartedSpace HB SphereDisk :=
  ChartedSpace.comp HB HA SphereDisk

/-! ### §3. `J5L` — `J5'` with `E`-space aligned to `J5` via `Lcle`

Applying `Lcle` to `J5'`'s euclidean space gives a model `J5L` with `J5`'s euclidean space `EB` but
`J5'`'s model space `HA`; its `IsManifold` is free (`instIsManifoldtransContinuousLinearEquiv`). The
remaining transport to `J5` is then a PURE model-space homeomorphism with identical euclidean model,
so the conjugation reduces to equal functions + equal sets (no `Lcle` at the `ContDiffOn` stage). -/

/-- `J5'` reparametrized so its euclidean space is `J5`'s (`EB = (E²×E²)×E¹`), keeping `J5'`'s model
space `HA`. -/
noncomputable def J5L : ModelWithCorners ℝ ((E2 × E2) × E1) HA :=
  J5'.transContinuousLinearEquiv Lcle

/-- `J5L`'s coordinate map is `Lcle ∘ J5'`. -/
theorem J5L_coe : ⇑J5L = Lcle ∘ ⇑J5' := rfl

/-- **Model equality on the associator**: `J5 ∘ αhomeo = J5L` (as functions `HA → EB`). -/
theorem J5_αhomeo_eq_J5L (p : HA) : (J5) (αhomeo p) = J5L p := rfl

/-- `J5L.symm = αhomeo.symm ∘ J5.symm` (as functions `EB → HA`). -/
theorem J5L_symm_eq (q : (E2 × E2) × E1) : (J5L).symm q = αhomeo.symm ((J5).symm q) := rfl

/-- `IsManifold J5L k S²×D³` — free, via the `transContinuousLinearEquiv` instance and the natural
`E²×(E²×H)` manifold structure of `S²×D³`. -/
theorem isManifold_J5L {k : WithTop ℕ∞} : IsManifold J5L k SphereDisk := by
  haveI : IsManifold (𝓡 2) k TwoSphere := .of_le le_top
  haveI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) k ThreeDisk := DiskManifoldSmooth.isManifold_threeDisk
  haveI : IsManifold J5' k SphereDisk := IsManifold.prod TwoSphere ThreeDisk
  exact ContinuousLinearEquiv.instIsManifoldtransContinuousLinearEquiv Lcle

/-- The euclidean ranges coincide: `range J5 = range J5L` (via `αhomeo` surjective). -/
theorem range_J5_eq_J5L : range (J5) = range J5L := by
  have h : range J5L = range (fun p => (J5) (αhomeo p)) := by
    apply congrArg; funext p; exact (J5_αhomeo_eq_J5L p).symm
  rw [h, Set.range_comp' (g := (J5)) (f := αhomeo)]
  · simp [αhomeo.surjective.range_eq]

/-! ### §4. The groupoid conjugation and `IsManifold J5` -/

@[simp] theorem αOPH_coe : ⇑αOPH = αhomeo := rfl
@[simp] theorem αOPH_symm_coe : ⇑αOPH.symm = αhomeo.symm := rfl
@[simp] theorem αOPH_source : αOPH.source = Set.univ := by
  simp [αOPH, Homeomorph.toOpenPartialHomeomorph]
@[simp] theorem αOPH_target : αOPH.target = Set.univ := by
  simp [αOPH, Homeomorph.toOpenPartialHomeomorph]

/-- `J5L.symm` as a function: `⇑J5L.symm = αhomeo.symm ∘ ⇑J5.symm`. -/
theorem J5L_symm_fun : ⇑(J5L).symm = αhomeo.symm ∘ ⇑(J5).symm := by
  funext q; exact J5L_symm_eq q

/-- The conjugated coordinate map: `⇑(αOPH.symm ≫ₕ g ≫ₕ αOPH) = αhomeo ∘ g ∘ αhomeo.symm`. -/
theorem conj_coe (g : OpenPartialHomeomorph HA HA) :
    ⇑(αOPH.symm.trans (g.trans αOPH)) = αhomeo ∘ ⇑g ∘ αhomeo.symm := by
  simp [OpenPartialHomeomorph.coe_trans]; rfl

/-- The conjugated source: `(αOPH.symm ≫ₕ g ≫ₕ αOPH).source = αhomeo.symm ⁻¹' g.source`. -/
theorem conj_source (g : OpenPartialHomeomorph HA HA) :
    (αOPH.symm.trans (g.trans αOPH)).source = αhomeo.symm ⁻¹' g.source := by simp

/-- **The `contDiffPregroupoid` property transfer under associator conjugation**: the essential
`ContDiffOn` step — a `J5L`-smooth transition `φ` on `HA` conjugates to a `J5`-smooth transition on
`HB`, with equal read-in-`E` maps (`J5 ∘ αhomeo = J5L`) and equal domains (no `Lcle` at this stage). -/
theorem conj_property_transfer {n : WithTop ℕ∞} (φ : HA → HA) (s : Set HA)
    (hφ : ContDiffOn ℝ n (⇑J5L ∘ φ ∘ ⇑(J5L).symm) (⇑(J5L).symm ⁻¹' s ∩ range J5L)) :
    ContDiffOn ℝ n (⇑J5 ∘ (αhomeo ∘ φ ∘ αhomeo.symm) ∘ ⇑(J5).symm)
      (⇑(J5).symm ⁻¹' (αhomeo.symm ⁻¹' s) ∩ range J5) := by
  have hfun : ⇑J5 ∘ (αhomeo ∘ φ ∘ αhomeo.symm) ∘ ⇑(J5).symm = ⇑J5L ∘ φ ∘ ⇑(J5L).symm := by
    funext y
    simp only [Function.comp_apply]
    rw [J5_αhomeo_eq_J5L, ← J5L_symm_eq]
  have hset : ⇑(J5).symm ⁻¹' (αhomeo.symm ⁻¹' s) ∩ range J5 = ⇑(J5L).symm ⁻¹' s ∩ range J5L := by
    rw [range_J5_eq_J5L, J5L_symm_fun, Set.preimage_comp]
  rw [hfun, hset]; exact hφ

/-- **Associator conjugation preserves `C^n` compatibility**: for a `J5L`-groupoid transition `g`
on `HA`, the associator-conjugate `αOPH.symm ≫ₕ g ≫ₕ αOPH` is a `J5`-groupoid transition on `HB`. -/
theorem conj_mem_J5 {n : WithTop ℕ∞} {g : OpenPartialHomeomorph HA HA}
    (hg : g ∈ contDiffGroupoid n J5L) :
    (αOPH.symm.trans (g.trans αOPH)) ∈ contDiffGroupoid n J5 := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg ⊢
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_⟩
  · -- forward property on the conjugate's source
    rw [conj_coe, conj_source]
    exact conj_property_transfer g g.source hg1
  · -- symm property on the conjugate's target
    have hsymm_coe : ⇑(αOPH.symm.trans (g.trans αOPH)).symm = αhomeo ∘ ⇑g.symm ∘ αhomeo.symm := by
      simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
        αOPH_coe, αOPH_symm_coe]
    have htarget : (αOPH.symm.trans (g.trans αOPH)).target = αhomeo.symm ⁻¹' g.target := by
      simp
    rw [hsymm_coe, htarget]
    exact conj_property_transfer g.symm g.target hg2

attribute [local instance] chartW

/-- **mfdW — gap 2 discharged**: `S²×D³` is a `C^k` manifold over the project `Bordism` collar model
`J5 = I4.prod (𝓡∂ 1)`, obtained by transporting its natural `E²×(E²×H)` structure (`S²` over `𝓡 2`,
`D³` over the `DiskChart`/`DiskManifoldSmooth` collar model) along the model prod-associator. The
manifold `S²×D³` is UNCHANGED — only the model grouping is re-associated. -/
theorem isManifold_J5 {k : WithTop ℕ∞} : IsManifold (J5) k SphereDisk := by
  haveI : IsManifold J5L k SphereDisk := isManifold_J5L
  haveI hg : HasGroupoid SphereDisk (contDiffGroupoid k (J5)) := by
    refine ⟨fun {e₁ e₂} he₁ he₂ => ?_⟩
    obtain ⟨f₁, hf₁, β₁, hβ₁, rfl⟩ := he₁
    obtain ⟨f₂, hf₂, β₂, hβ₂, rfl⟩ := he₂
    obtain rfl : β₁ = αOPH := hβ₁
    obtain rfl : β₂ = αOPH := hβ₂
    have heq : (f₁.trans αOPH).symm.trans (f₂.trans αOPH)
        = αOPH.symm.trans ((f₁.symm.trans f₂).trans αOPH) := by
      simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
    rw [heq]
    exact conj_mem_J5 ((contDiffGroupoid k J5L).compatible hf₁ hf₂)
  exact IsManifold.mk' (J5) k SphereDisk

end SKEFTHawking.SpinSigmaRoute
