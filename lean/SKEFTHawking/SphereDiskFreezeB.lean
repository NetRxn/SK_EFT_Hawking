/-
# Phase 5q.H (N1a) — Freeze-B concrete discharge: the complete `SphereDiskSmoothData`

Assembles the two still-open `SphereDiskSmoothData` fields on the re-associated collar atlas
`chartW`/`J5` of `S²×D³` (`SphereDiskJ5.lean`, gap 2) and fires the concrete Freeze-B discharge.
-/
import Mathlib
import SKEFTHawking.SphereProductBounding
import SKEFTHawking.SphereDiskJ5

namespace SKEFTHawking.SpinSigmaRoute

open scoped Manifold
open Metric Set
open SKEFTHawking.DiskChart SKEFTHawking.DiskManifold SKEFTHawking.DiskManifoldSmooth

/-! ### §1. The boundary of the closed 3-ball -/

/-- frontier of the disk collar model range: `univ ×ˢ {half-space wall}`. -/
theorem frontier_range_diskModel :
    frontier (range ((𝓡 2).prod (𝓡∂ 1)))
      = (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) ×ˢ
        {y : EuclideanSpace ℝ (Fin 1) | (0:ℝ) = y 0} := by
  rw [ModelWithCorners.range_prod, frontier_prod_eq,
    ModelWithCorners.range_eq_univ (I := 𝓡 2), frontier_univ, closure_univ,
    frontier_range_modelWithCornersEuclideanHalfSpace, Set.empty_prod, Set.union_empty]

/-- **The boundary of `D³`** (collar model): the bounding unit sphere `‖v‖ = 1`. -/
theorem boundary_threeDisk :
    ((𝓡 2).prod (𝓡∂ 1)).boundary ThreeDisk
      = {v : ThreeDisk | ‖(v : EuclideanSpace ℝ (Fin 3))‖ = 1} := by
  ext v
  simp only [ModelWithCorners.boundary, ModelWithCorners.IsBoundaryPoint, Set.mem_setOf_eq,
    frontier_range_diskModel, Set.mem_prod, Set.mem_univ, true_and]
  rw [extChartAt_coe]
  simp only [Function.comp_apply, ModelWithCorners.prod_apply]
  by_cases h : ‖(v : EuclideanSpace ℝ (Fin 3))‖ < 1
  · rw [show chartAt (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)) v
        = diskInteriorChart from if_pos h]
    show (0:ℝ) = (WithLp.toLp 2
        (fun _ : Fin 1 => (v : EuclideanSpace ℝ (Fin 3)).ofLp (Fin.last 2) + 2)).ofLp 0
        ↔ ‖(v : EuclideanSpace ℝ (Fin 3))‖ = 1
    rw [WithLp.ofLp_toLp]
    apply iff_of_false
    · intro heq
      have h2 : ‖(v : EuclideanSpace ℝ (Fin 3)).ofLp (Fin.last 2)‖
          ≤ ‖(v : EuclideanSpace ℝ (Fin 3))‖ := PiLp.norm_apply_le _ _
      rw [Real.norm_eq_abs] at h2
      have h3 := (abs_le.mp (h2.trans (le_of_lt h))).1
      linarith
    · exact ne_of_lt h
  · rw [show chartAt (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)) v
        = diskCollarChart (diskDir v) from if_neg h]
    show (0:ℝ) = (WithLp.toLp 2
        (fun _ : Fin 1 => 1 - ‖(v : EuclideanSpace ℝ (Fin 3))‖)).ofLp 0
        ↔ ‖(v : EuclideanSpace ℝ (Fin 3))‖ = 1
    rw [WithLp.ofLp_toLp]
    constructor <;> intro heq <;> linarith

/-! ### §2. The two open `SphereDiskSmoothData` fields on the re-associated atlas -/

attribute [local instance] SKEFTHawking.SpinSigmaRoute.chartW

/-- The extended chart of the re-associated atlas is the natural extended chart post-composed with
the euclidean associator `Lcle` (pointwise, at any base point `q` and any point `z`). -/
theorem extChartAt_J5_apply (q z : SphereDisk) :
    (extChartAt J5 q) z = Lcle ((extChartAt J5' q) z) := by
  rw [extChartAt_coe, Function.comp_apply, extChartAt_coe, Function.comp_apply]
  exact J5_comp_αhomeo _

/-- The re-associated and natural extended charts share the same source. -/
theorem extChartAt_J5_source (q : SphereDisk) :
    (extChartAt J5 q).source = (extChartAt J5' q).source := by
  rw [extChartAt_source, extChartAt_source]
  show ((chartAt HA q).trans αOPH).source = (chartAt HA q).source
  rw [OpenPartialHomeomorph.trans_source, αOPH_source, Set.preimage_univ, Set.inter_univ]

/-- The boundary sphere inclusion `S² ↪ D³`, `y ↦ (y : E³) ∈ D³` (the `.2` factor of
`sphereDiskIncl`). -/
def bincl : TwoSphere → ThreeDisk :=
  fun y => ⟨(y : EuclideanSpace ℝ (Fin 3)), sphere_subset_closedBall y.2⟩

theorem bincl_continuous : Continuous bincl :=
  (continuous_subtype_val.subtype_mk _)

theorem bincl_coe (y : TwoSphere) :
    (bincl y : EuclideanSpace ℝ (Fin 3)) = (y : EuclideanSpace ℝ (Fin 3)) := rfl

theorem bincl_norm (y : TwoSphere) : ‖(bincl y : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
  mem_sphere_zero_iff_norm.mp y.2

/-- The direction of the boundary-included point is the sphere point itself. -/
theorem diskDir_bincl (y : TwoSphere) : diskDir (bincl y) = y := by
  apply Subtype.ext
  rw [diskDir_coe (by rw [bincl_coe]; exact ne_zero_of_mem_unit_sphere y), bincl_coe,
    mem_sphere_zero_iff_norm.mp y.2, inv_one, one_smul]

/-- **The boundary sphere inclusion is `C^k`** into the collar-modelled `D³`: in the polar collar
chart it reads as the sphere chart transition paired with the constant radial coordinate `0`. -/
theorem bincl_contMDiff {k : WithTop ℕ∞} :
    ContMDiff (𝓡 2) ((𝓡 2).prod (𝓡∂ 1)) k bincl := by
  haveI : IsManifold (𝓡 2) k TwoSphere := .of_le le_top
  haveI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) k ThreeDisk := isManifold_threeDisk
  rw [contMDiff_iff]
  refine ⟨bincl_continuous, ?_⟩
  intro x y
  by_cases hy : ‖(y : EuclideanSpace ℝ (Fin 3))‖ < 1
  · -- `y` in the open interior: `bincl` (a unit-sphere point) never lands in the interior chart,
    -- so the transition domain is empty.
    have hempty : bincl ⁻¹' (extChartAt ((𝓡 2).prod (𝓡∂ 1)) y).source = ∅ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hmem
      rw [extChartAt_source, show chartAt (ModelProd (EuclideanSpace ℝ (Fin 2))
        (EuclideanHalfSpace 1)) y = diskInteriorChart from if_pos hy] at hmem
      have hb : ‖(bincl u : EuclideanSpace ℝ (Fin 3))‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
      have hlt : ‖(bincl u : EuclideanSpace ℝ (Fin 3))‖ < 1 := hmem
      rw [hb] at hlt
      exact lt_irrefl 1 hlt
    rw [hempty, Set.preimage_empty, Set.inter_empty]
    exact contDiffOn_empty
  · -- `y` on the boundary sphere: chart at `y` is the collar chart at `u₀ = diskDir y`, in which
    -- `bincl` reads as the sphere-chart transition `chartAt u₀ ∘ (chartAt x)⁻¹` paired with `0`.
    set u₀ := diskDir y with hu₀
    have hpre : bincl ⁻¹' (extChartAt ((𝓡 2).prod (𝓡∂ 1)) y).source
        = (extChartAt (𝓡 2) u₀).source := by
      rw [extChartAt_source, extChartAt_source,
        show chartAt (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)) y
          = diskCollarChart u₀ from if_neg hy]
      ext u
      simp only [Set.mem_preimage]
      constructor
      · intro hmem
        have h2 := hmem.2
        rwa [diskDir_bincl] at h2
      · intro hmem
        exact ⟨by rw [bincl_coe]; exact ne_zero_of_mem_unit_sphere u,
          by rw [diskDir_bincl]; exact hmem⟩
    have hcompute : ∀ s : TwoSphere,
        extChartAt ((𝓡 2).prod (𝓡∂ 1)) y (bincl s)
          = (extChartAt (𝓡 2) u₀ s, (0 : EuclideanSpace ℝ (Fin 1))) := by
      intro s
      rw [extChartAt_coe, Function.comp_apply,
        show chartAt (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)) y
          = diskCollarChart u₀ from if_neg hy,
        ModelWithCorners.prod_apply, extChartAt_coe, Function.comp_apply]
      refine Prod.ext ?_ ?_
      · show (𝓡 2) ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀) (diskDir (bincl s)))
          = (𝓡 2) ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀) s)
        rw [diskDir_bincl]
      · show WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖(bincl s : EuclideanSpace ℝ (Fin 3))‖)
          = (0 : EuclideanSpace ℝ (Fin 1))
        rw [show (fun _ : Fin 1 => 1 - ‖(bincl s : EuclideanSpace ℝ (Fin 3))‖) = fun _ => 0 from by
          funext _; rw [bincl_norm]; ring]
        rfl
    have hDT : (extChartAt (𝓡 2) x).target ∩ ↑(extChartAt (𝓡 2) x).symm ⁻¹'
          (bincl ⁻¹' (extChartAt ((𝓡 2).prod (𝓡∂ 1)) y).source)
        = ((extChartAt (𝓡 2) x).symm.trans (extChartAt (𝓡 2) u₀)).source := by
      rw [hpre, PartialEquiv.trans_source, PartialEquiv.symm_source]
    rw [hDT]
    apply ContDiffOn.congr ((contDiffOn_sphereTransition x u₀).prodMk contDiffOn_const)
    intro w _
    exact hcompute ((extChartAt (𝓡 2) x).symm w)

/-- **smooth_incl field** — the boundary inclusion `S²×S² → S²×D³` is `C^k` for the re-associated
`J5` atlas: reduces to the natural product smoothness (`id ×ˢ bincl`) post-composed with the
euclidean associator `Lcle` (which is smooth), via the intertwining `extChartAt_J5_apply`. -/
theorem smooth_incl_J5 {k : WithTop ℕ∞} :
    ContMDiff I4 J5 k sphereDiskIncl := by
  haveI : IsManifold (𝓡 2) k TwoSphere := .of_le le_top
  haveI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) k ThreeDisk := isManifold_threeDisk
  haveI : IsManifold J5' k SphereDisk := IsManifold.prod TwoSphere ThreeDisk
  haveI : IsManifold J5 k SphereDisk := isManifold_J5
  have hnat : ContMDiff I4 J5' k sphereDiskIncl :=
    contMDiff_fst.prodMk (bincl_contMDiff.comp contMDiff_snd)
  rw [contMDiff_iff] at hnat ⊢
  obtain ⟨hcont, hnat2⟩ := hnat
  refine ⟨hcont, fun p q => ?_⟩
  rw [show (extChartAt J5 q).source = (extChartAt J5' q).source from extChartAt_J5_source q]
  refine ((Lcle.contDiff.of_le le_top).comp_contDiffOn (hnat2 p q)).congr ?_
  intro z _
  simp only [Function.comp_apply]
  exact (extChartAt_J5_apply q _).symm

/-- The re-associated collar range is the euclidean-associator image of the natural collar range. -/
theorem range_J5_eq_Lcle_image : range ⇑(J5) = ⇑Lcle '' range ⇑J5' := by
  rw [range_J5_eq_J5L, J5L_coe, Set.range_comp]

/-- **Associator invariance of the boundary**: the re-associated atlas has the same manifold boundary
as the natural product atlas (the boundary set is a homeomorphism invariant). -/
theorem boundary_J5_eq_boundary_J5' :
    (J5).boundary SphereDisk = J5'.boundary SphereDisk := by
  ext x
  simp only [ModelWithCorners.boundary, ModelWithCorners.IsBoundaryPoint, Set.mem_setOf_eq]
  rw [extChartAt_J5_apply, range_J5_eq_Lcle_image]
  simp only [← ContinuousLinearEquiv.coe_toHomeomorph]
  rw [← Homeomorph.image_frontier]
  exact Lcle.toHomeomorph.injective.mem_set_image

/-- boundary_eq field -/
theorem boundary_J5_eq :
    (J5).boundary SphereDisk = sphereDiskBoundarySet := by
  rw [boundary_J5_eq_boundary_J5', ModelWithCorners.boundary_of_boundaryless_left,
    boundary_threeDisk]
  ext ⟨a, b⟩
  exact ⟨fun h => mem_sphere_zero_iff_norm.mpr h.2,
    fun h => ⟨Set.mem_univ _, mem_sphere_zero_iff_norm.mp h⟩⟩

/-! ### §3. The complete `SphereDiskSmoothData` and the concrete Freeze-B discharge -/

/-- **The complete `SphereDiskSmoothData` on the re-associated collar atlas of `S²×D³`**: the two
Mathlib gaps of the freeze are discharged — `chartW`/`mfdW` by the associator transport
(`SphereDiskJ5.lean`, gap 2), `smooth_incl`/`boundary_eq` here — so the disclosed-data freeze is
inhabited by a genuine term. -/
noncomputable def sphereDiskSmoothData (k : WithTop ℕ∞) : SphereDiskSmoothData k where
  chartW := chartW
  mfdW := isManifold_J5
  smooth_incl := smooth_incl_J5
  boundary_eq := boundary_J5_eq

/-- **Freeze B discharged for the concrete `S²×S²` presentation** — end-to-end: the trivial
σ-presentation with the genuine `S²×S²` manifold in the distinguished slot satisfies
`SphereProductBounds` (`[S²×S²] = 0`), the §5 conditional fired on the complete `SphereDiskSmoothData`.
No `sorry`/axiom: the bordism `S²×S² = ∂(S²×D³)` is a genuine `C^k` project `Bordism`. -/
theorem trivialSpherePresentation_freezeB (k : WithTop ℕ∞) :
    (trivialSpherePresentation k).SphereProductBounds :=
  trivialSpherePresentation_sphereProductBounds k (sphereDiskSmoothData k)

end SKEFTHawking.SpinSigmaRoute
