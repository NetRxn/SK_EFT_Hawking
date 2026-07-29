/-
# Phase 5q.H — closed 3-ball smooth atlas (SphereDiskSmoothData freeze, slice B)

Slice B of discharging the `SphereProductBounding.SphereDiskSmoothData` freeze: this module builds
the genuine smooth atlas of the closed unit 3-ball `D³ = ThreeDisk = closedBall(0,1) ⊆ E³` on the
half-space model `ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)` — attacking Mathlib
gap 1 of the freeze (`Metric.closedBall` has no `ChartedSpace`/`IsManifold` instance for `n ≥ 2`).

Built from the slice-A radial-geometry primitives (`SKEFTHawking.DiskManifold`):
* `diskInteriorChart` — the interior chart on the open ball `{‖v‖<1}`, `v ↦ (splitLo v, v₂+2)`
  (the last coordinate translated into the half-space interior);
* `diskCollarChart u₀` — the polar collar chart family, `v ↦ (chart_{S²}(v/‖v‖), 1−‖v‖)`, sending
  the boundary sphere `‖v‖=1` onto the half-space wall `t=0`;
* the `ChartedSpace (ModelProd E² (EuclideanHalfSpace 1)) D³` assembly.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.DiskManifold

open Metric Set
open scoped Manifold

namespace SKEFTHawking.DiskChart

open SKEFTHawking.SpinSigmaRoute (TwoSphere ThreeDisk)
open SKEFTHawking.DiskManifold

noncomputable section

/-! ### §0. Round-trip lemmas for the `E² × ℝ ≅ E³` coordinate iso -/

/-- `splitLo` is a left inverse of `assemble` in the first block. -/
theorem splitLo_assemble (a : EuclideanSpace ℝ (Fin 2)) (s : ℝ) :
    splitLo (assemble a s) = a := by
  apply WithLp.ofLp_injective
  funext i
  rw [splitLo_ofLp, assemble_ofLp_castSucc]

/-- The full reconstruction: reassembling the low block and the last coordinate recovers `v`. -/
theorem assemble_splitLo (v : EuclideanSpace ℝ (Fin 3)) :
    assemble (splitLo v) (v.ofLp (Fin.last 2)) = v := by
  apply WithLp.ofLp_injective
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [assemble_ofLp_last]
  · rw [assemble_ofLp_castSucc, splitLo_ofLp]

/-- Half-space membership for the interior chart's target coordinate: for `v ∈ D³` the translated
last coordinate `v₂ + 2` is nonnegative (indeed `≥ 1`). -/
theorem interior_last_add_two_nonneg (v : ThreeDisk) :
    (0 : ℝ) ≤ (v : EuclideanSpace ℝ (Fin 3)).ofLp (Fin.last 2) + 2 := by
  have h1 : ‖(v : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := mem_closedBall_zero_iff.mp v.2
  have h2 : ‖(v : EuclideanSpace ℝ (Fin 3)).ofLp (Fin.last 2)‖
      ≤ ‖(v : EuclideanSpace ℝ (Fin 3))‖ := PiLp.norm_apply_le _ _
  rw [Real.norm_eq_abs] at h2
  have h3 := (abs_le.mp (h2.trans h1)).1
  linarith

/-- On `E¹`, reassembling the single coordinate recovers the vector. -/
theorem toLp_ofLp_fin_one (x : EuclideanSpace ℝ (Fin 1)) :
    WithLp.toLp 2 (fun _ : Fin 1 => x.ofLp 0) = x := by
  apply WithLp.ofLp_injective
  funext i
  rw [Subsingleton.elim i 0]

/-! ### §1. The interior chart -/

/-- **The interior chart** of `D³`: on the open ball `{‖v‖ < 1}`, the coordinate translation
`v ↦ (splitLo v, v₂ + 2)` landing in the interior of the half-space model. -/
def diskInteriorChart :
    OpenPartialHomeomorph ThreeDisk
      (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)) where
  source := {z : ThreeDisk | ‖(z : EuclideanSpace ℝ (Fin 3))‖ < 1}
  target := {p : ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1) |
    ‖assemble p.1 ((p.2.val).ofLp 0 - 2)‖ < 1}
  toFun v := (splitLo (v : EuclideanSpace ℝ (Fin 3)),
    ⟨WithLp.toLp 2 (fun _ : Fin 1 => (v : EuclideanSpace ℝ (Fin 3)).ofLp (Fin.last 2) + 2),
      interior_last_add_two_nonneg v⟩)
  invFun p := ballClamp (assemble p.1 ((p.2.val).ofLp 0 - 2))
  map_source' := by
    intro x hx
    change ‖assemble (splitLo (↑x : EuclideanSpace ℝ (Fin 3)))
      ((↑x : EuclideanSpace ℝ (Fin 3)).ofLp (Fin.last 2) + 2 - 2)‖ < 1
    rw [add_sub_cancel_right, assemble_splitLo]
    exact hx
  map_target' := by
    intro p hp
    simp only [mem_setOf_eq] at hp ⊢
    rw [ballClamp_coe_of_norm_le (le_of_lt hp)]
    exact hp
  left_inv' := by
    intro x hx
    apply Subtype.ext
    show (↑(ballClamp (assemble (splitLo (↑x : EuclideanSpace ℝ (Fin 3)))
      ((↑x : EuclideanSpace ℝ (Fin 3)).ofLp (Fin.last 2) + 2 - 2))) : EuclideanSpace ℝ (Fin 3))
        = (↑x : EuclideanSpace ℝ (Fin 3))
    rw [add_sub_cancel_right, assemble_splitLo]
    exact ballClamp_coe_of_norm_le (le_of_lt hx)
  right_inv' := by
    intro p hp
    have hw : (↑(ballClamp (assemble p.1 (p.2.val.ofLp 0 - 2))) :
        EuclideanSpace ℝ (Fin 3))
        = assemble p.1 (p.2.val.ofLp 0 - 2) :=
      ballClamp_coe_of_norm_le (le_of_lt hp)
    refine Prod.ext ?_ ?_
    · show splitLo (↑(ballClamp (assemble p.1 (p.2.val.ofLp 0 - 2))) :
        EuclideanSpace ℝ (Fin 3)) = p.1
      rw [hw, splitLo_assemble]
    · apply Subtype.ext
      show WithLp.toLp 2 (fun _ : Fin 1 =>
        (↑(ballClamp (assemble p.1 (p.2.val.ofLp 0 - 2))) :
          EuclideanSpace ℝ (Fin 3)).ofLp (Fin.last 2) + 2)
          = p.2.val
      rw [hw, assemble_ofLp_last, sub_add_cancel]
      exact toLp_ofLp_fin_one _
  open_source := isOpen_lt (by fun_prop) continuous_const
  open_target := by
    apply isOpen_lt _ continuous_const
    refine Continuous.norm (continuous_assemble.comp (Continuous.prodMk continuous_fst ?_))
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
      (continuous_subtype_val.comp continuous_snd)).sub continuous_const
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.prodMk
    · exact continuous_splitLo.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro _
      exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (Fin.last 2)).comp
        continuous_subtype_val).add continuous_const
  continuousOn_invFun := by
    apply Continuous.continuousOn
    refine continuous_ballClamp.comp
      (continuous_assemble.comp (Continuous.prodMk continuous_fst ?_))
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
      (continuous_subtype_val.comp continuous_snd)).sub continuous_const

/-! ### §2. The polar collar chart family -/

/-- Half-space membership for the collar chart's target coordinate: for `v ∈ D³` the collar
coordinate `1 − ‖v‖` is nonnegative (it is `0` exactly on the boundary sphere). -/
theorem collar_one_sub_norm_nonneg (v : ThreeDisk) :
    (0 : ℝ) ≤ 1 - ‖(↑v : EuclideanSpace ℝ (Fin 3))‖ := by
  have := mem_closedBall_zero_iff.mp v.2
  linarith

/-- The collar chart's inverse lands in the closed ball: `max 0 (1−t) • u` (with `u ∈ S²`, `t ≥ 0`)
has norm `max 0 (1−t) ≤ 1`. -/
theorem collar_invFun_mem (u₀ : TwoSphere)
    (p : ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)) :
    (max 0 (1 - p.2.val.ofLp 0) •
      ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 3)))
      ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm p.1).2, mul_one,
    abs_of_nonneg (le_max_left _ _)]
  have ht : (0 : ℝ) ≤ p.2.val.ofLp 0 := p.2.2
  exact max_le zero_le_one (by linarith)

/-- `diskDir` of a positive scalar multiple of a unit vector (any nonneg-ball membership proof) is
that unit vector — the proof-irrelevant reformulation of `diskDir_smul_unit` that lets the collar
inverse's junk-value ball membership be substituted. -/
theorem diskDir_scaled (u : TwoSphere) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (h : c • (↑u : EuclideanSpace ℝ (Fin 3)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    diskDir ⟨c • (↑u : EuclideanSpace ℝ (Fin 3)), h⟩ = u :=
  diskDir_smul_unit hc hc1

/-- The stereographic chart at any base point of `S²` has full target. -/
theorem chart_target_univ (u₀ : TwoSphere) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) u₀).target = Set.univ := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact stereographic'_target _

/-- **The polar collar chart** of `D³` at a base point `u₀ ∈ S²`: on the punctured ball with
direction in the `u₀`-stereographic chart's source, `v ↦ (chart_{S²}(v/‖v‖), 1 − ‖v‖)`. The
boundary sphere `‖v‖ = 1` lands on the half-space wall `t = 0`. -/
def diskCollarChart (u₀ : TwoSphere) :
    OpenPartialHomeomorph ThreeDisk
      (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)) where
  source := {v : ThreeDisk | (↑v : EuclideanSpace ℝ (Fin 3)) ≠ 0 ∧
    diskDir v ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) u₀).source}
  target := {p : ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1) |
    (p.2.val).ofLp 0 < 1}
  toFun v := (chartAt (EuclideanSpace ℝ (Fin 2)) u₀ (diskDir v),
    ⟨WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖(↑v : EuclideanSpace ℝ (Fin 3))‖),
      collar_one_sub_norm_nonneg v⟩)
  invFun p := ⟨max 0 (1 - (p.2.val).ofLp 0) •
    ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 3)),
    collar_invFun_mem u₀ p⟩
  map_source' := by
    intro v hv
    show (1 : ℝ) - ‖(↑v : EuclideanSpace ℝ (Fin 3))‖ < 1
    have : (0 : ℝ) < ‖(↑v : EuclideanSpace ℝ (Fin 3))‖ := norm_pos_iff.mpr hv.1
    linarith
  map_target' := by
    intro p hp
    simp only [mem_setOf_eq] at hp
    have ht : (0 : ℝ) ≤ p.2.val.ofLp 0 := p.2.2
    have hlt : (0 : ℝ) < 1 - p.2.val.ofLp 0 := by linarith
    have hc : (0 : ℝ) < max 0 (1 - p.2.val.ofLp 0) := lt_of_lt_of_le hlt (le_max_right _ _)
    have hc1 : max 0 (1 - p.2.val.ofLp 0) ≤ 1 := max_le zero_le_one (by linarith)
    refine ⟨?_, ?_⟩
    · show (max 0 (1 - p.2.val.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 3))) ≠ 0
      rw [smul_ne_zero_iff]
      refine ⟨ne_of_gt hc, ?_⟩
      rw [← norm_ne_zero_iff,
        mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm p.1).2]
      norm_num
    · rw [diskDir_scaled _ hc hc1 (collar_invFun_mem u₀ p)]
      exact (chartAt (EuclideanSpace ℝ (Fin 2)) u₀).map_target
        (by rw [chart_target_univ]; exact Set.mem_univ p.1)
  left_inv' := by
    intro v hv
    apply Subtype.ext
    show max 0 (1 - (1 - ‖(↑v : EuclideanSpace ℝ (Fin 3))‖)) •
        ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm
          (chartAt (EuclideanSpace ℝ (Fin 2)) u₀ (diskDir v)) : EuclideanSpace ℝ (Fin 3))
        = (↑v : EuclideanSpace ℝ (Fin 3))
    rw [(chartAt (EuclideanSpace ℝ (Fin 2)) u₀).left_inv hv.2, sub_sub_cancel,
      max_eq_right (norm_nonneg _), diskDir_coe hv.1, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv.1), one_smul]
  right_inv' := by
    intro p hp
    simp only [mem_setOf_eq] at hp
    have ht : (0 : ℝ) ≤ p.2.val.ofLp 0 := p.2.2
    have hlt : (0 : ℝ) < 1 - p.2.val.ofLp 0 := by linarith
    have hc : (0 : ℝ) < max 0 (1 - p.2.val.ofLp 0) := lt_of_lt_of_le hlt (le_max_right _ _)
    have hc1 : max 0 (1 - p.2.val.ofLp 0) ≤ 1 := max_le zero_le_one (by linarith)
    have hmax : max 0 (1 - p.2.val.ofLp 0) = 1 - p.2.val.ofLp 0 := max_eq_right (le_of_lt hlt)
    have hnorm : ‖(max 0 (1 - p.2.val.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 3)))‖
        = max 0 (1 - p.2.val.ofLp 0) := by
      rw [norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm p.1).2, mul_one,
        abs_of_nonneg (le_max_left _ _)]
    refine Prod.ext ?_ ?_
    · show (chartAt (EuclideanSpace ℝ (Fin 2)) u₀)
        (diskDir ⟨max 0 (1 - p.2.val.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 3)),
          collar_invFun_mem u₀ p⟩) = p.1
      rw [diskDir_scaled _ hc hc1 (collar_invFun_mem u₀ p)]
      exact (chartAt (EuclideanSpace ℝ (Fin 2)) u₀).right_inv
        (by rw [chart_target_univ]; exact Set.mem_univ p.1)
    · apply Subtype.ext
      show WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖(max 0 (1 - p.2.val.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 3)))‖)
          = p.2.val
      rw [hnorm, hmax, sub_sub_cancel]
      exact toLp_ofLp_fin_one _
  open_source := by
    have hU : IsOpen {v : ThreeDisk | (↑v : EuclideanSpace ℝ (Fin 3)) ≠ 0} :=
      isOpen_compl_singleton.preimage continuous_subtype_val
    exact continuousOn_diskDir.isOpen_inter_preimage hU
      (chartAt (EuclideanSpace ℝ (Fin 2)) u₀).open_source
  open_target := by
    apply isOpen_lt _ continuous_const
    exact (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
      (continuous_subtype_val.comp continuous_snd)
  continuousOn_toFun := by
    apply ContinuousOn.prodMk
    · exact (chartAt (EuclideanSpace ℝ (Fin 2)) u₀).continuousOn.comp
        (continuousOn_diskDir.mono (fun v hv => hv.1)) (fun v hv => hv.2)
    · apply Continuous.continuousOn
      apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro _
      exact continuous_const.sub (continuous_norm.comp continuous_subtype_val)
  continuousOn_invFun := by
    have hsymm : Continuous fun x => (chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x := by
      have h := (chartAt (EuclideanSpace ℝ (Fin 2)) u₀).continuousOn_symm
      rw [chart_target_univ] at h
      exact continuousOn_univ.mp h
    -- v4.32: `Continuous.smul` concludes the PI-smul form `(f • g)`, so `apply` no longer
    -- unifies it with the pointwise goal. Bind both factors, ascribe the product at the
    -- POINTWISE type (still defeq), and close with `exact`.
    apply Continuous.continuousOn
    have hscal : Continuous fun p : EuclideanSpace ℝ (Fin 2) × EuclideanHalfSpace 1 =>
        max 0 (1 - p.2.val.ofLp 0) :=
      continuous_const.max (continuous_const.sub
        ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
          (continuous_subtype_val.comp continuous_snd)))
    have hvec : Continuous fun p : EuclideanSpace ℝ (Fin 2) × EuclideanHalfSpace 1 =>
        ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 3)) :=
      continuous_subtype_val.comp (hsymm.comp continuous_fst)
    have hprod : Continuous fun p : EuclideanSpace ℝ (Fin 2) × EuclideanHalfSpace 1 =>
        max 0 (1 - p.2.val.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 3)) :=
      hscal.smul hvec
    exact Continuous.subtype_mk hprod _

/-! ### §3. The charted-space structure on `D³` -/

/-- **The closed unit 3-ball is a charted space** on the half-space model
`ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)` (`= (𝓡 2).prod (𝓡∂ 1)`): the atlas is
the single interior chart together with the polar collar chart family, with the interior chart
covering `{‖v‖ < 1}` and the collar chart at `diskDir v` covering the boundary sphere `‖v‖ = 1`.
This removes Mathlib gap 1 of the `S²×D³` bounding freeze (`Metric.closedBall` had no
`ChartedSpace` instance for `n ≥ 2`). -/
instance instChartedSpaceThreeDisk :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)) ThreeDisk where
  atlas := insert diskInteriorChart (Set.range diskCollarChart)
  chartAt v := if ‖(↑v : EuclideanSpace ℝ (Fin 3))‖ < 1 then diskInteriorChart
    else diskCollarChart (diskDir v)
  mem_chart_source v := by
    by_cases h : ‖(↑v : EuclideanSpace ℝ (Fin 3))‖ < 1
    · rw [if_pos h]; exact h
    · rw [if_neg h]
      have hv1 : ‖(↑v : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
        le_antisymm (mem_closedBall_zero_iff.mp v.2) (not_lt.mp h)
      refine ⟨?_, mem_chart_source (EuclideanSpace ℝ (Fin 2)) (diskDir v)⟩
      rw [← norm_ne_zero_iff, hv1]; norm_num
  chart_mem_atlas v := by
    by_cases h : ‖(↑v : EuclideanSpace ℝ (Fin 3))‖ < 1
    · rw [if_pos h]; exact Set.mem_insert _ _
    · rw [if_neg h]; exact Set.mem_insert_of_mem _ (Set.mem_range_self _)

end

end SKEFTHawking.DiskChart
