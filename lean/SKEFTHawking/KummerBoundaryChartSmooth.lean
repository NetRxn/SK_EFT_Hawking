/-
# Phase 5q.H — the smoothness upgrade of the `T⁴°` boundary-chart certificate

This module upgrades the banked TOPOLOGICAL `ChartedSpace` certificate of `KummerBoundaryChart.lean`
(`instChartedSpacePuncturedTorus`) toward the SMOOTH `IsManifold ((𝓡 3).prod (𝓡∂ 1)) k` structure by
proving its atlas transition maps are `C^k`. It is the `S³`-boundary analogue, one dimension up, of
`DiskManifoldSmooth.lean` (the closed-3-ball `IsManifold` arc): the reusable smoothness substrate
(`contDiffOn_normalize` on `E⁴`, the `S³` stereographic chart transitions, the `stereographic ∘
normalize` keystone) is the same shape as the `S²` substrate there, and drives the four transition
classes of the punctured-torus atlas.

Reusable smoothness substrate (§0, consumed by the transition classes):
* `contDiffOn_normalize` — `v ↦ ‖v‖⁻¹ • v` is `C^k` on the punctured `E⁴`;
* `contDiff_chartSymm_coe` — the inverse `S³` stereographic chart `E³ → E⁴` is `C^k`;
* `contDiffOn_reprStereoNormalize` — the `stereographic ∘ normalize` composite (the crux keystone).

First GREEN deliverable: `isManifold_extShell` — the exterior shell `ExtShell` (whose atlas is the
polar collar chart family alone) is a smooth manifold-with-boundary. This is the heart of the
collar–collar transition class of the punctured torus (they reduce to shell transitions through the
common `collarHomeo`), and it is a clean, self-contained certificate in its own right.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerBoundaryChart

open Metric Set
open scoped Manifold

namespace SKEFTHawking.KummerBoundaryChartSmooth

open SKEFTHawking.KummerShellChart
open SKEFTHawking.KummerBoundaryChart
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerK3Base
open SKEFTHawking.DiskChartGeneric (NSphere)

noncomputable section

/-- Local dimension fact for `S³ ⊆ E⁴`, needed by every `stereographic'` unfold and by the sphere's
own `ChartedSpace`/`IsManifold` instances. -/
instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (3 + 1))) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-! ### §0. Reusable smoothness primitives for `S³ ⊆ E⁴` -/

/-- **Normalization is smooth away from the origin.** `v ↦ ‖v‖⁻¹ • v` (the underlying vector of
`shellDir`) is `C^k` on the punctured 4-space `{v ≠ 0}`. -/
theorem contDiffOn_normalize {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun v : EuclideanSpace ℝ (Fin 4) => ‖v‖⁻¹ • v) {v | v ≠ 0} := by
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hn : ContDiffAt ℝ n (fun v : EuclideanSpace ℝ (Fin 4) => ‖v‖) x := contDiffAt_norm ℝ hx0
  have hinv : ContDiffAt ℝ n (fun v : EuclideanSpace ℝ (Fin 4) => ‖v‖⁻¹) x :=
    hn.inv (norm_ne_zero_iff.mpr hx0)
  exact (hinv.smul contDiffAt_id).contDiffWithinAt

/-- Forward-apply of the `S³` stereographic chart in the `stereoToFun`/`repr` normal form. -/
theorem chartAt_threeSphere_apply (u s : NSphere 3) :
    (chartAt (EuclideanSpace ℝ (Fin 3)) u) s
      = (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
          (ne_zero_of_mem_unit_sphere (-u))).repr
          (stereoToFun ((-u : NSphere 3) : EuclideanSpace ℝ (Fin 4))
            (s : EuclideanSpace ℝ (Fin 4))) := rfl

/-- The `S³` stereographic chart's source is the complement of the base point's antipode. -/
theorem chartAt_threeSphere_source (u : NSphere 3) :
    (chartAt (EuclideanSpace ℝ (Fin 3)) u).source = {-u}ᶜ := stereographic'_source (-u)

/-- Bridge: for a **unit** vector `y`, the north-pole exclusion `⟪-u, y⟫ ≠ 1` of `stereoToFun`
is equivalent to the sphere point being in the `u`-chart's source. -/
theorem innerSL_ne_one_of_mem_source {u y : NSphere 3}
    (hmem : y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) u).source) :
    innerSL ℝ ((-u : NSphere 3) : EuclideanSpace ℝ (Fin 4))
      (y : EuclideanSpace ℝ (Fin 4)) ≠ 1 := by
  rw [chartAt_threeSphere_source] at hmem
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hmem
  intro h
  rw [innerSL_apply_apply] at h
  have hu : ‖((-u : NSphere 3) : EuclideanSpace ℝ (Fin 4))‖ = 1 := mem_sphere_zero_iff_norm.mp (-u).2
  have hy : ‖(y : EuclideanSpace ℝ (Fin 4))‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
  rw [inner_eq_one_iff_of_norm_eq_one hu hy] at h
  exact hmem (Subtype.ext h).symm

/-- **The inverse `S³` stereographic chart is `C^k`** as a map into `E⁴` (`stereoInvFun`, `repr.symm`,
and the orthocomplement inclusion are all `C^k`). The reusable input to the collar → interior
transition (the `stereographic⁻¹` reconstruction). -/
theorem contDiff_chartSymm_coe {k : WithTop ℕ∞} (u : NSphere 3) :
    ContDiff ℝ k (fun w : EuclideanSpace ℝ (Fin 3) =>
      ((chartAt (EuclideanSpace ℝ (Fin 3)) u).symm w : EuclideanSpace ℝ (Fin 4))) := by
  have hcomp : ContDiff ℝ k (fun w : EuclideanSpace ℝ (Fin 3) =>
      stereoInvFunAux ((-u : NSphere 3) : EuclideanSpace ℝ (Fin 4))
        (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
            (ne_zero_of_mem_unit_sphere (-u))).repr.symm w :
          (ℝ ∙ ((-u : NSphere 3) : EuclideanSpace ℝ (Fin 4)))ᗮ) :
          EuclideanSpace ℝ (Fin 4))) :=
    contDiff_stereoInvFunAux.comp
      ((ℝ ∙ ((-u : NSphere 3) : EuclideanSpace ℝ (Fin 4)))ᗮ.subtypeL.contDiff.comp
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
          (ne_zero_of_mem_unit_sphere (-u))).repr.symm.contDiff)
  have heq : ∀ w : EuclideanSpace ℝ (Fin 3),
      ((chartAt (EuclideanSpace ℝ (Fin 3)) u).symm w : EuclideanSpace ℝ (Fin 4))
        = stereoInvFunAux ((-u : NSphere 3) : EuclideanSpace ℝ (Fin 4))
          (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
              (ne_zero_of_mem_unit_sphere (-u))).repr.symm w :
            (ℝ ∙ ((-u : NSphere 3) : EuclideanSpace ℝ (Fin 4)))ᗮ) :
            EuclideanSpace ℝ (Fin 4)) := by
    intro w
    show ((stereographic' 3 (-u)).symm w : EuclideanSpace ℝ (Fin 4)) = _
    rw [stereographic'_symm_apply, stereoInvFunAux_apply, smul_add]
  simpa only [heq] using hcomp

/-! ### §0b. Keystone: the `stereographic ∘ normalize` composite (crux input for collar ↔ interior) -/

/-- **Keystone.** The raw composite `w ↦ repr (stereoToFun (-u) (w/‖w‖))` — i.e.
`chartAt_{S³} u ∘ shellDir` unfolded to coordinate level — is `C^k` on the punctured non-north-pole
locus. Built purely from `contDiffOn_normalize`, Mathlib's `contDiffOn_stereoToFun`, and the
`repr` linear isometry — NO `ContMDiff`↔`ContDiffOn` bridge. -/
theorem contDiffOn_reprStereoNormalize {k : WithTop ℕ∞} (u : NSphere 3) :
    ContDiffOn ℝ k
      (fun w : EuclideanSpace ℝ (Fin 4) =>
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
          (ne_zero_of_mem_unit_sphere (-u))).repr
          (stereoToFun ((-u : NSphere 3) : EuclideanSpace ℝ (Fin 4)) (‖w‖⁻¹ • w)))
      {w : EuclideanSpace ℝ (Fin 4) | w ≠ 0 ∧
        innerSL ℝ ((-u : NSphere 3) : EuclideanSpace ℝ (Fin 4)) (‖w‖⁻¹ • w) ≠ 1} :=
  (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
        (ne_zero_of_mem_unit_sphere (-u))).repr.contDiff.comp_contDiffOn
      contDiffOn_stereoToFun).comp
    (contDiffOn_normalize.mono (fun _ hw => hw.1)) (fun _ hw => hw.2))

/-! ### §1. The exterior shell `ExtShell` is a smooth manifold-with-boundary -/

/-- **Collar–collar transition of `ExtShell`.** The coordinate change from the `u₀`-polar-collar chart
to the `u₁`-polar-collar chart is `C^k`. Its sphere block is the `S³` chart transition
`chartAt u₁ ∘ chartAt u₀⁻¹` (the radial factor cancels via `shellDir_scaled`); its radial block is the
identity (`‖(1/2 + t)•dir‖ − 1/2 = t`). This is the `S³` analogue of `DiskManifoldSmooth`'s CC class,
with a pure-identity radial block (no `1 − ‖·‖`). -/
theorem contDiffOn_shellTransition_CC {k : WithTop ℕ∞} (u₀ u₁ : NSphere 3) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘ ↑((shellCollarChart u₀).symm ≫ₕ shellCollarChart u₁) ∘
        ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' ((shellCollarChart u₀).symm ≫ₕ shellCollarChart u₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  have key : ∀ x ∈ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        ((shellCollarChart u₀).symm ≫ₕ shellCollarChart u₁).source ∩ range ↑((𝓡 3).prod (𝓡∂ 1))),
      0 ≤ x.2.ofLp 0 ∧
        innerSL ℝ ((-u₁ : NSphere 3) : EuclideanSpace ℝ (Fin 4))
          ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm x.1 : EuclideanSpace ℝ (Fin 4)) ≠ 1 := by
    intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.symm_source, Set.mem_preimage] at hxsrc
    simp only [ModelWithCorners.prod_symm_apply, modelWithCornersSelf_coe_symm, id_eq] at hxsrc
    obtain ⟨-, hpg⟩ := hxsrc
    rw [ModelWithCorners.range_prod] at hxrange
    have hge : (0 : ℝ) ≤ x.2.ofLp 0 := by
      have h2 := hxrange.2
      rw [range_modelWithCornersEuclideanHalfSpace] at h2
      exact h2
    have hri := ModelWithCorners.right_inv (𝓡∂ 1) hxrange.2
    set z : EuclideanHalfSpace 1 := (𝓡∂ 1).symm x.2 with hzdef
    have hzval : z.val = x.2 := hri
    have hr : (1 : ℝ) / 2 ≤ 1 / 2 + z.val.ofLp 0 := by
      have : (0 : ℝ) ≤ z.val.ofLp 0 := z.2
      linarith
    have hdir : shellDir ((shellCollarChart u₀).symm (x.1, z))
        = (chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm x.1 :=
      shellDir_scaled _ hr (collar_invFun_mem u₀ (x.1, z))
    have hpg' : shellDir ((shellCollarChart u₀).symm (x.1, z))
        ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) u₁).source := hpg
    rw [hdir] at hpg'
    exact ⟨hge, innerSL_ne_one_of_mem_source hpg'⟩
  apply ContDiffOn.congr (f := fun x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
      (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
          (ne_zero_of_mem_unit_sphere (-u₁))).repr
          (stereoToFun ((-u₁ : NSphere 3) : EuclideanSpace ℝ (Fin 4))
            ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm x.1 : EuclideanSpace ℝ (Fin 4)))),
        x.2))
  · refine ContDiffOn.prodMk ?_ contDiff_snd.contDiffOn
    exact ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
        (ne_zero_of_mem_unit_sphere (-u₁))).repr.contDiff.comp_contDiffOn
        contDiffOn_stereoToFun).comp ((contDiff_chartSymm_coe u₀).comp contDiff_fst).contDiffOn
      (fun x hx => (key x hx).2)
  · intro x hx
    obtain ⟨hge, -⟩ := key x hx
    obtain ⟨-, hxrange⟩ := hx
    rw [ModelWithCorners.range_prod] at hxrange
    have hri := ModelWithCorners.right_inv (𝓡∂ 1) hxrange.2
    set z : EuclideanHalfSpace 1 := (𝓡∂ 1).symm x.2 with hzdef
    have hzval : z.val = x.2 := hri
    have hr : (1 : ℝ) / 2 ≤ 1 / 2 + z.val.ofLp 0 := by
      have : (0 : ℝ) ≤ z.val.ofLp 0 := z.2
      linarith
    set q : ExtShell := (shellCollarChart u₀).symm (x.1, z) with hqdef
    have hdir : shellDir q = (chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm x.1 :=
      shellDir_scaled _ hr (collar_invFun_mem u₀ (x.1, z))
    have hnormq : ‖(q : EuclideanSpace ℝ (Fin 4))‖ = 1 / 2 + x.2.ofLp 0 := by
      show ‖(1 / 2 + z.val.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm x.1 : EuclideanSpace ℝ (Fin 4))‖
          = 1 / 2 + x.2.ofLp 0
      rw [norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm x.1).2, mul_one,
        abs_of_nonneg (by linarith), hzval]
    show (chartAt (EuclideanSpace ℝ (Fin 3)) u₁ (shellDir q),
        WithLp.toLp 2 (fun _ : Fin 1 => ‖(q : EuclideanSpace ℝ (Fin 4))‖ - 1 / 2)) = _
    rw [hdir, chartAt_threeSphere_apply]
    congr 1
    rw [hnormq, add_sub_cancel_left]
    exact DiskChartGeneric.toLp_ofLp_fin_one x.2

/-- **`ExtShell` is a smooth manifold-with-boundary** on `(𝓡 3).prod (𝓡∂ 1)`. Its atlas is the polar
collar chart family alone; every transition is the collar–collar class, discharged by
`contDiffOn_shellTransition_CC`. The `S³`-boundary analogue of `DiskManifoldSmooth.isManifold_threeDisk`,
one dimension up. -/
theorem isManifold_extShell {k : WithTop ℕ∞} :
    IsManifold ((𝓡 3).prod (𝓡∂ 1)) k ExtShell := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨u₀, rfl⟩ := he
  obtain ⟨u₁, rfl⟩ := he'
  exact contDiffOn_shellTransition_CC u₀ u₁

/-! ### §2. Toward `IsManifold ↥puncturedTorus` — the T⁴° atlas transition classes -/

/-- Each collar sits inside the metric `3/4`-ball at its fixed point: the chart-radius is `< 3/4`
and the sup-metric distance is bounded by the chart radius (`dist_centeredChartParam_lt`). -/
theorem collarSet_subset_ball34 (c : TorusFour) :
    collarSet c ⊆ Metric.ball c (3 / 4) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [centeredChartParamE4_apply, Metric.mem_ball]
  refine dist_centeredChartParam_lt c (by norm_num) ?_
  rw [sqNorm_ofE4]
  nlinarith [hw.2, norm_nonneg w]

/-- **Different-`c` collars are disjoint.** The fixed points have separation `≥ 2` (`fixedSet_dist_ge`)
and each collar lies in the metric `3/4`-ball, so `3/4 + 3/4 = 3/2 < 2` forces disjointness. The
geometric content behind the vacuous collar–collar (different-`c`) transition class. -/
theorem collarSet_disjoint {c c' : TorusFour} (hc : c ∈ fixedSet) (hc' : c' ∈ fixedSet)
    (hne : c ≠ c') : Disjoint (collarSet c) (collarSet c') := by
  rw [Set.disjoint_left]
  intro y hy hy'
  have h1 : dist y c < 3 / 4 := collarSet_subset_ball34 c hy
  have h2 : dist y c' < 3 / 4 := collarSet_subset_ball34 c' hy'
  have hsep : (2 : ℝ) ≤ dist c c' := fixedSet_dist_ge hc hc' hne
  have htri : dist c c' ≤ dist c y + dist y c' := dist_triangle _ _ _
  rw [dist_comm c y] at htri
  linarith

/-- The `.symm` of a boundary chart lands (underlying `TorusFour` point) in its own collar. -/
theorem boundaryChart_symm_coe_mem {c : TorusFour} (hc : c ∈ fixedSet) (u₀ : NSphere 3) (p : Model) :
    (((boundaryChart c u₀ hc).symm p : ↥puncturedTorus) : TorusFour) ∈ collarSet c := by
  rw [boundaryChart, OpenPartialHomeomorph.lift_openEmbedding_symm]
  exact ((innerCollarChart c u₀).symm p).2

/-- A point in a boundary chart's source has underlying `TorusFour` point in that collar. -/
theorem boundaryChart_source_coe_mem {c' : TorusFour} (hc' : c' ∈ fixedSet) (u₁ : NSphere 3)
    {q : ↥puncturedTorus} (hq : q ∈ (boundaryChart c' u₁ hc').source) :
    (q : TorusFour) ∈ collarSet c' := by
  rw [boundaryChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hq
  obtain ⟨q₀, _, rfl⟩ := hq
  exact q₀.2

/-- **Transition class: collar → collar, different fixed points (vacuous).** For `c ≠ c'` the two
collars are disjoint, so the transition's source is empty and the coordinate change is `C^k` vacuously. -/
theorem contDiffOn_transition_collar_collar_diff {k : WithTop ℕ∞}
    {c c' : TorusFour} (hc : c ∈ fixedSet) (hc' : c' ∈ fixedSet) (hne : c ≠ c')
    (u₀ u₁ : NSphere 3) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((boundaryChart c u₀ hc).symm ≫ₕ boundaryChart c' u₁ hc') ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((boundaryChart c u₀ hc).symm ≫ₕ boundaryChart c' u₁ hc').source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  have hempty : ((boundaryChart c u₀ hc).symm ≫ₕ boundaryChart c' u₁ hc').source = ∅ := by
    rw [OpenPartialHomeomorph.trans_source]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hp2
    rw [Set.mem_preimage] at hp2
    have hmem : (((boundaryChart c u₀ hc).symm p : ↥puncturedTorus) : TorusFour) ∈ collarSet c :=
      boundaryChart_symm_coe_mem hc u₀ p
    have hmem' : (((boundaryChart c u₀ hc).symm p : ↥puncturedTorus) : TorusFour) ∈ collarSet c' :=
      boundaryChart_source_coe_mem hc' u₁ hp2
    exact (Set.disjoint_left.mp (collarSet_disjoint hc hc' hne) hmem) hmem'
  rw [hempty, Set.preimage_empty, Set.empty_inter]
  exact contDiffOn_empty

/-- **Transition class: collar → collar, same fixed point.** Reduces (via `lift_openEmbedding_trans`,
both charts lifted along the same collar open embedding) to the inner transition
`(innerCollarChart c u₀).symm ≫ (innerCollarChart c u₁)`, whose coordinate map is the shell collar–collar
transition (the shared `collarHomeo`/shell-embedding prefix cancels), discharged by
`contDiffOn_shellTransition_CC`. -/
theorem contDiffOn_transition_collar_collar_same {k : WithTop ℕ∞}
    {c : TorusFour} (hc : c ∈ fixedSet) (u₀ u₁ : NSphere 3) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((boundaryChart c u₀ hc).symm ≫ₕ boundaryChart c u₁ hc) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((boundaryChart c u₀ hc).symm ≫ₕ boundaryChart c u₁ hc).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  simp only [boundaryChart, OpenPartialHomeomorph.lift_openEmbedding_trans]
  -- The shared prefix is `A = (collarHomeo c).symm.toOPH` then `E = shell open-embedding`; both cancel.
  -- From the inner target, the shell preimage lies in `E.target`.
  have hkey : ∀ p : Model, p ∈ (innerCollarChart c u₀).target →
      (shellCollarChart u₀).symm p ∈
        (Topology.IsOpenEmbedding.toOpenPartialHomeomorph shellIncl isOpenEmbedding_shellIncl).target := by
    intro p hp
    simp only [innerCollarChart, OpenPartialHomeomorph.trans_target, Set.mem_inter_iff,
      Set.mem_preimage, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
      Homeomorph.toOpenPartialHomeomorph_target] at hp
    exact hp.1.2
  -- The prefix cancels: `innerCollarChart u₁ ∘ (innerCollarChart u₀).symm = B₁ ∘ B₀.symm`.
  have hval : ∀ p : Model, p ∈ (innerCollarChart c u₀).target →
      innerCollarChart c u₁ ((innerCollarChart c u₀).symm p)
        = shellCollarChart u₁ ((shellCollarChart u₀).symm p) := by
    intro p hp
    have hE := hkey p hp
    simp only [innerCollarChart, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
      Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.toOpenPartialHomeomorph_symm_apply,
      Homeomorph.symm_symm, Homeomorph.symm_apply_apply]
    rw [(Topology.IsOpenEmbedding.toOpenPartialHomeomorph shellIncl
      isOpenEmbedding_shellIncl).right_inv hE]
  -- The source condition transfers likewise (the `chartAt u₁`-source membership is preserved).
  have hsrc : ∀ p : Model, p ∈ (innerCollarChart c u₀).target →
      (innerCollarChart c u₀).symm p ∈ (innerCollarChart c u₁).source →
      (shellCollarChart u₀).symm p ∈ (shellCollarChart u₁).source := by
    intro p hp hs
    have hE := hkey p hp
    simp only [innerCollarChart, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      Set.mem_preimage, OpenPartialHomeomorph.coe_trans_symm,
      Function.comp_apply, Homeomorph.toOpenPartialHomeomorph_apply,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.symm_symm,
      Homeomorph.symm_apply_apply] at hs
    rw [(Topology.IsOpenEmbedding.toOpenPartialHomeomorph shellIncl
      isOpenEmbedding_shellIncl).right_inv hE] at hs
    exact hs.2.2
  refine ((contDiffOn_shellTransition_CC u₀ u₁).mono ?_).congr ?_
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.symm_source, Set.mem_preimage] at hxsrc
    obtain ⟨ht, hs⟩ := hxsrc
    refine ⟨?_, hxrange⟩
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.symm_source, Set.mem_preimage]
    exact ⟨Set.mem_univ _, hsrc _ ht hs⟩
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.symm_source, Set.mem_preimage] at hxsrc
    obtain ⟨ht, _⟩ := hxsrc
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans]
    rw [hval _ ht]

/-! ### §2b. Reusable smoothness of the interior reshaping `interiorReshape` (crux input for 1a/1d) -/

/-- **Forward reshape coordinate map is `C^k`.** `↑I ∘ interiorReshape` (the first three ambient
coordinates repackaged into `𝔼³`, the fourth pushed through `Real.exp` into the boundary coordinate)
is `C^k` everywhere. The `φ` of the interior transition factoring. -/
theorem contDiff_I_interiorReshape {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
        EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
      (((𝓡 3).prod (𝓡∂ 1)) (interiorReshape p))) := by
  have h : (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
        EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
        (((𝓡 3).prod (𝓡∂ 1)) (interiorReshape p)))
      = (fun p => (WithLp.toLp 2 ![p.1.ofLp 0, p.2.1.ofLp 0, p.2.2.1.ofLp 0],
          WithLp.toLp 2 (fun _ : Fin 1 => Real.exp (p.2.2.2.ofLp 0)))) := rfl
  rw [h]
  apply ContDiff.prodMk
  · exact PiLp.contDiff_toLp.comp (contDiff_pi.mpr (fun i => by fin_cases i <;> simp <;> fun_prop))
  · exact PiLp.contDiff_toLp.comp (contDiff_pi.mpr (fun _ => by fun_prop))

/-- **Clean inverse reshape coordinate map is `C^k` on the interior region.** On `{0 < m.2.ofLp 0}` the
map `m ↦ (m.1 split into three, Real.log m.2.ofLp 0)` (the boundary coordinate pulled back by `Real.log`)
is `C^k`. This is `interiorReshape.symm ∘ I.symm` with the half-space clamp already resolved to the
identity by positivity — the `ψ` of the interior transition factoring. -/
theorem contDiffOn_interiorReshapeSymm_clean {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
        ((WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 0),
         WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 1),
         WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 2),
         WithLp.toLp 2 (fun _ : Fin 1 => Real.log (m.2.ofLp 0))) :
        EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
      {m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) | 0 < m.2.ofLp 0} := by
  apply ContDiffOn.prodMk
  · exact (PiLp.contDiff_toLp.comp (contDiff_pi.mpr (fun _ => by fun_prop))).contDiffOn
  apply ContDiffOn.prodMk
  · exact (PiLp.contDiff_toLp.comp (contDiff_pi.mpr (fun _ => by fun_prop))).contDiffOn
  apply ContDiffOn.prodMk
  · exact (PiLp.contDiff_toLp.comp (contDiff_pi.mpr (fun _ => by fun_prop))).contDiffOn
  · apply PiLp.contDiff_toLp.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro _
    apply Real.contDiffOn_log.comp
    · exact ((contDiff_apply ℝ ℝ 0).comp (PiLp.contDiff_ofLp.comp contDiff_snd)).contDiffOn
    · intro m hm
      exact ne_of_gt hm

/-- On the interior region `{0 < m.2.ofLp 0}`, the clean inverse reshape coordinate map equals the
genuine `interiorReshape.symm ∘ I.symm` (the half-space clamp `max · 0` is inactive by positivity). -/
theorem interiorReshapeSymm_eq_clean {m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)}
    (hpos : 0 < m.2.ofLp 0) :
    ((WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 0),
      WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 1),
      WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 2),
      WithLp.toLp 2 (fun _ : Fin 1 => Real.log (m.2.ofLp 0))) :
        EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
      = interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m) := by
  have he : (((𝓡 3).prod (𝓡∂ 1)).symm m).2.val.ofLp 0 = m.2.ofLp 0 :=
    max_eq_left (le_of_lt hpos)
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  show (WithLp.toLp 2 (fun _ : Fin 1 => Real.log (m.2.ofLp 0)) : EuclideanSpace ℝ (Fin 1))
      = WithLp.toLp 2 (fun _ : Fin 1 => Real.log ((((𝓡 3).prod (𝓡∂ 1)).symm m).2.val.ofLp 0))
  rw [he]

/-- Domain-membership extractor for the interior → interior transition on the reduced
`(chartAt x ≫ interiorReshape)`-form domain: positivity of the boundary coordinate, plus the ambient
chart target/source memberships of the reshaped point. -/
theorem interior_transition_key (x x' : ↥interiorOpens)
    {m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)}
    (hm : m ∈ ↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        ((chartAt PModel x ≫ₕ interiorReshape).symm ≫ₕ chartAt PModel x' ≫ₕ interiorReshape).source ∩
      range ↑((𝓡 3).prod (𝓡∂ 1))) :
    0 < m.2.ofLp 0 ∧
    interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m) ∈ (chartAt PModel x).target ∧
    (chartAt PModel x).symm (interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m)) ∈
      (chartAt PModel x').source := by
  obtain ⟨hmsrc, hmrange⟩ := hm
  rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, OpenPartialHomeomorph.trans_target, Set.mem_inter_iff] at hmsrc
  obtain ⟨⟨hmtarget, htgt2⟩, hsrc3⟩ := hmsrc
  have hval : (0 : ℝ) < (((𝓡 3).prod (𝓡∂ 1)).symm m).2.val.ofLp 0 := hmtarget
  have hposm : 0 < m.2.ofLp 0 := by
    have he : (((𝓡 3).prod (𝓡∂ 1)).symm m).2.val.ofLp 0 = max (m.2.ofLp 0) 0 := rfl
    rw [he] at hval
    rcases lt_max_iff.mp hval with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)
  refine ⟨hposm, ?_, ?_⟩
  · rw [Set.mem_preimage] at htgt2; exact htgt2
  · rw [Set.mem_preimage] at hsrc3
    simp only [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
      OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at hsrc3
    exact hsrc3.1

/-- **Transition class: interior → interior.** The coordinate change between two round-ball interior
charts is `C^k`. The lift embeddings cancel (`lift_openEmbedding_trans`), leaving
`interiorReshape.symm ≫ (ambient torus transition) ≫ interiorReshape`; the ambient block is `C^ω`
(the `T⁴` product smooth structure via `contDiffOn_ext_coord_change`) and the reshape blocks are the
`φ`/`ψ` exp/log coordinate maps above. -/
theorem contDiffOn_transition_interior_interior {k : WithTop ℕ∞} (x x' : ↥interiorOpens) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((interiorChartR x).symm ≫ₕ interiorChartR x') ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((interiorChartR x).symm ≫ₕ interiorChartR x').source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  simp only [interiorChartR, OpenPartialHomeomorph.lift_openEmbedding_trans]
  -- `MapsTo` of the clean inverse reshape into the ambient transition source.
  have hmaps : Set.MapsTo
      (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
        ((WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 0),
          WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 1),
          WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 2),
          WithLp.toLp 2 (fun _ : Fin 1 => Real.log (m.2.ofLp 0))) :
            EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
              EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((chartAt PModel x ≫ₕ interiorReshape).symm ≫ₕ chartAt PModel x' ≫ₕ interiorReshape).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1)))
      ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) x).symm.trans
        (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) x')).source := by
    intro m hm
    obtain ⟨hposm, htgt, hsrc⟩ := interior_transition_key x x' hm
    dsimp only
    rw [interiorReshapeSymm_eq_clean hposm, PartialEquiv.trans_source]
    refine ⟨?_, ?_⟩
    · rw [PartialEquiv.symm_source, extChartAt_target]
      exact ⟨htgt, interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m), rfl⟩
    · rw [Set.mem_preimage, extChartAt_source]
      exact hsrc
  -- Assemble the `φ ∘ T ∘ ψ` factoring; its function is inferred, so no expensive unification.
  have hF := (contDiff_I_interiorReshape (k := k)).comp_contDiffOn
    ((contDiffOn_ext_coord_change
        (I := (𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) (n := k) x' x).comp
      (contDiffOn_interiorReshapeSymm_clean.mono
        (fun m hm => (interior_transition_key x x' hm).1))
      hmaps)
  -- The genuine transition equals the factoring on the domain (positivity kills the clamp).
  refine hF.congr (fun m hm => ?_)
  obtain ⟨hposm, _, _⟩ := interior_transition_key x x' hm
  simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.coe_trans_symm]
  rw [interiorReshapeSymm_eq_clean hposm]
  rfl

/-! ### §2c. The round chart is smooth — the crux enabler for the collar ↔ interior seam (1d) -/

/-- **The extended round chart `centeredChartParamE4 c` is `C^k` into `T⁴`.** In `E⁴` coordinates
`w ↦ centeredChartParam c (ofE4 w) = (c.i · Circle.exp (w.ofLp i))ᵢ`, each factor is
`(left-translate by cᵢ) ∘ Circle.exp ∘ (coordinate projection)` — all `ContMDiff` (`Circle.exp` via
`contMDiff_circleExp`, left-translation via the `Circle` Lie-group `contMDiff_mul_left`). This is the
geometric heart of the collar ↔ interior transition class: the round chart of a boundary sphere is
smoothly compatible with the ambient `T⁴` product charts. -/
theorem contMDiff_centeredChartParamE4 {k : WithTop ℕ∞} (c : TorusFour) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4)))
      ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) k
      (fun w : EuclideanSpace ℝ (Fin 4) => centeredChartParam c (ofE4 w)) := by
  have hfac : ∀ (a : Circle) (j : Fin 4),
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4))) (𝓡 1) k
        (fun w : EuclideanSpace ℝ (Fin 4) => a * Circle.exp (w.ofLp j)) := by
    intro a j
    have hcoord : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4))) (𝓘(ℝ, ℝ)) k
        (fun w : EuclideanSpace ℝ (Fin 4) => w.ofLp j) := by
      rw [contMDiff_iff_contDiff]
      exact (contDiff_apply ℝ ℝ j).comp PiLp.contDiff_ofLp
    exact contMDiff_mul_left.comp ((contMDiff_circleExp (m := k)).comp hcoord)
  have h : (fun w : EuclideanSpace ℝ (Fin 4) => centeredChartParam c (ofE4 w))
      = fun w => (c.1 * Circle.exp (w.ofLp 0), c.2.1 * Circle.exp (w.ofLp 1),
          c.2.2.1 * Circle.exp (w.ofLp 2), c.2.2.2 * Circle.exp (w.ofLp 3)) := rfl
  rw [h]
  exact (hfac c.1 0).prodMk ((hfac c.2.1 1).prodMk ((hfac c.2.2.1 2).prodMk (hfac c.2.2.2 3)))

/-- **The round-chart → interior-coordinate smooth core.** On the locus where the round chart lands in
the ambient product chart's source, the coordinate map
`w ↦ I (interiorReshape (extChartAt J y (centeredChartParam c (ofE4 w))))` is `C^k`. This is the
analysis heart of the collar → interior transition class (1d): the round chart `centeredChartParamE4 c`
of a boundary sphere is `ContMDiff` (`contMDiff_centeredChartParamE4`), its `extChartAt`-coordinate rep
lands in the genuine normed product (`contMDiffOn_extChartAt` + `contMDiffOn_iff_contDiffOn`, dodging the
`ModelProd` instance opacity), and `I ∘ interiorReshape` is `C^k` (`contDiff_I_interiorReshape`). -/
theorem contDiffOn_roundToInterior_core {k : WithTop ℕ∞} (c : TorusFour) (y : TorusFour) :
    ContDiffOn ℝ k
      (fun w : EuclideanSpace ℝ (Fin 4) =>
        ((𝓡 3).prod (𝓡∂ 1)) (interiorReshape (extChartAt
          ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y (centeredChartParam c (ofE4 w)))))
      ((fun w : EuclideanSpace ℝ (Fin 4) => centeredChartParam c (ofE4 w)) ⁻¹'
        (chartAt PModel y).source) := by
  have hext : ContMDiffOn ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) k
      (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y) (chartAt PModel y).source :=
    contMDiffOn_extChartAt
  have hcomp := hext.comp (contMDiff_centeredChartParamE4 c).contMDiffOn (fun w hw => hw)
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact contDiff_I_interiorReshape.comp_contDiffOn hcomp

/-! ### §2d. The collar ↔ interior seams (1d-CI, 1d-IC) — the round chart glued to the interior atlas -/

/-- Value of the collar homeomorphism: `collarHomeo c` sends a shell-band point to the round-chart
image of its `E⁴` vector. -/
theorem collarHomeo_coe (c : TorusFour) (s : ↥shellSetE4) :
    ((collarHomeo c s : ↥(collarSet c)) : TorusFour)
      = centeredChartParam c (ofE4 (s : EuclideanSpace ℝ (Fin 4))) := rfl

/-- **Gateway value lemma.** For `p` in the inner collar chart's target, the underlying `TorusFour`
point of `(boundaryChart c u₀ hc).symm p` is the round-chart image of the reconstructed `E⁴` shell
vector `(1/2 + p.2.ofLp 0) • (chart_{S³} u₀).symm p.1`. Unwraps the collar lift embedding
(`lift_openEmbedding_symm`), the `shellIncl` open embedding (`right_inv` on the shell band threaded
from the domain), and the `collarHomeo` `homeomorphOfImageSubsetSource` value. -/
theorem boundaryChart_symm_coe_eq {c : TorusFour} (hc : c ∈ fixedSet) (u₀ : NSphere 3)
    {p : Model} (hp : p ∈ (innerCollarChart c u₀).target) :
    ((boundaryChart c u₀ hc).symm p : TorusFour)
      = centeredChartParam c (ofE4 ((1 / 2 + p.2.val.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 4)))) := by
  have hE : (shellCollarChart u₀).symm p ∈
      (Topology.IsOpenEmbedding.toOpenPartialHomeomorph shellIncl isOpenEmbedding_shellIncl).target := by
    simp only [innerCollarChart, OpenPartialHomeomorph.trans_target, Set.mem_inter_iff,
      Set.mem_preimage, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
      Homeomorph.toOpenPartialHomeomorph_target] at hp
    exact hp.1.2
  rw [boundaryChart, OpenPartialHomeomorph.lift_openEmbedding_symm]
  show ((innerCollarChart c u₀).symm p : TorusFour) = _
  simp only [innerCollarChart, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
    Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.symm_symm]
  rw [collarHomeo_coe]
  congr 2
  have hri : shellIncl ((Topology.IsOpenEmbedding.toOpenPartialHomeomorph shellIncl
        isOpenEmbedding_shellIncl).symm ((shellCollarChart u₀).symm p))
      = (shellCollarChart u₀).symm p := by
    have h := (Topology.IsOpenEmbedding.toOpenPartialHomeomorph shellIncl
      isOpenEmbedding_shellIncl).right_inv hE
    rwa [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply] at h
  exact congrArg (fun t : ExtShell => (t : EuclideanSpace ℝ (Fin 4))) hri

/-- Value of the interior chart on a point of the round-ball interior region: `interiorChartR x'`
factors as `interiorReshape ∘ (ambient chart at ↑x')`, via the interior lift-embedding unwrapping
(`lift_openEmbedding_apply`) and the `Opens`-chart value bridge (`subtypeRestr_coe`). -/
theorem interiorChartR_apply_coe (x' : ↥interiorOpens) {y : ↥puncturedTorus}
    (hy : (y : TorusFour) ∈ interiorSet) :
    interiorChartR x' y
      = interiorReshape (chartAt PModel (x' : TorusFour) (y : TorusFour)) := by
  have happ := OpenPartialHomeomorph.lift_openEmbedding_apply
    (chartAt PModel x' ≫ₕ interiorReshape) isOpenEmbedding_interiorIncl
    (x := (⟨(y : TorusFour), hy⟩ : ↥interiorOpens))
  have hq : Set.inclusion interiorSet_subset_puncturedTorus
      (⟨(y : TorusFour), hy⟩ : ↥interiorOpens) = y := Subtype.ext rfl
  rw [hq] at happ
  rw [interiorChartR, happ, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe,
    Set.restrict_apply]

/-- A point of the interior chart's source has underlying `TorusFour` point in the round-ball
interior region. -/
theorem interiorChartR_source_coe_mem (x' : ↥interiorOpens) {q : ↥puncturedTorus}
    (hq : q ∈ (interiorChartR x').source) : (q : TorusFour) ∈ interiorSet := by
  rw [interiorChartR, OpenPartialHomeomorph.lift_openEmbedding_source] at hq
  obtain ⟨q₀, _, rfl⟩ := hq
  exact q₀.2

/-- A point of the interior chart's source has underlying `TorusFour` point in the ambient product
chart's source (the `Opens`-chart source pulled back to `T⁴`). -/
theorem interiorChartR_source_coe_mem_chartSource (x' : ↥interiorOpens) {q : ↥puncturedTorus}
    (hq : q ∈ (interiorChartR x').source) :
    (q : TorusFour) ∈ (chartAt PModel (x' : TorusFour)).source := by
  rw [interiorChartR, OpenPartialHomeomorph.lift_openEmbedding_source] at hq
  obtain ⟨q₀, hq₀, rfl⟩ := hq
  rw [OpenPartialHomeomorph.trans_source] at hq₀
  obtain ⟨hq₀src, -⟩ := hq₀
  rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
    Set.mem_preimage] at hq₀src
  exact hq₀src

/-- **Transition class: collar → interior (1d-CI).** The coordinate change from the `(c, u₀)`-boundary
collar chart to the round-ball interior chart `interiorChartR x'` is `C^k`. The collar chart inverse
reconstructs the `E⁴` shell vector `S m = (1/2 + m.2) • (chart_{S³} u₀).symm m.1` (`C^k` via
`contDiff_chartSymm_coe`), whose round image is the collar point; feeding it into
`contDiffOn_roundToInterior_core` gives the interior coordinate. -/
theorem contDiffOn_transition_collar_interior {k : WithTop ℕ∞}
    {c : TorusFour} (hc : c ∈ fixedSet) (u₀ : NSphere 3) (x' : ↥interiorOpens) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((boundaryChart c u₀ hc).symm ≫ₕ interiorChartR x') ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((boundaryChart c u₀ hc).symm ≫ₕ interiorChartR x').source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  have hS : ContDiff ℝ k (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
      (1 / 2 + m.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 :
        EuclideanSpace ℝ (Fin 4))) :=
    (contDiff_const.add ((contDiff_apply ℝ ℝ 0).comp (PiLp.contDiff_ofLp.comp contDiff_snd))).smul
      ((contDiff_chartSymm_coe u₀).comp contDiff_fst)
  have key : ∀ m ∈ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        ((boundaryChart c u₀ hc).symm ≫ₕ interiorChartR x').source ∩ range ↑((𝓡 3).prod (𝓡∂ 1))),
      ((boundaryChart c u₀ hc).symm (((𝓡 3).prod (𝓡∂ 1)).symm m) : TorusFour)
          = centeredChartParam c (ofE4 ((1 / 2 + m.2.ofLp 0) •
              ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 : EuclideanSpace ℝ (Fin 4)))) ∧
      ((boundaryChart c u₀ hc).symm (((𝓡 3).prod (𝓡∂ 1)).symm m)) ∈ (interiorChartR x').source := by
    intro m hm
    obtain ⟨hmsrc, hmrange⟩ := hm
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] at hmsrc
    obtain ⟨htgt, hsrc⟩ := hmsrc
    rw [boundaryChart, OpenPartialHomeomorph.lift_openEmbedding_target] at htgt
    rw [ModelWithCorners.range_prod] at hmrange
    have hri := ModelWithCorners.right_inv (𝓡∂ 1) hmrange.2
    have hval := boundaryChart_symm_coe_eq hc u₀ htgt
    have h1 : (((𝓡 3).prod (𝓡∂ 1)).symm m).1 = m.1 := rfl
    have h2 : (((𝓡 3).prod (𝓡∂ 1)).symm m).2.val = m.2 := hri
    rw [h1, h2] at hval
    exact ⟨hval, hsrc⟩
  apply ContDiffOn.congr (f := fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
      ((𝓡 3).prod (𝓡∂ 1)) (interiorReshape (extChartAt
        ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) (x' : TorusFour)
        (centeredChartParam c (ofE4 ((1 / 2 + m.2.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 : EuclideanSpace ℝ (Fin 4))))))))
  · exact (contDiffOn_roundToInterior_core c (x' : TorusFour)).comp hS.contDiffOn
      (fun m hm => by
        rw [Set.mem_preimage, ← (key m hm).1]
        exact interiorChartR_source_coe_mem_chartSource x' (key m hm).2)
  · intro m hm
    obtain ⟨hval, hsrc⟩ := key m hm
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    rw [interiorChartR_apply_coe x' (interiorChartR_source_coe_mem x' hsrc), hval]
    rfl

/-! ### §2e. The round-chart inverse is smooth — the re-centered `arg` inverse (the 1d-IC enabler)

The (1d-IC) seam needs the collar chart *forward*, whose analytic core is the round-chart inverse
`(centeredChartParamE4 c).symm` — built by `ofContinuousOpenRestrict`, so carrying no smoothness,
and Mathlib has no `HasMFDerivAt Circle.exp` for the manifold-IFT route. Instead we take the
**explicit re-centered `arg` route**: `centeredChartParam c` is per-factor `yᵢ = cᵢ · exp(tᵢ·I)`,
so its inverse is `tᵢ = arg (yᵢ · cᵢ⁻¹)`. The re-centering by `cᵢ⁻¹` is what kills the branch cut:
on the chart ball `‖w‖ < 3/4` every factor ratio `yᵢ · cᵢ⁻¹ = exp(tᵢ·I)` has `|tᵢ| ≤ ‖w‖ < 3/4 < π`,
so the ratio stays inside `slitPlane` regardless of where on the circle the factor `yᵢ` itself sits —
no second branch is ever needed. `arg = im ∘ log` is `C^k` on `slitPlane` (`analyticAt_clog`), giving
a `C^k` explicit inverse `roundChartInvE4 c : T⁴ → E⁴` on the slit-good open locus, agreeing with
`(collarHomeo c).symm` on the collar (`collarHomeo_symm_coe`). -/

/-- Local dimension fact for `Circle = S¹ ⊆ ℂ`, needed to apply the generic sphere smoothness
toolkit (`contMDiff_coe_sphere`) to the `Circle` factors of `T⁴`. -/
instance : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩

set_option backward.isDefEq.respectTransparency false in
/-- **`Complex.arg` is `C^k` on the slit plane**: `arg = im ∘ log` (`Complex.log_im`) with `log`
`ℂ`-analytic on `slitPlane` (`analyticAt_clog`), restricted to `ℝ`-scalars. (The
`respectTransparency` workaround is Mathlib's own idiom for the ℝ/ℂ `restrictScalars` instance
defeq — see `Mathlib.Analysis.SpecialFunctions.Complex.Analytic`, section `ReOfReal`.) -/
theorem contDiffOn_arg {k : WithTop ℕ∞} : ContDiffOn ℝ k Complex.arg Complex.slitPlane := by
  intro z hz
  have hlog : ContDiffAt ℝ k Complex.log z := ((analyticAt_clog hz).restrictScalars).contDiffAt
  have hd : ContDiffAt ℝ k (fun w => (Complex.log w).im) z :=
    (Complex.imCLM.contDiff.contDiffAt).comp z hlog
  exact (hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun w => (Complex.log_im w).symm)).contDiffWithinAt

/-- The re-centered circle angle at base `c₀`: the argument of the ratio `z · c₀⁻¹`. The per-factor
inverse of the centered chart `t ↦ c₀ · Circle.exp t`. -/
def circleCenteredArg (c₀ : Circle) (z : Circle) : ℝ := Complex.arg ((z * c₀⁻¹ : Circle) : ℂ)

/-- The slit-good locus of the `c`-centered round chart: all four factor ratios avoid the branch
cut. Contains the collar (`collarSet_subset_slitGoodSet`); on it the re-centered `arg` inverse is
`C^k` (`contMDiffOn_roundChartInvE4`). -/
def slitGoodSet (c : TorusFour) : Set TorusFour :=
  {y : TorusFour | ((y.1 * c.1⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane ∧
    ((y.2.1 * c.2.1⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane ∧
    ((y.2.2.1 * c.2.2.1⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane ∧
    ((y.2.2.2 * c.2.2.2⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane}

/-- **The explicit round-chart inverse** `T⁴ → E⁴`: the four re-centered factor angles packed into
`E⁴`. On the chart ball it inverts `centeredChartParamE4 c` exactly (`roundChartInvE4_param`). -/
def roundChartInvE4 (c : TorusFour) (y : TorusFour) : EuclideanSpace ℝ (Fin 4) :=
  toE4 (circleCenteredArg c.1 y.1, circleCenteredArg c.2.1 y.2.1,
    circleCenteredArg c.2.2.1 y.2.2.1, circleCenteredArg c.2.2.2 y.2.2.2)

/-- `arg (exp (a·I)) = a` inside the principal branch — the per-factor chart-inversion identity. -/
theorem arg_circleExp {a : ℝ} (ha : |a| < Real.pi) : ((Circle.exp a : Circle) : ℂ).arg = a := by
  rw [Circle.coe_exp, Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I ⟨(abs_lt.mp ha).1, (abs_lt.mp ha).2.le⟩

/-- A circle exponential inside the principal branch stays in the slit plane. -/
theorem circleExp_mem_slitPlane {a : ℝ} (ha : |a| < Real.pi) :
    ((Circle.exp a : Circle) : ℂ) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff_arg.mpr
    ⟨by rw [arg_circleExp ha]; exact ne_of_lt (abs_lt.mp ha).2, Circle.coe_ne_zero _⟩

/-- Coordinate bound in `E⁴`: each coordinate is dominated by the Euclidean norm. -/
theorem abs_ofLp_le_norm (w : EuclideanSpace ℝ (Fin 4)) (i : Fin 4) : |w.ofLp i| ≤ ‖w‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  calc w.ofLp i ^ 2 = ‖w.ofLp i‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ j, ‖w.ofLp j‖ ^ 2 := Finset.single_le_sum
        (f := fun j => ‖w.ofLp j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- Chart-ball coordinates lie strictly inside the principal branch: `‖w‖ < 3/4 < π`. -/
theorem abs_ofLp_lt_pi {w : EuclideanSpace ℝ (Fin 4)} (hw : ‖w‖ < 3 / 4) (i : Fin 4) :
    |w.ofLp i| < Real.pi :=
  lt_of_le_of_lt (abs_ofLp_le_norm w i) (lt_trans hw (by linarith [Real.pi_gt_three]))

/-- **The agreement identity**: on the chart ball `‖w‖ < 3/4`, the re-centered `arg` inverse
recovers the round-chart coordinate exactly. -/
theorem roundChartInvE4_param {c : TorusFour} {w : EuclideanSpace ℝ (Fin 4)}
    (hw : ‖w‖ < 3 / 4) : roundChartInvE4 c (centeredChartParam c (ofE4 w)) = w := by
  have hcomp : ∀ (c₀ : Circle) (i : Fin 4),
      circleCenteredArg c₀ (c₀ * Circle.exp (w.ofLp i)) = w.ofLp i := by
    intro c₀ i
    rw [circleCenteredArg, mul_inv_cancel_comm]
    exact arg_circleExp (abs_ofLp_lt_pi hw i)
  show toE4 (circleCenteredArg c.1 (c.1 * Circle.exp (w.ofLp 0)),
      circleCenteredArg c.2.1 (c.2.1 * Circle.exp (w.ofLp 1)),
      circleCenteredArg c.2.2.1 (c.2.2.1 * Circle.exp (w.ofLp 2)),
      circleCenteredArg c.2.2.2 (c.2.2.2 * Circle.exp (w.ofLp 3))) = w
  rw [hcomp c.1 0, hcomp c.2.1 1, hcomp c.2.2.1 2, hcomp c.2.2.2 3]
  exact toE4_ofE4 w

/-- The collar lies in the slit-good locus: every collar factor ratio is `exp(tᵢ·I)` with
`|tᵢ| < 3/4 < π`. -/
theorem collarSet_subset_slitGoodSet {c : TorusFour} : collarSet c ⊆ slitGoodSet c := by
  rintro y ⟨w, hw, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (((c.1 * Circle.exp (w.ofLp 0)) * c.1⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane
    rw [mul_inv_cancel_comm]
    exact circleExp_mem_slitPlane (abs_ofLp_lt_pi hw.2 0)
  · show (((c.2.1 * Circle.exp (w.ofLp 1)) * c.2.1⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane
    rw [mul_inv_cancel_comm]
    exact circleExp_mem_slitPlane (abs_ofLp_lt_pi hw.2 1)
  · show (((c.2.2.1 * Circle.exp (w.ofLp 2)) * c.2.2.1⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane
    rw [mul_inv_cancel_comm]
    exact circleExp_mem_slitPlane (abs_ofLp_lt_pi hw.2 2)
  · show (((c.2.2.2 * Circle.exp (w.ofLp 3)) * c.2.2.2⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane
    rw [mul_inv_cancel_comm]
    exact circleExp_mem_slitPlane (abs_ofLp_lt_pi hw.2 3)

/-- **The collar homeomorphism inverse in explicit form**: on the collar, `(collarHomeo c).symm`
IS the re-centered `arg` inverse. -/
theorem collarHomeo_symm_coe (c : TorusFour) (p : ↥(collarSet c)) :
    (((collarHomeo c).symm p : ↥shellSetE4) : EuclideanSpace ℝ (Fin 4))
      = roundChartInvE4 c (p : TorusFour) := by
  obtain ⟨s, rfl⟩ := (collarHomeo c).surjective p
  rw [Homeomorph.symm_apply_apply, collarHomeo_coe]
  exact (roundChartInvE4_param s.2.2).symm

/-- The re-centered circle angle is `C^k` on the slit-good factor locus, as a manifold map
`S¹ → ℝ`: `arg ∘ coe ∘ (· * c₀⁻¹)`, with the coercion smooth by `contMDiff_coe_sphere` and the
translation smooth by the `Circle` Lie-group structure. -/
theorem contMDiffOn_circleCenteredArg {k : WithTop ℕ∞} (c₀ : Circle) :
    ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) k (circleCenteredArg c₀)
      {z : Circle | ((z * c₀⁻¹ : Circle) : ℂ) ∈ Complex.slitPlane} := by
  have hcm : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) k (fun z : Circle => ((z * c₀⁻¹ : Circle) : ℂ)) :=
    contMDiff_coe_sphere.comp contMDiff_mul_right
  have harg : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) k Complex.arg Complex.slitPlane :=
    contMDiffOn_iff_contDiffOn.mpr contDiffOn_arg
  exact harg.comp hcm.contMDiffOn (fun z hz => hz)

/-- **The explicit round-chart inverse is `C^k` on the slit-good locus**, as a manifold map
`T⁴ → E⁴`: each coordinate is the re-centered factor angle through the corresponding projection,
packed by `WithLp.toLp`. -/
theorem contMDiffOn_roundChartInvE4 {k : WithTop ℕ∞} (c : TorusFour) :
    ContMDiffOn ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 4))) k (roundChartInvE4 c) (slitGoodSet c) := by
  have h0 : ContMDiffOn ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) 𝓘(ℝ, ℝ) k
      (fun y : TorusFour => circleCenteredArg c.1 y.1) (slitGoodSet c) :=
    (contMDiffOn_circleCenteredArg c.1).comp contMDiff_fst.contMDiffOn (fun y hy => hy.1)
  have h1 : ContMDiffOn ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) 𝓘(ℝ, ℝ) k
      (fun y : TorusFour => circleCenteredArg c.2.1 y.2.1) (slitGoodSet c) :=
    (contMDiffOn_circleCenteredArg c.2.1).comp
      (contMDiff_fst.comp contMDiff_snd).contMDiffOn (fun y hy => hy.2.1)
  have h2 : ContMDiffOn ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) 𝓘(ℝ, ℝ) k
      (fun y : TorusFour => circleCenteredArg c.2.2.1 y.2.2.1) (slitGoodSet c) :=
    (contMDiffOn_circleCenteredArg c.2.2.1).comp
      (contMDiff_fst.comp (contMDiff_snd.comp contMDiff_snd)).contMDiffOn (fun y hy => hy.2.2.1)
  have h3 : ContMDiffOn ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) 𝓘(ℝ, ℝ) k
      (fun y : TorusFour => circleCenteredArg c.2.2.2 y.2.2.2) (slitGoodSet c) :=
    (contMDiffOn_circleCenteredArg c.2.2.2).comp
      (contMDiff_snd.comp (contMDiff_snd.comp contMDiff_snd)).contMDiffOn (fun y hy => hy.2.2.2)
  have hφ : ContMDiffOn ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) 𝓘(ℝ, Fin 4 → ℝ) k
      (fun y : TorusFour => (![circleCenteredArg c.1 y.1, circleCenteredArg c.2.1 y.2.1,
        circleCenteredArg c.2.2.1 y.2.2.1, circleCenteredArg c.2.2.2 y.2.2.2] : Fin 4 → ℝ))
      (slitGoodSet c) := by
    rw [contMDiffOn_pi_space]
    intro i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  have htoLp : ContMDiff 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) k
      (WithLp.toLp 2 : (Fin 4 → ℝ) → EuclideanSpace ℝ (Fin 4)) :=
    contMDiff_iff_contDiff.mpr PiLp.contDiff_toLp
  exact (htoLp.comp_contMDiffOn hφ).congr (fun y hy => rfl)

/-- **The interior-coordinate → round-coordinate smooth core** — the (1d-IC) mirror of
`contDiffOn_roundToInterior_core`: the explicit round-chart inverse read through the ambient
product chart's inverse is `C^k` on the slit-good part of the extended chart target. -/
theorem contDiffOn_interiorToRound_core {k : WithTop ℕ∞} (c y : TorusFour) :
    ContDiffOn ℝ k
      (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
        roundChartInvE4 c
          ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).symm p))
      ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).target ∩
        (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).symm ⁻¹'
          slitGoodSet c) := by
  have hsymm : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
        EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
      ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) k
      ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).symm)
      (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).target :=
    contMDiffOn_extChartAt_symm y
  have hcomp := (contMDiffOn_roundChartInvE4 c).comp
    (hsymm.mono Set.inter_subset_left) (fun p hp => hp.2)
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp

/-- Forward value of the boundary chart on a collar point: unlift to the inner collar chart —
`shellCollarChart u₁` applied to the shell vector of the collar homeomorphism inverse. -/
theorem boundaryChart_apply_eq {c : TorusFour} (hc : c ∈ fixedSet) (u₁ : NSphere 3)
    {q : ↥puncturedTorus} (hq : (q : TorusFour) ∈ collarSet c) :
    boundaryChart c u₁ hc q
      = shellCollarChart u₁ (shellIncl ((collarHomeo c).symm ⟨(q : TorusFour), hq⟩)) := by
  have happ := OpenPartialHomeomorph.lift_openEmbedding_apply
    (innerCollarChart c u₁) (isOpenEmbedding_collarIncl hc)
    (x := (⟨(q : TorusFour), hq⟩ : ↥(collarSet c)))
  have hq' : Set.inclusion (collarSet_subset_puncturedTorus hc)
      (⟨(q : TorusFour), hq⟩ : ↥(collarSet c)) = q := Subtype.ext rfl
  rw [hq'] at happ
  rw [boundaryChart, happ]
  simp only [innerCollarChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    Homeomorph.toOpenPartialHomeomorph_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]

/-- **Inverse value of the interior chart** — the (1d-IC) mirror of `boundaryChart_symm_coe_eq`.
For `m'` in the interior chart's target: the boundary coordinate is strictly positive, the
un-reshaped coordinate lies in the ambient product chart's target, and the underlying `T⁴` point
of `(interiorChartR x).symm m'` is its ambient-chart inverse. -/
theorem interiorChartR_symm_key (x : ↥interiorOpens) {m' : Model}
    (hm' : m' ∈ (interiorChartR x).target) :
    0 < m'.2.val.ofLp 0 ∧
    interiorReshape.symm m' ∈ (chartAt PModel (x : TorusFour)).target ∧
    (((interiorChartR x).symm m' : ↥puncturedTorus) : TorusFour)
      = (chartAt PModel (x : TorusFour)).symm (interiorReshape.symm m') := by
  rw [interiorChartR, OpenPartialHomeomorph.lift_openEmbedding_target,
    OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at hm'
  obtain ⟨hresh, hopens⟩ := hm'
  rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_def,
    OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at hopens
  obtain ⟨htgt, hU⟩ := hopens
  refine ⟨hresh, htgt, ?_⟩
  rw [interiorChartR, OpenPartialHomeomorph.lift_openEmbedding_symm]
  show (((chartAt PModel x ≫ₕ interiorReshape).symm m' : ↥interiorOpens) : TorusFour) = _
  simp only [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
  rw [TopologicalSpace.Opens.chartAt_eq]
  refine ((chartAt PModel (x : TorusFour)).subtypeRestr_symm_eqOn
    (Nonempty.intro x) ?_).symm
  rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
    Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨htgt, hU⟩

/-- A collar point in the `(c, u₁)`-boundary chart's source has its shell direction in the base
`S³`-chart's source — the sphere-block admissibility of the collar chart forward. -/
theorem interior_collar_shell_key {c : TorusFour} (hc : c ∈ fixedSet) (u₁ : NSphere 3)
    {q : ↥puncturedTorus} (hsrc : q ∈ (boundaryChart c u₁ hc).source)
    (hcol : (q : TorusFour) ∈ collarSet c) :
    shellDir (shellIncl ((collarHomeo c).symm ⟨(q : TorusFour), hcol⟩))
      ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) u₁).source := by
  rw [boundaryChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hsrc
  obtain ⟨q₀, hq₀, hq₀q⟩ := hsrc
  have hcoe : (q₀ : TorusFour) = (q : TorusFour) :=
    congrArg (Subtype.val : ↥puncturedTorus → TorusFour) hq₀q
  have hq₀eq : q₀ = ⟨(q : TorusFour), hcol⟩ := Subtype.ext hcoe
  rw [hq₀eq] at hq₀
  simp only [innerCollarChart, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
    Set.mem_preimage, Homeomorph.toOpenPartialHomeomorph_source,
    Homeomorph.toOpenPartialHomeomorph_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply] at hq₀
  exact hq₀.2.2

/-- Domain-membership extractor for the interior → collar transition: positivity of the boundary
coordinate, the boundary-chart source membership of the reconstructed point, and the ambient-chart
target membership + value of the interior chart inverse. -/
theorem interior_collar_transition_key {c : TorusFour} (hc : c ∈ fixedSet) (u₁ : NSphere 3)
    (x : ↥interiorOpens) {m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)}
    (hm : m ∈ ↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        ((interiorChartR x).symm ≫ₕ boundaryChart c u₁ hc).source ∩
      range ↑((𝓡 3).prod (𝓡∂ 1))) :
    0 < m.2.ofLp 0 ∧
    (interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m) ∈ (boundaryChart c u₁ hc).source ∧
    interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m)
      ∈ (chartAt PModel (x : TorusFour)).target ∧
    (((interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m) : ↥puncturedTorus) : TorusFour)
      = (chartAt PModel (x : TorusFour)).symm
          (interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m)) := by
  obtain ⟨hmsrc, hmrange⟩ := hm
  rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage] at hmsrc
  obtain ⟨htgt, hsrc⟩ := hmsrc
  have hkey := interiorChartR_symm_key x htgt
  have hval : (0 : ℝ) < ((((𝓡 3).prod (𝓡∂ 1)).symm m).2).val.ofLp 0 := hkey.1
  have hposm : 0 < m.2.ofLp 0 := by
    have he : ((((𝓡 3).prod (𝓡∂ 1)).symm m).2).val.ofLp 0 = max (m.2.ofLp 0) 0 := rfl
    rw [he] at hval
    rcases lt_max_iff.mp hval with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)
  exact ⟨hposm, hsrc, hkey.2.1, hkey.2.2⟩

/-- **Transition class: interior → collar (1d-IC).** The coordinate change from the round-ball
interior chart `interiorChartR x` to the `(c, u₁)`-boundary collar chart is `C^k`. The interior
chart inverse reconstructs the `T⁴` point through the ambient product chart
(`interiorChartR_symm_key`); the explicit re-centered `arg` inverse `roundChartInvE4 c` produces
its `E⁴` shell vector (`collarHomeo_symm_coe`), smoothly (`contDiffOn_interiorToRound_core`); and
the polar collar chart forward maps it to the half-space model
(`contDiffOn_reprStereoNormalize` + the norm block). Mirror of
`contDiffOn_transition_collar_interior`, closing the fourth atlas transition class. -/
theorem contDiffOn_transition_interior_collar {k : WithTop ℕ∞}
    {c : TorusFour} (hc : c ∈ fixedSet) (u₁ : NSphere 3) (x : ↥interiorOpens) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((interiorChartR x).symm ≫ₕ boundaryChart c u₁ hc) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((interiorChartR x).symm ≫ₕ boundaryChart c u₁ hc).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  set V : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 4) :=
    fun m => roundChartInvE4 c
      ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) (x : TorusFour)).symm
        ((WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 0),
          WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 1),
          WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 2),
          WithLp.toLp 2 (fun _ : Fin 1 => Real.log (m.2.ofLp 0))))) with hVdef
  -- The per-point shell vector: `V m` is the shell vector of the reconstructed collar point.
  have keyV : ∀ m ∈ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        ((interiorChartR x).symm ≫ₕ boundaryChart c u₁ hc).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))), ∃ s : ↥shellSetE4,
      V m = (s : EuclideanSpace ℝ (Fin 4)) ∧
      shellDir (shellIncl s) ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) u₁).source ∧
      boundaryChart c u₁ hc ((interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m))
        = shellCollarChart u₁ (shellIncl s) := by
    intro m hm
    obtain ⟨hposm, hsrc, htgt, hval⟩ := interior_collar_transition_key hc u₁ x hm
    have hcol : (((interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m) :
        ↥puncturedTorus) : TorusFour) ∈ collarSet c :=
      boundaryChart_source_coe_mem hc u₁ hsrc
    refine ⟨(collarHomeo c).symm ⟨_, hcol⟩, ?_, interior_collar_shell_key hc u₁ hsrc hcol,
      boundaryChart_apply_eq hc u₁ hcol⟩
    rw [collarHomeo_symm_coe, hVdef]
    show roundChartInvE4 c _ = roundChartInvE4 c _
    rw [interiorReshapeSymm_eq_clean hposm]
    exact congrArg (roundChartInvE4 c) hval.symm
  -- Smoothness of the shell-vector field.
  have hVs : ContDiffOn ℝ k V (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
      ((interiorChartR x).symm ≫ₕ boundaryChart c u₁ hc).source ∩
      range ↑((𝓡 3).prod (𝓡∂ 1))) := by
    rw [hVdef]
    apply (contDiffOn_interiorToRound_core c (x : TorusFour)).comp
      (contDiffOn_interiorReshapeSymm_clean.mono
        (fun m hm => (interior_collar_transition_key hc u₁ x hm).1))
    intro m hm
    obtain ⟨hposm, hsrc, htgt, hval⟩ := interior_collar_transition_key hc u₁ x hm
    have hcol : (((interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m) :
        ↥puncturedTorus) : TorusFour) ∈ collarSet c :=
      boundaryChart_source_coe_mem hc u₁ hsrc
    dsimp only
    rw [interiorReshapeSymm_eq_clean hposm]
    constructor
    · rw [extChartAt_target]
      exact ⟨htgt, interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m), rfl⟩
    · rw [Set.mem_preimage]
      show (chartAt PModel (x : TorusFour)).symm
        (interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m)) ∈ slitGoodSet c
      rw [← hval]
      exact collarSet_subset_slitGoodSet hcol
  -- The factored composite: sphere block ∘ shell vector, radial block ∘ shell vector.
  apply ContDiffOn.congr (f := fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
    ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
        (ne_zero_of_mem_unit_sphere (-u₁))).repr
        (stereoToFun ((-u₁ : NSphere 3) : EuclideanSpace ℝ (Fin 4)) (‖V m‖⁻¹ • V m)),
      WithLp.toLp 2 (fun _ : Fin 1 => ‖V m‖ - 1 / 2)))
  · refine ContDiffOn.prodMk ?_ ?_
    · refine (contDiffOn_reprStereoNormalize u₁).comp hVs (fun m hm => ?_)
      obtain ⟨s, hVs_eq, hdir, -⟩ := keyV m hm
      have hne : V m ≠ 0 := by
        rw [hVs_eq]
        intro h
        have h2 := s.2.1
        rw [h, norm_zero] at h2
        linarith
      refine ⟨hne, ?_⟩
      have := innerSL_ne_one_of_mem_source hdir
      rwa [shellDir_coe, show ((shellIncl s : ExtShell) : EuclideanSpace ℝ (Fin 4))
        = (s : EuclideanSpace ℝ (Fin 4)) from rfl, ← hVs_eq] at this
    · apply PiLp.contDiff_toLp.comp_contDiffOn
      apply contDiffOn_pi.mpr
      intro _
      refine ContDiffOn.sub ?_ contDiffOn_const
      refine ContDiffOn.comp (g := fun v : EuclideanSpace ℝ (Fin 4) => ‖v‖)
        (t := {v : EuclideanSpace ℝ (Fin 4) | v ≠ 0})
        (fun v hv => (contDiffAt_norm ℝ hv).contDiffWithinAt) hVs (fun m hm => ?_)
      obtain ⟨s, hVs_eq, -, -⟩ := keyV m hm
      show V m ≠ 0
      rw [hVs_eq]
      intro h
      have h2 : (1 : ℝ) / 2 ≤ 0 := by
        have := s.2.1
        rwa [show ((s : EuclideanSpace ℝ (Fin 4))) = 0 from h, norm_zero] at this
      linarith
  · intro m hm
    obtain ⟨s, hVs_eq, hdir, happly⟩ := keyV m hm
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans]
    rw [happly]
    show (chartAt (EuclideanSpace ℝ (Fin 3)) u₁ (shellDir (shellIncl s)),
        WithLp.toLp 2 (fun _ : Fin 1 =>
          ‖((shellIncl s : ExtShell) : EuclideanSpace ℝ (Fin 4))‖ - 1 / 2)) = _
    rw [chartAt_threeSphere_apply, shellDir_coe]
    rw [show ((shellIncl s : ExtShell) : EuclideanSpace ℝ (Fin 4))
      = (s : EuclideanSpace ℝ (Fin 4)) from rfl, ← hVs_eq]

/-! ### §3. THE CERTIFICATE — `T⁴°` is a smooth manifold-with-boundary -/

/-- **`T⁴° = ↥puncturedTorus` is a `C^k` manifold-with-boundary** on `(𝓡 3).prod (𝓡∂ 1)` — the
smooth upgrade of the K4′′ topological certificate `instChartedSpacePuncturedTorus`. The atlas has
two chart families (round-ball interior charts, 16 boundary collar chart families), so four
transition classes, each discharged above: interior–interior
(`contDiffOn_transition_interior_interior`), collar → interior
(`contDiffOn_transition_collar_interior`), interior → collar
(`contDiffOn_transition_interior_collar`, via the re-centered `arg` round-chart inverse), and
collar–collar (`contDiffOn_transition_collar_collar_same`/`_diff`). Parametric in
`k : WithTop ℕ∞` — the structure is `C^k` for every `k`, up to `ω`. -/
theorem isManifold_puncturedTorus {k : WithTop ℕ∞} :
    IsManifold ((𝓡 3).prod (𝓡∂ 1)) k (↥puncturedTorus) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨x, rfl⟩ | he
  · rcases he' with ⟨x', rfl⟩ | he'
    · exact contDiffOn_transition_interior_interior x x'
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at he'
      obtain ⟨c, u₁, hc, rfl⟩ := he'
      exact contDiffOn_transition_interior_collar hc u₁ x
  · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at he
    obtain ⟨c, u₀, hc, rfl⟩ := he
    rcases he' with ⟨x', rfl⟩ | he'
    · exact contDiffOn_transition_collar_interior hc u₀ x'
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at he'
      obtain ⟨c', u₁, hc', rfl⟩ := he'
      by_cases hcc : c = c'
      · subst hcc
        exact contDiffOn_transition_collar_collar_same hc u₀ u₁
      · exact contDiffOn_transition_collar_collar_diff hc hc' hcc u₀ u₁

end

end SKEFTHawking.KummerBoundaryChartSmooth
