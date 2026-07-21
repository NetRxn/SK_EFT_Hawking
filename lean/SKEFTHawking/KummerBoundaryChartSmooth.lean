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

end

end SKEFTHawking.KummerBoundaryChartSmooth
