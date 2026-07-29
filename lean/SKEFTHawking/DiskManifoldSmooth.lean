/-
# Phase 5q.H — closed 3-ball smooth atlas (SphereDiskSmoothData freeze, slice C)

Slice C of discharging the `SphereProductBounding.SphereDiskSmoothData` freeze: this module proves
the SMOOTHNESS half of Mathlib gap 1 — the transition maps of the closed-3-ball atlas
(`SKEFTHawking.DiskChart.instChartedSpaceThreeDisk`) are `C^k`, giving

  `IsManifold ((𝓡 2).prod (𝓡∂ 1)) k ThreeDisk`

on the half-space model `ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)` that the
`ChartedSpace` instance uses (slice B removed the ATLAS half).

Reusable smoothness substrate (built here, consumed by the transition classes):
* `contDiffOn_normalize` — `v ↦ ‖v‖⁻¹ • v` is `C^k` on the punctured space `{v ≠ 0}`;
* `contDiff_assemble` / `contDiff_splitLo` — the `E² × ℝ ≅ E³` coordinate iso is `C^k`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.DiskChart

open Metric Set
open scoped Manifold

namespace SKEFTHawking.DiskManifoldSmooth

open SKEFTHawking.SpinSigmaRoute (TwoSphere ThreeDisk)
open SKEFTHawking.DiskManifold
open SKEFTHawking.DiskChart

noncomputable section

/-! ### §0. Reusable smoothness primitives -/

/-- **Normalization is smooth away from the origin.** `v ↦ ‖v‖⁻¹ • v` (the underlying vector of
`diskDir`) is `C^k` on the punctured 3-space `{v ≠ 0}`. -/
theorem contDiffOn_normalize {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖⁻¹ • v) {v | v ≠ 0} := by
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hn : ContDiffAt ℝ n (fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖) x := contDiffAt_norm ℝ hx0
  have hinv : ContDiffAt ℝ n (fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖⁻¹) x :=
    hn.inv (norm_ne_zero_iff.mpr hx0)
  exact (hinv.smul contDiffAt_id).contDiffWithinAt

/-- `assemble` is smooth in its two arguments (the `E² × ℝ → E³` half of the coordinate iso). -/
theorem contDiff_assemble {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => assemble p.1 p.2) := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using contDiff_snd
  · -- v4.32: the composed form and the `WithLp`/`EuclideanSpace` synonym differ syntactically
    -- but not definitionally, and `simpa`'s closing step will not bridge them. Normalise the
    -- hypothesis first, then close.
    have h : ContDiff ℝ n (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => p.1.ofLp j) :=
      (contDiff_apply ℝ ℝ j).comp (PiLp.contDiff_ofLp.comp contDiff_fst)
    simp only [Function.comp_def] at h
    simpa only [Fin.snoc_castSucc] using h

/-- `splitLo` is smooth (the `E³ → E²` low-block projection). -/
theorem contDiff_splitLo {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun w : EuclideanSpace ℝ (Fin 3) => splitLo w) :=
  PiLp.contDiff_toLp.comp
    (contDiff_pi.mpr fun i => (contDiff_apply ℝ ℝ (Fin.castSucc i)).comp PiLp.contDiff_ofLp)

/-- **The stereographic chart transition of `S²` is `C^k`.** Extracted from the sphere's own
`IsManifold (𝓡 2) ω` structure (`ω`-smooth ⟹ `C^k` via `IsManifold.of_le le_top`); the reusable
input to the collar-chart transition classes of `D³`. -/
theorem contDiffOn_sphereTransition {k : WithTop ℕ∞} (u₀ u₁ : TwoSphere) :
    ContDiffOn ℝ k (↑(extChartAt (𝓡 2) u₁) ∘ ↑(extChartAt (𝓡 2) u₀).symm)
      ((extChartAt (𝓡 2) u₀).symm.trans (extChartAt (𝓡 2) u₁)).source := by
  haveI : IsManifold (𝓡 2) k TwoSphere := IsManifold.of_le le_top
  exact contDiffOn_ext_coord_change (I := 𝓡 2) u₁ u₀

/-! ### §0b. Keystone: the `stereographic ∘ normalize` composite -/

/-- Local dimension fact for `S² ⊆ E³`, needed by every `stereographic'` unfold. -/
instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Forward-apply of the `S²` stereographic chart in the `stereoToFun`/`repr` normal form. -/
theorem chartAt_twoSphere_apply (u s : TwoSphere) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) u) s
      = (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
          (ne_zero_of_mem_unit_sphere (-u))).repr
          (stereoToFun ((-u : TwoSphere) : EuclideanSpace ℝ (Fin 3))
            (s : EuclideanSpace ℝ (Fin 3))) := rfl

/-- **Keystone.** The raw composite `w ↦ repr (stereoToFun (-u) (w/‖w‖))` — i.e.
`chartAt_{S²} u ∘ diskDir` unfolded to coordinate level — is `C^k` on the punctured non-north-pole
locus. Built purely from `contDiffOn_normalize`, Mathlib's `contDiffOn_stereoToFun`, and the
`repr` linear isometry — NO `ContMDiff`↔`ContDiffOn` bridge. -/
theorem contDiffOn_reprStereoNormalize {k : WithTop ℕ∞} (u : TwoSphere) :
    ContDiffOn ℝ k
      (fun w : EuclideanSpace ℝ (Fin 3) =>
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
          (ne_zero_of_mem_unit_sphere (-u))).repr
          (stereoToFun ((-u : TwoSphere) : EuclideanSpace ℝ (Fin 3)) (‖w‖⁻¹ • w)))
      {w : EuclideanSpace ℝ (Fin 3) | w ≠ 0 ∧
        innerSL ℝ ((-u : TwoSphere) : EuclideanSpace ℝ (Fin 3)) (‖w‖⁻¹ • w) ≠ 1} :=
  (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
        (ne_zero_of_mem_unit_sphere (-u))).repr.contDiff.comp_contDiffOn
      contDiffOn_stereoToFun).comp
    (contDiffOn_normalize.mono (fun _ hw => hw.1)) (fun _ hw => hw.2))

/-- The `S²` stereographic chart's source is the complement of the base point's antipode. -/
theorem chartAt_twoSphere_source (u : TwoSphere) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) u).source = {-u}ᶜ := stereographic'_source (-u)

/-- Bridge: for a **unit** vector `y`, the north-pole exclusion `⟪-u, y⟫ ≠ 1` of `stereoToFun`
is equivalent to the sphere point being in the `u`-chart's source. -/
theorem innerSL_ne_one_of_mem_source {u : TwoSphere} {y : TwoSphere}
    (hmem : y ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) u).source) :
    innerSL ℝ ((-u : TwoSphere) : EuclideanSpace ℝ (Fin 3))
      (y : EuclideanSpace ℝ (Fin 3)) ≠ 1 := by
  rw [chartAt_twoSphere_source] at hmem
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hmem
  intro h
  rw [innerSL_apply_apply] at h
  have hu : ‖((-u : TwoSphere) : EuclideanSpace ℝ (Fin 3))‖ = 1 := mem_sphere_zero_iff_norm.mp (-u).2
  have hy : ‖(y : EuclideanSpace ℝ (Fin 3))‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
  rw [inner_eq_one_iff_of_norm_eq_one hu hy] at h
  exact hmem (Subtype.ext h).symm

/-- **The inverse `S²` stereographic chart is `C^k`** as a map into `E³` (`stereoInvFun`,
`repr.symm`, and the orthocomplement inclusion are all `C^k`). The reusable input to the
collar → interior transition (the `stereographic⁻¹` reconstruction). -/
theorem contDiff_chartSymm_coe {k : WithTop ℕ∞} (u : TwoSphere) :
    ContDiff ℝ k (fun w : EuclideanSpace ℝ (Fin 2) =>
      ((chartAt (EuclideanSpace ℝ (Fin 2)) u).symm w : EuclideanSpace ℝ (Fin 3))) := by
  have hcomp : ContDiff ℝ k (fun w : EuclideanSpace ℝ (Fin 2) =>
      stereoInvFunAux ((-u : TwoSphere) : EuclideanSpace ℝ (Fin 3))
        (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
            (ne_zero_of_mem_unit_sphere (-u))).repr.symm w :
          (ℝ ∙ ((-u : TwoSphere) : EuclideanSpace ℝ (Fin 3)))ᗮ) :
          EuclideanSpace ℝ (Fin 3))) :=
    contDiff_stereoInvFunAux.comp
      ((ℝ ∙ ((-u : TwoSphere) : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL.contDiff.comp
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
          (ne_zero_of_mem_unit_sphere (-u))).repr.symm.contDiff)
  have heq : ∀ w : EuclideanSpace ℝ (Fin 2),
      ((chartAt (EuclideanSpace ℝ (Fin 2)) u).symm w : EuclideanSpace ℝ (Fin 3))
        = stereoInvFunAux ((-u : TwoSphere) : EuclideanSpace ℝ (Fin 3))
          (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
              (ne_zero_of_mem_unit_sphere (-u))).repr.symm w :
            (ℝ ∙ ((-u : TwoSphere) : EuclideanSpace ℝ (Fin 3)))ᗮ) :
            EuclideanSpace ℝ (Fin 3)) := by
    intro w
    show ((stereographic' 2 (-u)).symm w : EuclideanSpace ℝ (Fin 3)) = _
    rw [stereographic'_symm_apply, stereoInvFunAux_apply, smul_add]
  simpa only [heq] using hcomp

/-- The interior-chart reconstruction map `p ↦ assemble p.1 (p.2₀ − 2)` is `C^k`. -/
theorem contDiff_assembleShift {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) =>
      assemble p.1 (p.2.ofLp 0 - 2)) :=
  contDiff_assemble.comp (contDiff_fst.prodMk
    (((contDiff_apply ℝ ℝ 0).comp (PiLp.contDiff_ofLp.comp contDiff_snd)).sub contDiff_const))

/-! ### §1. `IsManifold` — the smooth atlas of `D³` (remaining transition-class assembly)

The headline instance `IsManifold ((𝓡 2).prod (𝓡∂ 1)) k ThreeDisk` follows from
`isManifold_of_contDiffOn`, splitting over the atlas `insert diskInteriorChart (range diskCollarChart)`
into four transition classes (`rcases he with rfl | ⟨u₀, rfl⟩ <;> rcases he' with rfl | ⟨u₁, rfl⟩`):

* **interior ↔ interior** (diagonal): closes immediately with
  `exact (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_contDiffGroupoid _)).1`.
* **collar u₀ ↔ collar u₁**: the coordinate transition is `Prod.map T id` with
  `T = chartAt E² u₁ ∘ (chartAt E² u₀).symm` (the radial coordinate is shared and cancels via
  `toLp_ofLp_fin_one`); `ContDiffOn.congr` against `fun p => (T p.1, p.2)`, whose smoothness is
  `contDiffOn_sphereTransition` (below) `Prod`-paired with `contDiffOn_snd`.
* **interior ↔ collar** and **collar ↔ interior**: the coordinate transition's sphere component is
  `chartAt E² u ∘ diskDir ∘ assemble` — the `stereographic∘normalize` composite; its `ContDiffOn` is
  the one remaining missing reusable lemma, buildable purely at the coordinate level (NO
  `ContMDiff`↔`ContDiffOn` bridge) from `contDiffOn_stereoToFun` (Mathlib) ∘ `contDiffOn_normalize`
  (below) ∘ `contDiff_assemble` (below), after unfolding `stereographic'`/`stereographic_apply`.

All four classes additionally need the `Set.MapsTo` domain-containment feeding each `ContDiffOn.comp`.
The four `§0` lemmas are the complete reusable substrate for this assembly. -/

/-- **Transition class: interior → collar.** The coordinate change from the interior chart to the
`u₁`-collar chart is `C^k`. Its sphere block is the `stereographic ∘ normalize` keystone precomposed
with the interior reconstruction `assemble`; its radial block is `1 − ‖·‖`. -/
theorem contDiffOn_transition_IC {k : WithTop ℕ∞} (u₁ : TwoSphere) :
    ContDiffOn ℝ k (↑((𝓡 2).prod (𝓡∂ 1)) ∘ ↑(diskInteriorChart.symm ≫ₕ diskCollarChart u₁) ∘
        ↑((𝓡 2).prod (𝓡∂ 1)).symm)
      (↑((𝓡 2).prod (𝓡∂ 1)).symm ⁻¹' (diskInteriorChart.symm ≫ₕ diskCollarChart u₁).source ∩
        range ↑((𝓡 2).prod (𝓡∂ 1))) := by
  have key : ∀ p ∈ (↑((𝓡 2).prod (𝓡∂ 1)).symm ⁻¹'
        (diskInteriorChart.symm ≫ₕ diskCollarChart u₁).source ∩ range ↑((𝓡 2).prod (𝓡∂ 1))),
        ‖assemble p.1 (p.2.ofLp 0 - 2)‖ < 1 ∧
        assemble p.1 (p.2.ofLp 0 - 2) ≠ 0 ∧
        innerSL ℝ ((-u₁ : TwoSphere) : EuclideanSpace ℝ (Fin 3))
          (‖assemble p.1 (p.2.ofLp 0 - 2)‖⁻¹ • assemble p.1 (p.2.ofLp 0 - 2)) ≠ 1 := by
    intro p hp
    obtain ⟨hpsrc, hprange⟩ := hp
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.symm_source, Set.mem_preimage] at hpsrc
    simp only [ModelWithCorners.prod_symm_apply, modelWithCornersSelf_coe_symm, id_eq] at hpsrc
    obtain ⟨hpt, hpg⟩ := hpsrc
    rw [ModelWithCorners.range_prod] at hprange
    have hri := ModelWithCorners.right_inv (𝓡∂ 1) hprange.2
    set z : EuclideanHalfSpace 1 := (𝓡∂ 1).symm p.2 with hzdef
    have hzval : z.val = p.2 := hri
    have hnorm : ‖assemble p.1 (p.2.ofLp 0 - 2)‖ < 1 := by
      have h : ‖assemble p.1 (z.val.ofLp 0 - 2)‖ < 1 := hpt
      rwa [hzval] at h
    set q : ThreeDisk := diskInteriorChart.symm (p.1, z) with hqdef
    have hqval : (q : EuclideanSpace ℝ (Fin 3)) = assemble p.1 (p.2.ofLp 0 - 2) := by
      show (ballClamp (assemble p.1 (z.val.ofLp 0 - 2)) : EuclideanSpace ℝ (Fin 3))
        = assemble p.1 (p.2.ofLp 0 - 2)
      rw [ballClamp_coe_of_norm_le (le_of_lt (by rw [hzval]; exact hnorm)), hzval]
    obtain ⟨hne0, hchart⟩ := hpg
    refine ⟨hnorm, ?_, ?_⟩
    · rw [← hqval]; exact hne0
    · have h := innerSL_ne_one_of_mem_source hchart
      rw [diskDir_coe hne0, hqval] at h
      exact h
  apply ContDiffOn.congr (f := fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) =>
      (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
          (ne_zero_of_mem_unit_sphere (-u₁))).repr
          (stereoToFun ((-u₁ : TwoSphere) : EuclideanSpace ℝ (Fin 3))
            (‖assemble p.1 (p.2.ofLp 0 - 2)‖⁻¹ • assemble p.1 (p.2.ofLp 0 - 2)))),
        (WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖assemble p.1 (p.2.ofLp 0 - 2)‖))))
  · refine ContDiffOn.prodMk ?_ ?_
    · exact (contDiffOn_reprStereoNormalize u₁).comp contDiff_assembleShift.contDiffOn
        (fun p hp => ⟨(key p hp).2.1, (key p hp).2.2⟩)
    · have hnorm_cd : ContDiffOn ℝ k (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) =>
          ‖assemble p.1 (p.2.ofLp 0 - 2)‖) _ :=
        fun p hp => ((contDiffAt_norm ℝ (key p hp).2.1).comp p
          contDiff_assembleShift.contDiffAt).contDiffWithinAt
      have htoLp : ContDiff ℝ k (fun r : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => r)) :=
        PiLp.contDiff_toLp.comp (contDiff_pi.mpr (fun _ => contDiff_id))
      exact htoLp.comp_contDiffOn (contDiffOn_const.sub hnorm_cd)
  · intro x hx
    obtain ⟨hnorm, hne0, -⟩ := key x hx
    obtain ⟨-, hxrange⟩ := hx
    rw [ModelWithCorners.range_prod] at hxrange
    have hri := ModelWithCorners.right_inv (𝓡∂ 1) hxrange.2
    set z : EuclideanHalfSpace 1 := (𝓡∂ 1).symm x.2 with hzdef
    have hzval : z.val = x.2 := hri
    set q : ThreeDisk := diskInteriorChart.symm (x.1, z) with hqdef
    have hqval : (q : EuclideanSpace ℝ (Fin 3)) = assemble x.1 (x.2.ofLp 0 - 2) := by
      show (ballClamp (assemble x.1 (z.val.ofLp 0 - 2)) : EuclideanSpace ℝ (Fin 3))
        = assemble x.1 (x.2.ofLp 0 - 2)
      rw [ballClamp_coe_of_norm_le (le_of_lt (by rw [hzval]; exact hnorm)), hzval]
    have hqne : (q : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by rw [hqval]; exact hne0
    show (chartAt (EuclideanSpace ℝ (Fin 2)) u₁ (diskDir q),
        WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖(q : EuclideanSpace ℝ (Fin 3))‖)) = _
    rw [chartAt_twoSphere_apply, diskDir_coe hqne, hqval]

/-- **Transition class: collar → interior.** The coordinate change from the `u₀`-collar chart to the
interior chart is `C^k`. Its reconstruction is the `stereographic⁻¹` inverse chart scaled by the
radial coordinate; both output blocks (`splitLo`, last coordinate `+2`) are linear in it. -/
theorem contDiffOn_transition_CI {k : WithTop ℕ∞} (u₀ : TwoSphere) :
    ContDiffOn ℝ k (↑((𝓡 2).prod (𝓡∂ 1)) ∘ ↑((diskCollarChart u₀).symm ≫ₕ diskInteriorChart) ∘
        ↑((𝓡 2).prod (𝓡∂ 1)).symm)
      (↑((𝓡 2).prod (𝓡∂ 1)).symm ⁻¹' ((diskCollarChart u₀).symm ≫ₕ diskInteriorChart).source ∩
        range ↑((𝓡 2).prod (𝓡∂ 1))) := by
  have key : ∀ x ∈ (↑((𝓡 2).prod (𝓡∂ 1)).symm ⁻¹'
        ((diskCollarChart u₀).symm ≫ₕ diskInteriorChart).source ∩ range ↑((𝓡 2).prod (𝓡∂ 1))),
      x.2.ofLp 0 < 1 := by
    intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.symm_source, Set.mem_preimage] at hxsrc
    simp only [ModelWithCorners.prod_symm_apply, modelWithCornersSelf_coe_symm, id_eq] at hxsrc
    obtain ⟨hpt, -⟩ := hxsrc
    rw [ModelWithCorners.range_prod] at hxrange
    have hri := ModelWithCorners.right_inv (𝓡∂ 1) hxrange.2
    set z : EuclideanHalfSpace 1 := (𝓡∂ 1).symm x.2 with hzdef
    have hzval : z.val = x.2 := hri
    have h : z.val.ofLp 0 < 1 := hpt
    rwa [hzval] at h
  have hV : ContDiff ℝ k (fun x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) =>
      (1 - x.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x.1 :
        EuclideanSpace ℝ (Fin 3))) :=
    (contDiff_const.sub ((contDiff_apply ℝ ℝ 0).comp (PiLp.contDiff_ofLp.comp contDiff_snd))).smul
      ((contDiff_chartSymm_coe u₀).comp contDiff_fst)
  have htoLp : ContDiff ℝ k (fun r : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => r)) :=
    PiLp.contDiff_toLp.comp (contDiff_pi.mpr (fun _ => contDiff_id))
  apply ContDiffOn.congr (f := fun x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) =>
      (splitLo ((1 - x.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x.1 :
          EuclideanSpace ℝ (Fin 3))),
        WithLp.toLp 2 (fun _ : Fin 1 =>
          ((1 - x.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x.1 :
            EuclideanSpace ℝ (Fin 3))).ofLp (Fin.last 2) + 2)))
  · exact ((contDiff_splitLo.comp hV).prodMk
      (htoLp.comp (((contDiff_apply ℝ ℝ (Fin.last 2)).comp
        (PiLp.contDiff_ofLp.comp hV)).add contDiff_const))).contDiffOn
  · intro x hx
    have hlt := key x hx
    obtain ⟨-, hxrange⟩ := hx
    rw [ModelWithCorners.range_prod] at hxrange
    have hri := ModelWithCorners.right_inv (𝓡∂ 1) hxrange.2
    set z : EuclideanHalfSpace 1 := (𝓡∂ 1).symm x.2 with hzdef
    have hzval : z.val = x.2 := hri
    set q : ThreeDisk := (diskCollarChart u₀).symm (x.1, z) with hqdef
    have hqval : (q : EuclideanSpace ℝ (Fin 3))
        = (1 - x.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x.1 :
          EuclideanSpace ℝ (Fin 3)) := by
      show (max 0 (1 - z.val.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x.1 :
          EuclideanSpace ℝ (Fin 3))) = _
      rw [hzval, max_eq_right (by linarith)]
    show (splitLo (q : EuclideanSpace ℝ (Fin 3)),
        WithLp.toLp 2 (fun _ : Fin 1 => (q : EuclideanSpace ℝ (Fin 3)).ofLp (Fin.last 2) + 2)) = _
    rw [hqval]

/-- **Transition class: collar → collar.** The coordinate change from the `u₀`-collar chart to the
`u₁`-collar chart is `C^k`. Its sphere block is the `S²` chart transition `chartAt u₁ ∘ chartAt u₀⁻¹`
(the radial factor cancels via `diskDir_smul_unit`); its radial block is the identity. -/
theorem contDiffOn_transition_CC {k : WithTop ℕ∞} (u₀ u₁ : TwoSphere) :
    ContDiffOn ℝ k (↑((𝓡 2).prod (𝓡∂ 1)) ∘ ↑((diskCollarChart u₀).symm ≫ₕ diskCollarChart u₁) ∘
        ↑((𝓡 2).prod (𝓡∂ 1)).symm)
      (↑((𝓡 2).prod (𝓡∂ 1)).symm ⁻¹' ((diskCollarChart u₀).symm ≫ₕ diskCollarChart u₁).source ∩
        range ↑((𝓡 2).prod (𝓡∂ 1))) := by
  have key : ∀ x ∈ (↑((𝓡 2).prod (𝓡∂ 1)).symm ⁻¹'
        ((diskCollarChart u₀).symm ≫ₕ diskCollarChart u₁).source ∩ range ↑((𝓡 2).prod (𝓡∂ 1))),
      (0 ≤ x.2.ofLp 0 ∧ x.2.ofLp 0 < 1) ∧
        innerSL ℝ ((-u₁ : TwoSphere) : EuclideanSpace ℝ (Fin 3))
          ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x.1 : EuclideanSpace ℝ (Fin 3)) ≠ 1 := by
    intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.symm_source, Set.mem_preimage] at hxsrc
    simp only [ModelWithCorners.prod_symm_apply, modelWithCornersSelf_coe_symm, id_eq] at hxsrc
    obtain ⟨hpt, hpg⟩ := hxsrc
    rw [ModelWithCorners.range_prod] at hxrange
    have hri := ModelWithCorners.right_inv (𝓡∂ 1) hxrange.2
    have hge : (0 : ℝ) ≤ x.2.ofLp 0 := by
      have h2 := hxrange.2
      rw [range_modelWithCornersEuclideanHalfSpace] at h2
      exact h2
    set z : EuclideanHalfSpace 1 := (𝓡∂ 1).symm x.2 with hzdef
    have hzval : z.val = x.2 := hri
    have hlt : x.2.ofLp 0 < 1 := by
      have h : z.val.ofLp 0 < 1 := hpt
      rwa [hzval] at h
    have hc0 : (0 : ℝ) < max 0 (1 - z.val.ofLp 0) :=
      lt_of_lt_of_le (by rw [hzval]; linarith) (le_max_right _ _)
    have hc1 : max 0 (1 - z.val.ofLp 0) ≤ 1 := max_le zero_le_one (by rw [hzval]; linarith)
    obtain ⟨-, hchart⟩ := hpg
    have hdir : diskDir ((diskCollarChart u₀).symm (x.1, z)) = (chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x.1 :=
      diskDir_scaled _ hc0 hc1 (collar_invFun_mem u₀ (x.1, z))
    rw [hdir] at hchart
    exact ⟨⟨hge, hlt⟩, innerSL_ne_one_of_mem_source hchart⟩
  apply ContDiffOn.congr (f := fun x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) =>
      (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
          (ne_zero_of_mem_unit_sphere (-u₁))).repr
          (stereoToFun ((-u₁ : TwoSphere) : EuclideanSpace ℝ (Fin 3))
            ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x.1 : EuclideanSpace ℝ (Fin 3)))),
        x.2))
  · refine ContDiffOn.prodMk ?_ contDiff_snd.contDiffOn
    exact ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
        (ne_zero_of_mem_unit_sphere (-u₁))).repr.contDiff.comp_contDiffOn
        contDiffOn_stereoToFun).comp ((contDiff_chartSymm_coe u₀).comp contDiff_fst).contDiffOn
      (fun x hx => (key x hx).2)
  · intro x hx
    obtain ⟨⟨hge, hlt⟩, -⟩ := key x hx
    obtain ⟨-, hxrange⟩ := hx
    rw [ModelWithCorners.range_prod] at hxrange
    have hri := ModelWithCorners.right_inv (𝓡∂ 1) hxrange.2
    set z : EuclideanHalfSpace 1 := (𝓡∂ 1).symm x.2 with hzdef
    have hzval : z.val = x.2 := hri
    have hc0 : (0 : ℝ) < max 0 (1 - z.val.ofLp 0) :=
      lt_of_lt_of_le (by rw [hzval]; linarith) (le_max_right _ _)
    have hc1 : max 0 (1 - z.val.ofLp 0) ≤ 1 := max_le zero_le_one (by rw [hzval]; linarith)
    set q : ThreeDisk := (diskCollarChart u₀).symm (x.1, z) with hqdef
    have hdir : diskDir q = (chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x.1 :=
      diskDir_scaled _ hc0 hc1 (collar_invFun_mem u₀ (x.1, z))
    have hnormq : ‖(q : EuclideanSpace ℝ (Fin 3))‖ = 1 - x.2.ofLp 0 := by
      show ‖max 0 (1 - z.val.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x.1 :
          EuclideanSpace ℝ (Fin 3))‖ = 1 - x.2.ofLp 0
      rw [norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin 2)) u₀).symm x.1).2, mul_one,
        abs_of_nonneg (le_max_left _ _), hzval, max_eq_right (by linarith)]
    show (chartAt (EuclideanSpace ℝ (Fin 2)) u₁ (diskDir q),
        WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖(q : EuclideanSpace ℝ (Fin 3))‖)) = _
    rw [hdir, chartAt_twoSphere_apply]
    congr 1
    rw [hnormq, sub_sub_cancel]
    exact toLp_ofLp_fin_one x.2

theorem isManifold_threeDisk {k : WithTop ℕ∞} :
    IsManifold ((𝓡 2).prod (𝓡∂ 1)) k ThreeDisk := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simp only [atlas] at he he'
  rcases he with rfl | ⟨u₀, rfl⟩ <;> rcases he' with rfl | ⟨u₁, rfl⟩
  · exact (mem_groupoid_of_pregroupoid.mp (symm_trans_mem_contDiffGroupoid _)).1
  · exact contDiffOn_transition_IC u₁
  · exact contDiffOn_transition_CI u₀
  · exact contDiffOn_transition_CC u₀ u₁

end

end SKEFTHawking.DiskManifoldSmooth
