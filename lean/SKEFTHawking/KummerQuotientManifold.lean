/-
# Phase 5q.H — the smooth manifold-with-boundary certificate of the Kummer free quotient `Q = T⁴°/τ`

This module descends the `T⁴°` smooth certificate (`KummerBoundaryChartSmooth.isManifold_puncturedTorus`)
through the free ℤ/2 quotient map `qmk : T⁴° ↠ Q`, producing the `ChartedSpace`/`IsManifold`
certificate of `Q` on the same half-space model `(𝓡 3).prod (𝓡∂ 1)` — the K5′ boundary-chart
certificate (the `Q`-side input of the Kummer weld).

Architecture. The `Q`-atlas charts are `(qmk_localOpenPartialHomeomorph x).symm ≫ₕ C` with `C` a
`T⁴°` atlas chart (`KummerBoundaryChart.qmkBoundaryChart`/`qmkInteriorChart`). A `Q`-transition
composes a chart inverse, the local `qmk`-inverse at `x'` after the local `qmk` at `x` — the deck
map — and a chart forward. By the two-point fibre structure (`qmk_eq_iff`) the deck map is
pointwise `id` or the involution `τ = (-1 : ℤˣ) • ·`, and by freeness (`neg_one_smul_ne`) +
continuity the branch is **locally constant** (§Q3). So every `Q`-transition is locally a `T⁴°`
transition (the certified four classes) or a **`τ`-twisted** `T⁴°` transition — the four new
classes of §Q2, each reduced to the banked smoothness substrate through the `τ`-equivariance of
the round charts (`centeredChartParam_involution`: `τ` is `w ↦ −w` in the round chart) and the
Lie-group smoothness of `τ` on `T⁴` (`torusFourInvolution_contMDiff`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerBoundaryChartSmooth

open Metric Set
open scoped Manifold

namespace SKEFTHawking.KummerQuotientManifold

open SKEFTHawking.KummerShellChart
open SKEFTHawking.KummerBoundaryChart
open SKEFTHawking.KummerBoundaryChartSmooth
open SKEFTHawking.KummerPuncturedTorus
open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerInvolution
open SKEFTHawking.KummerFreeQuotient
open SKEFTHawking.KummerChartedSpace
open SKEFTHawking.DiskChartGeneric (NSphere)

noncomputable section

/-! ### §Q0. The deck involution on `T⁴°`, packaged -/

/-- The deck involution `τ = (-1 : ℤˣ) • ·` as a homeomorphism of `T⁴°` (the free ℤ/2 action). -/
def tauP : (↥puncturedTorus) ≃ₜ (↥puncturedTorus) := Homeomorph.smul ((-1 : ℤˣ))

@[simp] theorem tauP_apply (y : ↥puncturedTorus) : tauP y = (-1 : ℤˣ) • y := rfl

theorem tauP_symm_apply (y : ↥puncturedTorus) : tauP.symm y = (-1 : ℤˣ) • y := by
  rw [Homeomorph.symm_apply_eq, tauP_apply, smul_smul, Int.units_mul_self, one_smul]

/-- The deck involution as an `OpenPartialHomeomorph` (source and target `univ`), the middle factor
of the `τ`-twisted transition composites. -/
def tauOPH : OpenPartialHomeomorph (↥puncturedTorus) (↥puncturedTorus) :=
  tauP.toOpenPartialHomeomorph

@[simp] theorem tauOPH_apply (y : ↥puncturedTorus) : tauOPH y = (-1 : ℤˣ) • y := rfl

@[simp] theorem tauOPH_source : tauOPH.source = univ :=
  Homeomorph.toOpenPartialHomeomorph_source tauP

/-! ### §Q1. `τ`-equivariance of the chart regions -/

/-- Negation passes through the tuple/`E⁴` packaging: `chartNeg (ofE4 w) = ofE4 (−w)`. -/
theorem chartNeg_ofE4 (w : EuclideanSpace ℝ (Fin 4)) : chartNeg (ofE4 w) = ofE4 (-w) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [chartNeg, ofE4]

/-- **`τ` is `w ↦ −w` in the round chart at a fixed point** — the `E⁴` form of
`centeredChartParam_involution`. -/
theorem param_invol {c : TorusFour} (hc : c ∈ fixedSet) (w : EuclideanSpace ℝ (Fin 4)) :
    torusFourInvolution (centeredChartParam c (ofE4 w)) = centeredChartParam c (ofE4 (-w)) := by
  rw [centeredChartParam_involution c hc (ofE4 w), chartNeg_ofE4]

/-- The collar of a fixed point is `τ`-invariant (`w ↦ −w` preserves the shell band). -/
theorem collarSet_invol {c : TorusFour} (hc : c ∈ fixedSet) {y : TorusFour}
    (hy : y ∈ collarSet c) : torusFourInvolution y ∈ collarSet c := by
  obtain ⟨w, hw, rfl⟩ := hy
  refine ⟨-w, ⟨?_, ?_⟩, ?_⟩
  · rw [norm_neg]; exact hw.1
  · rw [norm_neg]; exact hw.2
  · exact (param_invol hc w).symm

/-- The round-ball interior region is `τ`-invariant (each excised round ball at a fixed point is). -/
theorem interiorSet_invol {y : TorusFour} (hy : y ∈ interiorSet) :
    torusFourInvolution y ∈ interiorSet := by
  intro hmem
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨c, hcF, w, hwball, heq⟩ := hmem
  refine hy ?_
  rw [Set.mem_iUnion₂]
  refine ⟨c, hcF, -w, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_neg]
    rwa [Metric.mem_closedBall, dist_zero_right] at hwball
  · have hτ : torusFourInvolution (torusFourInvolution y) = y := torusFourInvolution_involutive y
    rw [← heq] at hτ
    rw [← hτ, param_invol ((mem_fixedFinset c).mp hcF) w]

/-! ### §Q2a. The `τ`-twisted smooth cores -/

/-- `τ` is `C^k` on `T⁴` for every `k` (from the `C^ω` Lie-group inversion). -/
theorem contMDiff_invol {k : WithTop ℕ∞} :
    ContMDiff ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1))))
      ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) k torusFourInvolution :=
  torusFourInvolution_contMDiff.of_le le_top

/-- **The `τ`-twisted ambient coordinate-change core** (for the `τ`-twisted interior–interior
class): the ambient chart at `y'`, after `τ`, after the ambient chart inverse at `y`, reshaped into
the half-space interior, is `C^k`. -/
theorem contDiffOn_tauAmbient_core {k : WithTop ℕ∞} (y y' : TorusFour) :
    ContDiffOn ℝ k
      (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
        ((𝓡 3).prod (𝓡∂ 1)) (interiorReshape
          (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y'
            (torusFourInvolution
              ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).symm p)))))
      ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).target ∩
        (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).symm ⁻¹'
          (torusFourInvolution ⁻¹' (chartAt PModel y').source)) := by
  have hmid : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
        EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
      ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) k
      (torusFourInvolution ∘
        (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).symm)
      ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).target ∩
        (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).symm ⁻¹'
          (torusFourInvolution ⁻¹' (chartAt PModel y').source)) :=
    contMDiff_invol.comp_contMDiffOn
      ((contMDiffOn_extChartAt_symm (n := k) y).mono Set.inter_subset_left)
  have hext : ContMDiffOn ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1))))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
        EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) k
      (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y')
      (chartAt PModel y').source := contMDiffOn_extChartAt
  have hcomp := hext.comp hmid (fun p hp => hp.2)
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact contDiff_I_interiorReshape.comp_contDiffOn hcomp

/-- **The `τ`-twisted interior-to-round core** (for the `τ`-twisted interior → collar class): the
explicit round-chart inverse, after `τ`, after the ambient chart inverse, is `C^k`. -/
theorem contDiffOn_tauInteriorToRound_core {k : WithTop ℕ∞} (c y : TorusFour) :
    ContDiffOn ℝ k
      (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
        roundChartInvE4 c (torusFourInvolution
          ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).symm p)))
      ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).target ∩
        (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).symm ⁻¹'
          (torusFourInvolution ⁻¹' slitGoodSet c)) := by
  have hmid : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
        EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
      ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) k
      (torusFourInvolution ∘
        (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).symm)
      ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).target ∩
        (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) y).symm ⁻¹'
          (torusFourInvolution ⁻¹' slitGoodSet c)) :=
    contMDiff_invol.comp_contMDiffOn
      ((contMDiffOn_extChartAt_symm (n := k) y).mono Set.inter_subset_left)
  have hcomp := (contMDiffOn_roundChartInvE4 c).comp hmid (fun p hp => hp.2)
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp

/-- **The `τ`-twisted collar-reconstruction shell-vector core** (for the `τ`-twisted collar-source
classes): the explicit round-chart inverse, after `τ`, after the round chart, after a `C^k` `E⁴`
vector field, is `C^k` wherever the twisted image is slit-good. -/
theorem contDiffOn_tauRoundToRound_core {k : WithTop ℕ∞} (c : TorusFour)
    {S : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 4)}
    (hS : ContDiff ℝ k S)
    {D : Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1))}
    (hD : ∀ m ∈ D, torusFourInvolution (centeredChartParam c (ofE4 (S m))) ∈ slitGoodSet c) :
    ContDiffOn ℝ k
      (fun m => roundChartInvE4 c (torusFourInvolution (centeredChartParam c (ofE4 (S m))))) D := by
  have hpre : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)))
      ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) k
      (fun m => torusFourInvolution (centeredChartParam c (ofE4 (S m)))) :=
    contMDiff_invol.comp ((contMDiff_centeredChartParamE4 c).comp (contMDiff_iff_contDiff.mpr hS))
  have hcomp := (contMDiffOn_roundChartInvE4 c).comp hpre.contMDiffOn hD
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp

/-! ### §Q2b. Shared key extractors -/

/-- Positivity transfer from the half-space clamp: if the clamped boundary coordinate of
`I.symm m` is positive, so is the raw one. -/
theorem pos_boundary_coord {m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)}
    (hval : (0 : ℝ) < ((((𝓡 3).prod (𝓡∂ 1)).symm m).2).val.ofLp 0) : 0 < m.2.ofLp 0 := by
  have he : ((((𝓡 3).prod (𝓡∂ 1)).symm m).2).val.ofLp 0 = max (m.2.ofLp 0) 0 := rfl
  rw [he] at hval
  rcases lt_max_iff.mp hval with h | h
  · exact h
  · exact absurd h (lt_irrefl 0)

/-- **The collar reconstruction key**: on the collar chart's target (with `m` in the model range),
the underlying `T⁴` point of the collar chart inverse is the round image of the reconstructed shell
vector `(1/2 + m.2) • (chart_{S³} u₀).symm m.1` — the `m`-level form of `boundaryChart_symm_coe_eq`. -/
theorem collar_symm_key {c : TorusFour} (hc : c ∈ fixedSet) (u₀ : NSphere 3)
    {m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)}
    (htgt : ((𝓡 3).prod (𝓡∂ 1)).symm m ∈ (boundaryChart c u₀ hc).target)
    (hmrange : m ∈ range ↑((𝓡 3).prod (𝓡∂ 1))) :
    (((boundaryChart c u₀ hc).symm (((𝓡 3).prod (𝓡∂ 1)).symm m) : ↥puncturedTorus) : TorusFour)
      = centeredChartParam c (ofE4 ((1 / 2 + m.2.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 : EuclideanSpace ℝ (Fin 4)))) := by
  rw [boundaryChart, OpenPartialHomeomorph.lift_openEmbedding_target] at htgt
  rw [ModelWithCorners.range_prod] at hmrange
  have hri := ModelWithCorners.right_inv (𝓡∂ 1) hmrange.2
  have hval := boundaryChart_symm_coe_eq hc u₀ htgt
  have h1 : ((((𝓡 3).prod (𝓡∂ 1)).symm m).1) = m.1 := rfl
  have h2 : ((((𝓡 3).prod (𝓡∂ 1)).symm m).2).val = m.2 := hri
  rw [h1, h2] at hval
  exact hval

/-! ### §Q2c. The four `τ`-twisted transition classes -/

/-- **`τ`-twisted transition: interior → interior.** The deck-twisted coordinate change between two
round-ball interior charts is `C^k` — the ambient coordinate change with the smooth `τ` inserted
(`contDiffOn_tauAmbient_core`). -/
theorem contDiffOn_transition_interior_interior_tau {k : WithTop ℕ∞} (x x' : ↥interiorOpens) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(((interiorChartR x).symm ≫ₕ tauOPH) ≫ₕ interiorChartR x') ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (((interiorChartR x).symm ≫ₕ tauOPH) ≫ₕ interiorChartR x').source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  have key : ∀ m ∈ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        (((interiorChartR x).symm ≫ₕ tauOPH) ≫ₕ interiorChartR x').source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))),
      0 < m.2.ofLp 0 ∧
      interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m)
        ∈ (chartAt PModel (x : TorusFour)).target ∧
      (((interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m) : ↥puncturedTorus) : TorusFour)
        = (chartAt PModel (x : TorusFour)).symm
            (interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m)) ∧
      ((-1 : ℤˣ) • ((interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m)))
        ∈ (interiorChartR x').source := by
    intro m hm
    obtain ⟨hmsrc, hmrange⟩ := hm
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_preimage] at hmsrc
    obtain ⟨⟨htgt, -⟩, hsrc⟩ := hmsrc
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, tauOPH_apply] at hsrc
    have hkey := interiorChartR_symm_key x htgt
    exact ⟨pos_boundary_coord hkey.1, hkey.2.1, hkey.2.2, hsrc⟩
  apply ContDiffOn.congr (f := fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
    ((𝓡 3).prod (𝓡∂ 1)) (interiorReshape
      (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) (x' : TorusFour)
        (torusFourInvolution
          ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) (x : TorusFour)).symm
            ((WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 0),
              WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 1),
              WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 2),
              WithLp.toLp 2 (fun _ : Fin 1 => Real.log (m.2.ofLp 0)))))))))
  · refine (contDiffOn_tauAmbient_core (x : TorusFour) (x' : TorusFour)).comp
      (contDiffOn_interiorReshapeSymm_clean.mono (fun m hm => (key m hm).1))
      (fun m hm => ?_)
    obtain ⟨hpos, htgt, hval, hsrc⟩ := key m hm
    dsimp only
    rw [interiorReshapeSymm_eq_clean hpos]
    refine ⟨?_, ?_⟩
    · rw [extChartAt_target]
      exact ⟨htgt, interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m), rfl⟩
    · show torusFourInvolution ((chartAt PModel (x : TorusFour)).symm
        (interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m)))
          ∈ (chartAt PModel (x' : TorusFour)).source
      rw [← hval, ← neg_one_smul_val]
      exact interiorChartR_source_coe_mem_chartSource x' hsrc
  · intro m hm
    obtain ⟨hpos, htgt, hval, hsrc⟩ := key m hm
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans, tauOPH_apply]
    rw [interiorChartR_apply_coe x' (interiorChartR_source_coe_mem x' hsrc), neg_one_smul_val,
      hval, ← interiorReshapeSymm_eq_clean hpos]
    rfl

/-- **`τ`-twisted transition: interior → collar.** The deck-twisted (1d-IC) seam — the re-centered
`arg` round-chart inverse after `τ` after the ambient chart inverse
(`contDiffOn_tauInteriorToRound_core`), fed to the polar collar chart forward. -/
theorem contDiffOn_transition_interior_collar_tau {k : WithTop ℕ∞}
    {c : TorusFour} (hc : c ∈ fixedSet) (u₁ : NSphere 3) (x : ↥interiorOpens) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(((interiorChartR x).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c u₁ hc) ∘
        ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (((interiorChartR x).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c u₁ hc).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  set V : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 4) :=
    fun m => roundChartInvE4 c (torusFourInvolution
      ((extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) (x : TorusFour)).symm
        ((WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 0),
          WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 1),
          WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp 2),
          WithLp.toLp 2 (fun _ : Fin 1 => Real.log (m.2.ofLp 0)))))) with hVdef
  have key : ∀ m ∈ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        (((interiorChartR x).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c u₁ hc).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))),
      0 < m.2.ofLp 0 ∧
      interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m)
        ∈ (chartAt PModel (x : TorusFour)).target ∧
      (((interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m) : ↥puncturedTorus) : TorusFour)
        = (chartAt PModel (x : TorusFour)).symm
            (interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m)) ∧
      ((-1 : ℤˣ) • ((interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m)))
        ∈ (boundaryChart c u₁ hc).source := by
    intro m hm
    obtain ⟨hmsrc, hmrange⟩ := hm
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_preimage] at hmsrc
    obtain ⟨⟨htgt, -⟩, hsrc⟩ := hmsrc
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, tauOPH_apply] at hsrc
    have hkey := interiorChartR_symm_key x htgt
    exact ⟨pos_boundary_coord hkey.1, hkey.2.1, hkey.2.2, hsrc⟩
  have keyV : ∀ m ∈ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        (((interiorChartR x).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c u₁ hc).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))), ∃ s : ↥shellSetE4,
      V m = (s : EuclideanSpace ℝ (Fin 4)) ∧
      shellDir (shellIncl s) ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) u₁).source ∧
      boundaryChart c u₁ hc
          ((-1 : ℤˣ) • ((interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m)))
        = shellCollarChart u₁ (shellIncl s) := by
    intro m hm
    obtain ⟨hpos, htgt, hval, hsrc⟩ := key m hm
    have hcol : ((((-1 : ℤˣ) • ((interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m))) :
        ↥puncturedTorus) : TorusFour) ∈ collarSet c :=
      boundaryChart_source_coe_mem hc u₁ hsrc
    refine ⟨(collarHomeo c).symm ⟨_, hcol⟩, ?_, interior_collar_shell_key hc u₁ hsrc hcol,
      boundaryChart_apply_eq hc u₁ hcol⟩
    rw [collarHomeo_symm_coe, hVdef]
    show roundChartInvE4 c _ = roundChartInvE4 c _
    rw [interiorReshapeSymm_eq_clean hpos]
    refine congrArg (roundChartInvE4 c) ?_
    rw [neg_one_smul_val, hval]
    exact rfl
  have hVs : ContDiffOn ℝ k V (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
      (((interiorChartR x).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c u₁ hc).source ∩
      range ↑((𝓡 3).prod (𝓡∂ 1))) := by
    rw [hVdef]
    apply (contDiffOn_tauInteriorToRound_core c (x : TorusFour)).comp
      (contDiffOn_interiorReshapeSymm_clean.mono (fun m hm => (key m hm).1))
    intro m hm
    obtain ⟨hpos, htgt, hval, hsrc⟩ := key m hm
    have hcol : ((((-1 : ℤˣ) • ((interiorChartR x).symm (((𝓡 3).prod (𝓡∂ 1)).symm m))) :
        ↥puncturedTorus) : TorusFour) ∈ collarSet c :=
      boundaryChart_source_coe_mem hc u₁ hsrc
    dsimp only
    rw [interiorReshapeSymm_eq_clean hpos]
    refine ⟨?_, ?_⟩
    · rw [extChartAt_target]
      exact ⟨htgt, interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m), rfl⟩
    · show torusFourInvolution ((chartAt PModel (x : TorusFour)).symm
        (interiorReshape.symm (((𝓡 3).prod (𝓡∂ 1)).symm m))) ∈ slitGoodSet c
      rw [← hval, ← neg_one_smul_val]
      exact collarSet_subset_slitGoodSet hcol
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
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans, tauOPH_apply]
    rw [happly]
    show (chartAt (EuclideanSpace ℝ (Fin 3)) u₁ (shellDir (shellIncl s)),
        WithLp.toLp 2 (fun _ : Fin 1 =>
          ‖((shellIncl s : ExtShell) : EuclideanSpace ℝ (Fin 4))‖ - 1 / 2)) = _
    rw [chartAt_threeSphere_apply, shellDir_coe]
    rw [show ((shellIncl s : ExtShell) : EuclideanSpace ℝ (Fin 4))
      = (s : EuclideanSpace ℝ (Fin 4)) from rfl, ← hVs_eq]

/-- **`τ`-twisted transition: collar → interior.** The deck-twisted (1d-CI) seam — the collar chart
inverse reconstructs the shell vector, the round chart re-parametrizes it, `τ` (smooth) twists it,
and the ambient chart + reshape read it into the half-space interior. -/
theorem contDiffOn_transition_collar_interior_tau {k : WithTop ℕ∞}
    {c : TorusFour} (hc : c ∈ fixedSet) (u₀ : NSphere 3) (x' : ↥interiorOpens) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ interiorChartR x') ∘
        ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ interiorChartR x').source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  have hS : ContDiff ℝ k (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
      (1 / 2 + m.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 :
        EuclideanSpace ℝ (Fin 4))) :=
    (contDiff_const.add ((contDiff_apply ℝ ℝ 0).comp (PiLp.contDiff_ofLp.comp contDiff_snd))).smul
      ((contDiff_chartSymm_coe u₀).comp contDiff_fst)
  have key : ∀ m ∈ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        (((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ interiorChartR x').source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))),
      (((boundaryChart c u₀ hc).symm (((𝓡 3).prod (𝓡∂ 1)).symm m) :
          ↥puncturedTorus) : TorusFour)
        = centeredChartParam c (ofE4 ((1 / 2 + m.2.ofLp 0) •
            ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 : EuclideanSpace ℝ (Fin 4)))) ∧
      ((-1 : ℤˣ) • ((boundaryChart c u₀ hc).symm (((𝓡 3).prod (𝓡∂ 1)).symm m)))
        ∈ (interiorChartR x').source := by
    intro m hm
    obtain ⟨hmsrc, hmrange⟩ := hm
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_preimage] at hmsrc
    obtain ⟨⟨htgt, -⟩, hsrc⟩ := hmsrc
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, tauOPH_apply] at hsrc
    exact ⟨collar_symm_key hc u₀ htgt hmrange, hsrc⟩
  apply ContDiffOn.congr (f := fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
    ((𝓡 3).prod (𝓡∂ 1)) (interiorReshape
      (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) (x' : TorusFour)
        (torusFourInvolution (centeredChartParam c (ofE4 ((1 / 2 + m.2.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 : EuclideanSpace ℝ (Fin 4)))))))))
  · have hpre : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1)))
        ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) k
        (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
          torusFourInvolution (centeredChartParam c (ofE4 ((1 / 2 + m.2.ofLp 0) •
            ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 : EuclideanSpace ℝ (Fin 4)))))) :=
      contMDiff_invol.comp
        ((contMDiff_centeredChartParamE4 c).comp (contMDiff_iff_contDiff.mpr hS))
    have hext : ContMDiffOn ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1))))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
          EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) k
        (extChartAt ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) (x' : TorusFour))
        (chartAt PModel (x' : TorusFour)).source := contMDiffOn_extChartAt
    have hcomp := hext.comp hpre.contMDiffOn (fun m hm => by
      obtain ⟨hval, hsrc⟩ := key m hm
      show torusFourInvolution (centeredChartParam c _) ∈ (chartAt PModel (x' : TorusFour)).source
      rw [← hval, ← neg_one_smul_val]
      exact interiorChartR_source_coe_mem_chartSource x' hsrc)
    rw [contMDiffOn_iff_contDiffOn] at hcomp
    exact contDiff_I_interiorReshape.comp_contDiffOn hcomp
  · intro m hm
    obtain ⟨hval, hsrc⟩ := key m hm
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans, tauOPH_apply]
    rw [interiorChartR_apply_coe x' (interiorChartR_source_coe_mem x' hsrc),
      neg_one_smul_val, hval]
    rfl

/-- **`τ`-twisted transition: collar → collar, same fixed point.** The deck-twisted collar
self-transition: the reconstructed shell vector is round-parametrized, `τ`-twisted (staying in the
`τ`-invariant collar), inverted by the re-centered `arg` inverse, and fed to the `u₁`-polar collar
chart forward. -/
theorem contDiffOn_transition_collar_collar_same_tau {k : WithTop ℕ∞}
    {c : TorusFour} (hc : c ∈ fixedSet) (u₀ u₁ : NSphere 3) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c u₁ hc) ∘
        ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c u₁ hc).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  have hS : ContDiff ℝ k (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
      (1 / 2 + m.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 :
        EuclideanSpace ℝ (Fin 4))) :=
    (contDiff_const.add ((contDiff_apply ℝ ℝ 0).comp (PiLp.contDiff_ofLp.comp contDiff_snd))).smul
      ((contDiff_chartSymm_coe u₀).comp contDiff_fst)
  have key : ∀ m ∈ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        (((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c u₁ hc).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))),
      (((boundaryChart c u₀ hc).symm (((𝓡 3).prod (𝓡∂ 1)).symm m) :
          ↥puncturedTorus) : TorusFour)
        = centeredChartParam c (ofE4 ((1 / 2 + m.2.ofLp 0) •
            ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 : EuclideanSpace ℝ (Fin 4)))) ∧
      ((-1 : ℤˣ) • ((boundaryChart c u₀ hc).symm (((𝓡 3).prod (𝓡∂ 1)).symm m)))
        ∈ (boundaryChart c u₁ hc).source := by
    intro m hm
    obtain ⟨hmsrc, hmrange⟩ := hm
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_preimage] at hmsrc
    obtain ⟨⟨htgt, -⟩, hsrc⟩ := hmsrc
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, tauOPH_apply] at hsrc
    exact ⟨collar_symm_key hc u₀ htgt hmrange, hsrc⟩
  have keyV : ∀ m ∈ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        (((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c u₁ hc).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))), ∃ s : ↥shellSetE4,
      roundChartInvE4 c (torusFourInvolution (centeredChartParam c
          (ofE4 ((1 / 2 + m.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 :
            EuclideanSpace ℝ (Fin 4))))))
        = (s : EuclideanSpace ℝ (Fin 4)) ∧
      shellDir (shellIncl s) ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) u₁).source ∧
      boundaryChart c u₁ hc
          ((-1 : ℤˣ) • ((boundaryChart c u₀ hc).symm (((𝓡 3).prod (𝓡∂ 1)).symm m)))
        = shellCollarChart u₁ (shellIncl s) := by
    intro m hm
    obtain ⟨hval, hsrc⟩ := key m hm
    have hcol : ((((-1 : ℤˣ) • ((boundaryChart c u₀ hc).symm (((𝓡 3).prod (𝓡∂ 1)).symm m))) :
        ↥puncturedTorus) : TorusFour) ∈ collarSet c :=
      boundaryChart_source_coe_mem hc u₁ hsrc
    refine ⟨(collarHomeo c).symm ⟨_, hcol⟩, ?_, interior_collar_shell_key hc u₁ hsrc hcol,
      boundaryChart_apply_eq hc u₁ hcol⟩
    rw [collarHomeo_symm_coe]
    refine congrArg (roundChartInvE4 c) ?_
    rw [neg_one_smul_val, hval]
  have hVs : ContDiffOn ℝ k
      (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
        roundChartInvE4 c (torusFourInvolution (centeredChartParam c
          (ofE4 ((1 / 2 + m.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 :
            EuclideanSpace ℝ (Fin 4)))))))
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c u₁ hc).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
    refine contDiffOn_tauRoundToRound_core c hS (fun m hm => ?_)
    obtain ⟨hval, hsrc⟩ := key m hm
    have hcol : ((((-1 : ℤˣ) • ((boundaryChart c u₀ hc).symm (((𝓡 3).prod (𝓡∂ 1)).symm m))) :
        ↥puncturedTorus) : TorusFour) ∈ collarSet c :=
      boundaryChart_source_coe_mem hc u₁ hsrc
    show torusFourInvolution (centeredChartParam c _) ∈ slitGoodSet c
    rw [← hval, ← neg_one_smul_val]
    exact collarSet_subset_slitGoodSet hcol
  apply ContDiffOn.congr (f := fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
    ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
        (ne_zero_of_mem_unit_sphere (-u₁))).repr
        (stereoToFun ((-u₁ : NSphere 3) : EuclideanSpace ℝ (Fin 4))
          (‖roundChartInvE4 c (torusFourInvolution (centeredChartParam c
              (ofE4 ((1 / 2 + m.2.ofLp 0) •
                ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 :
                  EuclideanSpace ℝ (Fin 4))))))‖⁻¹ •
            roundChartInvE4 c (torusFourInvolution (centeredChartParam c
              (ofE4 ((1 / 2 + m.2.ofLp 0) •
                ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 :
                  EuclideanSpace ℝ (Fin 4)))))))),
      WithLp.toLp 2 (fun _ : Fin 1 =>
        ‖roundChartInvE4 c (torusFourInvolution (centeredChartParam c
          (ofE4 ((1 / 2 + m.2.ofLp 0) •
            ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 :
              EuclideanSpace ℝ (Fin 4))))))‖ - 1 / 2)))
  · refine ContDiffOn.prodMk ?_ ?_
    · refine (contDiffOn_reprStereoNormalize u₁).comp hVs (fun m hm => ?_)
      obtain ⟨s, hVs_eq, hdir, -⟩ := keyV m hm
      have hne : roundChartInvE4 c (torusFourInvolution (centeredChartParam c
          (ofE4 ((1 / 2 + m.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 :
            EuclideanSpace ℝ (Fin 4)))))) ≠ 0 := by
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
      show roundChartInvE4 c (torusFourInvolution (centeredChartParam c
        (ofE4 ((1 / 2 + m.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm m.1 :
          EuclideanSpace ℝ (Fin 4)))))) ≠ 0
      rw [hVs_eq]
      intro h
      have h2 : (1 : ℝ) / 2 ≤ 0 := by
        have := s.2.1
        rwa [show ((s : EuclideanSpace ℝ (Fin 4))) = 0 from h, norm_zero] at this
      linarith
  · intro m hm
    obtain ⟨s, hVs_eq, hdir, happly⟩ := keyV m hm
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans, tauOPH_apply]
    rw [happly]
    show (chartAt (EuclideanSpace ℝ (Fin 3)) u₁ (shellDir (shellIncl s)),
        WithLp.toLp 2 (fun _ : Fin 1 =>
          ‖((shellIncl s : ExtShell) : EuclideanSpace ℝ (Fin 4))‖ - 1 / 2)) = _
    rw [chartAt_threeSphere_apply, shellDir_coe]
    rw [show ((shellIncl s : ExtShell) : EuclideanSpace ℝ (Fin 4))
      = (s : EuclideanSpace ℝ (Fin 4)) from rfl, ← hVs_eq]

/-- **`τ`-twisted transition: collar → collar, different fixed points (vacuous).** The collar of a
fixed point is `τ`-invariant, so the twisted source is still confined to the disjoint collar. -/
theorem contDiffOn_transition_collar_collar_diff_tau {k : WithTop ℕ∞}
    {c c' : TorusFour} (hc : c ∈ fixedSet) (hc' : c' ∈ fixedSet) (hne : c ≠ c')
    (u₀ u₁ : NSphere 3) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c' u₁ hc') ∘
        ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c' u₁ hc').source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  have hempty :
      (((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c' u₁ hc').source = ∅ := by
    rw [OpenPartialHomeomorph.trans_source]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hp2
    rw [Set.mem_preimage] at hp2
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, tauOPH_apply] at hp2
    have hmem : (((boundaryChart c u₀ hc).symm p : ↥puncturedTorus) : TorusFour) ∈ collarSet c :=
      boundaryChart_symm_coe_mem hc u₀ p
    have hmem2 : ((((-1 : ℤˣ) • ((boundaryChart c u₀ hc).symm p)) :
        ↥puncturedTorus) : TorusFour) ∈ collarSet c := by
      rw [neg_one_smul_val]
      exact collarSet_invol hc hmem
    have hmem' : ((((-1 : ℤˣ) • ((boundaryChart c u₀ hc).symm p)) :
        ↥puncturedTorus) : TorusFour) ∈ collarSet c' :=
      boundaryChart_source_coe_mem hc' u₁ hp2
    exact (Set.disjoint_left.mp (collarSet_disjoint hc hc' hne) hmem2) hmem'
  rw [hempty, Set.preimage_empty, Set.empty_inter]
  exact contDiffOn_empty

/-! ### §Q3. The deck branch is locally constant -/

/-- The `qmk`-chart overlap at base points `x, x'`. -/
def qmkOverlap (x x' : ↥puncturedTorus) : Set (↥puncturedTorus) :=
  (qmk_localOpenPartialHomeomorph x).source ∩
    qmk ⁻¹' (qmk_localOpenPartialHomeomorph x').target

theorem isOpen_qmkOverlap (x x' : ↥puncturedTorus) : IsOpen (qmkOverlap x x') :=
  (qmk_localOpenPartialHomeomorph x).open_source.inter
    ((qmk_localOpenPartialHomeomorph x').open_target.preimage
      qmk_isLocalHomeomorph.continuous)

/-- The deck map at `x'`: locally invert `qmk` after `qmk`. -/
def deckMap (x' : ↥puncturedTorus) : ↥puncturedTorus → ↥puncturedTorus :=
  fun y => (qmk_localOpenPartialHomeomorph x').symm (qmk y)

/-- **The deck dichotomy**: on the overlap, the deck map is the identity or the involution
(the fibre of `qmk` is the two-point orbit, `qmk_eq_iff`). -/
theorem deckMap_dichotomy (x x' : ↥puncturedTorus) {y : ↥puncturedTorus}
    (hy : y ∈ qmkOverlap x x') : deckMap x' y = y ∨ deckMap x' y = (-1 : ℤˣ) • y := by
  have hq : qmk (deckMap x' y) = qmk y := by
    have h := (qmk_localOpenPartialHomeomorph x').right_inv hy.2
    rwa [qmk_localOpenPartialHomeomorph_apply] at h
  exact (qmk_eq_iff (deckMap x' y) y).mp hq

/-- **Both deck branches are open**: the two branch loci are complementary relatively-closed
subsets of the open overlap (freeness `neg_one_smul_ne` separates them), hence relatively open,
hence open. -/
theorem isOpen_deckBranch (x x' : ↥puncturedTorus) :
    IsOpen {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = y} ∧
    IsOpen {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = (-1 : ℤˣ) • y} := by
  have hU : IsOpen (qmkOverlap x x') := isOpen_qmkOverlap x x'
  have hcont : ContinuousOn (deckMap x') (qmkOverlap x x') :=
    (qmk_localOpenPartialHomeomorph x').continuousOn_symm.comp
      qmk_isLocalHomeomorph.continuous.continuousOn (fun y hy => hy.2)
  have hcont' : Continuous ((qmkOverlap x x').restrict (deckMap x')) := hcont.restrict
  have hAc : IsClosed {u : ↥(qmkOverlap x x') |
      (qmkOverlap x x').restrict (deckMap x') u = (u : ↥puncturedTorus)} :=
    isClosed_eq hcont' continuous_subtype_val
  have hBc : IsClosed {u : ↥(qmkOverlap x x') |
      (qmkOverlap x x').restrict (deckMap x') u = (-1 : ℤˣ) • (u : ↥puncturedTorus)} :=
    isClosed_eq hcont' ((continuous_const_smul _).comp continuous_subtype_val)
  have hAB : {u : ↥(qmkOverlap x x') |
        (qmkOverlap x x').restrict (deckMap x') u = (u : ↥puncturedTorus)}
      = {u : ↥(qmkOverlap x x') |
        (qmkOverlap x x').restrict (deckMap x') u = (-1 : ℤˣ) • (u : ↥puncturedTorus)}ᶜ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · intro h h'
      rw [h] at h'
      exact neg_one_smul_ne (u : ↥puncturedTorus) h'.symm
    · intro h
      rcases deckMap_dichotomy x x' u.2 with h' | h'
      · exact h'
      · exact absurd h' h
  have hAopen : IsOpen {u : ↥(qmkOverlap x x') |
      (qmkOverlap x x').restrict (deckMap x') u = (u : ↥puncturedTorus)} := by
    rw [hAB]; exact hBc.isOpen_compl
  have hBopen : IsOpen {u : ↥(qmkOverlap x x') |
      (qmkOverlap x x').restrict (deckMap x') u = (-1 : ℤˣ) • (u : ↥puncturedTorus)} := by
    have h : {u : ↥(qmkOverlap x x') |
        (qmkOverlap x x').restrict (deckMap x') u = (-1 : ℤˣ) • (u : ↥puncturedTorus)}
        = {u : ↥(qmkOverlap x x') |
          (qmkOverlap x x').restrict (deckMap x') u = (u : ↥puncturedTorus)}ᶜ := by
      rw [hAB, compl_compl]
    rw [h]; exact hAc.isOpen_compl
  have hemb := hU.isOpenEmbedding_subtypeVal
  constructor
  · have himg : {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = y}
        = Subtype.val '' {u : ↥(qmkOverlap x x') |
          (qmkOverlap x x').restrict (deckMap x') u = (u : ↥puncturedTorus)} := by
      ext y
      constructor
      · rintro ⟨hyU, hy⟩; exact ⟨⟨y, hyU⟩, hy, rfl⟩
      · rintro ⟨u, hu, rfl⟩; exact ⟨u.2, hu⟩
    rw [himg]
    exact hemb.isOpenMap _ hAopen
  · have himg : {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = (-1 : ℤˣ) • y}
        = Subtype.val '' {u : ↥(qmkOverlap x x') |
          (qmkOverlap x x').restrict (deckMap x') u = (-1 : ℤˣ) • (u : ↥puncturedTorus)} := by
      ext y
      constructor
      · rintro ⟨hyU, hy⟩; exact ⟨⟨y, hyU⟩, hy, rfl⟩
      · rintro ⟨u, hu, rfl⟩; exact ⟨u.2, hu⟩
    rw [himg]
    exact hemb.isOpenMap _ hBopen

/-! ### §Q4. Generic descent: `Q`-transitions from the two branch transitions -/

/-- **Generic `qmk`-descent of transition smoothness.** If for a chart pair `C, C'` of `T⁴°` both
the plain and the `τ`-twisted coordinate changes are `C^k`, then the `qmk`-descended `Q`-transition
is `C^k`: the deck branch is locally constant (§Q3), so near every domain point the `Q`-transition
agrees with one of the two `T⁴°`-level coordinate changes. -/
theorem contDiffOn_qmkTransition {k : WithTop ℕ∞} (x x' : ↥puncturedTorus)
    (C C' : OpenPartialHomeomorph (↥puncturedTorus) Model)
    (hid : ContDiffOn ℝ k
      (↑((𝓡 3).prod (𝓡∂ 1)) ∘ ↑(C.symm ≫ₕ C') ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (C.symm ≫ₕ C').source ∩ range ↑((𝓡 3).prod (𝓡∂ 1))))
    (htau : ContDiffOn ℝ k
      (↑((𝓡 3).prod (𝓡∂ 1)) ∘ ↑((C.symm ≫ₕ tauOPH) ≫ₕ C') ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' ((C.symm ≫ₕ tauOPH) ≫ₕ C').source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1)))) :
    ContDiffOn ℝ k
      (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).symm ≫ₕ
          ((qmk_localOpenPartialHomeomorph x').symm ≫ₕ C')) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).symm ≫ₕ
            ((qmk_localOpenPartialHomeomorph x').symm ≫ₕ C')).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  -- Membership + value extractor.
  have key : ∀ m ∈ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
        (((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).symm ≫ₕ
          ((qmk_localOpenPartialHomeomorph x').symm ≫ₕ C')).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))),
      ((𝓡 3).prod (𝓡∂ 1)).symm m ∈ C.target ∧
      C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m) ∈ qmkOverlap x x' ∧
      deckMap x' (C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m)) ∈ C'.source ∧
      (↑((𝓡 3).prod (𝓡∂ 1)) ∘
          ↑(((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).symm ≫ₕ
            ((qmk_localOpenPartialHomeomorph x').symm ≫ₕ C')) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm) m
        = ((𝓡 3).prod (𝓡∂ 1))
            (C' (deckMap x' (C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m)))) := by
    intro m hm
    obtain ⟨hmsrc, -⟩ := hm
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] at hmsrc
    obtain ⟨hpE, hpE'⟩ := hmsrc
    rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage,
      OpenPartialHomeomorph.symm_target] at hpE
    obtain ⟨hpC, hpA⟩ := hpE
    simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
      Function.comp_apply, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage,
      qmk_localOpenPartialHomeomorph_apply] at hpE'
    obtain ⟨hqt, hzC'⟩ := hpE'
    refine ⟨hpC, ⟨hpA, hqt⟩, hzC', ?_⟩
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
      qmk_localOpenPartialHomeomorph_apply]
    rfl
  intro m₀ hm₀
  obtain ⟨hpC₀, hyU₀, hzC₀, hQval₀⟩ := key m₀ hm₀
  have hh : ContinuousWithinAt
      (fun m' : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
        C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m'))
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).symm ≫ₕ
            ((qmk_localOpenPartialHomeomorph x').symm ≫ₕ C')).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) m₀ :=
    (C.continuousOn_symm.comp
      (((𝓡 3).prod (𝓡∂ 1)).continuous_symm.continuousOn)
      (fun m' hm' => (key m' hm').1)).continuousWithinAt hm₀
  rcases deckMap_dichotomy x x' hyU₀ with hb | hb
  · -- identity branch: locally agrees with the plain transition
    have hW : IsOpen {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = y} := (isOpen_deckBranch x x').1
    have hyW : C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m₀)
        ∈ {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = y} := ⟨hyU₀, hb⟩
    have hP := hh.preimage_mem_nhdsWithin (hW.mem_nhds hyW)
    have hsub : (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).symm ≫ₕ
            ((qmk_localOpenPartialHomeomorph x').symm ≫ₕ C')).source ∩
          range ↑((𝓡 3).prod (𝓡∂ 1))) ∩
        ((fun m' : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
          C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m')) ⁻¹'
          {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = y})
        ⊆ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (C.symm ≫ₕ C').source ∩
          range ↑((𝓡 3).prod (𝓡∂ 1))) := by
      rintro m' ⟨hm', hm'W⟩
      obtain ⟨hpC', hyU', hzC'', -⟩ := key m' hm'
      have hm'W2 : deckMap x' (C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m'))
          = C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m') := hm'W.2
      refine ⟨?_, hm'.2⟩
      rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage]
      refine ⟨hpC', ?_⟩
      rw [← hm'W2]
      exact hzC''
    have hcd : ContDiffOn ℝ k
        (↑((𝓡 3).prod (𝓡∂ 1)) ∘
          ↑(((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).symm ≫ₕ
            ((qmk_localOpenPartialHomeomorph x').symm ≫ₕ C')) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
        ((↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
            (((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).symm ≫ₕ
              ((qmk_localOpenPartialHomeomorph x').symm ≫ₕ C')).source ∩
            range ↑((𝓡 3).prod (𝓡∂ 1))) ∩
          ((fun m' : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
            C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m')) ⁻¹'
            {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = y})) :=
      (hid.mono hsub).congr (fun m' hm' => by
        obtain ⟨-, -, -, hQval'⟩ := key m' hm'.1
        have hb' : deckMap x' (C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m'))
            = C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m') := hm'.2.2
        rw [hQval', hb']
        simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans])
    exact (hcd.contDiffWithinAt ⟨hm₀, hyW⟩).mono_of_mem_nhdsWithin
      (Filter.inter_mem self_mem_nhdsWithin hP)
  · -- involution branch: locally agrees with the `τ`-twisted transition
    have hW : IsOpen {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = (-1 : ℤˣ) • y} :=
      (isOpen_deckBranch x x').2
    have hyW : C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m₀)
        ∈ {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = (-1 : ℤˣ) • y} := ⟨hyU₀, hb⟩
    have hP := hh.preimage_mem_nhdsWithin (hW.mem_nhds hyW)
    have hsub : (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).symm ≫ₕ
            ((qmk_localOpenPartialHomeomorph x').symm ≫ₕ C')).source ∩
          range ↑((𝓡 3).prod (𝓡∂ 1))) ∩
        ((fun m' : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
          C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m')) ⁻¹'
          {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = (-1 : ℤˣ) • y})
        ⊆ (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' ((C.symm ≫ₕ tauOPH) ≫ₕ C').source ∩
          range ↑((𝓡 3).prod (𝓡∂ 1))) := by
      rintro m' ⟨hm', hm'W⟩
      obtain ⟨hpC', hyU', hzC'', -⟩ := key m' hm'
      have hm'W2 : deckMap x' (C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m'))
          = (-1 : ℤˣ) • C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m') := hm'W.2
      refine ⟨?_, hm'.2⟩
      rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
        OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage]
      refine ⟨⟨hpC', by rw [tauOPH_source]; exact Set.mem_univ _⟩, ?_⟩
      simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, tauOPH_apply]
      rw [← hm'W2]
      exact hzC''
    have hcd : ContDiffOn ℝ k
        (↑((𝓡 3).prod (𝓡∂ 1)) ∘
          ↑(((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).symm ≫ₕ
            ((qmk_localOpenPartialHomeomorph x').symm ≫ₕ C')) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
        ((↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
            (((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).symm ≫ₕ
              ((qmk_localOpenPartialHomeomorph x').symm ≫ₕ C')).source ∩
            range ↑((𝓡 3).prod (𝓡∂ 1))) ∩
          ((fun m' : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
            C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m')) ⁻¹'
            {y | y ∈ qmkOverlap x x' ∧ deckMap x' y = (-1 : ℤˣ) • y})) :=
      (htau.mono hsub).congr (fun m' hm' => by
        obtain ⟨-, -, -, hQval'⟩ := key m' hm'.1
        have hb' : deckMap x' (C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m'))
            = (-1 : ℤˣ) • C.symm (((𝓡 3).prod (𝓡∂ 1)).symm m') := hm'.2.2
        rw [hQval', hb']
        simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans, tauOPH_apply])
    exact (hcd.contDiffWithinAt ⟨hm₀, hyW⟩).mono_of_mem_nhdsWithin
      (Filter.inter_mem self_mem_nhdsWithin hP)

/-! ### §Q5. THE CERTIFICATE — `Q = T⁴°/τ` is a smooth manifold-with-boundary -/

/-- The image `qmk x` lies in the source of every `qmk`-descended chart at base `x` whose `T⁴°`
chart contains `x`. -/
theorem qmk_mem_descended_source (x : ↥puncturedTorus)
    (C : OpenPartialHomeomorph (↥puncturedTorus) Model) (hxC : x ∈ C.source) :
    qmk x ∈ ((qmk_localOpenPartialHomeomorph x).symm ≫ₕ C).source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · have h := (qmk_localOpenPartialHomeomorph x).map_source
      (mem_qmk_localOpenPartialHomeomorph_source x)
    rwa [qmk_localOpenPartialHomeomorph_apply] at h
  · have h : (qmk_localOpenPartialHomeomorph x).symm (qmk x) = x := by
      have h2 := (qmk_localOpenPartialHomeomorph x).left_inv
        (mem_qmk_localOpenPartialHomeomorph_source x)
      rwa [qmk_localOpenPartialHomeomorph_apply] at h2
    rw [h]
    exact hxC

open Classical in
/-- **`Q = FreeQuotient` is a charted space on the half-space model `(𝓡 3).prod (𝓡∂ 1)`** — the
K5′ boundary-chart certificate opener. The atlas is the family of `qmk`-descended boundary and
interior charts (`qmkBoundaryChart`/`qmkInteriorChart`); `chartAt` dispatches on the canonical
orbit representative. -/
noncomputable instance instChartedSpaceFreeQuotient : ChartedSpace Model FreeQuotient where
  atlas := (⋃ (x : ↥puncturedTorus) (h : (x : TorusFour) ∉ interiorSet),
      {qmkBoundaryChart x h}) ∪
    ⋃ (x : ↥puncturedTorus) (h : (x : TorusFour) ∈ interiorSet), {qmkInteriorChart x h}
  chartAt q :=
    if h : ((Quotient.out q : ↥puncturedTorus) : TorusFour) ∈ interiorSet
    then qmkInteriorChart (Quotient.out q) h
    else qmkBoundaryChart (Quotient.out q) h
  mem_chart_source q := by
    have hout : qmk (Quotient.out q) = q := Quotient.out_eq q
    by_cases h : ((Quotient.out q : ↥puncturedTorus) : TorusFour) ∈ interiorSet
    · rw [dif_pos h]
      have hx : (⟨((Quotient.out q : ↥puncturedTorus) : TorusFour),
          interiorSet_subset_puncturedTorus h⟩ : ↥puncturedTorus) = Quotient.out q :=
        Subtype.ext rfl
      have hsrc := mem_interiorChartR_source
        (⟨((Quotient.out q : ↥puncturedTorus) : TorusFour), h⟩ : ↥interiorOpens)
      rw [hx] at hsrc
      have hmem := qmk_mem_descended_source (Quotient.out q) _ hsrc
      rwa [hout] at hmem
    · rw [dif_neg h]
      have hmem := qmk_mem_descended_source (Quotient.out q) _ (mem_bdyChartAt_source h)
      rwa [hout] at hmem
  chart_mem_atlas q := by
    by_cases h : ((Quotient.out q : ↥puncturedTorus) : TorusFour) ∈ interiorSet
    · rw [dif_pos h]
      refine Or.inr ?_
      simp only [Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨Quotient.out q, h, rfl⟩
    · rw [dif_neg h]
      refine Or.inl ?_
      simp only [Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨Quotient.out q, h, rfl⟩

/-- Boundary–boundary `T⁴°` transitions, both branches, uniform in the two fixed points. -/
theorem contDiffOn_bb {k : WithTop ℕ∞} {c c' : TorusFour}
    (hc : c ∈ fixedSet) (hc' : c' ∈ fixedSet) (u₀ u₁ : NSphere 3) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((boundaryChart c u₀ hc).symm ≫ₕ boundaryChart c' u₁ hc') ∘
        ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((boundaryChart c u₀ hc).symm ≫ₕ boundaryChart c' u₁ hc').source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  by_cases hcc : c = c'
  · subst hcc
    exact contDiffOn_transition_collar_collar_same hc u₀ u₁
  · exact contDiffOn_transition_collar_collar_diff hc hc' hcc u₀ u₁

/-- Boundary–boundary `τ`-twisted `T⁴°` transitions, uniform in the two fixed points. -/
theorem contDiffOn_bb_tau {k : WithTop ℕ∞} {c c' : TorusFour}
    (hc : c ∈ fixedSet) (hc' : c' ∈ fixedSet) (u₀ u₁ : NSphere 3) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c' u₁ hc') ∘
        ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (((boundaryChart c u₀ hc).symm ≫ₕ tauOPH) ≫ₕ boundaryChart c' u₁ hc').source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  by_cases hcc : c = c'
  · subst hcc
    exact contDiffOn_transition_collar_collar_same_tau hc u₀ u₁
  · exact contDiffOn_transition_collar_collar_diff_tau hc hc' hcc u₀ u₁

/-- **`Q = T⁴°/τ` is a `C^k` manifold-with-boundary** on `(𝓡 3).prod (𝓡∂ 1)` — the K5′
certificate, the `Q`-side input of the Kummer weld. Every `Q`-atlas transition descends through
`qmk` (`contDiffOn_qmkTransition`) to a `T⁴°` transition or its `τ`-twist, and all eight classes
are certified. Parametric in `k : WithTop ℕ∞`, up to `ω`. -/
theorem isManifold_freeQuotient {k : WithTop ℕ∞} :
    IsManifold ((𝓡 3).prod (𝓡∂ 1)) k FreeQuotient := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with he | he
  · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at he
    obtain ⟨x, hx, rfl⟩ := he
    rcases he' with he' | he'
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at he'
      obtain ⟨x', hx', rfl⟩ := he'
      exact contDiffOn_qmkTransition x x' _ _
        (contDiffOn_bb (chosenC_mem hx) (chosenC_mem hx') _ _)
        (contDiffOn_bb_tau (chosenC_mem hx) (chosenC_mem hx') _ _)
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at he'
      obtain ⟨x', hx', rfl⟩ := he'
      exact contDiffOn_qmkTransition x x' _ _
        (contDiffOn_transition_collar_interior (chosenC_mem hx) _
          ⟨((x' : ↥puncturedTorus) : TorusFour), hx'⟩)
        (contDiffOn_transition_collar_interior_tau (chosenC_mem hx) _
          ⟨((x' : ↥puncturedTorus) : TorusFour), hx'⟩)
  · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at he
    obtain ⟨x, hx, rfl⟩ := he
    rcases he' with he' | he'
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at he'
      obtain ⟨x', hx', rfl⟩ := he'
      exact contDiffOn_qmkTransition x x' _ _
        (contDiffOn_transition_interior_collar (chosenC_mem hx') _
          ⟨((x : ↥puncturedTorus) : TorusFour), hx⟩)
        (contDiffOn_transition_interior_collar_tau (chosenC_mem hx') _
          ⟨((x : ↥puncturedTorus) : TorusFour), hx⟩)
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at he'
      obtain ⟨x', hx', rfl⟩ := he'
      exact contDiffOn_qmkTransition x x' _ _
        (contDiffOn_transition_interior_interior
          ⟨((x : ↥puncturedTorus) : TorusFour), hx⟩
          ⟨((x' : ↥puncturedTorus) : TorusFour), hx'⟩)
        (contDiffOn_transition_interior_interior_tau
          ⟨((x : ↥puncturedTorus) : TorusFour), hx⟩
          ⟨((x' : ↥puncturedTorus) : TorusFour), hx'⟩)

end

end SKEFTHawking.KummerQuotientManifold
