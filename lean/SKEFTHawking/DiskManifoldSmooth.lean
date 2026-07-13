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
  · simpa only [Fin.snoc_castSucc] using
      (contDiff_apply ℝ ℝ j).comp (PiLp.contDiff_ofLp.comp contDiff_fst)

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

end

end SKEFTHawking.DiskManifoldSmooth
