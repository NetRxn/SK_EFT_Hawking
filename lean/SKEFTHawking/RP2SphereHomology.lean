import Mathlib
import SKEFTHawking.RP2PointSet
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularConvexStageIso
import SKEFTHawking.SingularConvexComplementConnected
import SKEFTHawking.SingularConvexRadialMiddle

/-!
# Phase 5q.G (B-arc, M1-a) — the punctured 2-sphere is acyclic

The first rung of the `H_*(S²;ℤ/2)` computation (toward the Smith sequence of the antipodal
cover): `S² ∖ {v} ≃ₜ ℝ²` by the stereographic chart (Mathlib's `stereographic'`, whose source
is exactly `{v}ᶜ` and target all of `ℝ²`), so its positive-degree homology vanishes by
transport onto the Euclidean acyclicity (`eucl_homology_zero`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open Metric
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.RP2PointSet SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularHomotopyInvariance

namespace SKEFTHawking.RP2SphereHomology

/-- **The punctured 2-sphere is homeomorphic to `ℝ²`** — the stereographic chart, whose source
is `{v}ᶜ` and target `univ`. -/
noncomputable def punctSphereHomeo (v : S2) :
    ↥({v}ᶜ : Set S2) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  ((Homeomorph.setCongr (stereographic'_source v).symm).trans
      (stereographic' 2 v).toHomeomorphSourceTarget).trans
    ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _))

/-- **The punctured 2-sphere is acyclic in positive degrees** — transport the Euclidean
vanishing along the stereographic homeomorphism. -/
theorem punctSphere_homology_eq_zero (v : S2) (k : ℕ)
    (x : Homology (sub (X := TopCat.of S2) ({v}ᶜ : Set S2)) (k + 1)) : x = 0 := by
  set e := punctSphereHomeo v
  set eC : C(↥(sub (X := TopCat.of S2) ({v}ᶜ : Set S2)),
      ↥(SingularEuclideanAcyclic.Eucl 2)) := ⟨e, e.continuous⟩ with heC
  set eC' : C(↥(SingularEuclideanAcyclic.Eucl 2),
      ↥(sub (X := TopCat.of S2) ({v}ᶜ : Set S2))) := ⟨e.symm, e.symm.continuous⟩ with heC'
  have hinj : Function.Injective (Homology.map eC (k + 1)) := by
    intro a b hab
    have h1 := congrArg (Homology.map eC' (k + 1)) hab
    rw [← LinearMap.comp_apply, ← Homology.map_comp, ← LinearMap.comp_apply,
      ← Homology.map_comp] at h1
    rwa [show eC'.comp eC = ContinuousMap.id _ from
        ContinuousMap.ext (fun z => e.symm_apply_apply z),
      Homology.map_id, LinearMap.id_apply, LinearMap.id_apply] at h1
  refine hinj ?_
  rw [map_zero]
  exact SKEFTHawking.SingularManifoldFundamentalClass.eucl_homology_zero 2 k _

/-! ## §2. `H₁(S²; ℤ/2) = 0`

The pair-LES at a point: `H₁(S²) ↪ H₁(S²|v)` (the punctured sphere is acyclic, §1), and
`H₁(S²|v) ≅ H₁(ℝ²|q) = 0` (the degree-1 chart transport — the same excision/chart-pair pieces
`chartLocalIso` composes, into the G1 degree-1 convex-compact vanishing at `K = {q}`). This is
the sole sphere-cohomology input to the surface Smith ladder (`H₂(S²) ≠ 0` is the top, no rung
above it). -/

open SKEFTHawking.SingularChartBridge SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularConvexStageIso SKEFTHawking.SingularEuclideanAcyclic
open SKEFTHawking.SingularConvexComplementConnected SKEFTHawking.SingularConvexRadialMiddle

/-- The `S²`-side point excision (fresh-budget piece 1). -/
noncomputable def sphereExcisionS (v : S2) (k : ℕ) :
    RelativeHomology
        (SKEFTHawking.SingularExcisionIso.restr (X := TopCat.of S2) {y | y ≠ v}
          (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) v).source) (k + 1)
      ≃ₗ[ZMod 2] RelativeHomology (X := TopCat.of S2) {y | y ≠ v} (k + 1) :=
  haveI : T1Space ↑(TopCat.of S2) := inferInstanceAs (T1Space S2)
  openPointExcisionEquiv (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) v).open_source
    (mem_chart_source _ v) k

/-- The chart-pair transport (fresh-budget piece 2; type inferred — the ascribed form
whnf-walls on the seam defeq). -/
noncomputable def sphereChartPair (v : S2) (k : ℕ) :=
  chartPairEquiv (M := TopCat.of S2) (m := 0)
    (mem_chart_source (EuclideanSpace ℝ (Fin (0 + 2))) v)
    (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) v).toHomeomorphSourceTarget rfl (k + 1)

/-- The `ℝ²`-side point excision (fresh-budget piece 3). -/
noncomputable def sphereExcisionE (v : S2) (k : ℕ) :
    RelativeHomology
        (SKEFTHawking.SingularExcisionIso.restr
          (X := SingularEuclideanAcyclic.Eucl (0 + 2))
          {y | y ≠ chartAt (EuclideanSpace ℝ (Fin (0 + 2))) v v}
          (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) v).target) (k + 1)
      ≃ₗ[ZMod 2] RelativeHomology (X := SingularEuclideanAcyclic.Eucl (0 + 2))
        {y | y ≠ chartAt (EuclideanSpace ℝ (Fin (0 + 2))) v v} (k + 1) :=
  openPointExcisionEquiv (X := SingularEuclideanAcyclic.Eucl (0 + 2))
    (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) v).open_target (mem_chart_target _ v) k

/-- The `S²` charted instance re-keyed at the `Fin (0 + 2)` spelling the chart-bridge machinery
uses (defeq; instance search is syntactic on the model key). -/
noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) S2 :=
  inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 2)) S2)

/-- **The degree-generic point-local transport for `S²`**: `H_{k+1}(S²|v) ≅ H_{k+1}(ℝ²|q)` —
`chartLocalIso`'s composite without the top-degree factor. -/
noncomputable def sphereLocalTransport (v : S2) (k : ℕ) :
    RelativeHomology (X := TopCat.of S2) {y | y ≠ v} (k + 1)
      ≃ₗ[ZMod 2] RelativeHomology (X := SingularEuclideanAcyclic.Eucl (0 + 2))
        {y | y ≠ chartAt (EuclideanSpace ℝ (Fin (0 + 2))) v v} (k + 1) :=
  (sphereExcisionS v k).symm.trans ((sphereChartPair v k).trans (sphereExcisionE v k))

/-- **The degree-1 local homology of `S²` at a point vanishes**: `H₁(S²|v) = 0` — transport +
`relHomology_one_convexCompact` at the convex compact `{q}`. (For the surface only the degree-1
rung is needed: `H₂(S²|v) ≅ ℤ/2 ≠ 0` is the top, so the middle/top rungs of the `ℝP⁴` tower have
no analogue here.) -/
theorem sphereLocal_eq_zero (v : S2) (k : ℕ) (hk : k + 1 ≤ 1)
    (x : RelativeHomology (X := TopCat.of S2) ({v}ᶜ : Set S2) (k + 1)) : x = 0 := by
  set q := chartAt (EuclideanSpace ℝ (Fin (0 + 2))) v v with hq
  -- bridge {v}ᶜ ↔ {y | y ≠ v}, transport to ℝ², bridge {y | y ≠ q} ↔ {q}ᶜ
  set b1 := relHomologySetCongr (X := TopCat.of S2)
    (S := ({v}ᶜ : Set S2)) (T := {y | y ≠ v})
    (fun y hy => hy) (fun y hy => hy) (k + 1) with hb1
  set b2 := relHomologySetCongr (X := SingularEuclideanAcyclic.Eucl (0 + 2))
    (S := {y | y ≠ q}) (T := ({q}ᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (0 + 2))))
    (fun y hy => hy) (fun y hy => hy) (k + 1) with hb2
  have hvanish : b2 (sphereLocalTransport v k (b1 x)) = 0 := by
    have hk0 : k = 0 := by omega
    subst hk0
    exact relHomology_one_convexCompact (convex_singleton q) isCompact_singleton _
  have h1 := (LinearEquiv.map_eq_zero_iff b2).mp hvanish
  have h2 := (LinearEquiv.map_eq_zero_iff (sphereLocalTransport v k)).mp h1
  exact (LinearEquiv.map_eq_zero_iff b1).mp h2

/-- **`H₁(S²; ℤ/2) = 0`** — the pair-LES at a point: exactness places any class in the image of
the (vanishing) punctured-sphere homology once its (vanishing) local image dies. Stated at the
degree-1 rung `1 ≤ k ≤ 1`; this is the only sphere-vanishing input the surface Smith ladder needs. -/
theorem sphere_homology_eq_zero (k : ℕ) (h1 : 1 ≤ k) (h3 : k ≤ 1)
    (x : Homology (TopCat.of S2) k) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have v : S2 := ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm]; simp⟩
  -- the local image vanishes
  have hproj : homProj ({v}ᶜ : Set S2) (k + 1) x = 0 :=
    sphereLocal_eq_zero v k h3 _
  -- exactness at H(X): x ∈ im homIncl
  have hexact := exact_homIncl_homProj (X := TopCat.of S2) (S := ({v}ᶜ : Set S2)) (k + 1)
  obtain ⟨y, hy⟩ := (hexact x).mp hproj
  rw [← hy, punctSphere_homology_eq_zero v k y, map_zero]

end SKEFTHawking.RP2SphereHomology
