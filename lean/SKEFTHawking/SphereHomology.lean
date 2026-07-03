import Mathlib
import SKEFTHawking.RP4PointSet
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularConvexStageIso
import SKEFTHawking.SingularConvexComplementConnected
import SKEFTHawking.SingularConvexRadialMiddle

/-!
# Phase 5q.G (B-arc, M1-a) — the punctured 4-sphere is acyclic

The first rung of the `H_*(S⁴;ℤ/2)` computation (toward the Smith sequence of the antipodal
cover): `S⁴ ∖ {v} ≃ₜ ℝ⁴` by the stereographic chart (Mathlib's `stereographic'`, whose source
is exactly `{v}ᶜ` and target all of `ℝ⁴`), so its positive-degree homology vanishes by
transport onto the Euclidean acyclicity (`eucl_homology_zero`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open Metric
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.RP4PointSet SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularHomotopyInvariance

namespace SKEFTHawking.SphereHomology

/-- **The punctured 4-sphere is homeomorphic to `ℝ⁴`** — the stereographic chart, whose source
is `{v}ᶜ` and target `univ`. -/
noncomputable def punctSphereHomeo (v : S4) :
    ↥({v}ᶜ : Set S4) ≃ₜ EuclideanSpace ℝ (Fin 4) :=
  ((Homeomorph.setCongr (stereographic'_source v).symm).trans
      (stereographic' 4 v).toHomeomorphSourceTarget).trans
    ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _))

/-- **The punctured 4-sphere is acyclic in positive degrees** — transport the Euclidean
vanishing along the stereographic homeomorphism. -/
theorem punctSphere_homology_eq_zero (v : S4) (k : ℕ)
    (x : Homology (sub (X := TopCat.of S4) ({v}ᶜ : Set S4)) (k + 1)) : x = 0 := by
  set e := punctSphereHomeo v
  set eC : C(↥(sub (X := TopCat.of S4) ({v}ᶜ : Set S4)),
      ↥(SingularEuclideanAcyclic.Eucl 4)) := ⟨e, e.continuous⟩ with heC
  set eC' : C(↥(SingularEuclideanAcyclic.Eucl 4),
      ↥(sub (X := TopCat.of S4) ({v}ᶜ : Set S4))) := ⟨e.symm, e.symm.continuous⟩ with heC'
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
  exact SKEFTHawking.SingularManifoldFundamentalClass.eucl_homology_zero 4 k _

/-! ## §2. `H_k(S⁴; ℤ/2) = 0` for `k = 1, 2, 3`

The pair-LES at a point: `H_k(S⁴) ↪ H_k(S⁴|v)` (the punctured sphere is acyclic, §1), and
`H_k(S⁴|v) ≅ H_k(ℝ⁴|q) = 0` for `k ≤ 3` (the degree-generic chart transport — the same
excision/chart-pair pieces `chartLocalIso` composes, minus its top-degree last factor — into
the G1 convex-compact vanishings at `K = {q}`). -/

open SKEFTHawking.SingularChartBridge SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularConvexStageIso SKEFTHawking.SingularEuclideanAcyclic
open SKEFTHawking.SingularConvexComplementConnected SKEFTHawking.SingularConvexRadialMiddle

/-- The `S⁴`-side point excision (fresh-budget piece 1). -/
noncomputable def sphereExcisionS (v : S4) (k : ℕ) :
    RelativeHomology
        (SKEFTHawking.SingularExcisionIso.restr (X := TopCat.of S4) {y | y ≠ v}
          (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) v).source) (k + 1)
      ≃ₗ[ZMod 2] RelativeHomology (X := TopCat.of S4) {y | y ≠ v} (k + 1) :=
  haveI : T1Space ↑(TopCat.of S4) := inferInstanceAs (T1Space S4)
  openPointExcisionEquiv (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) v).open_source
    (mem_chart_source _ v) k

/-- The chart-pair transport (fresh-budget piece 2; type inferred — the ascribed form
whnf-walls on the seam defeq). -/
noncomputable def sphereChartPair (v : S4) (k : ℕ) :=
  chartPairEquiv (M := TopCat.of S4) (m := 2)
    (mem_chart_source (EuclideanSpace ℝ (Fin (2 + 2))) v)
    (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) v).toHomeomorphSourceTarget rfl (k + 1)

/-- The `ℝ⁴`-side point excision (fresh-budget piece 3). -/
noncomputable def sphereExcisionE (v : S4) (k : ℕ) :
    RelativeHomology
        (SKEFTHawking.SingularExcisionIso.restr
          (X := SingularEuclideanAcyclic.Eucl (2 + 2))
          {y | y ≠ chartAt (EuclideanSpace ℝ (Fin (2 + 2))) v v}
          (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) v).target) (k + 1)
      ≃ₗ[ZMod 2] RelativeHomology (X := SingularEuclideanAcyclic.Eucl (2 + 2))
        {y | y ≠ chartAt (EuclideanSpace ℝ (Fin (2 + 2))) v v} (k + 1) :=
  openPointExcisionEquiv (X := SingularEuclideanAcyclic.Eucl (2 + 2))
    (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) v).open_target (mem_chart_target _ v) k

/-- The `S⁴` charted instance re-keyed at the `Fin (2 + 2)` spelling the chart-bridge machinery
uses (defeq; instance search is syntactic on the model key). -/
noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) S4 :=
  inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 4)) S4)

/-- **The degree-generic point-local transport for `S⁴`**: `H_{k+1}(S⁴|v) ≅ H_{k+1}(ℝ⁴|q)` —
`chartLocalIso`'s composite without the top-degree factor. -/
noncomputable def sphereLocalTransport (v : S4) (k : ℕ) :
    RelativeHomology (X := TopCat.of S4) {y | y ≠ v} (k + 1)
      ≃ₗ[ZMod 2] RelativeHomology (X := SingularEuclideanAcyclic.Eucl (2 + 2))
        {y | y ≠ chartAt (EuclideanSpace ℝ (Fin (2 + 2))) v v} (k + 1) :=
  (sphereExcisionS v k).symm.trans ((sphereChartPair v k).trans (sphereExcisionE v k))

/-- **The local homology of `S⁴` at a point vanishes below the top degree**: `H_{k+1}(S⁴|v) = 0`
for `k + 1 ≤ 3` — transport + `relHomology_one` (degree 1) / `vanishMiddle_convexCompact`
(degrees 2, 3) at the convex compact `{q}`. -/
theorem sphereLocal_eq_zero (v : S4) (k : ℕ) (hk : k + 1 ≤ 3)
    (x : RelativeHomology (X := TopCat.of S4) ({v}ᶜ : Set S4) (k + 1)) : x = 0 := by
  set q := chartAt (EuclideanSpace ℝ (Fin (2 + 2))) v v with hq
  -- bridge {v}ᶜ ↔ {y | y ≠ v}, transport to ℝ⁴, bridge {y | y ≠ q} ↔ {q}ᶜ
  set b1 := relHomologySetCongr (X := TopCat.of S4)
    (S := ({v}ᶜ : Set S4)) (T := {y | y ≠ v})
    (fun y hy => hy) (fun y hy => hy) (k + 1) with hb1
  set b2 := relHomologySetCongr (X := SingularEuclideanAcyclic.Eucl (2 + 2))
    (S := {y | y ≠ q}) (T := ({q}ᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))))
    (fun y hy => hy) (fun y hy => hy) (k + 1) with hb2
  have hvanish : b2 (sphereLocalTransport v k (b1 x)) = 0 := by
    have hk2 : k ≤ 2 := by omega
    interval_cases k
    · exact relHomology_one_convexCompact (convex_singleton q) isCompact_singleton _
    · exact vanishMiddle_convexCompact (convex_singleton q) isCompact_singleton
        (Set.mem_singleton q) 2 (by norm_num) (by norm_num) _
    · exact vanishMiddle_convexCompact (convex_singleton q) isCompact_singleton
        (Set.mem_singleton q) 3 (by norm_num) (by norm_num) _
  have h1 := (LinearEquiv.map_eq_zero_iff b2).mp hvanish
  have h2 := (LinearEquiv.map_eq_zero_iff (sphereLocalTransport v k)).mp h1
  exact (LinearEquiv.map_eq_zero_iff b1).mp h2

/-- **`H_k(S⁴; ℤ/2) = 0` for `1 ≤ k ≤ 3`** — the pair-LES at a point: exactness places any class
in the image of the (vanishing) punctured-sphere homology once its (vanishing) local image dies. -/
theorem sphere_homology_eq_zero (k : ℕ) (h1 : 1 ≤ k) (h3 : k ≤ 3)
    (x : Homology (TopCat.of S4) k) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have v : S4 := ⟨EuclideanSpace.single (0 : Fin 5) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm]; simp⟩
  -- the local image vanishes
  have hproj : homProj ({v}ᶜ : Set S4) (k + 1) x = 0 :=
    sphereLocal_eq_zero v k h3 _
  -- exactness at H(X): x ∈ im homIncl
  have hexact := exact_homIncl_homProj (X := TopCat.of S4) (S := ({v}ᶜ : Set S4)) (k + 1)
  obtain ⟨y, hy⟩ := (hexact x).mp hproj
  rw [← hy, punctSphere_homology_eq_zero v k y, map_zero]

end SKEFTHawking.SphereHomology
