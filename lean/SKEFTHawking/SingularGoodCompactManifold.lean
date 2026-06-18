import Mathlib
import SKEFTHawking.SingularGoodCompact
import SKEFTHawking.SingularGoodCompactChart
import SKEFTHawking.SingularCompactChartCover

/-!
# Phase 5q.F (w₂-foundation, brick 72c-4n) — `goodCompact` for a compact set inside a chart source

For a topological manifold `M` modelled on `ℝⁿ` (`n = m+2`, a Mathlib `ChartedSpace`), a compact set
`K ⊆ M` contained in a single chart source is `goodCompact (m+2) K`. The chart `chartAt x` supplies the
homeomorphism of pairs `goodCompact_chart` consumes: the chart-image `C = (chartAt x) '' K` is compact
(continuous image of a compact), lands in the chart target, and matches `K` point-for-point (the chart
is injective on its source). This is the manifold-level single-chart base case the finite-union
fundamental-class assembly stacks on.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularGoodCompact

namespace SKEFTHawking.SingularGoodCompactManifold

/-- **A compact set inside a chart source is `goodCompact`**: extract the chart data
(`C = chartAt x '' K`, `e = (chartAt x).toHomeomorphSourceTarget`, point-compatibility from chart
injectivity) and apply `goodCompact_chart`. -/
theorem goodCompact_compact_in_chart_source {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {K : Set M} {x : M}
    (hK : IsCompact K) (hKsub : K ⊆ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x).source) :
    SKEFTHawking.SingularGoodCompact.goodCompact (X := TopCat.of M) (m + 2) K := by
  haveI : T1Space ↑(TopCat.of M) := inferInstanceAs (T1Space M)
  set c := chartAt (EuclideanSpace ℝ (Fin (m + 2))) x with hc
  refine SingularGoodCompactChart.goodCompact_chart (M := TopCat.of M) (U := c.source)
    (C := c '' K) (V := c.target) hK.isClosed c.open_source hKsub
    (hK.image_of_continuousOn (c.continuousOn.mono hKsub)) c.open_target
    ((Set.image_mono hKsub).trans c.mapsTo.image_subset) c.toHomeomorphSourceTarget ?_
  intro u
  rw [show (c.toHomeomorphSourceTarget u : EuclideanSpace ℝ (Fin (m + 2))) = c (u : M) from
      c.toHomeomorphSourceTarget_apply_coe u]
  exact (c.injOn.mem_image_iff hKsub u.2)

/-- **A compact charted manifold is `goodCompact` on all of `M`** (Hatcher step 4): cover `M` by
finitely many compact chart pieces (`exists_finite_compact_chart_cover`), each `goodCompact`
(`goodCompact_compact_in_chart_source`); every sub-intersection is a closed subset of one of them,
hence compact inside the same chart source and again `goodCompact`, so `goodCompact_biUnion` gives
`goodCompact (m+2) (univ : Set M)`. The penultimate step toward the fundamental class `[M]`. -/
theorem goodCompact_univ {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] :
    SKEFTHawking.SingularGoodCompact.goodCompact (X := TopCat.of M) (m + 2)
      (Set.univ : Set M) := by
  classical
  obtain ⟨s, K, hs, hKcomp, hKchart, hcov⟩ :=
    SingularCompactChartCover.exists_finite_compact_chart_cover (m := m) (M := M)
  rw [← hcov]
  refine SingularGoodCompact.goodCompact_biUnion (X := TopCat.of M) hs K (fun t ht htne => ?_)
  obtain ⟨j, hj⟩ := htne
  have hsubKj : (⋂ x ∈ t, K x) ⊆ K j := Set.biInter_subset_of_mem hj
  have hclosed : IsClosed (⋂ x ∈ t, K x) :=
    isClosed_biInter (fun x hx => (hKcomp x (ht hx)).isClosed)
  have hcompInter : IsCompact (⋂ x ∈ t, K x) :=
    (hKcomp j (ht hj)).of_isClosed_subset hclosed hsubKj
  exact ⟨hclosed, goodCompact_compact_in_chart_source hcompInter
    (hsubKj.trans (hKchart j (ht hj)))⟩

/-- **Restriction to a point of a closed-ball chart neighbourhood is bijective** (M:Type, *concrete*
chart form of F1): for a closed ball `B̄(chartAt y₀ · y₀, r)` inside the chart target and a point `y` in
its chart-pullback `K = (chartAt y₀).symm '' B̄`, the restriction `Hₘ₊₂(M|K) → Hₘ₊₂(M|y)` is bijective.
Applies `SingularGoodCompactChart.restrictToPoint_convexChart_bijective` (F1) with the **concrete** chart
`(chartAt y₀).toHomeomorphSourceTarget` (whose type pins the topology instances) — sidestepping the
`isDefEq` wall that an *abstract* chart hypothesis triggers under the `M:Type ↔ TopCat.of M` coercion.
The local-homology iso the fundamental-class local-constancy argument rides on. -/
theorem restrictToPoint_chartBall_bijective {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (y₀ : M) {r : ℝ}
    (hrsub : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) r
      ⊆ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).target)
    {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).symm ''
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) r) :
    Function.Bijective
      (SingularManifoldFundamentalClass.restrictToPoint (X := TopCat.of M) hy (m + 2)) := by
  haveI : T1Space ↑(TopCat.of M) := inferInstanceAs (T1Space M)
  set c := chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ with hc
  have hCcomp : IsCompact (Metric.closedBall (c y₀) r) := isCompact_closedBall _ _
  have hKsub : c.symm '' Metric.closedBall (c y₀) r ⊆ c.source := by
    rintro p ⟨z, hz, rfl⟩; exact c.map_target (hrsub hz)
  have hKcomp : IsCompact (c.symm '' Metric.closedBall (c y₀) r) :=
    hCcomp.image_of_continuousOn (c.continuousOn_symm.mono hrsub)
  have hcompat : ∀ u : ↥c.source,
      ((c.toHomeomorphSourceTarget u : ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
          ∈ Metric.closedBall (c y₀) r)
        ↔ ((u : M) ∈ c.symm '' Metric.closedBall (c y₀) r) := by
    intro u
    rw [c.toHomeomorphSourceTarget_apply_coe]
    constructor
    · intro h; exact ⟨c u, h, c.left_inv u.2⟩
    · rintro ⟨z, hz, hzu⟩; rw [← hzu, c.right_inv (hrsub hz)]; exact hz
  exact SKEFTHawking.SingularGoodCompactChart.restrictToPoint_convexChart_bijective hKcomp.isClosed
    c.open_source hKsub (convex_closedBall _ _) hCcomp c.open_target hrsub
    c.toHomeomorphSourceTarget hcompat hy

/-- **A point has a closed-ball chart neighbourhood**: for `x₀` in a charted manifold there is `r > 0`
with `B̄(chartAt x₀ · x₀, r) ⊆ (chartAt x₀).target` and `x₀` in the **interior** of the chart-pullback
`(chartAt x₀).symm '' B̄`. The open neighbourhood on which the fundamental-class restriction value is
locally constant (`localComposite_agree_chartBall`). -/
theorem exists_chartBall_nbhd {m : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x₀ : M) :
    ∃ r > 0, Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x₀ x₀) r
        ⊆ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x₀).target ∧
      x₀ ∈ interior ((chartAt (EuclideanSpace ℝ (Fin (m + 2))) x₀).symm ''
        Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x₀ x₀) r) := by
  set c := chartAt (EuclideanSpace ℝ (Fin (m + 2))) x₀ with hc
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp c.open_target (c x₀) (mem_chart_target _ x₀)
  refine ⟨r / 2, by positivity,
    (Metric.closedBall_subset_ball (by linarith)).trans hrsub, ?_⟩
  -- `x₀ = c.symm (c x₀)` lies in `c.symm '' ball ⊆ interior (c.symm '' closedBall)`.
  have hball_sub : Metric.ball (c x₀) (r / 2) ⊆ c.target :=
    (Metric.ball_subset_closedBall.trans
      ((Metric.closedBall_subset_ball (by linarith)).trans hrsub))
  have hopen : IsOpen (c.symm '' Metric.ball (c x₀) (r / 2)) :=
    c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hball_sub
  apply interior_mono (Set.image_mono Metric.ball_subset_closedBall)
  rw [hopen.interior_eq]
  exact ⟨c x₀, Metric.mem_ball_self (by positivity), c.left_inv (mem_chart_source _ x₀)⟩

end SKEFTHawking.SingularGoodCompactManifold
