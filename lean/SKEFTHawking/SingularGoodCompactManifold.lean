import Mathlib
import SKEFTHawking.SingularGoodCompact
import SKEFTHawking.SingularGoodCompactChart

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

end SKEFTHawking.SingularGoodCompactManifold
