import Mathlib
import SKEFTHawking.SingularGoodCompactInt
import SKEFTHawking.SingularGoodCompactUnionInt
import SKEFTHawking.SingularGoodCompactChartInt
import SKEFTHawking.SingularCompactChartCover

/-!
# The integral "good compact" property for a compact charted manifold (Hatcher step 4, ℤ) — brick 18f

The ℤ analog of the mod-2 `SingularGoodCompactManifold`. For a topological manifold `M` modelled on
`ℝⁿ` (`n = m+2`, a Mathlib `ChartedSpace`):

* `goodCompactInt_compact_in_chart_source` — a compact set `K ⊆ M` contained in a single chart source
  is `goodCompactInt (m+2) K` (extract the chart data + apply `goodCompactInt_chart`);
* `goodCompactInt_univ` — a compact charted manifold is `goodCompactInt (m+2)` on all of `M` (cover `M`
  by finitely many compact chart pieces — `exists_finite_compact_chart_cover`, coefficient-free, reused
  — each `goodCompactInt`, and glue by `goodCompactInt_biUnion`).

These are the manifold-level headlines the oriented fundamental-class construction stacks on. Both
reuse the coefficient-free chart-cover topology of the mod-2 development directly.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularGoodCompactInt

namespace SKEFTHawking.SingularGoodCompactManifoldInt

/-- **A compact set inside a chart source is `goodCompactInt`** (ℤ): extract the chart data
(`C = chartAt x '' K`, `e = (chartAt x).toHomeomorphSourceTarget`, point-compatibility from chart
injectivity) and apply `goodCompactInt_chart`. -/
theorem goodCompactInt_compact_in_chart_source {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {K : Set M} {x : M}
    (hK : IsCompact K) (hKsub : K ⊆ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x).source) :
    goodCompactInt (X := TopCat.of M) (m + 2) K := by
  haveI : T1Space ↑(TopCat.of M) := inferInstanceAs (T1Space M)
  set c := chartAt (EuclideanSpace ℝ (Fin (m + 2))) x with hc
  refine SingularGoodCompactChartInt.goodCompactInt_chart (M := TopCat.of M) (U := c.source)
    (C := c '' K) (V := c.target) hK.isClosed c.open_source hKsub
    (hK.image_of_continuousOn (c.continuousOn.mono hKsub)) c.open_target
    ((Set.image_mono hKsub).trans c.mapsTo.image_subset) c.toHomeomorphSourceTarget ?_
  intro u
  rw [show (c.toHomeomorphSourceTarget u : EuclideanSpace ℝ (Fin (m + 2))) = c (u : M) from
      c.toHomeomorphSourceTarget_apply_coe u]
  exact (c.injOn.mem_image_iff hKsub u.2)

/-- **A compact charted manifold is `goodCompactInt` on all of `M`** (Hatcher step 4, ℤ): cover `M` by
finitely many compact chart pieces (`exists_finite_compact_chart_cover`, coefficient-free), each
`goodCompactInt` (`goodCompactInt_compact_in_chart_source`); every sub-intersection is a closed subset
of one of them, hence compact inside the same chart source and again `goodCompactInt`, so
`goodCompactInt_biUnion` gives `goodCompactInt (m+2) (univ : Set M)`. The penultimate step toward the
oriented fundamental class `[M]`. -/
theorem goodCompactInt_univ {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] :
    goodCompactInt (X := TopCat.of M) (m + 2) (Set.univ : Set M) := by
  classical
  obtain ⟨s, K, hs, hKcomp, hKchart, hcov⟩ :=
    SingularCompactChartCover.exists_finite_compact_chart_cover (m := m) (M := M)
  rw [← hcov]
  refine SingularGoodCompactUnionInt.goodCompactInt_biUnion (X := TopCat.of M) hs K
    (fun t ht htne => ?_)
  obtain ⟨j, hj⟩ := htne
  have hsubKj : (⋂ x ∈ t, K x) ⊆ K j := Set.biInter_subset_of_mem hj
  have hclosed : IsClosed (⋂ x ∈ t, K x) :=
    isClosed_biInter (fun x hx => (hKcomp x (ht hx)).isClosed)
  have hcompInter : IsCompact (⋂ x ∈ t, K x) :=
    (hKcomp j (ht hj)).of_isClosed_subset hclosed hsubKj
  exact ⟨hclosed, goodCompactInt_compact_in_chart_source hcompInter
    (hsubKj.trans (hKchart j (ht hj)))⟩

end SKEFTHawking.SingularGoodCompactManifoldInt
