import Mathlib
import SKEFTHawking.SingularCSCVanishAbove
import SKEFTHawking.SingularGoodCompactManifold

/-!
# Phase 5q.F (w₂-foundation, G1 PD track A) — W-relative geometric cofinality of `vanishAbove` stages

The geometric input closing the top-degree vanishing of `Hᵏ_c(W)` for an **open** `W` in a charted
manifold: every compact `K ⊆ W` is contained in a compact `K' ⊆ W` that is a **finite union of
chart-ball pieces inside `W`** and hence satisfies the Hatcher-3.27 vanishing `vanishAbove (m+2) K'`.

* `exists_chartBall_subset_open` — a point of an open `W` has a closed chart ball whose chart-pullback
  stays inside `W` (shrink a ball into `target ∩ (chartAt x).symm ⁻¹' W`).
* `vanishAbove_cofinal` — the **W-relative geometric cofinality**: cover the compact `K` by finitely
  many such chart-ball pieces (compactness of `K`), take `K' :=` their union. Every nonempty
  sub-intersection of the pieces is a compact subset of a *single* chart source — the multi-chart
  Hatcher subtlety is absorbed by the arbitrary-compact single-chart result
  (`goodCompact_compact_in_chart_source`, riding on `vanishAbove_eucl_compact`) exactly as in the L1
  `[M]`-finale (`goodCompact_univ` / `hasFundClass_univ`) — so `vanishAbove_biUnion` glues.
* `cscOpen_eq_zero_of_isOpen` — the corollary: `Hᵏ_c(W) = 0` for every open `W` and every degree
  `k > m+2`, by composing with `cscOpen_eq_zero_of_vanishAbove_cofinal`. The top-degree vanishing
  input of the G1 Poincaré-duality open-cover induction.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularManifoldFundamentalClass SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularCompactlySupportedOpen

namespace SKEFTHawking.SingularCSCVanishAboveGeom

/-- **A chart ball inside an open set**: for `x ∈ W` (`W` open) there is `r > 0` with the closed ball
`B̄(chartAt x · x, r)` inside the chart target *and* its chart-pullback inside `W`. Shrink a ball into
the open set `target ∩ (chartAt x).symm ⁻¹' W` (open since `symm` is continuous on the open target),
which contains `chartAt x · x`. -/
theorem exists_chartBall_subset_open {m : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {W : Set M} (hW : IsOpen W) {x : M}
    (hxW : x ∈ W) :
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x x) r
          ⊆ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x).target ∧
      (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x).symm ''
          Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x x) r ⊆ W := by
  set c := chartAt (EuclideanSpace ℝ (Fin (m + 2))) x with hc
  have hT_open : IsOpen (c.target ∩ c.symm ⁻¹' W) :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target hW
  have hcx_mem : c x ∈ c.target ∩ c.symm ⁻¹' W := by
    refine ⟨mem_chart_target _ x, ?_⟩
    rw [Set.mem_preimage, c.left_inv (mem_chart_source _ x)]
    exact hxW
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hT_open _ hcx_mem
  have hsub' : Metric.closedBall (c x) (r / 2) ⊆ c.target ∩ c.symm ⁻¹' W :=
    (Metric.closedBall_subset_ball (by linarith)).trans hsub
  refine ⟨r / 2, by linarith, hsub'.trans Set.inter_subset_left, ?_⟩
  rintro p ⟨z, hz, rfl⟩
  exact (hsub' hz).2

/-- **W-relative geometric cofinality of the `vanishAbove` stages** (G1 track A, geometric input):
every compact `K ⊆ W` (`W` open) is contained in a compact `K' ⊆ W` with
`vanishAbove (m+2) ↑K'` — take `K'` = a finite union of closed chart-ball pieces inside `W` covering
`K` (`exists_chartBall_subset_open` + compactness). Every nonempty sub-intersection of the pieces is
a compact subset of a single piece's chart source, hence `vanishAbove` by the arbitrary-compact
single-chart result (`goodCompact_compact_in_chart_source`), so `vanishAbove_biUnion` glues — the
same cover-then-glue as the L1 `hasFundClass_univ`/`goodCompact_univ`, run inside `W`. -/
theorem vanishAbove_cofinal {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {W : Set M} (hW : IsOpen W)
    (K : CompactsIn W) :
    ∃ K' : CompactsIn W, K ≤ K' ∧
      vanishAbove (X := TopCat.of M) (m + 2) (↑K'.1 : Set M) := by
  classical
  rcases Set.eq_empty_or_nonempty (↑K.1 : Set M) with hKe | hKne
  · -- Empty compact: `K' := K` itself, `vanishAbove` of `∅`.
    refine ⟨K, le_refl K, ?_⟩
    rw [hKe]
    exact (SingularGoodCompactEuclidean.goodCompact_empty (X := TopCat.of M) (m + 2)).1
  · have hKW : (↑K.1 : Set M) ⊆ W := K.2
    set c : M → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 2))) :=
      fun x => chartAt (EuclideanSpace ℝ (Fin (m + 2))) x with hc
    -- Per-point chart-ball radii inside `W`, indexed by the points of `K`.
    have hball : ∀ i : (↑K.1 : Set M), ∃ r : ℝ, 0 < r ∧
        Metric.closedBall ((c i) i) r ⊆ (c i).target ∧
        (c i).symm '' Metric.closedBall ((c i) i) r ⊆ W :=
      fun i => exists_chartBall_subset_open hW (hKW i.2)
    choose r hrpos hrsub hrW using hball
    -- The closed chart-ball pieces `B i ⊆ W` and their open cores `O i`.
    set B : (↑K.1 : Set M) → Set M :=
      fun i => (c i).symm '' Metric.closedBall ((c i) i) (r i) with hB
    set O : (↑K.1 : Set M) → Set M :=
      fun i => (c i).symm '' Metric.ball ((c i) i) (r i) with hO
    have hO_open : ∀ i, IsOpen (O i) := fun i =>
      (c i).isOpen_image_symm_of_subset_target Metric.isOpen_ball
        (Metric.ball_subset_closedBall.trans (hrsub i))
    have hO_mem : ∀ i : (↑K.1 : Set M), (i : M) ∈ O i := fun i =>
      ⟨(c i) i, Metric.mem_ball_self (hrpos i), (c i).left_inv (mem_chart_source _ _)⟩
    have hOB : ∀ i, O i ⊆ B i := fun i => Set.image_mono Metric.ball_subset_closedBall
    -- Finite subcover of the compact `K` by the open cores.
    have hcover : (↑K.1 : Set M) ⊆ ⋃ i, O i := fun x hx =>
      Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hO_mem ⟨x, hx⟩⟩
    obtain ⟨t, ht⟩ := K.1.isCompact'.elim_finite_subcover O hO_open hcover
    have hB_compact : ∀ i, IsCompact (B i) := fun i =>
      (ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
        ((c i).continuousOn_symm.mono (hrsub i))
    have hB_source : ∀ i, B i ⊆ (c i).source := fun i => by
      rintro p ⟨z, hz, rfl⟩
      exact (c i).symm_mapsTo (hrsub i hz)
    have hKK' : (↑K.1 : Set M) ⊆ ⋃ i ∈ t, B i :=
      ht.trans (Set.iUnion₂_mono fun i _ => hOB i)
    have ht_ne : t.Nonempty := by
      obtain ⟨x, hx⟩ := hKne
      obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp (ht hx)
      exact ⟨i, hi⟩
    have hK'_compact : IsCompact (⋃ i ∈ t, B i) :=
      t.finite_toSet.isCompact_biUnion (fun i _ => hB_compact i)
    have hK'_W : (⋃ i ∈ t, B i) ⊆ W := Set.iUnion₂_subset (fun i _ => hrW i)
    refine ⟨⟨⟨⋃ i ∈ t, B i, hK'_compact⟩, hK'_W⟩, hKK', ?_⟩
    -- Glue `vanishAbove` over the pieces: every nonempty sub-intersection is a compact subset of a
    -- single piece's chart source.
    refine vanishAbove_biUnion (X := TopCat.of M) ht_ne B (fun t' ht' ht'ne => ?_)
    obtain ⟨j, hj⟩ := ht'ne
    have hsubBj : (⋂ i ∈ t', B i) ⊆ B j := Set.biInter_subset_of_mem hj
    have hclosed : IsClosed (⋂ i ∈ t', B i) :=
      isClosed_biInter (fun i hi => (hB_compact i).isClosed)
    have hcompInter : IsCompact (⋂ i ∈ t', B i) :=
      (hB_compact j).of_isClosed_subset hclosed hsubBj
    exact ⟨hclosed, (SingularGoodCompactManifold.goodCompact_compact_in_chart_source hcompInter
      (hsubBj.trans (hB_source j))).1⟩

/-- **Top-degree vanishing of `Hᵏ_c(W)` for an open `W` in a charted manifold** (G1 track A,
combined): for every open `W ⊆ M` and every degree `k > m+2`, every class of the compactly-supported
cohomology `Hᵏ_c(W)` vanishes. The geometric cofinality (`vanishAbove_cofinal`) feeds the colimit
lemma (`cscOpen_eq_zero_of_vanishAbove_cofinal`). -/
theorem cscOpen_eq_zero_of_isOpen {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {W : Set M} (hW : IsOpen W) {k : ℕ}
    (hk : m + 2 < k) (α : CompactlySupportedCohomologyOpen (M := TopCat.of M) W k) : α = 0 :=
  SingularCSCVanishAbove.cscOpen_eq_zero_of_vanishAbove_cofinal (M := TopCat.of M) hk
    (fun K => vanishAbove_cofinal hW K) α

end SKEFTHawking.SingularCSCVanishAboveGeom
