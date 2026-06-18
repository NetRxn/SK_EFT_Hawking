import Mathlib

/-!
# Phase 5q.F (w₂-foundation, brick 72c-4o) — finite compact cover of a charted compact space by chart pieces

A compact topological manifold `M` modelled on `ℝⁿ` (`n = m+2`, a Mathlib `ChartedSpace`) is covered by
finitely many **compact** sets, each contained in a single chart source. Pull back closed balls under the
charts and take a finite subcover of the (open) interiors. This is the manifold-level cover the
fundamental-class finite-union compactness induction consumes.
-/

namespace SKEFTHawking.SingularCompactChartCover

theorem exists_finite_compact_chart_cover {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] :
    ∃ (s : Finset M) (K : M → Set M), s.Nonempty ∧
      (∀ x ∈ s, IsCompact (K x)) ∧
      (∀ x ∈ s, K x ⊆ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) x).source) ∧
      (⋃ x ∈ s, K x) = Set.univ := by
  set c : M → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 2))) :=
    fun x => chartAt (EuclideanSpace ℝ (Fin (m + 2))) x with hc
  -- For each `x`, the chart target is open and contains `(c x) x`, so a closed ball fits inside it.
  have hball : ∀ x : M, ∃ r : ℝ, 0 < r ∧ Metric.closedBall ((c x) x) r ⊆ (c x).target := by
    intro x
    have hmem : (c x) x ∈ (c x).target := mem_chart_target _ x
    have hopen : IsOpen (c x).target := (c x).open_target
    rw [Metric.isOpen_iff] at hopen
    obtain ⟨r, hr, hsub⟩ := hopen _ hmem
    exact ⟨r / 2, by linarith, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩
  -- Global radius function recording `0 < r x` and `closedBall ((c x) x) (r x) ⊆ (c x).target`.
  choose r hr_pos hr_sub using hball
  -- The open cover: pushforward of the open ball under the chart inverse.
  set O : M → Set M := fun x => (c x).symm '' Metric.ball ((c x) x) (r x) with hO
  have hball_sub_target : ∀ x : M, Metric.ball ((c x) x) (r x) ⊆ (c x).target := fun x =>
    (Metric.ball_subset_closedBall).trans (hr_sub x)
  have hO_open : ∀ x : M, IsOpen (O x) := fun x =>
    (c x).isOpen_image_symm_of_subset_target Metric.isOpen_ball (hball_sub_target x)
  have hO_mem : ∀ x : M, x ∈ O x := by
    intro x
    refine ⟨(c x) x, ?_, (c x).left_inv (mem_chart_source _ x)⟩
    exact Metric.mem_ball_self (hr_pos x)
  -- `M` is compact, so the open cover `{O x}` admits a finite subcover.
  have hcover : (Set.univ : Set M) ⊆ ⋃ x, O x := fun x _ => Set.mem_iUnion.mpr ⟨x, hO_mem x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO_open hcover
  -- The compact chart pieces: pushforward of the closed ball under the chart inverse.
  set K : M → Set M := fun x => (c x).symm '' Metric.closedBall ((c x) x) (r x) with hK
  -- `O x ⊆ K x` because `ball ⊆ closedBall`.
  have hOK : ∀ x : M, O x ⊆ K x := fun x =>
    Set.image_mono Metric.ball_subset_closedBall
  -- `s` is nonempty: otherwise the finite union is empty, contradicting nonemptiness of `M`.
  have hs_ne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with hempty | hne
    · exfalso
      obtain ⟨x⟩ := ‹Nonempty M›
      have hx : x ∈ ⋃ i ∈ s, O i := hs (Set.mem_univ x)
      rw [hempty] at hx
      simp at hx
    · exact hne
  refine ⟨s, K, hs_ne, ?_, ?_, ?_⟩
  · -- Each `K x` is compact: continuous image of a compact closed ball.
    intro x _
    exact (ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
      ((c x).continuousOn_symm.mono (hr_sub x))
  · -- Each `K x` lies in the chart source: `symm` maps target into source.
    intro x _
    rw [hK]
    simp only [hc]
    rw [Set.image_subset_iff]
    exact fun y hy => (c x).symm_mapsTo (hr_sub x hy)
  · -- The union of the `K x` over `s` is everything: it contains `⋃ O`, which already covers `univ`.
    refine Set.eq_univ_of_univ_subset (hs.trans ?_)
    exact Set.iUnion₂_mono fun x _ => hOK x

end SKEFTHawking.SingularCompactChartCover
