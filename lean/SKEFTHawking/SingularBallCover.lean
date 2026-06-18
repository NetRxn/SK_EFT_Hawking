import Mathlib

/-!
# Phase 5q.F (w₂-foundation, brick 72c-4h) — finite closed-ball cover of a compact set

A compact `K` inside an open `U ⊆ ℝⁿ` is covered by finitely many closed balls, each centered at a
point of `K` and contained in `U`. The cover that feeds the Hatcher 3.27 step-3 colimit: replacing the
abstract compact neighbourhood `C ⊇ K` by a finite union of convex compacts (closed balls), so the
`goodCompact` finite-union induction applies, and (for the determined-by-points half) each ball's
centre lies in `K` where the class already restricts to 0.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

namespace SKEFTHawking.SingularBallCover

theorem exists_finite_closedBall_cover {n : ℕ} {K U : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hKne : K.Nonempty) :
    ∃ (s : Finset (EuclideanSpace ℝ (Fin n))) (r : EuclideanSpace ℝ (Fin n) → ℝ),
      s.Nonempty ∧ (↑s ⊆ K) ∧ (∀ c ∈ s, 0 < r c) ∧
      (K ⊆ ⋃ c ∈ s, Metric.closedBall c (r c)) ∧
      (∀ c ∈ s, Metric.closedBall c (r c) ⊆ U) := by
  -- For each point of `K`, an open neighbourhood gives a closed ball inside `U`.
  have hball : ∀ x ∈ K, ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x ρ ⊆ U := by
    intro x hx
    have hxU : U ∈ nhds x := hU.mem_nhds (hKU hx)
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hxU
    refine ⟨ε / 2, by positivity, ?_⟩
    exact (Metric.closedBall_subset_ball (by linarith)).trans hεU
  -- A radius function: chosen `ρ` on `K`, junk value `1` off `K`.
  classical
  set r : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => if hx : x ∈ K then Classical.choose (hball x hx) else 1 with hr
  have hr_pos : ∀ x ∈ K, 0 < r x := by
    intro x hx
    simp only [hr, dif_pos hx]
    exact (Classical.choose_spec (hball x hx)).1
  have hr_sub : ∀ x ∈ K, Metric.closedBall x (r x) ⊆ U := by
    intro x hx
    simp only [hr, dif_pos hx]
    exact (Classical.choose_spec (hball x hx)).2
  -- The open balls centred on `K` cover `K`.
  have hcov : K ⊆ ⋃ x ∈ K, Metric.ball x (r x) := by
    intro x hx
    exact Set.mem_biUnion hx (Metric.mem_ball_self (hr_pos x hx))
  have hopen : ∀ x ∈ K, IsOpen (Metric.ball x (r x)) := fun x _ => Metric.isOpen_ball
  obtain ⟨b', hb'K, hb'fin, hb'cov⟩ := hK.elim_finite_subcover_image hopen hcov
  -- `b'` is nonempty: otherwise its union is empty, contradicting `K.Nonempty`.
  have hb'ne : b'.Nonempty := by
    rcases b'.eq_empty_or_nonempty with hb | hb
    · obtain ⟨x, hx⟩ := hKne
      have := hb'cov hx
      simp [hb] at this
    · exact hb
  refine ⟨hb'fin.toFinset, r, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.Finite.toFinset_nonempty hb'fin]
    exact hb'ne
  · rw [Set.Finite.coe_toFinset]
    exact hb'K
  · intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    exact hr_pos c (hb'K hc)
  · intro x hx
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (hb'cov hx)
    refine Set.mem_iUnion₂.mpr ⟨c, ?_, Metric.ball_subset_closedBall hxc⟩
    rw [Set.Finite.mem_toFinset]
    exact hc
  · intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    exact hr_sub c (hb'K hc)

end SKEFTHawking.SingularBallCover
