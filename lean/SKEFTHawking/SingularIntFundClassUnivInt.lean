import Mathlib
import SKEFTHawking.SingularIntFundClassUnionInt
import SKEFTHawking.SingularGoodCompactManifoldInt
import SKEFTHawking.SingularCompactChartCover

/-!
# The oriented fundamental class on all of `M` (brick 18g)

The `univ` step of the ℤ chart-cover fundamental-class induction: a compact charted 4-manifold with a
chart-compatible orientation section `orient` has the oriented fundamental class on all of `M`
(`hasOrientedFundClassInt orient univ`). Cover `M` by finitely many chart balls
(`exists_finite_chartBall_cover`, coefficient-free — reused as-is); each ball carries the oriented
fundamental class w.r.t. `orient` (the `hballs` hypothesis — the ORIENTATION compatibility, provable
per-ball by the base case `hasOrientedFundClassInt_chartBall` when `orient` matches the chart's
local-generator direction there); every nonempty sub-intersection is a compact subset of a chart
source, hence `goodCompactInt` (`goodCompactInt_compact_in_chart_source`); so
`hasOrientedFundClassInt_biUnion` glues them into `hasOrientedFundClassInt orient univ`.

This is the direct ℤ/oriented mirror of `SingularFundamentalClass.hasFundClass_univ`. The `hballs`
hypothesis packages orientability: a global `orient` that is realisable on every chart ball. For an
oriented 4-manifold (the σ÷16 setting) such an `orient` is the orientation. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularIntFundamentalClassExist
open SKEFTHawking.SingularIntFundClassUnionInt

namespace SKEFTHawking.SingularIntFundClassUnivInt

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **The oriented fundamental class on all of `M`** (Hatcher 3.27(b), oriented `univ` step): for a
global orientation section `orient` realisable on every chart ball (`hballs`), the oriented
fundamental class exists on `univ`. Cover by finite chart balls + `hasOrientedFundClassInt_biUnion`. -/
theorem hasOrientedFundClassInt_univ (orient : M → ℤ)
    (hballs : ∀ (x : M) (ρ : ℝ), 0 ≤ ρ →
        Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ
          ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) x).target →
        hasOrientedFundClassInt orient ((chartAt (EuclideanSpace ℝ (Fin 4)) x).symm ''
          Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ)) :
    hasOrientedFundClassInt orient (Set.univ : Set M) := by
  classical
  obtain ⟨s, r, hs, hr0, hrsub, hcov⟩ :=
    SingularCompactChartCover.exists_finite_chartBall_cover (m := 2) (M := M)
  set K : M → Set M := fun x => (chartAt (EuclideanSpace ℝ (Fin 4)) x).symm ''
    Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) (r x) with hK
  have hKcompact : ∀ x ∈ s, IsCompact (K x) := fun x hx =>
    (ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin 4)) x).continuousOn_symm.mono (hrsub x hx))
  have hKsource : ∀ x ∈ s, K x ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) x).source := by
    intro x hx
    rw [hK, Set.image_subset_iff]
    exact fun y hy => (chartAt (EuclideanSpace ℝ (Fin 4)) x).symm_mapsTo (hrsub x hx hy)
  rw [← hcov]
  refine hasOrientedFundClassInt_biUnion orient hs K (fun t ht htne => ?_)
    (fun x hx => hballs x (r x) (hr0 x hx) (hrsub x hx))
  obtain ⟨j, hj⟩ := htne
  have hsubKj : (⋂ i ∈ t, K i) ⊆ K j := Set.biInter_subset_of_mem hj
  have hclosed : IsClosed (⋂ i ∈ t, K i) :=
    isClosed_biInter (fun i hi => (hKcompact i (ht hi)).isClosed)
  have hcompInter : IsCompact (⋂ i ∈ t, K i) :=
    (hKcompact j (ht hj)).of_isClosed_subset hclosed hsubKj
  exact ⟨hclosed, SingularGoodCompactManifoldInt.goodCompactInt_compact_in_chart_source
    hcompInter (hsubKj.trans (hKsource j (ht hj)))⟩

end SKEFTHawking.SingularIntFundClassUnivInt
