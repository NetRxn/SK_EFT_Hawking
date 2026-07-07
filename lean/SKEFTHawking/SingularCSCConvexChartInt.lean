/-
# Phase 5q.H (E1 CSC-PD tower, base-case B3) — CSC vanishing on chart-convex opens (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularCSCConvexChart.cscOpen_eq_zero_of_chartConvex`:
`Hᵏ_c(W;ℤ) = 0` for a chart-convex open `W` in the middle band `2 ≤ k < m+2`. Every compact stage `K`
absorbs into a chart-convex compact stage `K'` (`exists_chartConvex_stage_above`, coeff-agnostic reuse),
where the stage cohomology `Hᵏ(M|K';ℤ) = RelativeCohomologyInt(K'ᶜ)(k)` vanishes by the integral relative
UCT (`relCohomology_eq_zero_of_relHomology_two_vanishInt`), which — unlike the mod-2 field bridge — needs
BOTH homology degrees `H_k(K'ᶜ) = 0` AND `H_{k-1}(K'ᶜ) = 0`, each obtained by the HOMOLOGY chart transport
(`openSetExcisionEquivInt`∘`chartPairEquiv_setInt`∘`openSetExcisionEquivInt`) to `H_·(C'ᶜ)` and killed by
`vanishMiddle_convexCompactInt` (degree ≥ 2) / `relHomology_one_convexCompactInt` (degree 1).

**The `Module.Projective ℤ (relBoundariesInt …)` instance (= infinite-rank Kaplansky, absent from Mathlib)
is THREADED as the hypothesis `hproj`** — a true ZFC theorem discharged separately (NOT a posit).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCSCConvexChart
import SKEFTHawking.SingularChartTransportInt
import SKEFTHawking.SingularCSCVanishAboveInt
import SKEFTHawking.SingularConvexRadialMiddleInt
import SKEFTHawking.SingularConvexComplementConnectedInt
import SKEFTHawking.SingularRelativeUCVanishInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularChartTransportInt
open SKEFTHawking.SingularCSCConvexChart (exists_chartConvex_stage_above)
open SKEFTHawking.SingularCSCVanishAboveInt
open SKEFTHawking.SingularConvexRadialMiddleInt
open SKEFTHawking.SingularConvexComplementConnectedInt
open SKEFTHawking.SingularRelativeUCVanishInt

namespace SKEFTHawking.SingularCSCConvexChartInt

/-- **B3 (integral): the CSC cohomology of a chart-convex open vanishes in the middle band** `2 ≤ k < m+2`.
The `Module.Projective ℤ (relBoundariesInt …)` instance is threaded as `hproj` (= infinite-rank Kaplansky,
a true ZFC theorem discharged separately). -/
theorem cscOpen_eq_zero_of_chartConvexInt {M : TopCat} [T2Space ↑M] {m : ℕ}
    (hproj : ∀ (S : Set ↑M) (j : ℕ), Module.Projective ℤ (relBoundariesInt S j))
    {U : Set ↑M} (hU : IsOpen U)
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))} (hV : IsOpen V)
    (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hCconv : Convex ℝ C) (hCopen : IsOpen C)
    (hCne : C.Nonempty) (hCV : C ⊆ V)
    {W : Set ↑M} (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : ↑M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C))
    {k : ℕ} (h2 : 2 ≤ k) (hlt : k < m + 2)
    (α : CompactlySupportedCohomologyOpenInt W k) : α = 0 := by
  obtain ⟨p₀, hp₀⟩ := hCne
  obtain ⟨M', rfl⟩ : ∃ M', k = M' + 2 := ⟨k - 2, by omega⟩
  refine cscOpen_eq_zero_of_cofinal_vanishInt (fun K => ?_) α
  obtain ⟨K', C', hKK', hC'conv, hC'comp, hC'C, hp₀C', hcompat'⟩ :=
    exists_chartConvex_stage_above e hCconv hCopen hp₀ hCV hWU hWe K
  have hK'closed : IsClosed (↑K'.1 : Set ↑M) := K'.1.isCompact'.isClosed
  have hK'U : (↑K'.1 : Set ↑M) ⊆ U := K'.2.trans hWU
  have hC'V : C' ⊆ (V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) := hC'C.trans hCV
  -- The chart transport of the stage homology to the convex-compact complement, at any degree.
  have htransport : ∀ (d : ℕ),
      (∀ γ : RelHomologyInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (C'ᶜ) (d + 1), γ = 0) →
      ∀ β : RelHomologyInt (X := M) ((↑K'.1 : Set ↑M)ᶜ) (d + 1), β = 0 := by
    intro d hvanC' β
    set TK := (openSetExcisionEquivInt hK'closed hU hK'U d).symm.trans
      ((chartPairEquiv_setInt e hcompat' (d + 1)).trans
        (openSetExcisionEquivInt hC'comp.isClosed hV hC'V d)) with hTKdef
    exact (LinearEquiv.map_eq_zero_iff TK).mp (hvanC' (TK β))
  refine ⟨K', hKK', fun x => ?_⟩
  haveI := hproj ((↑K'.1 : Set ↑M)ᶜ) M'
  refine relCohomology_eq_zero_of_relHomology_two_vanishInt ((↑K'.1 : Set ↑M)ᶜ) ?_ ?_ x
  · -- H_{M'+1}(K'ᶜ) = 0
    refine htransport M' ?_
    rcases M' with _ | M''
    · exact fun γ => relHomology_one_convexCompactInt hC'conv hC'comp ⟨p₀, hp₀C'⟩ γ
    · exact fun γ =>
        vanishMiddle_convexCompactInt hC'conv hC'comp hp₀C' (M'' + 1 + 1) (by omega) (by omega) γ
  · -- H_{M'+2}(K'ᶜ) = 0
    refine htransport (M' + 1) ?_
    exact fun γ => vanishMiddle_convexCompactInt hC'conv hC'comp hp₀C' (M' + 2) (by omega) (by omega) γ

end SKEFTHawking.SingularCSCConvexChartInt
