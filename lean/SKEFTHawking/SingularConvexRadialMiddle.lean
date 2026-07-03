import Mathlib
import SKEFTHawking.SingularConvexRadialBase
import SKEFTHawking.SingularSphereMiddle

/-!
# Phase 5q.G (G1 PD-induction, base-case B2) — the middle local homology of a convex compact

`Hᵢ(ℝᵐ⁺² | K) = 0` for `2 ≤ i < m+2` and `K` compact convex — the BELOW-top companion of
`vanishAbove_convexCompact`, by the identical four-step retract chase (acyclic connecting →
radial retract → translation → normalize) ending in the MIDDLE sphere vanishing
(`sphere_homology_middle`) instead of the high one. Together with `vanishAbove_convexCompact`
this pins the local homology of a convex compact to the single degree `m+2` (in the band
`i ≥ 2`; the `i ∈ {0,1}` edges are not needed by the PD base case, whose cohomGW window only
consumes `i ∈ {2,3}` at `m = 2`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularManifoldFundamentalClass SKEFTHawking.SingularConvexRadialBase
open SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularConvexRadialMiddle

/-- **The middle local homology of a convex compact vanishes**: `Hᵢ(ℝᵐ⁺² | K) = 0` for
`2 ≤ i < m + 2`, by the `vanishAbove_convexCompact` retract chase with the middle-sphere ending. -/
theorem vanishMiddle_convexCompact {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    {O : EuclideanSpace ℝ (Fin (m + 2))} (hOK : O ∈ K)
    (i : ℕ) (h2 : 2 ≤ i) (hlt : i < m + 2)
    (x : RelativeHomology (X := SingularEuclideanAcyclic.Eucl (m + 2)) Kᶜ i) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 + 1 := ⟨i - 2, by omega⟩
  set a₁ := euclRelHomologyEquiv m Kᶜ k x with ha₁
  set a₂ := Homology.map (SingularConvexRadialRetract.inclMapRadial hOK) (k + 1) a₁ with ha₂
  set a₃ := Homology.map (translateMap O) (k + 1) a₂ with ha₃
  have h4 : Homology.map (SingularPuncturedRetract.normalize (n := m + 2)) (k + 1) a₃ = 0 :=
    SKEFTHawking.SingularSphereMiddle.sphere_homology_middle (k + 1) (m + 1)
      (Nat.succ_pos k) (by omega) _
  have h3 : a₃ = 0 :=
    (SingularPuncturedRetract.homology_map_normalize_bijective (n := m + 2) k).injective
      (h4.trans (map_zero _).symm)
  have h2' : a₂ = 0 :=
    (homology_map_translateMap_bijective O (k + 1)).injective
      ((ha₃ ▸ h3).trans (map_zero _).symm)
  have h1 : a₁ = 0 :=
    (SingularConvexRadialRetract.homology_map_inclMapRadial_bijective hKconv hKcomp hOK k).injective
      ((ha₂ ▸ h2').trans (map_zero _).symm)
  exact (euclRelHomologyEquiv m Kᶜ k).injective ((ha₁ ▸ h1).trans (map_zero _).symm)

end SKEFTHawking.SingularConvexRadialMiddle
