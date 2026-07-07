/-
# Phase 5q.H (E1 CSC-PD tower) — `H₁(ℝⁿ|K convex) = 0` (integral, the i=1 companion of vanishMiddle)

Integral (`ZMod 2 → ℤ`) mirror of `SingularConvexComplementConnected.relHomology_one_convexCompact`:
`H₁(ℝᵐ⁺², ℝᵐ⁺²∖K;ℤ) = 0` for a nonempty convex compact `K`. The bottom pair-LES: the connecting
`δ : H₁(ℝⁿ, ℝⁿ∖K) → H₀(ℝⁿ∖K)` is injective (`H₁(ℝⁿ;ℤ) = 0`, `eucl_homology_trivialInt`), with range
`ker ε̄` (`ε̄_{ℝⁿ}` injective); and `ε̄_{ℝⁿ∖K}` is injective (the complement is path-connected — the
coeff-agnostic `isPathConnected_compl_convexCompact` + `augHInt_injective_pathConnected`). So `δ x = 0`,
hence `x = 0`.

The `H_{k-1}=0` input (at `k = 2`) of the base-case B3 CSC-vanishing (its convex-compact `C'` is nonempty).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConvexComplementConnected
import SKEFTHawking.SingularH0PathConnectedInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularLineMinusPointInt (augHInt eucl_augHInt_injective
  connectingInt_zero_injective_of_acyclic connectingInt_zero_range_of_augHInt_injective)
open SKEFTHawking.SingularLocalHomologyInt (eucl_homology_trivialInt)
open SKEFTHawking.SingularH0PathConnectedInt (augHInt_injective_pathConnected)
open SKEFTHawking.SingularConvexComplementConnected (isPathConnected_compl_convexCompact)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularConvexComplementConnectedInt

/-- **`H₁(ℝᵐ⁺² | K;ℤ) = 0` for a nonempty convex compact `K`** (integral). -/
theorem relHomology_one_convexCompactInt {m : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K) (hKne : K.Nonempty)
    (x : RelHomologyInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) (0 + 1)) : x = 0 := by
  haveI hpcs : PathConnectedSpace ↥(sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ)) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_convexCompact hKconv hKcomp hKne)
  have hδinj : Function.Injective
      (connectingInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) 0) :=
    connectingInt_zero_injective_of_acyclic (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ)
      (fun w => eucl_homology_trivialInt (m + 2) 0 w)
  have hrange := connectingInt_zero_range_of_augHInt_injective
    (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) (eucl_augHInt_injective (m + 2))
  have haug : Function.Injective
      (augHInt (sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ))) :=
    augHInt_injective_pathConnected
  have h0 : connectingInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) 0 x = 0 := by
    have hker : connectingInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) 0 x
        ∈ LinearMap.ker (augHInt (sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ))) := by
      rw [← hrange]
      exact LinearMap.mem_range_self _ x
    exact haug (by rw [LinearMap.mem_ker.mp hker, map_zero])
  exact hδinj (by rw [h0, map_zero])

end SKEFTHawking.SingularConvexComplementConnectedInt
