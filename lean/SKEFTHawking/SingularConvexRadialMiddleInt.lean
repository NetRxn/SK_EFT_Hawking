/-
# Phase 5q.H (E1 CSC-PD tower, base-case B5-cohomology-input) — middle vanishing of a convex compact (ℤ)

Integral (`ZMod 2 → ℤ`) mirror of `SingularConvexRadialMiddle.vanishMiddle_convexCompact`:
`H_i(ℝⁿ, ℝⁿ∖K;ℤ) = 0` for a convex compact `K ⊆ ℝⁿ` (`O ∈ K`) and `2 ≤ i < n = m+2`. Same radial/translate/
normalize retract chase as the integral `vanishAboveInt_convexCompact` (`SingularConvexRadialBaseInt`), but
the sphere landing uses `sphere_homology_middleInt` (`0 < j < n`) instead of `sphere_homology_high` (`j > n`).

This is the middle-band relative-HOMOLOGY vanishing input of the base-case B3 CSC-cohomology vanishing
(after the ℤ-UCT bridge lifts homology-vanishing to cohomology-vanishing).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConvexRadialBaseInt
import SKEFTHawking.SingularConvexRadialRetractInt
import SKEFTHawking.SingularSphereMiddleInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularConvexRadialBaseInt (euclRelHomologyEquivInt homology_mapInt_translateMap_bijective)
open SKEFTHawking.SingularConvexRadialRetractInt (homology_mapInt_inclMapRadial_bijective)
open SKEFTHawking.SingularConvexRadialBase (translateMap)

namespace SKEFTHawking.SingularConvexRadialMiddleInt

/-- **The middle relative homology of a convex-compact complement vanishes** (integral): for `K` convex
compact in `ℝⁿ = ℝ^{m+2}` with `O ∈ K` and `2 ≤ i < m+2`, `H_i(ℝⁿ, ℝⁿ∖K;ℤ) = 0`. -/
theorem vanishMiddle_convexCompactInt {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    {O : EuclideanSpace ℝ (Fin (m + 2))} (hOK : O ∈ K)
    (i : ℕ) (h2 : 2 ≤ i) (hlt : i < m + 2)
    (x : RelHomologyInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) Kᶜ i) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 + 1 := ⟨i - 2, by omega⟩
  set a₁ := euclRelHomologyEquivInt m Kᶜ k x with ha₁
  set a₂ := Homology.mapInt (SingularConvexRadialRetract.inclMapRadial hOK) (k + 1) a₁ with ha₂
  set a₃ := Homology.mapInt (translateMap O) (k + 1) a₂ with ha₃
  have h4 : Homology.mapInt (SingularPuncturedRetract.normalize (n := m + 2)) (k + 1) a₃ = 0 :=
    SingularSphereMiddleInt.sphere_homology_middleInt (k + 1) (m + 1) (Nat.succ_pos k) (by omega) _
  have h3 : a₃ = 0 :=
    (SingularPuncturedRetractInt.homology_mapInt_normalize_bijective (m + 2) k).injective
      (h4.trans (map_zero _).symm)
  have h2' : a₂ = 0 :=
    (homology_mapInt_translateMap_bijective O (k + 1)).injective
      ((ha₃ ▸ h3).trans (map_zero _).symm)
  have h1 : a₁ = 0 :=
    (homology_mapInt_inclMapRadial_bijective hKconv hKcomp hOK k).injective
      ((ha₂ ▸ h2').trans (map_zero _).symm)
  exact (euclRelHomologyEquivInt m Kᶜ k).injective ((ha₁ ▸ h1).trans (map_zero _).symm)

end SKEFTHawking.SingularConvexRadialMiddleInt
