/-
# Phase 5q.H (E1 CSC-PD tower) — `H₀(ℝⁿ|K convex) = 0` (integral, the i=0 companion)

`H₀(ℝᵐ⁺², ℝᵐ⁺²∖K;ℤ) = 0` for a nonempty convex compact `K`. Unlike the mod-2 field route (which needs
only `H₁ = 0` at degree 1 via the perfect pairing), the integral `k = 1` CSC-vanishing needs BOTH `H₁ = 0`
AND `H₀ = 0` (the `Ext` term of the bottom UCT). The H₀-end of the pair-LES: `homIncl : H₀(sub Kᶜ) → H₀(ℝⁿ)`
is SURJECTIVE — `ε̄_{ℝⁿ}` is injective (`eucl_augHInt_injective`, ℝⁿ reduced-acyclic) and `ε̄_{sub Kᶜ}` is
surjective (`Kᶜ` nonempty — `isPathConnected_compl_convexCompact`), so `ε̄_{ℝⁿ}∘homIncl = ε̄_{sub Kᶜ}`
surjective + `ε̄_{ℝⁿ}` injective ⟹ `homIncl` onto. Then `ker(homProjInt) = range(homIncl) = ⊤` ⟹
`homProjInt = 0`, and `homProjInt` is onto `H₀(ℝⁿ,ℝⁿ∖K)`, so that relative group is `0`.

The `H₀(K'ᶜ) = 0` input of the `k = 1` CSC-vanishing (`cscOpen_one_eq_zero_of_chartConvexInt`), fed to the
bottom UCT `relCohomology_one_eq_zero_of_relHomology_bottom_vanishInt`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConvexComplementConnectedInt
import SKEFTHawking.SingularSphereHomologyInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularLineMinusPointInt
  (augHInt eucl_augHInt_injective augHInt_homIncl augHInt_surjective)
open SKEFTHawking.SingularSphereHomologyInt (homProjInt_homIncl)
open SKEFTHawking.SingularConvexComplementConnected (isPathConnected_compl_convexCompact)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularConvexComplementH0Int

/-- **`H₀(ℝᵐ⁺² | K;ℤ) = 0` for a nonempty convex compact `K`** (integral). -/
theorem relHomology_zero_convexCompactInt {m : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hKconv : Convex ℝ K) (hKcomp : IsCompact K) (hKne : K.Nonempty)
    (x : RelHomologyInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) 0) : x = 0 := by
  obtain ⟨pt, hpt⟩ := (isPathConnected_compl_convexCompact hKconv hKcomp hKne).nonempty
  -- `ε̄_{sub Kᶜ}` surjective (Kᶜ nonempty).
  have hsurj_sub : Function.Surjective
      (augHInt (sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ))) :=
    augHInt_surjective (sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ))
      (SKEFTHawking.SingularHomotopyInvariance.constSimplex
        (⟨pt, hpt⟩ : (sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) : TopCat)) 0)
  -- `ε̄_{ℝⁿ}` injective.
  have hXinj := eucl_augHInt_injective (m + 2)
  -- `homIncl` surjective.
  have hincl_surj : Function.Surjective
      (homIncl (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) 0) := by
    intro z
    obtain ⟨y, hy⟩ := hsurj_sub (augHInt (SingularEuclideanAcyclic.Eucl (m + 2)) z)
    exact ⟨y, hXinj (by rw [augHInt_homIncl, hy])⟩
  -- `homProjInt S 0` surjective (lift a relative 0-cycle to an absolute 0-cycle; `∂₀ = 0`).
  have hproj_surj : Function.Surjective
      (homProjInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) (Kᶜ) 0) := by
    intro w
    obtain ⟨⟨cbar, hcbar⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ cbar
    exact ⟨Homology.mk (SingularEuclideanAcyclic.Eucl (m + 2)) 0 ⟨c, Submodule.mem_top⟩, rfl⟩
  -- Combine: every `w` is `homProjInt (homIncl y) = 0`.
  obtain ⟨z, rfl⟩ := hproj_surj x
  obtain ⟨y, rfl⟩ := hincl_surj z
  rw [homProjInt_homIncl]

end SKEFTHawking.SingularConvexComplementH0Int
