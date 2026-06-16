import Mathlib
import SKEFTHawking.SingularSphereAcyclic
import SKEFTHawking.SingularReducedH0

/-!
# The bottom-degree sphere suspension `H₁(Sⁿ) ≅ H̃₀(Sⁿ ∖ {v, -v})`

The `k = -1` end of `sphere_suspension_bijective`. Where the degree-`≥ 1` suspension uses the
acyclicity (`Hₖ = 0`) of the contractible hemispheres `Sⁿ ∖ {±v}`, the bottom uses their
**reduced**-acyclicity (`ε̄` injective, from the stereographic homeomorphism to the contractible `ℝⁿ`).
The connecting map at the bottom is no longer surjective onto `H₀(Sⁿ∖{v,-v})` — its range is exactly
reduced `H̃₀ = ker ε̄`. Composed with excision and the bottom projection this gives
`H₁(Sⁿ) ≅ H̃₀(Sⁿ∖{v,-v})`, whose `n = 1` instance is the base `H₁(S¹) ≅ H̃₀(S⁰) ≅ ℤ/2`.
-/

open CategoryTheory Opposite Metric
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularEuclideanAcyclic SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularHomotopyInvariance SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularH0
open SKEFTHawking.SingularReducedH0 SKEFTHawking.SingularSphereAcyclic

namespace SKEFTHawking.SingularSphereBottom

variable {n : ℕ} {v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}

/-- The stereographic map induces an isomorphism `Hₘ(Sⁿ ∖ {v}) ≅ Hₘ(ℝⁿ)` in **every** degree `m`
(including `0`) — a genuine homeomorphism, so functoriality alone suffices. -/
theorem stereoMap_bijective_all (m : ℕ) :
    Function.Bijective (Homology.map (stereoMap n v) m) :=
  Homology.map_bijective_of_comp_id_all (stereoMap n v) (stereoMapInv n v)
    stereoMapInv_comp_stereoMap stereoMap_comp_stereoMapInv m

/-- **The punctured sphere `Sⁿ ∖ {v}` is reduced-acyclic**: `ε̄ : H₀(Sⁿ∖{v}) → ℤ/2` is injective,
transported from `ℝⁿ` reduced-acyclic across the stereographic homeomorphism. -/
theorem punctured_sphere_augH_injective : Function.Injective (augH (Apunc n v)) :=
  augH_injective_of_map (stereoMap n v) (stereoMap_bijective_all 0).injective
    (eucl_augH_injective n)

/-- **The bottom-degree sphere suspension map** `H₁(Sⁿ) → H₀(Sⁿ∖{v,-v})`: the composite
`δ ∘ excision⁻¹ ∘ j_*` at degree `1` (the `k = -1` analogue of `sphere_suspension_bijective`). -/
noncomputable def bottomSuspMap (n : ℕ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Homology (Sph n) 1 →ₗ[ZMod 2]
      Homology (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))) 0 :=
  (connecting (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) 0).comp
    (((excisionEquiv ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) 0
          (polar_cover (ne_antipode v))).symm.toLinearMap).comp
      (homProj ({v}ᶜ : Set ↑(Sph n)) 1))

/-- The bottom projection `j_* : H₁(Sⁿ) → H₁(Sⁿ, Sⁿ∖{v})` is bijective: `Sⁿ∖{v}` is reduced-acyclic. -/
theorem homProj_bottom_bijective :
    Function.Bijective (homProj ({v}ᶜ : Set ↑(Sph n)) 1) :=
  homProj_one_bijective_of_reduced_acyclic ({v}ᶜ : Set ↑(Sph n))
    (punctured_sphere_homology_trivial 0) punctured_sphere_augH_injective

/-- **The bottom suspension is injective** (composite of the injective bottom connecting map, the
excision iso, and the bijective bottom projection). -/
theorem bottomSuspMap_injective : Function.Injective (bottomSuspMap n v) := by
  rw [bottomSuspMap, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (connecting_zero_injective_of_acyclic (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))
    (punctured_sphere_homology_trivial (v := antipode v) 0)).comp
    (((excisionEquiv ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) 0
        (polar_cover (ne_antipode v))).symm.injective).comp homProj_bottom_bijective.injective)

/-- **The bottom suspension has range exactly reduced `H̃₀(Sⁿ∖{v,-v}) = ker ε̄`**: the connecting map's
range is `ker ε̄` (the ambient `Sⁿ∖{-v}` is reduced-acyclic), and the preceding excision and bottom
projection are surjective. Hence `H₁(Sⁿ) ≅ H̃₀(Sⁿ∖{v,-v})`. -/
theorem bottomSuspMap_range :
    LinearMap.range (bottomSuspMap n v)
      = LinearMap.ker (augH (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)))) := by
  have hsurj : Function.Surjective ⇑(((excisionEquiv ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) 0
      (polar_cover (ne_antipode v))).symm.toLinearMap).comp (homProj ({v}ᶜ : Set ↑(Sph n)) 1)) := by
    rw [LinearMap.coe_comp]
    exact (excisionEquiv ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) 0
      (polar_cover (ne_antipode v))).symm.surjective.comp homProj_bottom_bijective.surjective
  rw [bottomSuspMap, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  exact connecting_zero_range_of_augH_injective (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))
    (punctured_sphere_augH_injective (v := antipode v))

end SKEFTHawking.SingularSphereBottom
