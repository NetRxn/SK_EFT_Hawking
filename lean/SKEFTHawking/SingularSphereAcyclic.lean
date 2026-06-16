import Mathlib
import SKEFTHawking.SingularEuclideanAcyclic
import SKEFTHawking.SingularLocalHomology

/-!
# The punctured sphere `Sⁿ ∖ {v}` is acyclic

Via Mathlib's stereographic projection `Sⁿ ∖ {v} ≃ₜ ℝⁿ`, the punctured sphere is homeomorphic to
Euclidean space, hence acyclic (`Hₖ₊₁ = 0`). The two punctured spheres (minus north / minus south)
are the contractible pieces of the Mayer–Vietoris computation of `Hₖ(Sⁿ)`.
-/

open CategoryTheory Opposite Metric
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularEuclideanAcyclic SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularHomotopyInvariance SKEFTHawking.SingularLocalHomology
open SKEFTHawking.SingularPairLES

namespace SKEFTHawking.SingularSphereAcyclic

/-- `Sⁿ ⊆ ℝⁿ⁺¹` as a topological space object. -/
abbrev Sph (n : ℕ) : TopCat := TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

instance instFactFinrank (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The punctured sphere `Sⁿ ∖ {v}` is homeomorphic to `ℝⁿ` (stereographic projection). -/
noncomputable def puncturedHomeo (n : ℕ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ↥({v}ᶜ : Set ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ≃ₜ
      EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source v).symm).trans
    (((stereographic' n v).toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _)))

variable {n : ℕ} {v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}

/-- The punctured sphere `Sⁿ ∖ {v}` as a space object. -/
abbrev Apunc (n : ℕ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : TopCat :=
  sub ({v}ᶜ : Set ↑(Sph n))

/-- The stereographic homeomorphism as a continuous map `Sⁿ ∖ {v} → ℝⁿ`. -/
noncomputable def stereoMap (n : ℕ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    C(↑(Apunc n v), ↑(Eucl n)) :=
  ⟨puncturedHomeo n v, (puncturedHomeo n v).continuous⟩

/-- Its inverse `ℝⁿ → Sⁿ ∖ {v}`. -/
noncomputable def stereoMapInv (n : ℕ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    C(↑(Eucl n), ↑(Apunc n v)) :=
  ⟨(puncturedHomeo n v).symm, (puncturedHomeo n v).symm.continuous⟩

theorem stereoMapInv_comp_stereoMap :
    (stereoMapInv n v).comp (stereoMap n v) = ContinuousMap.id _ :=
  ContinuousMap.ext fun x => (puncturedHomeo n v).symm_apply_apply x

theorem stereoMap_comp_stereoMapInv :
    (stereoMap n v).comp (stereoMapInv n v) = ContinuousMap.id _ :=
  ContinuousMap.ext fun x => (puncturedHomeo n v).apply_symm_apply x

/-- The stereographic map induces an isomorphism `Hₖ₊₁(Sⁿ ∖ {v}) ≅ Hₖ₊₁(ℝⁿ)`. -/
theorem stereoMap_bijective (k : ℕ) :
    Function.Bijective (Homology.map (stereoMap n v) (k + 1)) :=
  Homology.map_bijective_of_comp_id (stereoMap n v) (stereoMapInv n v)
    stereoMapInv_comp_stereoMap stereoMap_comp_stereoMapInv k

/-- **The punctured sphere `Sⁿ ∖ {v}` is acyclic**: every cycle in degree `k + 1` is a boundary
(transported from `ℝⁿ` acyclic across the stereographic homeomorphism). -/
theorem punctured_sphere_acyclic (k : ℕ) (z : SingularChain (Apunc n v) (k + 1))
    (hz : chainBoundary (Apunc n v) k z = 0) : z ∈ boundaries (Apunc n v) (k + 1) :=
  boundaries_of_homology_trivial
    (homology_trivial_of_bijective (stereoMap n v) (stereoMap_bijective k)
      (eucl_homology_trivial n k)) z hz

/-- The homology of the punctured sphere is trivial in positive degrees. -/
theorem punctured_sphere_homology_trivial (k : ℕ) (x : Homology (Apunc n v) (k + 1)) : x = 0 :=
  homology_trivial_of_acyclic (fun z hz => punctured_sphere_acyclic k z hz) x

/-- **`Hₖ₊₂(Sⁿ) ≅ Hₖ₊₂(Sⁿ, Sⁿ ∖ {v})`**: the projection is an isomorphism because the punctured
sphere `Sⁿ ∖ {v}` is acyclic. This is the first step of the sphere suspension `Hₖ(Sⁿ) ≅ Hₖ₋₁(Sⁿ⁻¹)`
(the relative group `Hₖ₊₂(Sⁿ, Sⁿ∖{v})` is the half that excision moves to the other pole). -/
theorem homProj_sphere_bijective (k : ℕ) :
    Function.Bijective (homProj ({v}ᶜ : Set ↑(Sph n)) (k + 2)) :=
  homProj_bijective_of_acyclic ({v}ᶜ : Set ↑(Sph n)) (k + 1)
    (punctured_sphere_homology_trivial (k + 1)) (punctured_sphere_homology_trivial k)

end SKEFTHawking.SingularSphereAcyclic
