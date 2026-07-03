import Mathlib
import SKEFTHawking.RP4PointSet
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularHomotopyInvariance

/-!
# Phase 5q.G (B-arc, M1-a) — the punctured 4-sphere is acyclic

The first rung of the `H_*(S⁴;ℤ/2)` computation (toward the Smith sequence of the antipodal
cover): `S⁴ ∖ {v} ≃ₜ ℝ⁴` by the stereographic chart (Mathlib's `stereographic'`, whose source
is exactly `{v}ᶜ` and target all of `ℝ⁴`), so its positive-degree homology vanishes by
transport onto the Euclidean acyclicity (`eucl_homology_zero`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open Metric
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.RP4PointSet SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularHomotopyInvariance

namespace SKEFTHawking.SphereHomology

/-- **The punctured 4-sphere is homeomorphic to `ℝ⁴`** — the stereographic chart, whose source
is `{v}ᶜ` and target `univ`. -/
noncomputable def punctSphereHomeo (v : S4) :
    ↥({v}ᶜ : Set S4) ≃ₜ EuclideanSpace ℝ (Fin 4) :=
  ((Homeomorph.setCongr (stereographic'_source v).symm).trans
      (stereographic' 4 v).toHomeomorphSourceTarget).trans
    ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _))

/-- **The punctured 4-sphere is acyclic in positive degrees** — transport the Euclidean
vanishing along the stereographic homeomorphism. -/
theorem punctSphere_homology_eq_zero (v : S4) (k : ℕ)
    (x : Homology (sub (X := TopCat.of S4) ({v}ᶜ : Set S4)) (k + 1)) : x = 0 := by
  set e := punctSphereHomeo v
  set eC : C(↥(sub (X := TopCat.of S4) ({v}ᶜ : Set S4)),
      ↥(SingularEuclideanAcyclic.Eucl 4)) := ⟨e, e.continuous⟩ with heC
  set eC' : C(↥(SingularEuclideanAcyclic.Eucl 4),
      ↥(sub (X := TopCat.of S4) ({v}ᶜ : Set S4))) := ⟨e.symm, e.symm.continuous⟩ with heC'
  have hinj : Function.Injective (Homology.map eC (k + 1)) := by
    intro a b hab
    have h1 := congrArg (Homology.map eC' (k + 1)) hab
    rw [← LinearMap.comp_apply, ← Homology.map_comp, ← LinearMap.comp_apply,
      ← Homology.map_comp] at h1
    rwa [show eC'.comp eC = ContinuousMap.id _ from
        ContinuousMap.ext (fun z => e.symm_apply_apply z),
      Homology.map_id, LinearMap.id_apply, LinearMap.id_apply] at h1
  refine hinj ?_
  rw [map_zero]
  exact SKEFTHawking.SingularManifoldFundamentalClass.eucl_homology_zero 4 k _

end SKEFTHawking.SphereHomology
