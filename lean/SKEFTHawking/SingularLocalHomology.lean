import Mathlib
import SKEFTHawking.SingularPairLES
import SKEFTHawking.SingularEuclideanAcyclic
import SKEFTHawking.SingularPuncturedRetract

/-!
# Local homology `Hₖ(ℝⁿ, ℝⁿ ∖ 0)`

Assembling the long exact sequence of the pair `(ℝⁿ, ℝⁿ ∖ 0)` with the acyclicity of `ℝⁿ`: since
`Hₖ(ℝⁿ) = 0` for `k ≥ 1`, the connecting map `δ : Hₖ₊₁(ℝⁿ, ℝⁿ∖0) → Hₖ(ℝⁿ∖0)` is an isomorphism,
and `Hₖ(ℝⁿ∖0) ≅ Hₖ(Sⁿ⁻¹)` (the deformation retract). This reduces the local homology to the homology
of spheres — the input to the fundamental class.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularEuclideanAcyclic SKEFTHawking.SingularPuncturedRetract

namespace SKEFTHawking.SingularLocalHomology

/-- **Acyclicity is triviality of homology**: if every `(n+1)`-cycle is a boundary, then
`Hₙ₊₁(X; ℤ/2) = 0` (every class is zero). -/
theorem homology_trivial_of_acyclic {X : TopCat} {n : ℕ}
    (hac : ∀ z : SingularChain X (n + 1), chainBoundary X n z = 0 → z ∈ boundaries X (n + 1))
    (x : Homology X (n + 1)) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  exact Submodule.mem_comap.mpr (hac z z.2)

/-- `Hₖ₊₁(ℝⁿ; ℤ/2) = 0` (every class is zero). -/
theorem eucl_homology_trivial (m k : ℕ) (x : Homology (SingularEuclideanAcyclic.Eucl m) (k + 1)) :
    x = 0 :=
  homology_trivial_of_acyclic (SingularEuclideanAcyclic.cycle_mem_boundaries m k) x

/-- **The connecting map is an isomorphism when the ambient space is acyclic**: if
`Hₙ₊₁(X) = 0` and `Hₙ(X) = 0`, the LES forces `δ : Hₙ₊₁(X, S) → Hₙ(S)` to be bijective. -/
theorem connecting_bijective_of_acyclic {X : TopCat} (S : Set ↑X) (n : ℕ)
    (hX1 : ∀ x : Homology X (n + 1), x = 0) (hX0 : ∀ x : Homology X n, x = 0) :
    Function.Bijective (connecting S n) := by
  have hproj0 : homProj S (n + 1) = 0 := by
    ext x; rw [LinearMap.zero_apply, hX1 x, map_zero]
  have hincl0 : homIncl S n = 0 := by
    ext y; rw [LinearMap.zero_apply]; exact hX0 _
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, (exact_homProj_connecting S n).linearMap_ker_eq, hproj0,
      LinearMap.range_zero]
  · rw [← LinearMap.range_eq_top, ← (exact_connecting_homIncl S n).linearMap_ker_eq, hincl0,
      LinearMap.ker_zero]

/-- **The local-homology connecting isomorphism `Hⱼ₊₂(ℝⁿ, ℝⁿ∖0) ≅ Hⱼ₊₁(ℝⁿ∖0)`** (for `n ≥ 1`): from
`ℝⁿ` acyclic, the LES connecting map is bijective. Composed with the deformation retract
`ℝⁿ∖0 ≃ Sⁿ⁻¹` (`homology_map_normalize_bijective`) this gives `Hⱼ₊₂(ℝⁿ, ℝⁿ∖0) ≅ Hⱼ₊₁(Sⁿ⁻¹)` — the
geometric input to the fundamental class. (Kept separate from the retract to avoid forcing the
`Punc n = sub {x ≠ 0}` defeq through `toSSet`.) -/
theorem connecting_eucl_bijective (n j : ℕ) :
    Function.Bijective (connecting (X := Eucl n) {x | x ≠ 0} (j + 1)) :=
  connecting_bijective_of_acyclic (X := Eucl n) {x | x ≠ 0} (j + 1)
    (eucl_homology_trivial n (j + 1)) (eucl_homology_trivial n j)

end SKEFTHawking.SingularLocalHomology
