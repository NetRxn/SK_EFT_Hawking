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

/-- The converse: if `Hₙ₊₁(X) = 0` then every `(n+1)`-cycle is a boundary. -/
theorem boundaries_of_homology_trivial {X : TopCat} {n : ℕ}
    (h : ∀ x : Homology X (n + 1), x = 0) (z : SingularChain X (n + 1))
    (hz : chainBoundary X n z = 0) : z ∈ boundaries X (n + 1) :=
  Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp (h (Homology.mk X (n + 1) ⟨z, hz⟩)))

/-- **Triviality of homology transports across a homology isomorphism**: if `Hₙ(f)` is bijective
and `Hₙ(Y) = 0`, then `Hₙ(X) = 0`. Combined with `boundaries_of_homology_trivial` this transports
acyclicity across a homotopy equivalence. -/
theorem homology_trivial_of_bijective {X Y : TopCat} {n : ℕ} (f : C(↑X, ↑Y))
    (hf : Function.Bijective (Homology.map f n)) (hY : ∀ y : Homology Y n, y = 0)
    (x : Homology X n) : x = 0 :=
  hf.injective (by rw [map_zero]; exact hY _)

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

/-- **The projection `j_* : Hₙ₊₁(X) → Hₙ₊₁(X, S)` is an isomorphism when the subspace is acyclic**:
if `Hₙ₊₁(S) = 0` and `Hₙ(S) = 0`, the LES forces `j_*` to be bijective. (Companion of
`connecting_bijective_of_acyclic`; the case `Hₖ(Sⁿ, A) ≅ Hₖ(Sⁿ)` for `A` a contractible hemisphere.) -/
theorem homProj_bijective_of_acyclic {X : TopCat} (S : Set ↑X) (n : ℕ)
    (hS1 : ∀ x : Homology (sub S) (n + 1), x = 0) (hS0 : ∀ x : Homology (sub S) n, x = 0) :
    Function.Bijective (homProj S (n + 1)) := by
  have hincl0 : homIncl S (n + 1) = 0 := by
    ext y; rw [LinearMap.zero_apply, hS1 y, map_zero]
  have hconn0 : connecting S n = 0 := by
    ext y; rw [LinearMap.zero_apply]; exact hS0 _
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, (exact_homIncl_homProj S (n + 1)).linearMap_ker_eq, hincl0,
      LinearMap.range_zero]
  · rw [← LinearMap.range_eq_top, ← (exact_homProj_connecting S n).linearMap_ker_eq, hconn0,
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
