import Mathlib
import SKEFTHawking.SingularH0
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularPairLES

/-!
# Reduced `H̃₀` — the bottom-degree pair-LES isomorphisms

The degree-`0` boundary of the local-homology computation. The connecting iso
`connecting_bijective_of_acyclic` and `homProj_bijective_of_acyclic` require the relevant space to be
acyclic in degrees `n` and `n+1`; at the bottom (`n = 0`) `H₀ = 0` is **false** (a nonempty space has
`H₀ ≠ 0`). The fix is the **reduced** statement: replace "`H₀ = 0`" by "the augmentation
`ε̄ : H₀ → ℤ/2` is injective" (reduced `H̃₀ = 0`). The augmentation is natural, so the bottom of the
pair LES `H₁(X, S) → H₀(S) → H₀(X)` becomes, on kernels, `H₁(X, S) ≅ ker(ε̄_S) = H̃₀(S)` when `X` is
reduced-acyclic. This is what makes the bottom suspension `H₁(Sⁿ) ≅ H̃₀(Sⁿ ∖ {v, -v})` work, hence the
base case `H₁(S¹) ≅ H̃₀(S⁰) ≅ ℤ/2` of the sphere/local-homology induction.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularH0
open SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularReducedH0

/-- **The augmentation is preserved by pushforward**: `ε_Y(f_# c) = ε_X(c)` — each simplex pushes to
exactly one simplex, so the coefficient sum is unchanged. -/
theorem augmentation_mapChain {X Y : TopCat} (f : C(↑X, ↑Y)) (c : SingularChain X 0) :
    augmentation Y (mapChain f 0 c) = augmentation X c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single σ a => rw [mapChain_single, augmentation_single, augmentation_single]

/-- **The augmentation `ε̄ : H₀ → ℤ/2` is natural**: `ε̄_Y ∘ H₀(f) = ε̄_X`. The reduced homology
`ker ε̄` is therefore a functor, and `ker(H₀(f)) ⊇ ker(ε̄_X)` whenever `ε̄_Y` is injective. -/
theorem augH_naturality {X Y : TopCat} (f : C(↑X, ↑Y)) (x : Homology X 0) :
    augH Y (Homology.map f 0 x) = augH X x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show augH Y (Homology.map f 0 (Homology.mk X 0 z)) = augH X (Homology.mk X 0 z)
  rw [Homology.map_mk, augH_mk, augH_mk, cyclesMap_coe]
  exact augmentation_mapChain f (z : SingularChain X 0)

end SKEFTHawking.SingularReducedH0
