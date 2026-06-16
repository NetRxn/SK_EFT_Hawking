import Mathlib
import SKEFTHawking.SingularHomologyMod2

/-!
# The augmentation and `H₀`

The augmentation `ε : C₀(X) → ℤ/2`, `∑ aᵢσᵢ ↦ ∑ aᵢ`, vanishes on boundaries (each `∂σ` of a
1-simplex has two faces, summing to `0` over ℤ/2). So `ε` descends to `H₀(X) → ℤ/2`; for a
path-connected space it is an isomorphism (reduced `H̃₀ = 0`). This is the base-case input for the
sphere/local-homology induction `Hₙ(ℝⁿ, ℝⁿ∖0) ≅ ℤ/2`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2

namespace SKEFTHawking.SingularH0

/-- The **augmentation** `ε : C₀(X) → ℤ/2`, the sum of the coefficients. -/
noncomputable def augmentation (X : TopCat) : SingularChain X 0 →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) (fun _ => 1)

@[simp] theorem augmentation_single (X : TopCat)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) (a : ZMod 2) :
    augmentation X (Finsupp.single σ a) = a := by
  rw [augmentation, Finsupp.linearCombination_single, smul_eq_mul, mul_one]

/-- **The augmentation vanishes on boundaries**: `ε(∂c) = 0` (a 1-simplex has two `0`-faces, which
cancel over ℤ/2). Hence `boundaries X 0 ≤ ker ε`. -/
theorem augmentation_chainBoundary (X : TopCat) (c : SingularChain X 1) :
    augmentation X (chainBoundary X 0 c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂, add_zero]
  | single σ a =>
      rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod 2) by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, map_smul, chainBoundary_single,
        boundaryBasis, map_sum]
      simp only [augmentation_single]
      rw [show (∑ _i : Fin 2, (1 : ZMod 2)) = 0 from by decide, smul_zero]

/-- The augmentation is surjective (it hits `1` on any point's `0`-simplex), provided `X` is
nonempty. -/
theorem augmentation_surjective (X : TopCat) (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    Function.Surjective (augmentation X) := by
  intro a
  exact ⟨Finsupp.single σ a, augmentation_single X σ a⟩

end SKEFTHawking.SingularH0
