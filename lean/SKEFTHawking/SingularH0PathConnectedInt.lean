/-
# Phase 5q.H (E1 CSC-PD tower) — integral `H₀` of a path-connected space (`ε̄` injective)

Integral (`ZMod 2 → ℤ`) mirror of the injectivity half of `SingularH0PathConnected`: for a path-connected
`X`, the augmentation `ε̄ : H₀(X;ℤ) → ℤ` is injective (reduced `H̃₀(X;ℤ) = 0`). A `0`-chain with vanishing
augmentation is a boundary (`pathWitnessInt`: a chosen path fills each `0`-simplex against the basepoint).
The path-simplex machinery (`pathSimplex`, `face_*_pathSimplex`, `simplexPoint`, `eq_constSimplex`) is
COEFFICIENT-AGNOSTIC and reused from the mod-2 module; only the `ℤ`-linear witness + its boundary + the
injectivity are re-proved.

**The one ℤ-vs-mod-2 sign:** over ℤ the boundary is `∂(W z) = z − ε(z)·c_b` (SIGNED — the mod-2 `+` hid a
`−`), but the sign vanishes when `ε(z) = 0`, so the injectivity argument is unaffected.

This is the doubly-punctured-sphere input of `sphere_homology_oneInt` (→ `sphere_homology_middleInt` →
`vanishMiddle_convexCompactInt` → the base-case B3 CSC-vanishing).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularH0PathConnected
import SKEFTHawking.SingularLineMinusPointInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt (face)
open SKEFTHawking.SingularLineMinusPointInt (augmentationInt augmentationInt_single augHInt augHInt_mk)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)
open SKEFTHawking.SingularH0PathConnected
  (pathSimplex face_zero_pathSimplex face_one_pathSimplex simplexPoint eq_constSimplex)

namespace SKEFTHawking.SingularH0PathConnectedInt

variable {X : TopCat}

/-- **The boundary of a path `1`-simplex** (ℤ, signed): `∂[pathSimplex p] = [x] − [b]` for `p : b ⤳ x`. -/
theorem chainBoundary_pathSimplexInt {b x : ↑X} (p : Path b x) :
    chainBoundary X 0 (Finsupp.single (pathSimplex p) (1 : ℤ))
      = Finsupp.single (constSimplex x 0) 1 - Finsupp.single (constSimplex b 0) 1 := by
  have hf0 : face (0 : Fin 2) (pathSimplex p) = constSimplex x 0 := face_zero_pathSimplex p
  have hf1 : face (1 : Fin 2) (pathSimplex p) = constSimplex b 0 := face_one_pathSimplex p
  rw [chainBoundary_single, boundaryBasis, Fin.sum_univ_two, hf0, hf1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  abel

variable [PathConnectedSpace ↑X]

/-- The **integral path-filling witness** of a `0`-chain relative to a basepoint `b`. -/
noncomputable def pathWitnessInt (b : ↑X) : SingularChainInt X 0 →ₗ[ℤ] SingularChainInt X 1 :=
  Finsupp.linearCombination ℤ
    (fun σ => Finsupp.single (pathSimplex (PathConnectedSpace.somePath b (simplexPoint σ))) 1)

theorem pathWitnessInt_single (b : ↑X)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    pathWitnessInt b (Finsupp.single σ 1)
      = Finsupp.single (pathSimplex (PathConnectedSpace.somePath b (simplexPoint σ))) 1 := by
  rw [pathWitnessInt, Finsupp.linearCombination_single, one_smul]

theorem chainBoundary_pathWitnessInt_single (b : ↑X)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    chainBoundary X 0 (pathWitnessInt b (Finsupp.single σ 1))
      = Finsupp.single σ 1 - Finsupp.single (constSimplex b 0) 1 := by
  rw [pathWitnessInt_single, chainBoundary_pathSimplexInt, ← eq_constSimplex]

/-- **The boundary of the witness fills `z` against `ε(z)·c_b`** (ℤ, signed): `∂(W z) = z − ε(z)·c_b`. -/
theorem chainBoundary_pathWitnessInt (b : ↑X) (z : SingularChainInt X 0) :
    chainBoundary X 0 (pathWitnessInt b z)
      = z - augmentationInt X z • Finsupp.single (constSimplex b 0) 1 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, h₁, h₂, map_add, add_smul]
      abel
  | single σ a =>
      rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : ℤ) by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      simp only [map_smul, chainBoundary_pathWitnessInt_single, augmentationInt_single, smul_sub,
        smul_eq_mul, mul_one]

/-- **A `0`-chain with vanishing augmentation is a boundary** (integral). -/
theorem mem_boundaries_of_augmentationInt_eq_zero (b : ↑X) (z : SingularChainInt X 0)
    (hz : augmentationInt X z = 0) : z ∈ boundaries X 0 := by
  refine ⟨pathWitnessInt b z, ?_⟩
  rw [chainBoundary_pathWitnessInt, hz, zero_smul, sub_zero]

/-- **The augmentation `ε̄ : H₀(X;ℤ) → ℤ` is injective** for path-connected `X` (reduced `H̃₀(X;ℤ) = 0`). -/
theorem augHInt_injective_pathConnected : Function.Injective (augHInt X) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.mem_ker] at hy
  have hz : augmentationInt X (z : SingularChainInt X 0) = 0 := hy
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.mem_comap.mpr (mem_boundaries_of_augmentationInt_eq_zero
      (Classical.arbitrary ↑X) (z : SingularChainInt X 0) hz))

end SKEFTHawking.SingularH0PathConnectedInt
