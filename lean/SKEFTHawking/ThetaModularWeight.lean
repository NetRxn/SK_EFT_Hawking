/-
Phase 5q.B, [Θ4]: the modular-weight finish — an even unimodular lattice has rank `8 ∣ d`.

The theta S-transformation (`ThetaSTransform.latticeTheta_S`) plus the T-invariance
(`LatticeTheta.latticeTheta_T_int`) make `Θ_G` a nonzero level-1 modular object of weight `d/2`; the automorphy
multiplier `(τ/i)^{d/2}` is consistent under `SL₂(ℤ)` (the relation `S² = (ST)³`) only when `8 ∣ d`.

This module builds the bricks: the cast/inverse commutation `(A.map ℤ→ℝ)⁻¹ = A⁻¹.map ℤ→ℝ`, the theta
self-duality `Θ_{M⁻¹} = Θ_M` for an even unimodular `M` (via `latticeTheta_congr` with `P = A⁻¹`), and the
resulting self-transform `Θ_M(-1/τ) = (τ/i)^{d/2} Θ_M(τ)`.

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.ThetaSTransform
import SKEFTHawking.ThetaModularity

namespace SKEFTHawking

open Matrix Complex
open scoped Real

/-- The integer-cast of a matrix commutes with the (nonsingular) inverse, for a matrix with unit determinant:
`(A.map ℤ→ℝ)⁻¹ = A⁻¹.map ℤ→ℝ`. (Both inverses are left-inverses of `A.map ℤ→ℝ`, since `A⁻¹·A = 1` over `ℤ`
casts entrywise.) -/
theorem cast_map_inv {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (hunit : IsUnit A.det) :
    (A.map (Int.cast : ℤ → ℝ))⁻¹ = A⁻¹.map (Int.cast : ℤ → ℝ) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, ← Int.cast_mul, ← Int.cast_sum]
  rw [show (∑ k, A⁻¹ i k * A k j) = (A⁻¹ * A) i j from (Matrix.mul_apply).symm,
    Matrix.nonsing_inv_mul A hunit]
  simp [Matrix.one_apply, apply_ite (Int.cast : ℤ → ℝ)]

/-- **Theta self-duality** for an even unimodular integer form `A` (`Aᵀ = A`, `det A` a unit): with `M = A.map
ℤ→ℝ`, `Θ_{M⁻¹} = Θ_M`. The dual lattice `M⁻¹ = (A⁻¹)ᵀ·M·(A⁻¹)` is `M` reindexed by the unimodular `A⁻¹`, so
`latticeTheta_congr` (with `P = A⁻¹`) identifies their thetas. -/
theorem latticeTheta_inv_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (hsymm : Aᵀ = A)
    (hunit : IsUnit A.det) (τ : ℂ) :
    latticeTheta ((A.map (Int.cast : ℤ → ℝ))⁻¹) τ = latticeTheta (A.map (Int.cast : ℤ → ℝ)) τ := by
  have hPdet : IsUnit (A⁻¹).det := by
    rw [Matrix.det_nonsing_inv]; exact hunit.ringInverse
  have hAinvT : (A⁻¹)ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsymm]
  have hLI : (A⁻¹).map (Int.cast : ℤ → ℝ) * A.map (Int.cast : ℤ → ℝ) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, ← Int.cast_mul, ← Int.cast_sum]
    rw [show (∑ k, A⁻¹ i k * A k j) = (A⁻¹ * A) i j from (Matrix.mul_apply).symm,
      Matrix.nonsing_inv_mul A hunit]
    simp [Matrix.one_apply, apply_ite (Int.cast : ℤ → ℝ)]
  rw [cast_map_inv A hunit, ← latticeTheta_congr A⁻¹ hPdet (A.map (Int.cast : ℤ → ℝ)) τ]
  congr 1
  rw [← Matrix.transpose_map, hAinvT, hLI, Matrix.one_mul]

/-- **The theta S self-transformation** for an even unimodular integer form `A` (`Aᵀ = A`, positive-definite
cast, hence `det A = 1`): with `M = A.map ℤ→ℝ` and `Im τ > 0`,
> `Θ_M(-1/τ) = (τ/i)^{d/2} · Θ_M(τ)`.
From `latticeTheta_S` (`det M = 1` kills the `(det)^{-1/2}`; `π/(-iπσ) = i/σ`), `latticeTheta_inv_eq`
(`Θ_{M⁻¹} = Θ_M`), and the substitution `σ = -1/τ`. The automorphy multiplier whose `SL₂(ℤ)`-consistency
forces `8 ∣ d`. -/
theorem latticeTheta_S_self {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (hsymm : Aᵀ = A)
    (hunim : IsUnimodular A) (hpd : (A.map (Int.cast : ℤ → ℝ)).PosDef) {τ : ℂ} (hτ : 0 < τ.im) :
    latticeTheta (A.map (Int.cast : ℤ → ℝ)) (-1 / τ)
      = (τ / I) ^ ((d : ℂ) / 2) * latticeTheta (A.map (Int.cast : ℤ → ℝ)) τ := by
  have hAdet : A.det = 1 := posDef_unimodular_det_one A hunim hpd
  have hunit : IsUnit A.det := by rw [hAdet]; exact isUnit_one
  have hdet1 : (A.map (Int.cast : ℤ → ℝ)).det = 1 := by rw [← Int.cast_det, hAdet, Int.cast_one]
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hσim : 0 < (-1 / τ).im := by
    have heq : (-1 / τ).im = τ.im / Complex.normSq τ := by
      rw [neg_div, one_div, Complex.neg_im, Complex.inv_im]; ring
    rw [heq]; exact div_pos hτ (Complex.normSq_pos.mpr hτ0)
  have hS := latticeTheta_S hpd hσim
  rw [hdet1, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul,
    latticeTheta_inv_eq A hsymm hunit, show (-1 / (-1 / τ)) = τ from by field_simp] at hS
  rw [hS]
  congr 2
  rw [div_eq_div_iff (by simp [hπ, hτ0, Complex.I_ne_zero]) Complex.I_ne_zero]
  field_simp

end SKEFTHawking
