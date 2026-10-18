import SKEFTHawking.FinitePositiveKernelDynamics

/-! Positive selfadjoint matrix transfers on the actual finite kernel quotient.
Weighted symmetry proves null preservation; positivity is a coefficient matrix
condition. Continuity follows from finite dimension, with no contraction assumed. -/
noncomputable section
open Matrix
open scoped ComplexOrder InnerProductSpace
namespace SKEFTHawking.FinitePositiveKernel
variable {ι : Type*} [Fintype ι] {K : Matrix ι ι ℂ} (hK : K.PosSemidef)

/-- Weighted symmetry preserves the derived null space even when `K` is singular. -/
theorem nullPreserving_of_weightedSymmetry (A : Matrix ι ι ℂ)
    (hA : K * A = Aᴴ * K) : NullPreserving hK (coefficientMap hK A) := by
  classical
  intro x hx
  apply (mem_nullSpace_iff K hK _).mpr
  apply (null_iff_mulVec_eq_zero K hK _).mpr
  have hx0 := (null_iff_mulVec_eq_zero K hK x).mp ((mem_nullSpace_iff K hK x).mp hx)
  change K *ᵥ (A *ᵥ x) = 0
  unfold Coefficients at x
  rw [Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, hx0, Matrix.mulVec_zero]

omit hK in
/-- The weighted matrix identity is symmetry of the coefficient pairing. -/
theorem pairing_weightedSymmetry (A : Matrix ι ι ℂ) (hA : K * A = Aᴴ * K)
    (x y : ι → ℂ) : pairing K (A *ᵥ x) y = pairing K x (A *ᵥ y) := by
  simp only [pairing, star_mulVec, dotProduct_mulVec, vecMul_vecMul, hA]

/-- Descend first, then use finite dimensionality for continuity. -/
def matrixTransfer (A : Matrix ι ι ℂ) (hA : K * A = Aᴴ * K) :
    Space K hK →L[ℂ] Space K hK :=
  (descend hK (coefficientMap hK A) (nullPreserving_of_weightedSymmetry hK A hA)).toContinuousLinearMap

theorem matrixTransfer_mk (A : Matrix ι ι ℂ) (hA : K * A = Aᴴ * K)
    (x : Coefficients hK) :
    matrixTransfer hK A hA (mk K hK x) = mk K hK (A *ᵥ x) :=
  descend_mk hK _ _ x

theorem matrixTransfer_symmetric (A : Matrix ι ι ℂ) (hA : K * A = Aᴴ * K) :
    (matrixTransfer hK A hA).IsSymmetric := by
  intro z w
  obtain ⟨x, rfl⟩ := mk_surjective K hK z
  obtain ⟨y, rfl⟩ := mk_surjective K hK w
  change ⟪matrixTransfer hK A hA (mk K hK x), mk K hK y⟫_ℂ =
    ⟪mk K hK x, matrixTransfer hK A hA (mk K hK y)⟫_ℂ
  simp only [matrixTransfer_mk, inner_mk]
  exact pairing_weightedSymmetry A hA x y

theorem matrixTransfer_selfAdjoint (A : Matrix ι ι ℂ) (hA : K * A = Aᴴ * K) :
    IsSelfAdjoint (matrixTransfer hK A hA) :=
  (matrixTransfer_symmetric hK A hA).isSelfAdjoint

/-- Full complex PSD of `K A` supplies positivity on every quotient vector. -/
theorem matrixTransfer_positive (A : Matrix ι ι ℂ) (hA : K * A = Aᴴ * K)
    (hP : (K * A).PosSemidef) : (matrixTransfer hK A hA).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨matrixTransfer_symmetric hK A hA, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := mk_surjective K hK z
  rw [matrixTransfer_mk, inner_mk, pairing_weightedSymmetry A hA]
  simpa only [pairing, Matrix.mulVec_mulVec] using hP.dotProduct_mulVec_nonneg x

/-- A PSD defect additionally makes the same selfadjoint transfer contractive. -/
theorem matrixTransfer_norm_le (A : Matrix ι ι ℂ) (hA : K * A = Aᴴ * K)
    (hD : (K - Aᴴ * K * A).PosSemidef) (z : Space K hK) :
    ‖matrixTransfer hK A hA z‖ ≤ ‖z‖ :=
  descend_norm_le hK _ (energy_le_of_defect hK A hD) z

include hK in
/-- Positivity of the weighted matrix already includes the required symmetry. -/
theorem weightedSymmetry_of_positive (A : Matrix ι ι ℂ) (hP : (K * A).PosSemidef) :
    K * A = Aᴴ * K := by
  have hh := hP.isHermitian.eq
  rw [Matrix.conjTranspose_mul, hK.isHermitian.eq] at hh
  exact hh.symm

/-- A positive transfer needs only PSD of the weighted matrix, beyond PSD of the kernel. -/
def positiveMatrixTransfer (A : Matrix ι ι ℂ) (hP : (K * A).PosSemidef) :
    Space K hK →L[ℂ] Space K hK :=
  matrixTransfer hK A (weightedSymmetry_of_positive hK A hP)

theorem positiveMatrixTransfer_mk (A : Matrix ι ι ℂ) (hP : (K * A).PosSemidef)
    (x : Coefficients hK) :
    positiveMatrixTransfer hK A hP (mk K hK x) = mk K hK (A *ᵥ x) :=
  matrixTransfer_mk hK A _ x

theorem positiveMatrixTransfer_positive (A : Matrix ι ι ℂ) (hP : (K * A).PosSemidef) :
    (positiveMatrixTransfer hK A hP).IsPositive :=
  matrixTransfer_positive hK A _ hP

theorem positiveMatrixTransfer_selfAdjoint (A : Matrix ι ι ℂ) (hP : (K * A).PosSemidef) :
    IsSelfAdjoint (positiveMatrixTransfer hK A hP) :=
  (positiveMatrixTransfer_positive hK A hP).isSelfAdjoint

section TwoRateExample

/-- Two surviving directions and a genuine null coefficient direction. -/
def twoRateKernel : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1, 1, 0]

/-- The null direction may expand on coefficients without affecting the quotient. -/
def twoRateMatrix : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1/2, 1/3, 2]

theorem twoRateKernel_posSemidef : twoRateKernel.PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [Complex.le_def]

theorem twoRate_weightedSymmetry :
    twoRateKernel * twoRateMatrix = twoRateMatrixᴴ * twoRateKernel := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoRateKernel, twoRateMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply]

theorem twoRate_weightedPositive : (twoRateKernel * twoRateMatrix).PosSemidef := by
  unfold twoRateKernel twoRateMatrix
  rw [Matrix.diagonal_mul_diagonal]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [Complex.le_def]

def twoRateTransfer : Space twoRateKernel twoRateKernel_posSemidef →L[ℂ]
    Space twoRateKernel twoRateKernel_posSemidef :=
  positiveMatrixTransfer twoRateKernel_posSemidef twoRateMatrix twoRate_weightedPositive

theorem twoRateTransfer_positive : twoRateTransfer.IsPositive :=
  positiveMatrixTransfer_positive _ _ twoRate_weightedPositive

theorem twoRateTransfer_selfAdjoint : IsSelfAdjoint twoRateTransfer :=
  positiveMatrixTransfer_selfAdjoint _ _ twoRate_weightedPositive

/-- This nonzero coefficient vector is killed by the reconstruction. -/
theorem twoRate_null :
    (Pi.single 2 1 : Fin 3 → ℂ) ≠ 0 ∧
      mk twoRateKernel twoRateKernel_posSemidef (Pi.single 2 1) = 0 := by
  constructor
  · intro h
    have hh := congrFun h 2
    norm_num at hh
  · apply (mk_eq_zero_iff _ _ _).mpr
    norm_num [pairing, twoRateKernel, Matrix.diagonal_apply, dotProduct, mulVec,
      Fin.sum_univ_succ, Pi.single_apply]
    rfl

theorem twoRate_feature_nonzero (i : Fin 3) (hi : i ≠ 2) :
    feature twoRateKernel twoRateKernel_posSemidef i ≠ 0 := by
  intro h
  have hh := inner_feature twoRateKernel twoRateKernel_posSemidef i i
  rw [h, inner_zero_left] at hh
  fin_cases i <;> simp_all [twoRateKernel]

/-- The descended action recovers each diagonal eigenvalue on actual quotient features. -/
theorem twoRate_feature_action (i : Fin 3) :
    twoRateTransfer (feature twoRateKernel twoRateKernel_posSemidef i) =
      (![1/2, 1/3, 2] : Fin 3 → ℂ) i • feature twoRateKernel twoRateKernel_posSemidef i := by
  change matrixTransfer _ _ twoRate_weightedSymmetry (mk _ _ (Pi.single i 1)) = _
  rw [matrixTransfer_mk]
  have he : twoRateMatrix *ᵥ Pi.single i 1 =
      (![1/2, 1/3, 2] : Fin 3 → ℂ) i • Pi.single i 1 := by
    ext j
    fin_cases i <;> fin_cases j <;>
      norm_num [twoRateMatrix, Matrix.diagonal_apply, mulVec, dotProduct,
        Fin.sum_univ_succ, Pi.single_apply]
  rw [he]
  exact (mkLinear twoRateKernel twoRateKernel_posSemidef).map_smul _ _

/-- Both nonzero surviving features strictly contract, with distinct positive rates. -/
theorem twoRate_strict (i : Fin 2) :
    ‖twoRateTransfer (feature twoRateKernel twoRateKernel_posSemidef i.castSucc)‖ <
      ‖feature twoRateKernel twoRateKernel_posSemidef i.castSucc‖ := by
  rw [twoRate_feature_action, norm_smul]
  have hp := norm_pos_iff.mpr (twoRate_feature_nonzero i.castSucc (by fin_cases i <;> decide))
  fin_cases i
  · change 0 < ‖feature twoRateKernel twoRateKernel_posSemidef 0‖ at hp
    norm_num
    linarith
  · change 0 < ‖feature twoRateKernel twoRateKernel_posSemidef 1‖ at hp
    norm_num
    linarith

/-- On coefficients the removed direction has eigenvalue two, despite quotient contraction. -/
theorem twoRate_null_coefficient_action :
    twoRateMatrix *ᵥ (Pi.single 2 1 : Fin 3 → ℂ) =
      (2 : ℂ) • (Pi.single 2 1 : Fin 3 → ℂ) := by
  ext i
  fin_cases i <;> norm_num [twoRateMatrix, Matrix.diagonal_apply, mulVec, dotProduct,
    Fin.sum_univ_succ, Pi.single_apply] <;> simp

/-- The coefficient expansion on the null direction contributes zero defect. -/
theorem twoRate_defect_positive :
    (twoRateKernel - twoRateMatrixᴴ * twoRateKernel * twoRateMatrix).PosSemidef := by
  unfold twoRateKernel twoRateMatrix
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [Complex.le_def]

theorem twoRate_norm_le (z : Space twoRateKernel twoRateKernel_posSemidef) :
    ‖twoRateTransfer z‖ ≤ ‖z‖ :=
  matrixTransfer_norm_le _ _ twoRate_weightedSymmetry twoRate_defect_positive z

/-- Distinct eigenvalues survive reconstruction, ruling out every scalar operator. -/
theorem twoRate_not_scalar :
    ¬ ∃ c : ℂ, ∀ z : Space twoRateKernel twoRateKernel_posSemidef,
      twoRateTransfer z = c • z := by
  rintro ⟨c, hc⟩
  have h0 := hc (feature twoRateKernel twoRateKernel_posSemidef 0)
  have h1 := hc (feature twoRateKernel twoRateKernel_posSemidef 1)
  rw [twoRate_feature_action] at h0 h1
  have hc0 := smul_left_injective ℂ (twoRate_feature_nonzero 0 (by decide)) h0
  have hc1 := smul_left_injective ℂ (twoRate_feature_nonzero 1 (by decide)) h1
  norm_num at hc0 hc1
  rw [← hc0] at hc1
  norm_num at hc1

end TwoRateExample
end SKEFTHawking.FinitePositiveKernel
