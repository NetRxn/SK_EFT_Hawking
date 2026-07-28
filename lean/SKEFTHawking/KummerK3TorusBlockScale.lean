/-
# Phase 5q.H — the descended `T⁴` block is `3H(2)`, not `3H`

placeholder
-/
import Mathlib
import SKEFTHawking.KummerK3EvenFromSpanningFamily

namespace SKEFTHawking.KummerK3TorusBlockScale

open Matrix QuadraticMap QuadraticForm
open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerWeld (KummerK3 EIndex)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SpinSigmaRoute (blockDiag blockDiag_def)
open SKEFTHawking.KummerInvolution (torusFourForm torusFourForm_isEvenUnimodular
  torusFourForm_latticeSig)
open SKEFTHawking.LatticeSigFullRank
open SKEFTHawking.KummerK3GramFromLattice
open SKEFTHawking.KummerK3GeometricFamily
open SKEFTHawking.KummerK3CapDualFamily
open SKEFTHawking.KummerK3EvenFromSpanningFamily

noncomputable section

variable {X : TopCat}

/-! ## §1. Signature is invariant under scaling by a positive integer -/

theorem latticeSig_smul_of_pos {n : ℕ} (c : ℤ) (hc : 0 < c) (M : Matrix (Fin n) (Fin n) ℤ) :
    latticeSig (c • M) = latticeSig M := by
  set Mr := M.map (Int.cast : ℤ → ℝ) with hMr
  set s : ℝ := Real.sqrt (c : ℝ) with hs
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hs2 : s * s = (c : ℝ) := Real.mul_self_sqrt hcR.le
  have hspos : 0 < s := Real.sqrt_pos.mpr hcR
  set Pr : Matrix (Fin n) (Fin n) ℝ := s • (1 : Matrix (Fin n) (Fin n) ℝ) with hPr
  have hmapentry : ((c • M).map (Int.cast : ℤ → ℝ)) = (c : ℝ) • Mr := by
    ext i j
    simp [hMr, Matrix.mul_apply, Matrix.intCast_apply]
  have hmap : ((c • M).map (Int.cast : ℤ → ℝ)) = Prᵀ * Mr * Pr := by
    rw [hmapentry, hPr, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hs2]
  have hPrdet : IsUnit Pr.det := by
    rw [hPr, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero).mpr (pow_ne_zero _ hspos.ne')
  letI : Invertible Pr := Matrix.invertibleOfIsUnitDet Pr hPrdet
  have hcoe : (↑(Pr.toLinearEquiv' inferInstance) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      = Matrix.mulVecLin Pr := by rw [Matrix.toLinearEquiv'_apply]; rfl
  have hequiv : QuadraticMap.Equivalent Mr.toQuadraticMap' (Prᵀ * Mr * Pr).toQuadraticMap' := by
    refine ⟨?_⟩
    have h := QuadraticMap.isometryEquivOfCompLinearEquiv Mr.toQuadraticMap'
      (Pr.toLinearEquiv' inferInstance)
    rwa [hcoe, ← toQuadraticMap'_congr] at h
  unfold latticeSig
  rw [hmap, ← hequiv.sigPos_eq, ← hequiv.sigNeg_eq]

/-! ## §2. Determinant, symmetry, evenness under scaling -/

theorem det_smul_ne_zero {n : ℕ} (c : ℤ) (hc : c ≠ 0) (M : Matrix (Fin n) (Fin n) ℤ)
    (hdet : M.det ≠ 0) : (c • M).det ≠ 0 := by
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) hdet

theorem transpose_smul_eq {n : ℕ} (c : ℤ) (M : Matrix (Fin n) (Fin n) ℤ) (hsym : Mᵀ = M) :
    (c • M)ᵀ = c • M := by
  rw [Matrix.transpose_smul, hsym]

theorem smul_even_diag {n : ℕ} (c : ℤ) (M : Matrix (Fin n) (Fin n) ℤ)
    (heven : ∀ i, (2 : ℤ) ∣ M i i) (i : Fin n) : (2 : ℤ) ∣ (c • M) i i := by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Dvd.dvd.mul_left (heven i) c

/-! ## §3. `IntCongr` commutes with scaling -/

theorem intCongr_smul {n : ℕ} (c : ℤ) {M N : Matrix (Fin n) (Fin n) ℤ} (h : IntCongr M N) :
    IntCongr (c • M) (c • N) := by
  obtain ⟨P, hP, hPMP⟩ := h
  refine ⟨P, hP, ?_⟩
  rw [Matrix.mul_smul, Matrix.smul_mul, hPMP]

end

end SKEFTHawking.KummerK3TorusBlockScale
