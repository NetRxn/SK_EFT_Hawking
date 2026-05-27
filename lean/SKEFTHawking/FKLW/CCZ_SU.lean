/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.1-substrate — Phase-corrected CCZ for SU(8)

The raw `CCZ_mat` (Phase 6x) is in U(8) but not SU(8) (det = −1). For
SU(8) compilation we use `CCZ_SU := ω • CCZ_mat` with
`ω = e^(iπ/8)`, giving det `ω^8 · det(CCZ_mat) = -1 · -1 = 1`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.1 CCZ-SU
packaging.

-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZAlphabet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CCZSUExtension

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. CCZ_mat is its own conjTranspose (real diagonal) -/

/-- The CCZ matrix is its own conjTranspose (real entries on diagonal). -/
theorem CCZ_mat_conjTranspose_self :
    SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat.conjTranspose =
      SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat := by
  unfold SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  by_cases h : i = (⟨7, by decide⟩ : Fin 8)
  · rw [if_pos h]; show (starRingEnd ℂ) (-1) = -1; simp
  · rw [if_neg h]; show (starRingEnd ℂ) (1) = 1; simp

/-! ## 2. CCZ_mat squared is the identity -/

/-- `CCZ_mat * CCZ_mat = 1` (diagonal entries are ±1, squared = 1). -/
theorem CCZ_mat_sq_eq_one :
    SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat *
      SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat = 1 := by
  unfold SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (1 : Matrix (Fin 8) (Fin 8) ℂ) = Matrix.diagonal (fun _ => (1 : ℂ)) from
      (Matrix.diagonal_one).symm]
  congr 1
  funext i
  by_cases h : i = (⟨7, by decide⟩ : Fin 8)
  · rw [if_pos h]; show (-1 : ℂ) * (-1) = 1; ring
  · rw [if_neg h]; show (1 : ℂ) * 1 = 1; ring

/-! ## 3. det(CCZ_mat) = -1 via Fin.prod_univ_eight -/

/-- Determinant of CCZ_mat = -1. Product of 7 ones and one -1. -/
theorem det_CCZ_mat : SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat.det = -1 := by
  unfold SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat
  rw [Matrix.det_diagonal]
  -- ∏ i : Fin 8, (if i = 7 then -1 else 1) = -1.
  rw [Fin.prod_univ_eight]
  -- Now goal: 8 explicit if-terms, all 1 except i=7 which is -1.
  -- The decidability needs to unfold the Fin.mk equality.
  simp [show (⟨0, by decide⟩ : Fin 8) ≠ ⟨7, by decide⟩ from by decide,
        show (⟨1, by decide⟩ : Fin 8) ≠ ⟨7, by decide⟩ from by decide,
        show (⟨2, by decide⟩ : Fin 8) ≠ ⟨7, by decide⟩ from by decide,
        show (⟨3, by decide⟩ : Fin 8) ≠ ⟨7, by decide⟩ from by decide,
        show (⟨4, by decide⟩ : Fin 8) ≠ ⟨7, by decide⟩ from by decide,
        show (⟨5, by decide⟩ : Fin 8) ≠ ⟨7, by decide⟩ from by decide,
        show (⟨6, by decide⟩ : Fin 8) ≠ ⟨7, by decide⟩ from by decide]

/-! ## 4. The phase ω = e^(iπ/8) -/

/-- The phase correction `ω = e^(π i / 8)` for SU(8) lift of CCZ. -/
noncomputable def ccz_phase : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I / 8)

/-- `ccz_phase` has unit modulus (purely imaginary exponent argument). -/
theorem ccz_phase_norm_one : ‖ccz_phase‖ = 1 := by
  unfold ccz_phase
  rw [Complex.norm_exp]
  -- (π · I / 8).re = 0
  have h : ((Real.pi : ℂ) * Complex.I / 8).re = 0 := by
    rw [Complex.div_re]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofNat]
  rw [h, Real.exp_zero]

/-- `ccz_phase^8 = -1` (8th power of e^(iπ/8) = e^(iπ) = -1). -/
theorem ccz_phase_pow_eight : ccz_phase ^ 8 = -1 := by
  unfold ccz_phase
  rw [← Complex.exp_nat_mul]
  have : (8 : ℕ) * ((Real.pi : ℂ) * Complex.I / 8) = (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [this]
  exact Complex.exp_pi_mul_I

/-- `ccz_phase * star ccz_phase = 1`. -/
theorem ccz_phase_mul_star : ccz_phase * star ccz_phase = 1 := by
  have h1 : ccz_phase * (starRingEnd ℂ) ccz_phase = (Complex.normSq ccz_phase : ℂ) :=
    Complex.mul_conj ccz_phase
  have h_starRing_eq_star : (starRingEnd ℂ) ccz_phase = star ccz_phase := rfl
  rw [h_starRing_eq_star] at h1
  rw [h1, Complex.normSq_eq_norm_sq, ccz_phase_norm_one]
  push_cast; ring

/-! ## 5. Phase-corrected CCZ and its SU(8) membership -/

/-- **Phase-corrected CCZ for SU(8)**: `CCZ_SU := ω • CCZ_mat`. -/
noncomputable def CCZ_SU : Matrix (Fin 8) (Fin 8) ℂ :=
  ccz_phase • SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat

/-- **`CCZ_SU ∈ specialUnitaryGroup (Fin 8) ℂ`** (substantive). -/
theorem CCZ_SU_mem_specialUnitaryGroup :
    CCZ_SU ∈ Matrix.specialUnitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · -- Unitary part.
    rw [Matrix.mem_unitaryGroup_iff]
    show CCZ_SU * star CCZ_SU = 1
    unfold CCZ_SU
    rw [star_smul]
    -- star CCZ_mat = CCZ_mat
    have h_star_CCZ : (star SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat :
        Matrix (Fin 8) (Fin 8) ℂ) = SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat :=
      CCZ_mat_conjTranspose_self
    rw [h_star_CCZ]
    rw [Matrix.smul_mul, Matrix.mul_smul, CCZ_mat_sq_eq_one, smul_smul]
    rw [ccz_phase_mul_star, one_smul]
  · -- det = 1 part.
    show CCZ_SU.det = 1
    unfold CCZ_SU
    rw [Matrix.det_smul, Fintype.card_fin, det_CCZ_mat, ccz_phase_pow_eight]
    ring

/-- **`CCZ_SU` as SU(8) subtype element**. -/
noncomputable def CCZ_SU_subtype : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  ⟨CCZ_SU, CCZ_SU_mem_specialUnitaryGroup⟩

end SKEFTHawking.FKLW.CCZSUExtension
