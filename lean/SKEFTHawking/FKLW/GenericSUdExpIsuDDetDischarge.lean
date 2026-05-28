/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SUBSTANTIVE discharge of `ExpIsud_det_eq_one_predicate`

For ANY Hermitian-traceless `F : Matrix (Fin (n+2)) (Fin (n+2)) ℂ`,

  `Matrix.det (NormedSpace.exp (Complex.I • F)) = 1`.

Proof via spectral decomposition + Matrix.exp_conj + Matrix.exp_diagonal +
Matrix.det_diagonal + Complex.exp_sum.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — det predicate substantive
discharge (1st of 4 substantive ingredients).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdExpIsuD

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- For unitary U, U is a unit (IsUnit) with two-sided inverse star U. -/
lemma unitaryGroup_isUnit_sud {d : ℕ}
    {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    IsUnit U := by
  refine ⟨⟨U, star U, ?_, ?_⟩, rfl⟩
  · exact Matrix.mem_unitaryGroup_iff.mp hU
  · exact Matrix.mem_unitaryGroup_iff'.mp hU

/-- For unitary U, the matrix inverse U⁻¹ equals star U. -/
lemma unitaryGroup_inv_eq_star_sud {d : ℕ}
    {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    U⁻¹ = star U :=
  Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hU)

/-- Complex-scalar smul commutes with the diagonal: c • diag(a) = diag(c • a). -/
lemma I_smul_diagonal_sud {d : ℕ} (a : Fin d → ℂ) :
    Complex.I • Matrix.diagonal a = Matrix.diagonal (fun k => Complex.I * a k) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.diagonal, smul_eq_mul]
  · simp [Matrix.diagonal, h, smul_eq_mul]

/-- For any U, D, V : Matrix (Fin d) (Fin d) ℂ:
    c • (U * D * V) = U * (c • D) * V (smul passes through middle factor). -/
lemma smul_conj_eq_sud {d : ℕ} (c : ℂ)
    (U D V : Matrix (Fin d) (Fin d) ℂ) :
    c • (U * D * V) = U * (c • D) * V := by
  -- U * D * V is parsed as (U * D) * V (left-assoc).
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]

/-- **SUBSTANTIVE DISCHARGE** of `ExpIsud_det_eq_one_predicate` at SU(d)
for d = n + 2 ≥ 2.

For any Hermitian-traceless `F : Matrix (Fin (n+2)) (Fin (n+2)) ℂ`,
`Matrix.det (NormedSpace.exp (Complex.I • F)) = 1`. -/
theorem expIsud_det_eq_one_predicate_holds (n : ℕ) :
    ExpIsud_det_eq_one_predicate (n + 2) := by
  intro F hF hF_tr
  set U := hF.eigenvectorUnitary with hU_def
  set a : Fin (n + 2) → ℂ := fun k => ((hF.eigenvalues k : ℝ) : ℂ) with ha_def
  have hU_isUnit : IsUnit U.val := unitaryGroup_isUnit_sud U.property
  have hU_inv_eq : U.val⁻¹ = star U.val := unitaryGroup_inv_eq_star_sud U.property
  -- Spectral theorem unfolded.
  have h_spec : F = U.val * Matrix.diagonal a * star U.val := by
    have h_st := hF.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h_st
    exact h_st
  -- I • F = U.val * diag(fun k => I * a k) * U.val⁻¹.
  have h_IF : Complex.I • F =
      U.val * Matrix.diagonal (fun k => Complex.I * a k) * U.val⁻¹ := by
    rw [h_spec, smul_conj_eq_sud, I_smul_diagonal_sud, ← hU_inv_eq]
  -- exp(I • F) = U.val * exp(diag(I•a)) * U.val⁻¹.
  rw [h_IF, Matrix.exp_conj _ _ hU_isUnit, Matrix.exp_diagonal]
  -- det(U * diag(exp(I•a)) * U⁻¹) = det U * det(diag(...)) * det(U⁻¹).
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  -- ∑ a k = 0 via F.trace = 0.
  have h_sum_a : ∑ k, a k = 0 := by
    have h_tr_F : F.trace = ∑ k, a k := by
      rw [h_spec, Matrix.trace_mul_cycle]
      have h_star_U : star U.val * U.val = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp U.property
      -- After trace_mul_cycle: (star U * U * diag a).trace = ∑ a k.
      rw [h_star_U, Matrix.one_mul, Matrix.trace_diagonal]
    rw [hF_tr] at h_tr_F; exact h_tr_F.symm
  -- ∏ NormedSpace.exp (fun k => I * a k) i = 1 via Complex.exp_sum + ∑ a = 0.
  -- Convert to a form using Complex.exp directly.
  have h_prod_eq :
      (∏ i, NormedSpace.exp (fun k : Fin (n+2) => Complex.I * a k) i) =
      (∏ i, Complex.exp (Complex.I * a i)) := by
    apply Finset.prod_congr rfl
    intros i _
    -- (NormedSpace.exp v) i = NormedSpace.exp (v i) via Pi.exp_def + beta.
    simp only [Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
  rw [h_prod_eq]
  have h_prod_exp :
      (∏ i, Complex.exp (Complex.I * a i)) = 1 := by
    rw [← Complex.exp_sum, ← Finset.mul_sum, h_sum_a, mul_zero, Complex.exp_zero]
  rw [h_prod_exp, mul_one]
  -- det U * det(U⁻¹) = det(U * U⁻¹) = det 1 = 1.
  have hU_det_isUnit : IsUnit U.val.det :=
    (Matrix.isUnit_iff_isUnit_det U.val).mp hU_isUnit
  rw [← Matrix.det_mul, Matrix.mul_nonsing_inv U.val hU_det_isUnit, Matrix.det_one]

end SKEFTHawking.FKLW.GenericSUd
