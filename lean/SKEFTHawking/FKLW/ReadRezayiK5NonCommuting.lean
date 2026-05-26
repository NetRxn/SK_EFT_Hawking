/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-B.5.2 substrate — non-commutativity of H_SU and T_RR5

Direct matrix computation showing `H_SU · T_RR5 ≠ T_RR5 · H_SU` in
`Matrix (Fin 2) (Fin 2) ℂ`. Load-bearing structural fact consumed by
the substantive discharge of `rr5_v4_witness_tracked` (Track T-B.5.2):
the closure-density argument's "not contained in any abelian closed
subgroup" step requires the generators to NOT commute.

Mirrors `CliffordTNonCommuting.lean` (Phase 6u Track T-S.2 substrate)
with phase `π/14` replacing `π/8`.

## Headline

  * `H_SU_T_RR5_not_commute : H_SU.val * T_RR5.val ≠ T_RR5.val * H_SU.val`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.

-/

import SKEFTHawking.FKLW.ReadRezayiK5GeneratingSet
import SKEFTHawking.FKLW.CliffordTGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix Complex Real

/-! ## 1. Non-commutativity of `H_SU` and `T_RR5` -/

/-- `(H_SU · T_RR5)(0, 1) = (i/√2) · exp(iπ/14)`. -/
private theorem H_SU_T_RR5_apply_0_1_off :
    (H_SU_mat * T_RR5_mat) ⟨0, by decide⟩ ⟨1, by decide⟩ =
      (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (Complex.I * Real.pi / 14) := by
  simp [H_SU_mat, T_RR5_mat, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

/-- `(T_RR5 · H_SU)(0, 1) = exp(-iπ/14) · (i/√2)`. -/
private theorem T_RR5_H_SU_apply_0_1 :
    (T_RR5_mat * H_SU_mat) ⟨0, by decide⟩ ⟨1, by decide⟩ =
      Complex.exp (-(Complex.I * Real.pi / 14)) * (Complex.I / Real.sqrt 2 : ℂ) := by
  simp [H_SU_mat, T_RR5_mat, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

/-- `exp(iπ/14) ≠ exp(-iπ/14)`: the imaginary parts differ.

`Im(exp(iπ/14)) = sin(π/14) > 0` and `Im(exp(-iπ/14)) = -sin(π/14) < 0`. -/
theorem exp_I_pi_14_ne_exp_neg_I_pi_14 :
    Complex.exp (Complex.I * Real.pi / 14) ≠
      Complex.exp (-(Complex.I * Real.pi / 14)) := by
  intro h
  have h_im : (Complex.exp (Complex.I * Real.pi / 14)).im =
              (Complex.exp (-(Complex.I * Real.pi / 14))).im := by rw [h]
  have h_pos : (0 : ℝ) < Real.sin (Real.pi / 14) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have h_pi_pos := Real.pi_pos
      positivity
    · have h_pi_pos := Real.pi_pos
      have h_pi_gt_3 : 3 < Real.pi := Real.pi_gt_three
      linarith
  have h_lhs : (Complex.exp (Complex.I * (Real.pi : ℂ) / 14)).im = Real.sin (Real.pi / 14) := by
    have h_eq : Complex.I * (Real.pi : ℂ) / 14 = ((Real.pi / 14 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h_eq, Complex.exp_mul_I, Complex.add_im, Complex.cos_ofReal_im,
        zero_add, Complex.mul_im, Complex.sin_ofReal_im, Complex.sin_ofReal_re,
        Complex.I_im, Complex.I_re]
    ring
  have h_rhs : (Complex.exp (-(Complex.I * (Real.pi : ℂ) / 14))).im
                = -Real.sin (Real.pi / 14) := by
    have h_eq : -(Complex.I * (Real.pi : ℂ) / 14) = ((-(Real.pi / 14) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h_eq, Complex.exp_mul_I, Complex.add_im, Complex.cos_ofReal_im,
        zero_add, Complex.mul_im, Complex.sin_ofReal_im, Complex.sin_ofReal_re,
        Complex.I_im, Complex.I_re, Real.sin_neg]
    ring
  rw [h_lhs, h_rhs] at h_im
  linarith

/-- **H_SU and T_RR5 do not commute in SU(2)**. -/
theorem H_SU_T_RR5_not_commute :
    (H_SU.val * T_RR5.val : Matrix (Fin 2) (Fin 2) ℂ) ≠ T_RR5.val * H_SU.val := by
  intro h_eq
  have h_at_0_1 : (H_SU.val * T_RR5.val : Matrix (Fin 2) (Fin 2) ℂ)
                    ⟨0, by decide⟩ ⟨1, by decide⟩ =
                  (T_RR5.val * H_SU.val : Matrix (Fin 2) (Fin 2) ℂ)
                    ⟨0, by decide⟩ ⟨1, by decide⟩ := by
    rw [h_eq]
  rw [show (H_SU.val : Matrix (Fin 2) (Fin 2) ℂ) = H_SU_mat from rfl,
      show (T_RR5.val : Matrix (Fin 2) (Fin 2) ℂ) = T_RR5_mat from rfl,
      H_SU_T_RR5_apply_0_1_off, T_RR5_H_SU_apply_0_1] at h_at_0_1
  have h_sqrt_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    push_cast
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h_factor : (Complex.I / Real.sqrt 2 : ℂ) ≠ 0 := by
    apply div_ne_zero
    · exact Complex.I_ne_zero
    · exact h_sqrt_ne_zero
  have h_swap : Complex.exp (-(Complex.I * Real.pi / 14)) * (Complex.I / Real.sqrt 2 : ℂ)
              = (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (-(Complex.I * Real.pi / 14)) := by
    ring
  rw [h_swap] at h_at_0_1
  have h_cancel : Complex.exp (Complex.I * Real.pi / 14) =
                  Complex.exp (-(Complex.I * Real.pi / 14)) :=
    mul_left_cancel₀ h_factor h_at_0_1
  exact exp_I_pi_14_ne_exp_neg_I_pi_14 h_cancel

end SKEFTHawking.FKLW.GenericSU2
