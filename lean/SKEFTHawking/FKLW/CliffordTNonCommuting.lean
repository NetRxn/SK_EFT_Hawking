/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Track T-S.2 substantive discharge substrate — non-commutativity of H_SU and T_SU

Direct matrix computation showing `H_SU · T_SU ≠ T_SU · H_SU` in
`Matrix (Fin 2) (Fin 2) ℂ`. This is a load-bearing structural fact
consumed by the substantive discharge of `cliffordT_v4_witness_tracked`
(Track T-S.2): the closure-density argument's "not contained in any
abelian closed subgroup" step requires the generators to NOT commute.

## Headline

  * `H_SU_T_SU_not_commute : H_SU.val * T_SU.val ≠ T_SU.val * H_SU.val` —
    explicit entrywise distinctness via `(H_SU · T_SU)(0,1) ≠ (T_SU · H_SU)(0,1)`.

## Why this is non-trivial

The (0,1) entry of `H_SU · T_SU` and `T_SU · H_SU` differ:
  - `(H_SU · T_SU)(0,1) = (i/√2) · exp(iπ/8)`
  - `(T_SU · H_SU)(0,1) = (i/√2) · exp(-iπ/8)`

These are unequal because `exp(iπ/8) ≠ exp(-iπ/8)` (the imaginary parts
have opposite signs, so they differ by `2·sin(π/8) ≠ 0`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
- **Strengthening discipline**: substantive (not rfl-discharged); load-
  bearing (substrate for T-S.2 discharge); cross-bridge integrity (used
  in `cliffordT_v4_witness_tracked` substantive proof per the discharge
  plan).

-/

import SKEFTHawking.FKLW.CliffordTGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix Complex Real

/-! ## 1. Non-commutativity of `H_SU` and `T_SU`

The product `H_SU · T_SU` differs from `T_SU · H_SU` in the (0, 1)
entry. This shows H_SU and T_SU are not contained in any abelian
subgroup of SU(2), and in particular `⟨H_SU, T_SU⟩` is not abelian. -/

/-- `(H_SU · T_SU)(0, 1) = (i/√2) · exp(iπ/8)`. -/
private theorem H_SU_T_SU_apply_0_1 :
    (H_SU_mat * T_SU_mat) ⟨0, by decide⟩ ⟨1, by decide⟩ =
      (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (Complex.I * Real.pi / 8) := by
  simp [H_SU_mat, T_SU_mat, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.smul_apply, smul_eq_mul]

/-- `(T_SU · H_SU)(0, 1) = (i/√2) · exp(-iπ/8)`. -/
private theorem T_SU_H_SU_apply_0_1 :
    (T_SU_mat * H_SU_mat) ⟨0, by decide⟩ ⟨1, by decide⟩ =
      Complex.exp (-(Complex.I * Real.pi / 8)) * (Complex.I / Real.sqrt 2 : ℂ) := by
  simp [H_SU_mat, T_SU_mat, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.smul_apply, smul_eq_mul]

/-- `exp(iπ/8) ≠ exp(-iπ/8)`: the imaginary parts differ.

Specifically, `Im(exp(iπ/8)) = sin(π/8) > 0` and `Im(exp(-iπ/8)) = -sin(π/8) < 0`. -/
theorem exp_I_pi_8_ne_exp_neg_I_pi_8 :
    Complex.exp (Complex.I * Real.pi / 8) ≠
      Complex.exp (-(Complex.I * Real.pi / 8)) := by
  intro h
  -- Take imaginary parts: Im(LHS) = sin(π/8), Im(RHS) = -sin(π/8).
  have h_im : (Complex.exp (Complex.I * Real.pi / 8)).im =
              (Complex.exp (-(Complex.I * Real.pi / 8))).im := by rw [h]
  -- exp(I · t) for real t = cos(t) + i·sin(t).
  -- exp(I * π/8) = cos(π/8) + i·sin(π/8), so Im = sin(π/8).
  -- exp(-(I * π/8)) = cos(-π/8) + i·sin(-π/8) = cos(π/8) - i·sin(π/8), so Im = -sin(π/8).
  -- Thus sin(π/8) = -sin(π/8) ⟹ 2·sin(π/8) = 0 ⟹ sin(π/8) = 0.
  -- But sin(π/8) > 0 (since 0 < π/8 < π).
  have h_pos : (0 : ℝ) < Real.sin (Real.pi / 8) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have h_pi_pos := Real.pi_pos
      positivity
    · have h_pi_pos := Real.pi_pos
      have h_pi_gt_3 : 3 < Real.pi := Real.pi_gt_three
      linarith
  -- Show the LHS's im evaluates to sin(π/8) using the real-exp identity.
  have h_lhs : (Complex.exp (Complex.I * (Real.pi : ℂ) / 8)).im = Real.sin (Real.pi / 8) := by
    have h_eq : Complex.I * (Real.pi : ℂ) / 8 = ((Real.pi / 8 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h_eq, Complex.exp_mul_I, Complex.add_im, Complex.cos_ofReal_im,
        zero_add, Complex.mul_im, Complex.sin_ofReal_im, Complex.sin_ofReal_re,
        Complex.I_im, Complex.I_re]
    ring
  have h_rhs : (Complex.exp (-(Complex.I * (Real.pi : ℂ) / 8))).im = -Real.sin (Real.pi / 8) := by
    have h_eq : -(Complex.I * (Real.pi : ℂ) / 8) = ((-(Real.pi / 8) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h_eq, Complex.exp_mul_I, Complex.add_im, Complex.cos_ofReal_im,
        zero_add, Complex.mul_im, Complex.sin_ofReal_im, Complex.sin_ofReal_re,
        Complex.I_im, Complex.I_re]
    push_cast; rw [Real.sin_neg]; ring
  rw [h_lhs, h_rhs] at h_im
  -- sin(π/8) = -sin(π/8) ⟹ 2·sin(π/8) = 0 ⟹ sin(π/8) = 0. But sin(π/8) > 0. Contradiction.
  linarith

/-- **H_SU and T_SU do not commute in SU(2)**.

Direct entrywise check on the (0,1) component: `H_SU · T_SU(0,1)` and
`T_SU · H_SU(0,1)` differ by a factor `exp(iπ/8) / exp(-iπ/8) = exp(iπ/4)
≠ 1`. -/
theorem H_SU_T_SU_not_commute :
    (H_SU.val * T_SU.val : Matrix (Fin 2) (Fin 2) ℂ) ≠ T_SU.val * H_SU.val := by
  intro h_eq
  -- Coerce to matrix equality, then specialize at (0, 1).
  have h_at_0_1 : (H_SU.val * T_SU.val : Matrix (Fin 2) (Fin 2) ℂ)
                    ⟨0, by decide⟩ ⟨1, by decide⟩ =
                  (T_SU.val * H_SU.val : Matrix (Fin 2) (Fin 2) ℂ)
                    ⟨0, by decide⟩ ⟨1, by decide⟩ := by
    rw [h_eq]
  -- LHS = (i/√2) · exp(iπ/8).
  -- RHS = exp(-iπ/8) · (i/√2).
  -- After commuting scalar multiplication: RHS = (i/√2) · exp(-iπ/8).
  rw [show (H_SU.val : Matrix (Fin 2) (Fin 2) ℂ) = H_SU_mat from rfl,
      show (T_SU.val : Matrix (Fin 2) (Fin 2) ℂ) = T_SU_mat from rfl,
      H_SU_T_SU_apply_0_1, T_SU_H_SU_apply_0_1] at h_at_0_1
  -- h_at_0_1 : (i/√2) · exp(iπ/8) = exp(-iπ/8) · (i/√2).
  have h_sqrt_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    push_cast
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h_factor : (Complex.I / Real.sqrt 2 : ℂ) ≠ 0 := by
    apply div_ne_zero
    · exact Complex.I_ne_zero
    · exact h_sqrt_ne_zero
  -- Commute and cancel the (i/√2) factor.
  have h_swap : Complex.exp (-(Complex.I * Real.pi / 8)) * (Complex.I / Real.sqrt 2 : ℂ)
              = (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (-(Complex.I * Real.pi / 8)) := by
    ring
  rw [h_swap] at h_at_0_1
  -- h_at_0_1 : (i/√2) · exp(iπ/8) = (i/√2) · exp(-iπ/8).
  have h_cancel : Complex.exp (Complex.I * Real.pi / 8) =
                  Complex.exp (-(Complex.I * Real.pi / 8)) :=
    mul_left_cancel₀ h_factor h_at_0_1
  -- Contradiction with exp_I_pi_8_ne_exp_neg_I_pi_8.
  exact exp_I_pi_8_ne_exp_neg_I_pi_8 h_cancel

end SKEFTHawking.FKLW.GenericSU2
