/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-B.7.2 substantive discharge — `H_of_G readRezayiK7` is infinite

This module ships the **load-bearing infinite-order witness** for the
substantive discharge of `rr7_v4_witness_tracked` (defined in
`ReadRezayiK7ClosureDenseWitness.lean`): the product `H_SU · T_RR7` is
an SU(2) element of *infinite order*.

## Mathematical strategy

Same as Track T-B.5 (Read-Rezayi level 5), but at phase `π/18` and with
a CLEANER Niven obstruction via the *triple-angle* identity:
  - `2α = √2 · sin(π/18)` (the trace of `H_SU · T_RR7`).
  - `(2α)² = 2 · sin²(π/18) = 1 − cos(π/9)`.
  - If `cos(qπ) = α` for some `q ∈ ℚ`, then `2α` is integral over ℤ,
    hence `cos(π/9)` is integral.
  - Triple-angle: `cos(3·(π/9)) = cos(π/3) = 1/2`, so via
    `cos(3θ) = 4 cos³ θ − 3 cos θ`, we get
    `4 cos³(π/9) − 3 cos(π/9) = 1/2`.
  - If `cos(π/9) ∈ ℤ̄`, the LHS is integral (ℤ̄ closed under +, −, ×),
    so `1/2 ∈ ℤ̄`. But `1/2 ∈ ℚ`; by
    `IsIntegral.exists_int_iff_exists_rat`, `1/2 ∈ ℤ` — contradiction.

This is structurally cleaner than the k=5 Chebyshev-T_7 factoring
argument: at k=7 we use the standard triple-angle identity directly,
with no polynomial factoring required.

## Headline theorems

  * `α_RR7_ne_cos_rat_mul_pi` — Niven-style obstruction.
  * `lambda_RR7_not_root_of_unity` — eigenvalue not a root of unity.
  * `H_SU_mul_T_RR7_eigen` — eigenvector / eigenvalue equation.
  * `H_SU_mul_T_RR7_infinite_order` — `¬ IsOfFinOrder (H_SU * T_RR7)`.
  * `H_of_G_readRezayiK7_isInfinite` — closed subgroup is infinite.
  * `rr7_accPt_one_unconditional` — `AccPt 1 ...` (T-B.7.2 anchor).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
-/

import SKEFTHawking.FKLW.ReadRezayiK7GeneratingSet
import SKEFTHawking.FKLW.CliffordTGeneratingSet
import SKEFTHawking.FKLW.GenericSU2GeneratingSet
import SKEFTHawking.FKLW.FibRepInfiniteOrder
import SKEFTHawking.FKLW.AharonovAradLemma6
import Mathlib.NumberTheory.Niven

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix Complex Real
open SKEFTHawking.FKLW

/-! ## 1. The eigenvalue's real part `α_RR7` and the key identity
`(2α)² = 1 - cos(π/9)` -/

/-- The eigenvalue's real part: `α_RR7 := √2·sin(π/18)/2`. -/
noncomputable def α_RR7 : ℝ := Real.sqrt 2 * Real.sin (Real.pi / 18) / 2

/-- `(2·α_RR7)² = 2·sin²(π/18) = 1 - cos(π/9)`. -/
lemma two_alpha_RR7_sq_eq :
    (2 * α_RR7) ^ 2 = 1 - Real.cos (Real.pi / 9) := by
  unfold α_RR7
  have h_sq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h_sin_sq : Real.sin (Real.pi / 18) ^ 2 = 1/2 - Real.cos (2 * (Real.pi / 18)) / 2 :=
    Real.sin_sq_eq_half_sub _
  have h_2pi18 : 2 * (Real.pi / 18) = Real.pi / 9 := by ring
  rw [h_2pi18] at h_sin_sq
  have : (2 * (Real.sqrt 2 * Real.sin (Real.pi / 18) / 2)) ^ 2
        = Real.sqrt 2 ^ 2 * Real.sin (Real.pi / 18) ^ 2 := by ring
  rw [this, h_sq2, h_sin_sq]
  ring

/-! ## 2. The triple-angle cubic at `cos(π/9)`

From `cos(3·(π/9)) = cos(π/3) = 1/2` and the triple-angle identity
`cos(3θ) = 4 cos³ θ − 3 cos θ`, we get the clean cubic
`4 cos³(π/9) − 3 cos(π/9) = 1/2`. -/

/-- **The level-7 triple-angle cubic**:
`4 cos³(π/9) - 3 cos(π/9) = 1/2`. -/
lemma cos_pi_div_nine_triple_angle :
    4 * (Real.cos (Real.pi / 9))^3 - 3 * Real.cos (Real.pi / 9) = 1/2 := by
  have h_3angle : Real.cos (3 * (Real.pi / 9))
                = 4 * (Real.cos (Real.pi / 9))^3 - 3 * Real.cos (Real.pi / 9) :=
    Real.cos_three_mul _
  have h_simp : (3 : ℝ) * (Real.pi / 9) = Real.pi / 3 := by ring
  have h_cos_pi3 : Real.cos (Real.pi / 3) = 1/2 := Real.cos_pi_div_three
  rw [h_simp, h_cos_pi3] at h_3angle
  linarith

/-! ## 3. Algebraic-integer obstruction for `cos(qπ) = α_RR7`

If `cos(qπ) = α_RR7` for `q ∈ ℚ`, then `1/2 ∈ ℤ̄` — contradiction.

  - `2·cos(qπ)` integral (Niven).
  - `(2α_RR7)² = 1 - cos(π/9)` integral, so `cos(π/9)` integral.
  - Triple-angle: `4 cos³(π/9) - 3 cos(π/9) = 1/2`. LHS integral, so
    `1/2 ∈ ℤ̄`.
  - `1/2 ∈ ℚ` and `IsIntegral.exists_int_iff_exists_rat` ⟹ `1/2 ∈ ℤ`.
    Contradiction (`2k = 1` has no integer solution).
-/

/-- If `α_RR7 = cos(rπ)` for some `r ∈ ℚ`, we derive a contradiction. -/
lemma α_RR7_ne_cos_rat_mul_pi (r : ℚ) :
    Real.cos (r * Real.pi) ≠ α_RR7 := by
  intro h_eq
  have h_int_2cos : IsIntegral ℤ (2 * Real.cos (r * Real.pi)) :=
    Real.isIntegral_two_mul_cos_rat_mul_pi r
  rw [h_eq] at h_int_2cos
  have h_int_sq : IsIntegral ℤ ((2 * α_RR7) ^ 2) := by
    rw [sq]
    exact h_int_2cos.mul h_int_2cos
  have h_int_one : IsIntegral ℤ (1 : ℝ) := isIntegral_one
  have h_int_cos9 : IsIntegral ℤ (Real.cos (Real.pi / 9)) := by
    have h_eq2 : Real.cos (Real.pi / 9) = 1 - (2 * α_RR7) ^ 2 := by
      rw [two_alpha_RR7_sq_eq]; ring
    rw [h_eq2]
    exact h_int_one.sub h_int_sq
  -- 4·cos³ - 3·cos = 1/2 → 1/2 ∈ ℤ̄.
  have h_cubic := cos_pi_div_nine_triple_angle
  have h_int_four : IsIntegral ℤ (4 : ℝ) := by
    have : (4 : ℝ) = 1 + 1 + 1 + 1 := by norm_num
    rw [this]
    exact ((h_int_one.add h_int_one).add h_int_one).add h_int_one
  have h_int_three : IsIntegral ℤ (3 : ℝ) := by
    have : (3 : ℝ) = 1 + 1 + 1 := by norm_num
    rw [this]
    exact (h_int_one.add h_int_one).add h_int_one
  have h_int_cos9_cube : IsIntegral ℤ ((Real.cos (Real.pi / 9))^3) := by
    rw [show (Real.cos (Real.pi / 9))^3 = Real.cos (Real.pi / 9) * Real.cos (Real.pi / 9)
            * Real.cos (Real.pi / 9) from by ring]
    exact (h_int_cos9.mul h_int_cos9).mul h_int_cos9
  have h_int_combined : IsIntegral ℤ (4 * (Real.cos (Real.pi / 9))^3
                                      - 3 * Real.cos (Real.pi / 9)) :=
    (h_int_four.mul h_int_cos9_cube).sub (h_int_three.mul h_int_cos9)
  have h_int_half : IsIntegral ℤ ((1 : ℝ)/2) := by
    rw [show ((1 : ℝ)/2) = 4 * (Real.cos (Real.pi / 9))^3 - 3 * Real.cos (Real.pi / 9) from
      h_cubic.symm]
    exact h_int_combined
  have h_rat : ∃ q : ℚ, ((1 : ℝ)/2) = (q : ℝ) := by
    refine ⟨(1 : ℚ)/2, ?_⟩
    push_cast
    rfl
  have h_int : ∃ k : ℤ, ((1 : ℝ)/2) = (k : ℝ) :=
    (IsIntegral.exists_int_iff_exists_rat h_int_half).mp h_rat
  obtain ⟨k, hk⟩ := h_int
  have : (2 * k : ℝ) = 1 := by linarith
  have h_int_eq : (2 * k : ℤ) = 1 := by exact_mod_cast this
  omega

/-! ## 4. The eigenvalue `λ_RR7` and its non-root-of-unity property -/

/-- The phase θ_RR7 := arccos(α_RR7). Lies in [0, π]. -/
noncomputable def θ_RR7 : ℝ := Real.arccos α_RR7

lemma alpha_RR7_abs_le_one : |α_RR7| ≤ 1 := by
  have h := two_alpha_RR7_sq_eq
  have h_cos_le : Real.cos (Real.pi / 9) ≤ 1 := Real.cos_le_one _
  have h_cos_ge : -1 ≤ Real.cos (Real.pi / 9) := Real.neg_one_le_cos _
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (2 * α_RR7 + 2)]
  · nlinarith [sq_nonneg (2 * α_RR7 - 2)]

lemma cos_θ_RR7 : Real.cos θ_RR7 = α_RR7 := by
  unfold θ_RR7
  rw [Real.cos_arccos]
  · exact neg_le_of_abs_le alpha_RR7_abs_le_one
  · exact le_of_abs_le alpha_RR7_abs_le_one

/-- The eigenvalue `lam_RR7 := exp(I · θ_RR7)` for `M := H_SU·T_RR7`. -/
noncomputable def lam_RR7 : ℂ := Complex.exp ((θ_RR7 : ℂ) * Complex.I)

lemma lam_RR7_re : lam_RR7.re = α_RR7 := by
  unfold lam_RR7
  rw [Complex.exp_ofReal_mul_I_re]
  exact cos_θ_RR7

lemma lambda_RR7_sq :
    lam_RR7 ^ 2 = 2 * (α_RR7 : ℂ) * lam_RR7 - 1 := by
  have h_inv : lam_RR7⁻¹ = Complex.exp (-(θ_RR7 : ℂ) * Complex.I) := by
    unfold lam_RR7
    rw [← Complex.exp_neg]
    congr 1
    ring
  have h_sum : lam_RR7 + lam_RR7⁻¹ = 2 * (α_RR7 : ℂ) := by
    rw [h_inv]
    unfold lam_RR7
    rw [show (θ_RR7 : ℂ) * Complex.I = ((θ_RR7 : ℝ) : ℂ) * Complex.I from rfl]
    rw [show -(θ_RR7 : ℂ) * Complex.I = ((-θ_RR7 : ℝ) : ℂ) * Complex.I from by
          push_cast; ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    have h_cos_C : Complex.cos ((θ_RR7 : ℝ) : ℂ) = ((α_RR7 : ℝ) : ℂ) := by
      rw [show Complex.cos ((θ_RR7 : ℝ) : ℂ) = ((Real.cos θ_RR7 : ℝ) : ℂ) from
          (Complex.ofReal_cos _).symm]
      rw [cos_θ_RR7]
    rw [h_cos_C]
    ring
  have h_ne : lam_RR7 ≠ 0 := by unfold lam_RR7; exact Complex.exp_ne_zero _
  have h_step : (lam_RR7 + lam_RR7⁻¹) * lam_RR7 = 2 * (α_RR7 : ℂ) * lam_RR7 := by
    rw [h_sum]
  have h_expand : (lam_RR7 + lam_RR7⁻¹) * lam_RR7 = lam_RR7^2 + 1 := by
    field_simp
  rw [h_expand] at h_step
  linear_combination h_step

theorem lambda_RR7_not_root_of_unity :
    ∀ n : ℕ, 0 < n → lam_RR7 ^ n ≠ 1 := by
  intro n hn h_pow
  unfold lam_RR7 at h_pow
  rw [← Complex.exp_nat_mul] at h_pow
  rw [Complex.exp_eq_one_iff] at h_pow
  obtain ⟨k, hk⟩ := h_pow
  have h_I_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h_real_C : (n : ℂ) * (θ_RR7 : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ)) := by
    have hl : (n : ℂ) * ((θ_RR7 : ℂ) * Complex.I)
          = ((n : ℂ) * (θ_RR7 : ℂ)) * Complex.I := by ring
    have hr : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
          = ((k : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by ring
    rw [hl, hr] at hk
    exact mul_right_cancel₀ h_I_ne hk
  have h_real_R : (n : ℝ) * θ_RR7 = (k : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.re h_real_C
    simp at this
    exact this
  have hn_R_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_R_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_R_pos
  have h_theta : θ_RR7 = ((2 * k : ℝ) / (n : ℝ)) * Real.pi := by
    field_simp
    linarith
  let r : ℚ := (2 * k : ℤ) / (n : ℤ)
  apply α_RR7_ne_cos_rat_mul_pi r
  rw [show ((r : ℝ) * Real.pi) = θ_RR7 from ?_]
  · exact cos_θ_RR7
  · rw [h_theta]
    have : ((r : ℝ) : ℝ) = (2 * k : ℝ) / (n : ℝ) := by
      simp only [r]
      push_cast
      rfl
    rw [this]

/-! ## 5. Entries, trace, and determinant of `H_SU · T_RR7` -/

private lemma H_SU_T_RR7_apply_0_0 :
    (H_SU_mat * T_RR7_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
      = (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (-(Complex.I * Real.pi / 18)) := by
  simp [H_SU_mat, T_RR7_mat, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

private lemma H_SU_T_RR7_apply_1_0 :
    (H_SU_mat * T_RR7_mat) ⟨1, by decide⟩ ⟨0, by decide⟩
      = (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (-(Complex.I * Real.pi / 18)) := by
  simp [H_SU_mat, T_RR7_mat, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

private lemma H_SU_T_RR7_apply_1_1 :
    (H_SU_mat * T_RR7_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
      = -((Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (Complex.I * Real.pi / 18)) := by
  simp [H_SU_mat, T_RR7_mat, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

private lemma H_SU_T_RR7_apply_0_1 :
    (H_SU_mat * T_RR7_mat) ⟨0, by decide⟩ ⟨1, by decide⟩
      = (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (Complex.I * Real.pi / 18) := by
  simp [H_SU_mat, T_RR7_mat, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

private lemma H_SU_T_RR7_apply_0_1_ne_zero :
    (H_SU_mat * T_RR7_mat) ⟨0, by decide⟩ ⟨1, by decide⟩ ≠ 0 := by
  rw [H_SU_T_RR7_apply_0_1]
  apply mul_ne_zero
  · apply div_ne_zero
    · exact Complex.I_ne_zero
    · exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  · exact Complex.exp_ne_zero _

private lemma H_SU_T_RR7_trace_eq :
    (H_SU_mat * T_RR7_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
      + (H_SU_mat * T_RR7_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
      = (2 * α_RR7 : ℂ) := by
  rw [H_SU_T_RR7_apply_0_0, H_SU_T_RR7_apply_1_1]
  have h_expp : Complex.exp (Complex.I * (Real.pi : ℂ) / 18)
              = ((Real.cos (Real.pi / 18) : ℝ) : ℂ)
                + ((Real.sin (Real.pi / 18) : ℝ) : ℂ) * Complex.I := by
    rw [show Complex.I * (Real.pi : ℂ) / 18 = ((Real.pi / 18 : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have h_expn : Complex.exp (-(Complex.I * (Real.pi : ℂ) / 18))
              = ((Real.cos (Real.pi / 18) : ℝ) : ℂ)
                - ((Real.sin (Real.pi / 18) : ℝ) : ℂ) * Complex.I := by
    rw [show -(Complex.I * (Real.pi : ℂ) / 18) = ((-(Real.pi / 18) : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
    rw [Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h_expp, h_expn]
  have h_alpha_cast : ((α_RR7 : ℝ) : ℂ)
        = ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sin (Real.pi / 18) : ℝ) : ℂ) / 2 := by
    unfold α_RR7; push_cast; ring
  rw [h_alpha_cast]
  have h_sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (2 : ℂ) := by
    have : ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h_cast : (((Real.sqrt 2 : ℝ) ^ 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by
      push_cast; ring
    rw [← h_cast, this]; push_cast; rfl
  have h_sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  field_simp
  have h_I_sq : Complex.I * Complex.I = -1 := by
    have := Complex.I_sq; rw [sq] at this; exact this
  rw [h_sqrt2_sq]
  ring_nf
  linear_combination (norm := ring_nf)
    (-2 * ((Real.sin (Real.pi / 18) : ℝ) : ℂ)) * h_I_sq

private lemma H_SU_T_RR7_det_eq :
    (H_SU_mat * T_RR7_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
      * (H_SU_mat * T_RR7_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
    - (H_SU_mat * T_RR7_mat) ⟨0, by decide⟩ ⟨1, by decide⟩
      * (H_SU_mat * T_RR7_mat) ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 := by
  rw [H_SU_T_RR7_apply_0_0, H_SU_T_RR7_apply_0_1, H_SU_T_RR7_apply_1_0, H_SU_T_RR7_apply_1_1]
  have h_sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (2 : ℂ) := by
    have : ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h_cast : (((Real.sqrt 2 : ℝ) ^ 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by
      push_cast; ring
    rw [← h_cast, this]; push_cast; rfl
  have h_sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have h_exp_id : Complex.exp (-(Complex.I * (Real.pi : ℂ) / 18))
                * Complex.exp (Complex.I * (Real.pi : ℂ) / 18) = 1 := by
    rw [← Complex.exp_add]
    have h_zero : -(Complex.I * (Real.pi : ℂ) / 18) + Complex.I * (Real.pi : ℂ) / 18 = 0 := by
      ring
    rw [h_zero, Complex.exp_zero]
  have h_exp_id' : Complex.exp (Complex.I * (Real.pi : ℂ) / 18)
                * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 18)) = 1 := by
    rw [mul_comm]; exact h_exp_id
  have target_lhs :
      Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 18))
      * (-(Complex.I / ((Real.sqrt 2 : ℝ) : ℂ)
          * Complex.exp (Complex.I * (Real.pi : ℂ) / 18)))
      -
      (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 18))
      * (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 18)))
      = - (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ))^2
        * (Complex.exp (-(Complex.I * (Real.pi : ℂ) / 18))
          * Complex.exp (Complex.I * (Real.pi : ℂ) / 18))
        -
        (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ))^2
        * (Complex.exp (Complex.I * (Real.pi : ℂ) / 18)
          * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 18))) := by ring
  rw [target_lhs, h_exp_id, h_exp_id']
  rw [div_pow, show Complex.I ^ 2 = -1 from Complex.I_sq, h_sqrt2_sq]
  ring

/-! ## 6. Eigenvector for `H_SU · T_RR7` and infinite-order witness -/

noncomputable def v_RR7 : Fin 2 → ℂ := fun j =>
  if j = (0 : Fin 2) then (H_SU.val * T_RR7.val) ⟨0, by decide⟩ ⟨1, by decide⟩
  else lam_RR7 - (H_SU.val * T_RR7.val) ⟨0, by decide⟩ ⟨0, by decide⟩

private lemma v_RR7_apply_0 :
    v_RR7 (0 : Fin 2) = (H_SU.val * T_RR7.val) ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  simp [v_RR7]

private lemma v_RR7_apply_1 :
    v_RR7 (1 : Fin 2) = lam_RR7 - (H_SU.val * T_RR7.val) ⟨0, by decide⟩ ⟨0, by decide⟩ := by
  simp [v_RR7]

lemma v_RR7_ne_zero : v_RR7 ≠ 0 := by
  intro h
  have h0 := congr_fun h (0 : Fin 2)
  rw [v_RR7_apply_0] at h0
  apply H_SU_T_RR7_apply_0_1_ne_zero
  show (H_SU_mat * T_RR7_mat) ⟨0, by decide⟩ ⟨1, by decide⟩ = 0
  exact h0

theorem H_SU_mul_T_RR7_eigen :
    (H_SU.val * T_RR7.val : Matrix (Fin 2) (Fin 2) ℂ).mulVec v_RR7
      = lam_RR7 • v_RR7 := by
  set a := (H_SU.val * T_RR7.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨0, by decide⟩ ⟨0, by decide⟩ with ha
  set b := (H_SU.val * T_RR7.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨0, by decide⟩ ⟨1, by decide⟩ with hb
  set c := (H_SU.val * T_RR7.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨1, by decide⟩ ⟨0, by decide⟩ with hc
  set d := (H_SU.val * T_RR7.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨1, by decide⟩ ⟨1, by decide⟩ with hd
  have h_tr : a + d = (2 * α_RR7 : ℂ) := by
    show (H_SU_mat * T_RR7_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
        + (H_SU_mat * T_RR7_mat) ⟨1, by decide⟩ ⟨1, by decide⟩ = (2 * α_RR7 : ℂ)
    exact H_SU_T_RR7_trace_eq
  have h_det : a * d - b * c = 1 := by
    show (H_SU_mat * T_RR7_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
       * (H_SU_mat * T_RR7_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
       - (H_SU_mat * T_RR7_mat) ⟨0, by decide⟩ ⟨1, by decide⟩
       * (H_SU_mat * T_RR7_mat) ⟨1, by decide⟩ ⟨0, by decide⟩ = 1
    exact H_SU_T_RR7_det_eq
  have h_char : lam_RR7 ^ 2 = (a + d) * lam_RR7 - 1 := by
    rw [h_tr]
    exact lambda_RR7_sq
  ext i
  fin_cases i
  · show (H_SU.val * T_RR7.val : Matrix (Fin 2) (Fin 2) ℂ).mulVec v_RR7 (0 : Fin 2)
        = (lam_RR7 • v_RR7) (0 : Fin 2)
    rw [Matrix.mulVec, Matrix.vec2_dotProduct, v_RR7_apply_0, v_RR7_apply_1]
    show a * b + b * (lam_RR7 - a) = (lam_RR7 • v_RR7) (0 : Fin 2)
    rw [Pi.smul_apply, smul_eq_mul, v_RR7_apply_0]
    show a * b + b * (lam_RR7 - a) = lam_RR7 * b
    ring
  · show (H_SU.val * T_RR7.val : Matrix (Fin 2) (Fin 2) ℂ).mulVec v_RR7 (1 : Fin 2)
        = (lam_RR7 • v_RR7) (1 : Fin 2)
    rw [Matrix.mulVec, Matrix.vec2_dotProduct, v_RR7_apply_0, v_RR7_apply_1]
    show c * b + d * (lam_RR7 - a) = (lam_RR7 • v_RR7) (1 : Fin 2)
    rw [Pi.smul_apply, smul_eq_mul, v_RR7_apply_1]
    show c * b + d * (lam_RR7 - a) = lam_RR7 * (lam_RR7 - a)
    have h_char' : lam_RR7^2 - a*lam_RR7 - d*lam_RR7 + 1 = 0 := by
      rw [h_char]; ring
    have h_bc : c * b - a * d = -1 := by linear_combination -h_det
    linear_combination -h_char' + h_bc

theorem H_SU_mul_T_RR7_infinite_order :
    ¬ IsOfFinOrder (H_SU * T_RR7) := by
  apply not_finOrder_of_eigenvalue_not_rootOfUnity
    (H_SU * T_RR7) v_RR7 v_RR7_ne_zero lam_RR7
  · show ((H_SU * T_RR7 : Matrix.specialUnitaryGroup (Fin 2) ℂ).val).mulVec v_RR7
        = lam_RR7 • v_RR7
    have h_coe : ((H_SU * T_RR7 : Matrix.specialUnitaryGroup (Fin 2) ℂ).val
                : Matrix (Fin 2) (Fin 2) ℂ) = H_SU.val * T_RR7.val := rfl
    rw [h_coe]
    exact H_SU_mul_T_RR7_eigen
  · exact lambda_RR7_not_root_of_unity

/-! ## 7. Lift to `H_of_G readRezayiK7GeneratingSet` -/

theorem H_SU_mul_T_RR7_pow_injective :
    Function.Injective (fun n : ℕ => (H_SU * T_RR7) ^ n) :=
  injective_pow_iff_not_isOfFinOrder.mpr H_SU_mul_T_RR7_infinite_order

theorem H_SU_mul_T_RR7_pow_range_infinite :
    (Set.range (fun n : ℕ => (H_SU * T_RR7) ^ n)).Infinite := by
  exact Set.infinite_range_of_injective H_SU_mul_T_RR7_pow_injective

/-- **Headline: `H_of_G readRezayiK7GeneratingSet` is infinite (as a set).** -/
theorem H_of_G_readRezayiK7_isInfinite :
    (H_of_G readRezayiK7GeneratingSet
      : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).Infinite := by
  apply Set.Infinite.mono _ H_SU_mul_T_RR7_pow_range_infinite
  rintro _ ⟨n, rfl⟩
  exact (H_of_G readRezayiK7GeneratingSet).pow_mem
    ((H_of_G readRezayiK7GeneratingSet).mul_mem
      H_SU_mem_H_of_G_RR7 T_RR7_mem_H_of_G_RR7) n

/-! ## 8. The T-B.7.2 headline: accumulation at the identity -/

/-- **HEADLINE: `1` is an accumulation point of `H_of_G readRezayiK7`.** -/
theorem rr7_accPt_one_unconditional :
    AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (Filter.principal (H_of_G readRezayiK7GeneratingSet : Set _)) :=
  one_accPt_of_infinite_closed_subgroup
    (H_of_G readRezayiK7GeneratingSet)
    (H_of_G_isClosed readRezayiK7GeneratingSet)
    H_of_G_readRezayiK7_isInfinite

end SKEFTHawking.FKLW.GenericSU2
