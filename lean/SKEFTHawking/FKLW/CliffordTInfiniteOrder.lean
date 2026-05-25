/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Track T-S.2 substantive discharge — `H_of_G cliffordT` is infinite

This module ships the **load-bearing infinite-order witness** for the
substantive discharge of `cliffordT_v4_witness_tracked`: the product
`H_SU · T_SU` is an SU(2) element of *infinite order*.

## Mathematical strategy

The eigenvalues of `M := H_SU · T_SU` are `λ, λ̄` on the unit circle, with
`λ + λ̄ = tr(M) = √2 · sin(π/8)` (real). So writing `λ = α + i·β`,
  α = (√2 · sin(π/8)) / 2  (so 2α = tr M)
  β = √(1 - α²)              (since |λ| = 1 ⟹ α² + β² = 1)

We show `λ^n ≠ 1` for all `n ≥ 1`:

1. If `λ^n = 1`, then `λ` is an n-th root of unity, so `λ = exp(2πI · k/n)`
   for some integer `k`. Hence `α = Re(λ) = cos(2π · k/n) = cos(r·π)`
   where `r := 2k/n ∈ ℚ`.

2. By `Real.isIntegral_two_mul_cos_rat_mul_pi`, `2·cos(rπ) = 2α = √2·sin(π/8)`
   is an algebraic integer over ℤ. So is its square `(2α)² = 2·sin²(π/8)`.

3. By the half-angle identity, `2·sin²(π/8) = 1 - cos(π/4) = 1 - √2/2`.
   So `√2/2 = 1 - (2α)²` is also an algebraic integer (closed under
   ring operations in ℤ-algebra).

4. So `(√2/2)² = 1/2` is an algebraic integer. But `1/2` is a rational
   number, so by `IsIntegral.exists_int_iff_exists_rat`, it must be an
   integer — contradicting `1/2 ∉ ℤ`. QED.

Then `H_SU · T_SU` has infinite order via
`not_finOrder_of_eigenvalue_not_rootOfUnity` (alphabet-agnostic substrate
in `FibRepInfiniteOrder.lean`), pushing through to:
  - `H_of_G_cliffordT_isInfinite : (H_of_G cliffordTGeneratingSet).Infinite`
  - `cliffordT_accPt_one_unconditional : AccPt 1 (Filter.principal ...)`

The latter is the headline consumed by the T-S.2 discharge.

## Headline theorems

  * `cliffordT_M_trace_eq` — `tr (H_SU · T_SU) = √2 · sin(π/8)`
  * `H_SU_mul_T_SU_eigenvalue_exists` — explicit eigenvector witness
  * `H_SU_mul_T_SU_infinite_order` — `¬ IsOfFinOrder (H_SU * T_SU)`
  * `H_SU_mul_T_SU_pow_injective` — `(H·T)^n` injective in n
  * `H_of_G_cliffordT_isInfinite` — the closed subgroup is infinite
  * `cliffordT_accPt_one_unconditional` — `AccPt 1 ...` (the T-S.2 anchor)

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
-/

import SKEFTHawking.FKLW.CliffordTGeneratingSet
import SKEFTHawking.FKLW.CliffordTNonCommuting
import SKEFTHawking.FKLW.GenericSU2GeneratingSet
import SKEFTHawking.FKLW.FibRepInfiniteOrder
import SKEFTHawking.FKLW.AharonovAradLemma6
import Mathlib.NumberTheory.Niven

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix Complex Real
open SKEFTHawking.FKLW

/-! ## 1. The eigenvalue and its key identity `(2α)² = 1 - √2/2`

`α := √2·sin(π/8)/2 = cos θ` is the real part of the SU(2)-eigenvalue
of `H_SU · T_SU`. We need two algebraic facts:

  * `two_alpha_sq_eq` : `(2α)² = 1 - √2/2`
  * `alpha_lt_one` : `α < 1` (so β = √(1-α²) > 0; eigenvalue is non-real)
-/

/-- The eigenvalue's real part: `α := √2·sin(π/8)/2`. -/
noncomputable def α_HT : ℝ := Real.sqrt 2 * Real.sin (Real.pi / 8) / 2

/-- `(2α)² = 2·sin²(π/8) = 1 - √2/2`. -/
lemma two_alpha_sq_eq :
    (2 * α_HT) ^ 2 = 1 - Real.sqrt 2 / 2 := by
  unfold α_HT
  have h_sq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h_sin_sq : Real.sin (Real.pi / 8) ^ 2 = 1/2 - Real.cos (2 * (Real.pi / 8)) / 2 :=
    Real.sin_sq_eq_half_sub _
  have h_2pi8 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
  rw [h_2pi8, Real.cos_pi_div_four] at h_sin_sq
  have : (2 * (Real.sqrt 2 * Real.sin (Real.pi / 8) / 2)) ^ 2
        = Real.sqrt 2 ^ 2 * Real.sin (Real.pi / 8) ^ 2 := by ring
  rw [this, h_sq2, h_sin_sq]
  ring

/-! ## 2. Algebraic-integer obstruction for `cos(qπ) = α`

The core arithmetic lemma: if `cos(qπ) = α` for `q ∈ ℚ`, then `1/2` is
an algebraic integer (contradiction). Proof:
  - `2·cos(qπ)` is integral over ℤ (Niven substrate).
  - `(2·cos(qπ))² = (2α)² = 1 - √2/2`.
  - So `√2/2 = 1 - (2·cos(qπ))²` is integral over ℤ (ℤ-algebra closure).
  - So `(√2/2)² = 1/2` is integral over ℤ.
  - But `1/2 : ℝ` is rational; integral rational ⟹ integer. Contradiction.
-/

/-- If `α = cos(rπ)` for some `r ∈ ℚ`, we derive a contradiction. -/
lemma alpha_ne_cos_rat_mul_pi (r : ℚ) :
    Real.cos (r * Real.pi) ≠ α_HT := by
  intro h_eq
  -- `2 · cos(rπ)` is integral over ℤ.
  have h_int_2cos : IsIntegral ℤ (2 * Real.cos (r * Real.pi)) :=
    Real.isIntegral_two_mul_cos_rat_mul_pi r
  -- Rewrite using α_HT = cos(rπ).
  rw [h_eq] at h_int_2cos
  -- (2α)² is integral.
  have h_int_sq : IsIntegral ℤ ((2 * α_HT) ^ 2) := by
    rw [sq]
    exact h_int_2cos.mul h_int_2cos
  -- 1 is integral.
  have h_int_one : IsIntegral ℤ (1 : ℝ) := isIntegral_one
  -- (2α)² = 1 - √2/2, so √2/2 = 1 - (2α)². Hence √2/2 is integral.
  have h_int_sqrt2_div_2 : IsIntegral ℤ (Real.sqrt 2 / 2) := by
    have h_eq2 : Real.sqrt 2 / 2 = 1 - (2 * α_HT) ^ 2 := by
      rw [two_alpha_sq_eq]; ring
    rw [h_eq2]
    exact h_int_one.sub h_int_sq
  -- (√2/2)² = 1/2 is integral.
  have h_int_half : IsIntegral ℤ ((1 : ℝ) / 2) := by
    have h_sq : ((1 : ℝ) / 2) = (Real.sqrt 2 / 2) ^ 2 := by
      rw [div_pow]
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [h_sq, sq]
    exact h_int_sqrt2_div_2.mul h_int_sqrt2_div_2
  -- But 1/2 = (1/2 : ℚ) cast to ℝ. So 1/2 is "rational" as a real.
  have h_rat : ∃ q : ℚ, ((1 : ℝ) / 2) = (q : ℝ) := by
    refine ⟨(1 : ℚ) / 2, ?_⟩
    push_cast
    rfl
  -- An algebraic-integer rational is an integer.
  have h_int : ∃ k : ℤ, ((1 : ℝ) / 2) = (k : ℝ) :=
    (IsIntegral.exists_int_iff_exists_rat h_int_half).mp h_rat
  -- Contradiction: 1/2 is not an integer.
  obtain ⟨k, hk⟩ := h_int
  have : (2 * k : ℝ) = 1 := by linarith
  -- 2k = 1 in ℝ; cast back to ℤ.
  have h_int_eq : (2 * k : ℤ) = 1 := by exact_mod_cast this
  -- 2k = 1 has no integer solutions.
  omega

/-! ## 3. The eigenvalue `λ` and its non-root-of-unity property

Define θ := arccos(α). Then 0 ≤ θ ≤ π and we set `lam_HT := exp(I·θ)`.
We show `lam_HT^n ≠ 1` for `n ≥ 1` via the algebraic-integer
obstruction (Section 2). -/

/-- The phase θ := arccos(α). Lies in [0, π]. -/
noncomputable def θ_HT : ℝ := Real.arccos α_HT

/-- We need `α ∈ [-1, 1]` to apply `Real.cos_arccos`. -/
lemma alpha_HT_abs_le_one : |α_HT| ≤ 1 := by
  -- (2α)² = 1 - √2/2 ∈ (0, 1], so α² ≤ 1/4 < 1, so |α| ≤ 1/2 < 1.
  have h := two_alpha_sq_eq
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (2 * α_HT + 2), sq_nonneg α_HT]
  · nlinarith [sq_nonneg (2 * α_HT - 2), sq_nonneg α_HT]

/-- `cos θ_HT = α_HT`. -/
lemma cos_θ_HT : Real.cos θ_HT = α_HT := by
  unfold θ_HT
  rw [Real.cos_arccos]
  · exact (neg_le_of_abs_le alpha_HT_abs_le_one)
  · exact (le_of_abs_le alpha_HT_abs_le_one)

/-- The eigenvalue `lam_HT := exp(I · θ)` for `M := H_SU·T_SU`. -/
noncomputable def lam_HT : ℂ := Complex.exp ((θ_HT : ℂ) * Complex.I)

/-- `Re(lam_HT) = cos(θ_HT) = α_HT`. -/
lemma lam_HT_re : lam_HT.re = α_HT := by
  unfold lam_HT
  rw [Complex.exp_ofReal_mul_I_re]
  exact cos_θ_HT

/-- Characteristic-polynomial relation: `lam_HT² = 2·α_HT·lam_HT - 1`.

Proof: write `lam_HT = exp(iθ)`. Then `lam_HT⁻¹ = exp(-iθ)`, and
`lam_HT + lam_HT⁻¹ = 2·cos(θ) = 2·α_HT`. So `lam_HT² - 2α·lam_HT + 1
= lam_HT·(lam_HT - 2α + lam_HT⁻¹) = lam_HT·0 = 0`. -/
lemma lambda_HT_sq :
    lam_HT ^ 2 = 2 * (α_HT : ℂ) * lam_HT - 1 := by
  -- lam_HT⁻¹ = exp(-iθ); lam_HT + lam_HT⁻¹ = 2cos(θ) = 2α
  have h_inv : lam_HT⁻¹ = Complex.exp (-(θ_HT : ℂ) * Complex.I) := by
    unfold lam_HT
    rw [← Complex.exp_neg]
    congr 1
    ring
  have h_sum : lam_HT + lam_HT⁻¹ = 2 * (α_HT : ℂ) := by
    rw [h_inv]
    unfold lam_HT
    -- exp(iθ) + exp(-iθ) = 2·cos(θ)
    rw [show (θ_HT : ℂ) * Complex.I = ((θ_HT : ℝ) : ℂ) * Complex.I from rfl]
    rw [show -(θ_HT : ℂ) * Complex.I = ((-θ_HT : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    -- Goal: cos(θ) + i·sin(θ) + (cos(θ) - i·sin(θ)) = 2α  (in ℂ)
    -- Use cos_θ_HT : Real.cos θ_HT = α_HT, lifted to ℂ.
    have h_cos_C : Complex.cos ((θ_HT : ℝ) : ℂ) = ((α_HT : ℝ) : ℂ) := by
      rw [show Complex.cos ((θ_HT : ℝ) : ℂ) = ((Real.cos θ_HT : ℝ) : ℂ) from (Complex.ofReal_cos _).symm]
      rw [cos_θ_HT]
    rw [h_cos_C]
    ring
  -- lam_HT ≠ 0 (it's an exp)
  have h_ne : lam_HT ≠ 0 := by unfold lam_HT; exact Complex.exp_ne_zero _
  -- (lam_HT + lam_HT⁻¹) · lam_HT = 2α · lam_HT
  -- lam_HT² + 1 = 2α · lam_HT
  -- lam_HT² = 2α · lam_HT - 1 ✓
  have h_step : (lam_HT + lam_HT⁻¹) * lam_HT = 2 * (α_HT : ℂ) * lam_HT := by
    rw [h_sum]
  have h_expand : (lam_HT + lam_HT⁻¹) * lam_HT = lam_HT^2 + 1 := by
    field_simp
  rw [h_expand] at h_step
  linear_combination h_step

/-- **The eigenvalue λ is not a root of unity.**

If `λ^n = 1` for some `n ≥ 1`, then by `Complex.exp_eq_one_iff`,
`n · I · θ = 2πI · k` for some integer `k`. So `θ = 2πk/n`, hence
`α = cos(θ) = cos(rπ)` for `r := 2k/n ∈ ℚ`. This contradicts
`alpha_ne_cos_rat_mul_pi`. -/
theorem lambda_HT_not_root_of_unity :
    ∀ n : ℕ, 0 < n → lam_HT ^ n ≠ 1 := by
  intro n hn h_pow
  -- lam_HT^n = exp(n · I · θ_HT) = 1 ⟹ n·I·θ = 2πI·k for some k ∈ ℤ
  unfold lam_HT at h_pow
  rw [← Complex.exp_nat_mul] at h_pow
  rw [Complex.exp_eq_one_iff] at h_pow
  obtain ⟨k, hk⟩ := h_pow
  -- hk : (n : ℂ) * ((θ_HT : ℂ) * Complex.I) = (k : ℂ) * (2 * π * Complex.I)
  -- Cancel I and convert to ℝ: n·θ = 2πk
  have h_I_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h_real_C : (n : ℂ) * (θ_HT : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ)) := by
    have hl : (n : ℂ) * ((θ_HT : ℂ) * Complex.I)
          = ((n : ℂ) * (θ_HT : ℂ)) * Complex.I := by ring
    have hr : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
          = ((k : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by ring
    rw [hl, hr] at hk
    exact mul_right_cancel₀ h_I_ne hk
  have h_real_R : (n : ℝ) * θ_HT = (k : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.re h_real_C
    simp at this
    exact this
  -- Solve: θ_HT = (2k/n) · π = r·π for r := (2k : ℚ) / (n : ℚ)
  have hn_R_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_R_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_R_pos
  have h_theta : θ_HT = ((2 * k : ℝ) / (n : ℝ)) * Real.pi := by
    field_simp
    linarith
  -- Define r := (2k : ℚ) / (n : ℚ). Then (r : ℝ) = (2k : ℝ)/(n : ℝ).
  let r : ℚ := (2 * k : ℤ) / (n : ℤ)
  -- Need: cos(r·π) = α_HT, contradicting alpha_ne_cos_rat_mul_pi.
  -- cos(θ_HT) = α_HT (cos_θ_HT). Also θ_HT = ((2k/n) : ℝ)·π.
  -- And ((2k/n : ℚ) : ℝ) = (2k : ℝ)/(n : ℝ) via push_cast.
  apply alpha_ne_cos_rat_mul_pi r
  rw [show ((r : ℝ) * Real.pi) = θ_HT from ?_]
  · exact cos_θ_HT
  · rw [h_theta]
    have : ((r : ℝ) : ℝ) = (2 * k : ℝ) / (n : ℝ) := by
      simp only [r]
      push_cast
      rfl
    rw [this]

/-! ## 4. Trace and determinant of `H_SU · T_SU`

`H_SU · T_SU` has trace `2α_HT = √2·sin(π/8)` and determinant 1 (it's in
SU(2)). These two facts plus the characteristic-polynomial identity
`lam_HT² - 2α·lam_HT + 1 = 0` will discharge the eigenvalue equation. -/

/-- The `(0,0)` entry of `H_SU · T_SU`. -/
private lemma H_SU_T_SU_apply_0_0 :
    (H_SU_mat * T_SU_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
      = (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (-(Complex.I * Real.pi / 8)) := by
  simp [H_SU_mat, T_SU_mat, Matrix.mul_apply, Fin.sum_univ_two,
        smul_eq_mul]

/-- The `(1,0)` entry of `H_SU · T_SU`. -/
private lemma H_SU_T_SU_apply_1_0 :
    (H_SU_mat * T_SU_mat) ⟨1, by decide⟩ ⟨0, by decide⟩
      = (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (-(Complex.I * Real.pi / 8)) := by
  simp [H_SU_mat, T_SU_mat, Matrix.mul_apply, Fin.sum_univ_two,
        smul_eq_mul]

/-- The `(1,1)` entry of `H_SU · T_SU`. -/
private lemma H_SU_T_SU_apply_1_1 :
    (H_SU_mat * T_SU_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
      = -((Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (Complex.I * Real.pi / 8)) := by
  simp [H_SU_mat, T_SU_mat, Matrix.mul_apply, Fin.sum_univ_two,
        smul_eq_mul]

/-- The `(0,1)` entry of `H_SU · T_SU` (re-stated public from `CliffordTNonCommuting`). -/
private lemma H_SU_T_SU_apply_0_1_pub :
    (H_SU_mat * T_SU_mat) ⟨0, by decide⟩ ⟨1, by decide⟩
      = (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (Complex.I * Real.pi / 8) := by
  simp [H_SU_mat, T_SU_mat, Matrix.mul_apply, Fin.sum_univ_two,
        smul_eq_mul]

/-- The `(0,1)` entry of `H_SU·T_SU` is nonzero (factor `i/√2` and `exp(...)`). -/
private lemma H_SU_T_SU_apply_0_1_ne_zero :
    (H_SU_mat * T_SU_mat) ⟨0, by decide⟩ ⟨1, by decide⟩ ≠ 0 := by
  rw [H_SU_T_SU_apply_0_1_pub]
  apply mul_ne_zero
  · apply div_ne_zero
    · exact Complex.I_ne_zero
    · exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  · exact Complex.exp_ne_zero _

/-- Trace of `H_SU·T_SU` as a complex number: `2·α_HT`. -/
private lemma H_SU_T_SU_trace_eq :
    (H_SU_mat * T_SU_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
      + (H_SU_mat * T_SU_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
      = (2 * α_HT : ℂ) := by
  rw [H_SU_T_SU_apply_0_0, H_SU_T_SU_apply_1_1]
  -- exp(iπ/8) = cos(π/8) + i·sin(π/8); exp(-iπ/8) = cos(π/8) - i·sin(π/8).
  -- Use Real.sin variant via Complex.ofReal_sin to make rewriting clean.
  have h_expp : Complex.exp (Complex.I * (Real.pi : ℂ) / 8)
              = ((Real.cos (Real.pi / 8) : ℝ) : ℂ) + ((Real.sin (Real.pi / 8) : ℝ) : ℂ) * Complex.I := by
    rw [show Complex.I * (Real.pi : ℂ) / 8 = ((Real.pi / 8 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have h_expn : Complex.exp (-(Complex.I * (Real.pi : ℂ) / 8))
              = ((Real.cos (Real.pi / 8) : ℝ) : ℂ) - ((Real.sin (Real.pi / 8) : ℝ) : ℂ) * Complex.I := by
    rw [show -(Complex.I * (Real.pi : ℂ) / 8) = ((-(Real.pi / 8) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h_expp, h_expn]
  -- Now both sides are in terms of Real.cos/sin lifted to ℂ.
  -- α_HT = √2 · sin(π/8) / 2 (real); cast to ℂ.
  have h_alpha_cast : ((α_HT : ℝ) : ℂ)
        = ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sin (Real.pi / 8) : ℝ) : ℂ) / 2 := by
    unfold α_HT; push_cast; ring
  rw [h_alpha_cast]
  -- (i/√2) · (cos - i·sin) - (i/√2) · (cos + i·sin) = (i/√2) · (-2i·sin) = (2/√2)·sin = √2·sin
  have h_sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (2 : ℂ) := by
    have : ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h_cast : (((Real.sqrt 2 : ℝ) ^ 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by push_cast; ring
    rw [← h_cast, this]
    push_cast
    rfl
  have h_sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  -- Final algebraic manipulation. After clearing 1/√2 denominators, the
  -- remaining identity uses Complex.I^2 = -1 plus √2² = 2.
  field_simp
  -- After field_simp, goal contains both ↑√2^2 and I*I (= I^2). Substitute both:
  have h_I_sq : Complex.I * Complex.I = -1 := by
    have := Complex.I_sq; rw [sq] at this; exact this
  -- Rewrite ↑√2^2 directly first (as it appears as a multiplicative factor).
  rw [h_sqrt2_sq]
  ring_nf
  -- Now substitute I*I = -1.
  linear_combination (norm := ring_nf)
    (-2 * ((Real.sin (Real.pi / 8) : ℝ) : ℂ)) * h_I_sq

/-- Determinant of `H_SU·T_SU` is 1 (since `H_SU * T_SU ∈ SU(2)`).
This is the "off-diagonal product" identity: M(0,0)·M(1,1) - M(0,1)·M(1,0) = 1. -/
private lemma H_SU_T_SU_det_eq :
    (H_SU_mat * T_SU_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
      * (H_SU_mat * T_SU_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
    - (H_SU_mat * T_SU_mat) ⟨0, by decide⟩ ⟨1, by decide⟩
      * (H_SU_mat * T_SU_mat) ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 := by
  rw [H_SU_T_SU_apply_0_0, H_SU_T_SU_apply_0_1_pub, H_SU_T_SU_apply_1_0, H_SU_T_SU_apply_1_1]
  -- = (i/√2)·e^{-iπ/8} · -(i/√2)·e^{iπ/8} - (i/√2)·e^{iπ/8} · (i/√2)·e^{-iπ/8}
  -- = -(i²/2)·e^0 - (i²/2)·e^0 = -(-1/2) - (-1/2) = 1/2 + 1/2 = 1
  have h_sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (2 : ℂ) := by
    have : ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h_cast : (((Real.sqrt 2 : ℝ) ^ 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by push_cast; ring
    rw [← h_cast, this]
    push_cast
    rfl
  have h_sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have h_exp_id : Complex.exp (-(Complex.I * (Real.pi : ℂ) / 8))
                * Complex.exp (Complex.I * (Real.pi : ℂ) / 8) = 1 := by
    rw [← Complex.exp_add]
    have h_zero : -(Complex.I * (Real.pi : ℂ) / 8) + Complex.I * (Real.pi : ℂ) / 8 = 0 := by ring
    rw [h_zero, Complex.exp_zero]
  have h_exp_id' : Complex.exp (Complex.I * (Real.pi : ℂ) / 8)
                * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 8)) = 1 := by
    rw [mul_comm]
    exact h_exp_id
  -- Compute by ring + h_exp_id and h_sqrt2_sq.
  have target_lhs :
      Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 8))
      * (-(Complex.I / ((Real.sqrt 2 : ℝ) : ℂ)
          * Complex.exp (Complex.I * (Real.pi : ℂ) / 8)))
      -
      (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 8))
      * (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 8)))
      = - (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ))^2
        * (Complex.exp (-(Complex.I * (Real.pi : ℂ) / 8))
          * Complex.exp (Complex.I * (Real.pi : ℂ) / 8))
        -
        (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ))^2
        * (Complex.exp (Complex.I * (Real.pi : ℂ) / 8)
          * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 8))) := by ring
  rw [target_lhs, h_exp_id, h_exp_id']
  -- Goal: -(I / √2)² · 1 - (I / √2)² · 1 = 1
  -- (I/√2)² = -1/2; -(-1/2) - (-1/2) = 1/2 + 1/2 = 1
  rw [div_pow, show Complex.I ^ 2 = -1 from Complex.I_sq, h_sqrt2_sq]
  ring

/-! ## 5. Eigenvector for `H_SU · T_SU` and infinite-order witness

The eigenvector `v := (M(0,1), λ - M(0,0))` works: by characteristic-
polynomial calculation, this satisfies `M · v = λ · v`. -/

/-- The eigenvector for `M := H_SU·T_SU` at eigenvalue `lam_HT`. -/
noncomputable def v_HT : Fin 2 → ℂ := fun j =>
  if j = (0 : Fin 2) then (H_SU.val * T_SU.val) ⟨0, by decide⟩ ⟨1, by decide⟩
  else lam_HT - (H_SU.val * T_SU.val) ⟨0, by decide⟩ ⟨0, by decide⟩

/-- `v_HT (0 : Fin 2) = M(0,1)`. -/
private lemma v_HT_apply_0 :
    v_HT (0 : Fin 2) = (H_SU.val * T_SU.val) ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  simp [v_HT]

/-- `v_HT (1 : Fin 2) = lam_HT - M(0,0)`. -/
private lemma v_HT_apply_1 :
    v_HT (1 : Fin 2) = lam_HT - (H_SU.val * T_SU.val) ⟨0, by decide⟩ ⟨0, by decide⟩ := by
  simp [v_HT]

lemma v_HT_ne_zero : v_HT ≠ 0 := by
  intro h
  have h0 := congr_fun h (0 : Fin 2)
  rw [v_HT_apply_0] at h0
  apply H_SU_T_SU_apply_0_1_ne_zero
  -- h0 : (H_SU.val * T_SU.val) ⟨0⟩ ⟨1⟩ = 0
  -- Need to match concrete form (H_SU_mat * T_SU_mat).
  show (H_SU_mat * T_SU_mat) ⟨0, by decide⟩ ⟨1, by decide⟩ = 0
  -- H_SU.val = H_SU_mat, T_SU.val = T_SU_mat by definition.
  exact h0

/-- The eigenvalue equation `M · v = λ · v` for `M := H_SU·T_SU` and
`v := v_HT`. Proved by direct entrywise calculation using the trace
formula `tr M = 2α`, the det-1 identity, and the characteristic-poly
relation `lam_HT² - 2α·lam_HT + 1 = 0`. -/
theorem H_SU_mul_T_SU_eigen :
    (H_SU.val * T_SU.val : Matrix (Fin 2) (Fin 2) ℂ).mulVec v_HT
      = lam_HT • v_HT := by
  -- Abbreviations.
  set a := (H_SU.val * T_SU.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨0, by decide⟩ ⟨0, by decide⟩ with ha
  set b := (H_SU.val * T_SU.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨0, by decide⟩ ⟨1, by decide⟩ with hb
  set c := (H_SU.val * T_SU.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨1, by decide⟩ ⟨0, by decide⟩ with hc
  set d := (H_SU.val * T_SU.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨1, by decide⟩ ⟨1, by decide⟩ with hd
  have h_tr : a + d = (2 * α_HT : ℂ) := by
    show (H_SU_mat * T_SU_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
        + (H_SU_mat * T_SU_mat) ⟨1, by decide⟩ ⟨1, by decide⟩ = (2 * α_HT : ℂ)
    exact H_SU_T_SU_trace_eq
  have h_det : a * d - b * c = 1 := by
    show (H_SU_mat * T_SU_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
       * (H_SU_mat * T_SU_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
       - (H_SU_mat * T_SU_mat) ⟨0, by decide⟩ ⟨1, by decide⟩
       * (H_SU_mat * T_SU_mat) ⟨1, by decide⟩ ⟨0, by decide⟩ = 1
    exact H_SU_T_SU_det_eq
  have h_char : lam_HT ^ 2 = (a + d) * lam_HT - 1 := by
    rw [h_tr]
    -- Characteristic-poly identity: lam_HT² = 2α·lam_HT - 1.
    exact lambda_HT_sq
  -- Verify entrywise.
  ext i
  fin_cases i
  · -- Row 0: M(0,0)·v(0) + M(0,1)·v(1) = lam_HT·v(0)
    --      = a·b + b·(lam_HT - a) = b·lam_HT.
    show (H_SU.val * T_SU.val : Matrix (Fin 2) (Fin 2) ℂ).mulVec v_HT (0 : Fin 2)
        = (lam_HT • v_HT) (0 : Fin 2)
    rw [Matrix.mulVec, Matrix.vec2_dotProduct, v_HT_apply_0, v_HT_apply_1]
    show a * b + b * (lam_HT - a) = (lam_HT • v_HT) (0 : Fin 2)
    rw [Pi.smul_apply, smul_eq_mul, v_HT_apply_0]
    show a * b + b * (lam_HT - a) = lam_HT * b
    ring
  · -- Row 1: M(1,0)·v(0) + M(1,1)·v(1) = lam_HT·v(1)
    show (H_SU.val * T_SU.val : Matrix (Fin 2) (Fin 2) ℂ).mulVec v_HT (1 : Fin 2)
        = (lam_HT • v_HT) (1 : Fin 2)
    rw [Matrix.mulVec, Matrix.vec2_dotProduct, v_HT_apply_0, v_HT_apply_1]
    show c * b + d * (lam_HT - a) = (lam_HT • v_HT) (1 : Fin 2)
    rw [Pi.smul_apply, smul_eq_mul, v_HT_apply_1]
    show c * b + d * (lam_HT - a) = lam_HT * (lam_HT - a)
    have h_char' : lam_HT^2 - a*lam_HT - d*lam_HT + 1 = 0 := by
      rw [h_char]; ring
    have h_bc : c * b - a * d = -1 := by linear_combination -h_det
    linear_combination -h_char' + h_bc

theorem H_SU_mul_T_SU_infinite_order :
    ¬ IsOfFinOrder (H_SU * T_SU) := by
  apply not_finOrder_of_eigenvalue_not_rootOfUnity
    (H_SU * T_SU) v_HT v_HT_ne_zero lam_HT
  · -- Eigenvalue equation: coerce subgroup product to matrix product.
    show ((H_SU * T_SU : Matrix.specialUnitaryGroup (Fin 2) ℂ).val).mulVec v_HT
        = lam_HT • v_HT
    have h_coe : ((H_SU * T_SU : Matrix.specialUnitaryGroup (Fin 2) ℂ).val
                : Matrix (Fin 2) (Fin 2) ℂ) = H_SU.val * T_SU.val := rfl
    rw [h_coe]
    exact H_SU_mul_T_SU_eigen
  · exact lambda_HT_not_root_of_unity

/-! ## 5. Lift to `H_of_G cliffordTGeneratingSet`

Once `H_SU * T_SU` has infinite order, its powers `(H·T)^n` for `n : ℕ`
are pairwise distinct, hence the closed subgroup is infinite. -/

/-- The powers `n ↦ (H·T)^n` are injective in `n` (since `H·T` has
infinite order). -/
theorem H_SU_mul_T_SU_pow_injective :
    Function.Injective (fun n : ℕ => (H_SU * T_SU) ^ n) :=
  injective_pow_iff_not_isOfFinOrder.mpr H_SU_mul_T_SU_infinite_order

/-- The subset `{(H·T)^n : n : ℕ}` of `H_of_G cliffordTGeneratingSet` is
infinite. -/
theorem H_SU_mul_T_SU_pow_range_infinite :
    (Set.range (fun n : ℕ => (H_SU * T_SU) ^ n)).Infinite := by
  exact Set.infinite_range_of_injective H_SU_mul_T_SU_pow_injective

/-- **Headline: `H_of_G cliffordTGeneratingSet` is infinite (as a set).**

The closed subgroup of SU(2) generated by H_SU and T_SU contains the
cyclic subgroup ⟨H_SU · T_SU⟩, which is infinite. -/
theorem H_of_G_cliffordT_isInfinite :
    (H_of_G cliffordTGeneratingSet : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).Infinite := by
  apply Set.Infinite.mono _ H_SU_mul_T_SU_pow_range_infinite
  -- Every power of (H·T) is in H_of_G cliffordTGeneratingSet.
  rintro _ ⟨n, rfl⟩
  exact (H_of_G cliffordTGeneratingSet).pow_mem
    ((H_of_G cliffordTGeneratingSet).mul_mem
      H_SU_mem_H_of_G_cliffordT T_SU_mem_H_of_G_cliffordT) n

/-! ## 6. The T-S.2 headline: accumulation at the identity

The headline consumed by `cliffordT_v4_witness_tracked`: the identity
is an accumulation point of the closed subgroup, via the alphabet-
agnostic `one_accPt_of_infinite_closed_subgroup` lemma. -/

/-- **HEADLINE: `1` is an accumulation point of `H_of_G cliffordT`.**

This is the load-bearing fact consumed by the substantive discharge of
`cliffordT_v4_witness_tracked` (Track T-S.2). -/
theorem cliffordT_accPt_one_unconditional :
    AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (Filter.principal (H_of_G cliffordTGeneratingSet : Set _)) :=
  one_accPt_of_infinite_closed_subgroup
    (H_of_G cliffordTGeneratingSet)
    (H_of_G_isClosed cliffordTGeneratingSet)
    H_of_G_cliffordT_isInfinite

end SKEFTHawking.FKLW.GenericSU2
