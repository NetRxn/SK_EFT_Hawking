/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-B.5.2 substantive discharge — `H_of_G readRezayiK5` is infinite

This module ships the **load-bearing infinite-order witness** for the
substantive discharge of `rr5_v4_witness_tracked` (defined in
`ReadRezayiK5ClosureDenseWitness.lean`): the product `H_SU · T_RR5` is
an SU(2) element of *infinite order*.

## Mathematical strategy

The eigenvalues of `M := H_SU · T_RR5` are `λ, λ̄` on the unit circle with
`λ + λ̄ = tr(M) = √2 · sin(π/14)` (real). So writing `λ = α + i·β`,
  α = (√2 · sin(π/14)) / 2  (so 2α = tr M)
  β = √(1 - α²)              (since |λ| = 1 ⟹ α² + β² = 1)

We show `λ^n ≠ 1` for all `n ≥ 1`:

1. If `λ^n = 1`, then `λ` is an n-th root of unity, so `α = cos(rπ)` for
   some `r ∈ ℚ`.

2. By `Real.isIntegral_two_mul_cos_rat_mul_pi`, `2α = √2·sin(π/14)` is
   an algebraic integer over ℤ. So is its square
   `(2α)² = 2·sin²(π/14) = 1 - cos(π/7)`.

3. Hence `cos(π/7) = 1 - (2α)²` is an algebraic integer.

4. By the Chebyshev factoring
   `T_7(x) + 1 = (x + 1) · (8x³ - 4x² - 4x + 1)²`,
   the cubic `8x³ - 4x² - 4x + 1` vanishes at `x = cos(π/7)`
   (since `T_7(cos(π/7)) = cos(π) = -1` and `cos(π/7) ≠ -1`).

5. Rearrange: `2·cos³(π/7) - cos²(π/7) - cos(π/7) = -1/4`. The LHS is
   an algebraic integer (closure of ℤ̄ under polynomial operations on
   `cos(π/7)`), so `-1/4` is too.

6. By `IsIntegral.exists_int_iff_exists_rat`, the rational algebraic
   integer `-1/4` must be a genuine integer — contradicting
   `-1/4 ∉ ℤ`. QED.

Then `H_SU · T_RR5` has infinite order via
`not_finOrder_of_eigenvalue_not_rootOfUnity` (alphabet-agnostic substrate
in `FibRepInfiniteOrder.lean`), pushing through to:
  - `H_of_G_readRezayiK5_isInfinite : (H_of_G readRezayiK5GeneratingSet).Infinite`
  - `rr5_accPt_one_unconditional : AccPt 1 (Filter.principal ...)`

The latter is the headline consumed by the T-B.5.2 discharge.

## Headline theorems

  * `α_RR5_ne_cos_rat_mul_pi` — Niven-style obstruction:
    `cos(rπ) ≠ α_RR5` for every `r ∈ ℚ`.
  * `lambda_RR5_not_root_of_unity` — `lam_RR5^n ≠ 1` for every `n ≥ 1`.
  * `H_SU_mul_T_RR5_eigen` — eigenvalue equation
    `(H_SU · T_RR5) · v_RR5 = lam_RR5 • v_RR5`.
  * `H_SU_mul_T_RR5_infinite_order` — `¬ IsOfFinOrder (H_SU * T_RR5)`.
  * `H_of_G_readRezayiK5_isInfinite` — the closed subgroup is infinite.
  * `rr5_accPt_one_unconditional` — `AccPt 1 ...` (the T-B.5.2 anchor).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
-/

import SKEFTHawking.FKLW.ReadRezayiK5GeneratingSet
import SKEFTHawking.FKLW.CliffordTGeneratingSet
import SKEFTHawking.FKLW.GenericSU2GeneratingSet
import SKEFTHawking.FKLW.FibRepInfiniteOrder
import SKEFTHawking.FKLW.AharonovAradLemma6
import Mathlib.NumberTheory.Niven
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix Complex Real
open SKEFTHawking.FKLW

/-! ## 1. The eigenvalue's real part `α_RR5` and the key identity
`(2α)² = 1 - cos(π/7)` -/

/-- The eigenvalue's real part: `α_RR5 := √2·sin(π/14)/2`. -/
noncomputable def α_RR5 : ℝ := Real.sqrt 2 * Real.sin (Real.pi / 14) / 2

/-- `(2·α_RR5)² = 2·sin²(π/14) = 1 - cos(π/7)`. -/
lemma two_alpha_RR5_sq_eq :
    (2 * α_RR5) ^ 2 = 1 - Real.cos (Real.pi / 7) := by
  unfold α_RR5
  have h_sq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h_sin_sq : Real.sin (Real.pi / 14) ^ 2 = 1/2 - Real.cos (2 * (Real.pi / 14)) / 2 :=
    Real.sin_sq_eq_half_sub _
  have h_2pi14 : 2 * (Real.pi / 14) = Real.pi / 7 := by ring
  rw [h_2pi14] at h_sin_sq
  have : (2 * (Real.sqrt 2 * Real.sin (Real.pi / 14) / 2)) ^ 2
        = Real.sqrt 2 ^ 2 * Real.sin (Real.pi / 14) ^ 2 := by ring
  rw [this, h_sq2, h_sin_sq]
  ring

/-! ## 2. The Chebyshev T_7 cubic relation at `cos(π/7)`

By `Polynomial.Chebyshev.T_real_cos`, `T_7(cos(π/7)) = cos(7·(π/7)) = cos(π) = -1`.

Expanding `T_7 = 64X⁷ - 112X⁵ + 56X³ - 7X` and using the factorisation
`T_7(x) + 1 = (x + 1)·(8x³ - 4x² - 4x + 1)²` (a polynomial identity provable
by `ring`), combined with `cos(π/7) > 0` (hence `cos(π/7) + 1 ≠ 0`), forces
`8·cos³(π/7) - 4·cos²(π/7) - 4·cos(π/7) + 1 = 0`. -/

/-- Chebyshev `T_7` over `ℝ` expands as `64X⁷ - 112X⁵ + 56X³ - 7X`. -/
private lemma chebyshev_T_seven_real :
    (Polynomial.Chebyshev.T ℝ 7 : Polynomial ℝ)
      = 64 * Polynomial.X^7 - 112 * Polynomial.X^5 + 56 * Polynomial.X^3
        - 7 * Polynomial.X := by
  have hT3 : (Polynomial.Chebyshev.T ℝ 3 : Polynomial ℝ)
        = 4 * Polynomial.X^3 - 3 * Polynomial.X := by
    have : (Polynomial.Chebyshev.T ℝ 3 : Polynomial ℝ) = Polynomial.Chebyshev.T ℝ (1 + 2) := by
      norm_num
    rw [this, Polynomial.Chebyshev.T_add_two, show (1 : ℤ) + 1 = 2 from rfl,
        Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one]
    ring
  have hT4 : (Polynomial.Chebyshev.T ℝ 4 : Polynomial ℝ)
        = 8 * Polynomial.X^4 - 8 * Polynomial.X^2 + 1 := by
    have : (Polynomial.Chebyshev.T ℝ 4 : Polynomial ℝ) = Polynomial.Chebyshev.T ℝ (2 + 2) := by
      norm_num
    rw [this, Polynomial.Chebyshev.T_add_two, show (2 : ℤ) + 1 = 3 from rfl,
        Polynomial.Chebyshev.T_two, hT3]
    ring
  have hT5 : (Polynomial.Chebyshev.T ℝ 5 : Polynomial ℝ)
        = 16 * Polynomial.X^5 - 20 * Polynomial.X^3 + 5 * Polynomial.X := by
    have : (Polynomial.Chebyshev.T ℝ 5 : Polynomial ℝ) = Polynomial.Chebyshev.T ℝ (3 + 2) := by
      norm_num
    rw [this, Polynomial.Chebyshev.T_add_two, show (3 : ℤ) + 1 = 4 from rfl, hT3, hT4]
    ring
  have hT6 : (Polynomial.Chebyshev.T ℝ 6 : Polynomial ℝ)
        = 32 * Polynomial.X^6 - 48 * Polynomial.X^4 + 18 * Polynomial.X^2 - 1 := by
    have : (Polynomial.Chebyshev.T ℝ 6 : Polynomial ℝ) = Polynomial.Chebyshev.T ℝ (4 + 2) := by
      norm_num
    rw [this, Polynomial.Chebyshev.T_add_two, show (4 : ℤ) + 1 = 5 from rfl, hT4, hT5]
    ring
  have : (Polynomial.Chebyshev.T ℝ 7 : Polynomial ℝ) = Polynomial.Chebyshev.T ℝ (5 + 2) := by
    norm_num
  rw [this, Polynomial.Chebyshev.T_add_two, show (5 : ℤ) + 1 = 6 from rfl, hT5, hT6]
  ring

/-- The numerical Chebyshev identity at `x = cos(π/7)`:
`64·cos⁷(π/7) - 112·cos⁵(π/7) + 56·cos³(π/7) - 7·cos(π/7) = -1`. -/
private lemma cos_pi_div_seven_chebyshev_eq :
    64 * (Real.cos (Real.pi / 7))^7 - 112 * (Real.cos (Real.pi / 7))^5
    + 56 * (Real.cos (Real.pi / 7))^3 - 7 * Real.cos (Real.pi / 7) = -1 := by
  -- Polynomial.eval (cos(π/7)) (T ℝ 7) = cos(7·(π/7)) = cos(π) = -1
  have h_eval : Polynomial.eval (Real.cos (Real.pi / 7)) (Polynomial.Chebyshev.T ℝ 7)
      = Real.cos (Real.pi) := by
    have := Polynomial.Chebyshev.T_real_cos (Real.pi / 7) 7
    push_cast at this
    rw [this]
    congr 1; ring
  -- Expand T_7 = 64X⁷ - 112X⁵ + 56X³ - 7X
  rw [chebyshev_T_seven_real] at h_eval
  simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_ofNat] at h_eval
  linarith

/-- `cos(π/7) > 0`. (Used to discharge `cos(π/7) + 1 ≠ 0`.) -/
private lemma cos_pi_div_seven_pos : 0 < Real.cos (Real.pi / 7) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have h_pi_pos : 0 < Real.pi := Real.pi_pos
    linarith
  · have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have : Real.pi / 7 < Real.pi / 2 := by
      have h7 : (0 : ℝ) < 7 := by norm_num
      have h2 : (0 : ℝ) < 2 := by norm_num
      rw [div_lt_div_iff₀ h7 h2]
      linarith
    linarith

/-- `cos(π/7) + 1 ≠ 0`. -/
private lemma cos_pi_div_seven_add_one_ne_zero :
    Real.cos (Real.pi / 7) + 1 ≠ 0 := by
  have h := cos_pi_div_seven_pos
  linarith

/-- **The level-5 cubic relation**:
`8·cos³(π/7) - 4·cos²(π/7) - 4·cos(π/7) + 1 = 0`.

Derived from the polynomial factorisation
`64x⁷ - 112x⁵ + 56x³ - 7x + 1 = (x + 1)·(8x³ - 4x² - 4x + 1)²`
combined with the Chebyshev identity `T_7(cos(π/7)) = -1` and the fact
`cos(π/7) + 1 ≠ 0`. -/
lemma cos_pi_div_seven_cubic :
    8 * (Real.cos (Real.pi / 7))^3 - 4 * (Real.cos (Real.pi / 7))^2
    - 4 * Real.cos (Real.pi / 7) + 1 = 0 := by
  set x := Real.cos (Real.pi / 7) with hx_def
  -- Polynomial identity (provable by ring): 64x⁷ - 112x⁵ + 56x³ - 7x + 1 = (x+1)·(8x³-4x²-4x+1)².
  have h_factor : 64 * x^7 - 112 * x^5 + 56 * x^3 - 7 * x + 1
      = (x + 1) * (8 * x^3 - 4 * x^2 - 4 * x + 1)^2 := by ring
  -- LHS = 0 at x = cos(π/7), via the Chebyshev identity.
  have h_lhs_zero : 64 * x^7 - 112 * x^5 + 56 * x^3 - 7 * x + 1 = 0 := by
    have := cos_pi_div_seven_chebyshev_eq
    rw [← hx_def] at this
    linarith
  -- Combine: (x+1)·(cubic)² = 0; since (x+1) ≠ 0, cubic² = 0, hence cubic = 0.
  rw [h_lhs_zero] at h_factor
  have h_x_add_one : x + 1 ≠ 0 := by
    rw [hx_def]; exact cos_pi_div_seven_add_one_ne_zero
  have h_sq_zero : (8 * x^3 - 4 * x^2 - 4 * x + 1)^2 = 0 := by
    -- h_factor : 0 = (x + 1) * (cubic)²; since x + 1 ≠ 0, the cubic² = 0.
    have h_prod : (x + 1) * (8 * x^3 - 4 * x^2 - 4 * x + 1)^2 = 0 := h_factor.symm
    rcases mul_eq_zero.mp h_prod with h1 | h2
    · exact absurd h1 h_x_add_one
    · exact h2
  exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h_sq_zero

/-! ## 3. Algebraic-integer obstruction for `cos(qπ) = α_RR5`

The core arithmetic lemma: if `cos(qπ) = α_RR5` for `q ∈ ℚ`, then
`-1/4` is an algebraic integer (contradiction). Proof:
  - `2·cos(qπ)` is integral over ℤ (Niven substrate).
  - `(2·cos(qπ))² = (2α_RR5)² = 1 - cos(π/7)`.
  - So `cos(π/7) = 1 - (2·cos(qπ))²` is integral over ℤ.
  - By the level-5 cubic `8·cos³(π/7) - 4·cos²(π/7) - 4·cos(π/7) + 1 = 0`,
    rearrange: `2·cos³(π/7) - cos²(π/7) - cos(π/7) = -1/4`. LHS integral
    over ℤ (ring closure), so `-1/4` is integral.
  - But `-1/4 : ℝ` is rational; integral rational ⟹ integer.
    Contradiction (`4k = -1` has no integer solution).
-/

/-- If `α_RR5 = cos(rπ)` for some `r ∈ ℚ`, we derive a contradiction. -/
lemma α_RR5_ne_cos_rat_mul_pi (r : ℚ) :
    Real.cos (r * Real.pi) ≠ α_RR5 := by
  intro h_eq
  -- 2·cos(rπ) is integral over ℤ.
  have h_int_2cos : IsIntegral ℤ (2 * Real.cos (r * Real.pi)) :=
    Real.isIntegral_two_mul_cos_rat_mul_pi r
  rw [h_eq] at h_int_2cos
  -- (2α_RR5)² is integral.
  have h_int_sq : IsIntegral ℤ ((2 * α_RR5) ^ 2) := by
    rw [sq]
    exact h_int_2cos.mul h_int_2cos
  -- 1 is integral.
  have h_int_one : IsIntegral ℤ (1 : ℝ) := isIntegral_one
  -- cos(π/7) = 1 - (2α)² is integral.
  have h_int_cos7 : IsIntegral ℤ (Real.cos (Real.pi / 7)) := by
    have h_eq2 : Real.cos (Real.pi / 7) = 1 - (2 * α_RR5) ^ 2 := by
      rw [two_alpha_RR5_sq_eq]; ring
    rw [h_eq2]
    exact h_int_one.sub h_int_sq
  -- The cubic 8·cos³ - 4·cos² - 4·cos + 1 = 0 rearranges to
  -- 2·cos³ - cos² - cos = -1/4.
  have h_cubic := cos_pi_div_seven_cubic
  have h_rearr : (-(1 : ℝ)/4) = 2 * (Real.cos (Real.pi / 7))^3
                              - (Real.cos (Real.pi / 7))^2
                              - Real.cos (Real.pi / 7) := by linarith
  -- 2 is integral.
  have h_int_two : IsIntegral ℤ (2 : ℝ) := by
    have : (2 : ℝ) = 1 + 1 := by norm_num
    rw [this]; exact h_int_one.add h_int_one
  -- 2·cos³ - cos² - cos ∈ ℤ̄.
  have h_int_cos7_cube : IsIntegral ℤ ((Real.cos (Real.pi / 7))^3) := by
    rw [show (Real.cos (Real.pi / 7))^3 = Real.cos (Real.pi / 7) * Real.cos (Real.pi / 7)
            * Real.cos (Real.pi / 7) from by ring]
    exact (h_int_cos7.mul h_int_cos7).mul h_int_cos7
  have h_int_cos7_sq : IsIntegral ℤ ((Real.cos (Real.pi / 7))^2) := by
    rw [sq]
    exact h_int_cos7.mul h_int_cos7
  have h_int_combined : IsIntegral ℤ (2 * (Real.cos (Real.pi / 7))^3
                                      - (Real.cos (Real.pi / 7))^2
                                      - Real.cos (Real.pi / 7)) :=
    ((h_int_two.mul h_int_cos7_cube).sub h_int_cos7_sq).sub h_int_cos7
  have h_int_neg_quarter : IsIntegral ℤ ((-(1 : ℝ)/4)) := by
    rw [h_rearr]
    exact h_int_combined
  -- -1/4 is rational.
  have h_rat : ∃ q : ℚ, ((-(1 : ℝ)/4)) = (q : ℝ) := by
    refine ⟨-(1 : ℚ)/4, ?_⟩
    push_cast
    ring
  -- An algebraic-integer rational is an integer.
  have h_int : ∃ k : ℤ, ((-(1 : ℝ)/4)) = (k : ℝ) :=
    (IsIntegral.exists_int_iff_exists_rat h_int_neg_quarter).mp h_rat
  obtain ⟨k, hk⟩ := h_int
  have : (4 * k : ℝ) = -1 := by linarith
  have h_int_eq : (4 * k : ℤ) = -1 := by exact_mod_cast this
  omega

/-! ## 4. The eigenvalue `λ_RR5` and its non-root-of-unity property

Define θ := arccos(α_RR5). Then 0 ≤ θ ≤ π and we set
`lam_RR5 := exp(I·θ)`. We show `lam_RR5^n ≠ 1` for `n ≥ 1` via the
algebraic-integer obstruction (Section 3). -/

/-- The phase θ_RR5 := arccos(α_RR5). Lies in [0, π]. -/
noncomputable def θ_RR5 : ℝ := Real.arccos α_RR5

/-- We need `α_RR5 ∈ [-1, 1]` to apply `Real.cos_arccos`. -/
lemma alpha_RR5_abs_le_one : |α_RR5| ≤ 1 := by
  -- (2α)² = 1 - cos(π/7) ∈ [0, 2] (since cos ∈ [-1, 1]), so α² ≤ 1/2, so |α| ≤ 1.
  have h := two_alpha_RR5_sq_eq
  have h_cos_le : Real.cos (Real.pi / 7) ≤ 1 := Real.cos_le_one _
  have h_cos_ge : -1 ≤ Real.cos (Real.pi / 7) := Real.neg_one_le_cos _
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (2 * α_RR5 + 2)]
  · nlinarith [sq_nonneg (2 * α_RR5 - 2)]

/-- `cos θ_RR5 = α_RR5`. -/
lemma cos_θ_RR5 : Real.cos θ_RR5 = α_RR5 := by
  unfold θ_RR5
  rw [Real.cos_arccos]
  · exact neg_le_of_abs_le alpha_RR5_abs_le_one
  · exact le_of_abs_le alpha_RR5_abs_le_one

/-- The eigenvalue `lam_RR5 := exp(I · θ_RR5)` for `M := H_SU·T_RR5`. -/
noncomputable def lam_RR5 : ℂ := Complex.exp ((θ_RR5 : ℂ) * Complex.I)

/-- `Re(lam_RR5) = cos(θ_RR5) = α_RR5`. -/
lemma lam_RR5_re : lam_RR5.re = α_RR5 := by
  unfold lam_RR5
  rw [Complex.exp_ofReal_mul_I_re]
  exact cos_θ_RR5

/-- Characteristic-polynomial relation: `lam_RR5² = 2·α_RR5·lam_RR5 - 1`. -/
lemma lambda_RR5_sq :
    lam_RR5 ^ 2 = 2 * (α_RR5 : ℂ) * lam_RR5 - 1 := by
  have h_inv : lam_RR5⁻¹ = Complex.exp (-(θ_RR5 : ℂ) * Complex.I) := by
    unfold lam_RR5
    rw [← Complex.exp_neg]
    congr 1
    ring
  have h_sum : lam_RR5 + lam_RR5⁻¹ = 2 * (α_RR5 : ℂ) := by
    rw [h_inv]
    unfold lam_RR5
    rw [show (θ_RR5 : ℂ) * Complex.I = ((θ_RR5 : ℝ) : ℂ) * Complex.I from rfl]
    rw [show -(θ_RR5 : ℂ) * Complex.I = ((-θ_RR5 : ℝ) : ℂ) * Complex.I from by
          push_cast; ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    have h_cos_C : Complex.cos ((θ_RR5 : ℝ) : ℂ) = ((α_RR5 : ℝ) : ℂ) := by
      rw [show Complex.cos ((θ_RR5 : ℝ) : ℂ) = ((Real.cos θ_RR5 : ℝ) : ℂ) from
          (Complex.ofReal_cos _).symm]
      rw [cos_θ_RR5]
    rw [h_cos_C]
    ring
  have h_ne : lam_RR5 ≠ 0 := by unfold lam_RR5; exact Complex.exp_ne_zero _
  have h_step : (lam_RR5 + lam_RR5⁻¹) * lam_RR5 = 2 * (α_RR5 : ℂ) * lam_RR5 := by
    rw [h_sum]
  have h_expand : (lam_RR5 + lam_RR5⁻¹) * lam_RR5 = lam_RR5^2 + 1 := by
    field_simp
  rw [h_expand] at h_step
  linear_combination h_step

/-- **The eigenvalue λ_RR5 is not a root of unity.** -/
theorem lambda_RR5_not_root_of_unity :
    ∀ n : ℕ, 0 < n → lam_RR5 ^ n ≠ 1 := by
  intro n hn h_pow
  unfold lam_RR5 at h_pow
  rw [← Complex.exp_nat_mul] at h_pow
  rw [Complex.exp_eq_one_iff] at h_pow
  obtain ⟨k, hk⟩ := h_pow
  have h_I_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h_real_C : (n : ℂ) * (θ_RR5 : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ)) := by
    have hl : (n : ℂ) * ((θ_RR5 : ℂ) * Complex.I)
          = ((n : ℂ) * (θ_RR5 : ℂ)) * Complex.I := by ring
    have hr : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
          = ((k : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by ring
    rw [hl, hr] at hk
    exact mul_right_cancel₀ h_I_ne hk
  have h_real_R : (n : ℝ) * θ_RR5 = (k : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.re h_real_C
    simp at this
    exact this
  have hn_R_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_R_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_R_pos
  have h_theta : θ_RR5 = ((2 * k : ℝ) / (n : ℝ)) * Real.pi := by
    field_simp
    linarith
  let r : ℚ := (2 * k : ℤ) / (n : ℤ)
  apply α_RR5_ne_cos_rat_mul_pi r
  rw [show ((r : ℝ) * Real.pi) = θ_RR5 from ?_]
  · exact cos_θ_RR5
  · rw [h_theta]
    have : ((r : ℝ) : ℝ) = (2 * k : ℝ) / (n : ℝ) := by
      simp only [r]
      push_cast
      rfl
    rw [this]

/-! ## 5. Entries, trace, and determinant of `H_SU · T_RR5`

These computations mirror their Clifford+T analogs (`H_SU · T_SU`) in
`CliffordTInfiniteOrder.lean` but with the phase `π/14` replacing
`π/8`. -/

/-- The `(0,0)` entry of `H_SU · T_RR5`. -/
private lemma H_SU_T_RR5_apply_0_0 :
    (H_SU_mat * T_RR5_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
      = (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (-(Complex.I * Real.pi / 14)) := by
  simp [H_SU_mat, T_RR5_mat, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

/-- The `(1,0)` entry of `H_SU · T_RR5`. -/
private lemma H_SU_T_RR5_apply_1_0 :
    (H_SU_mat * T_RR5_mat) ⟨1, by decide⟩ ⟨0, by decide⟩
      = (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (-(Complex.I * Real.pi / 14)) := by
  simp [H_SU_mat, T_RR5_mat, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

/-- The `(1,1)` entry of `H_SU · T_RR5`. -/
private lemma H_SU_T_RR5_apply_1_1 :
    (H_SU_mat * T_RR5_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
      = -((Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (Complex.I * Real.pi / 14)) := by
  simp [H_SU_mat, T_RR5_mat, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

/-- The `(0,1)` entry of `H_SU · T_RR5`. -/
private lemma H_SU_T_RR5_apply_0_1 :
    (H_SU_mat * T_RR5_mat) ⟨0, by decide⟩ ⟨1, by decide⟩
      = (Complex.I / Real.sqrt 2 : ℂ) * Complex.exp (Complex.I * Real.pi / 14) := by
  simp [H_SU_mat, T_RR5_mat, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

/-- The `(0,1)` entry of `H_SU · T_RR5` is nonzero. -/
private lemma H_SU_T_RR5_apply_0_1_ne_zero :
    (H_SU_mat * T_RR5_mat) ⟨0, by decide⟩ ⟨1, by decide⟩ ≠ 0 := by
  rw [H_SU_T_RR5_apply_0_1]
  apply mul_ne_zero
  · apply div_ne_zero
    · exact Complex.I_ne_zero
    · exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  · exact Complex.exp_ne_zero _

/-- Trace of `H_SU·T_RR5` as a complex number: `2·α_RR5`. -/
private lemma H_SU_T_RR5_trace_eq :
    (H_SU_mat * T_RR5_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
      + (H_SU_mat * T_RR5_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
      = (2 * α_RR5 : ℂ) := by
  rw [H_SU_T_RR5_apply_0_0, H_SU_T_RR5_apply_1_1]
  have h_expp : Complex.exp (Complex.I * (Real.pi : ℂ) / 14)
              = ((Real.cos (Real.pi / 14) : ℝ) : ℂ)
                + ((Real.sin (Real.pi / 14) : ℝ) : ℂ) * Complex.I := by
    rw [show Complex.I * (Real.pi : ℂ) / 14 = ((Real.pi / 14 : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have h_expn : Complex.exp (-(Complex.I * (Real.pi : ℂ) / 14))
              = ((Real.cos (Real.pi / 14) : ℝ) : ℂ)
                - ((Real.sin (Real.pi / 14) : ℝ) : ℂ) * Complex.I := by
    rw [show -(Complex.I * (Real.pi : ℂ) / 14) = ((-(Real.pi / 14) : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
    rw [Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h_expp, h_expn]
  have h_alpha_cast : ((α_RR5 : ℝ) : ℂ)
        = ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sin (Real.pi / 14) : ℝ) : ℂ) / 2 := by
    unfold α_RR5; push_cast; ring
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
    (-2 * ((Real.sin (Real.pi / 14) : ℝ) : ℂ)) * h_I_sq

/-- Determinant of `H_SU·T_RR5` is 1. -/
private lemma H_SU_T_RR5_det_eq :
    (H_SU_mat * T_RR5_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
      * (H_SU_mat * T_RR5_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
    - (H_SU_mat * T_RR5_mat) ⟨0, by decide⟩ ⟨1, by decide⟩
      * (H_SU_mat * T_RR5_mat) ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 := by
  rw [H_SU_T_RR5_apply_0_0, H_SU_T_RR5_apply_0_1, H_SU_T_RR5_apply_1_0, H_SU_T_RR5_apply_1_1]
  have h_sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (2 : ℂ) := by
    have : ((Real.sqrt 2 : ℝ) ^ 2 : ℝ) = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h_cast : (((Real.sqrt 2 : ℝ) ^ 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by
      push_cast; ring
    rw [← h_cast, this]; push_cast; rfl
  have h_sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have h_exp_id : Complex.exp (-(Complex.I * (Real.pi : ℂ) / 14))
                * Complex.exp (Complex.I * (Real.pi : ℂ) / 14) = 1 := by
    rw [← Complex.exp_add]
    have h_zero : -(Complex.I * (Real.pi : ℂ) / 14) + Complex.I * (Real.pi : ℂ) / 14 = 0 := by
      ring
    rw [h_zero, Complex.exp_zero]
  have h_exp_id' : Complex.exp (Complex.I * (Real.pi : ℂ) / 14)
                * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 14)) = 1 := by
    rw [mul_comm]; exact h_exp_id
  have target_lhs :
      Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 14))
      * (-(Complex.I / ((Real.sqrt 2 : ℝ) : ℂ)
          * Complex.exp (Complex.I * (Real.pi : ℂ) / 14)))
      -
      (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (Real.pi : ℂ) / 14))
      * (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 14)))
      = - (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ))^2
        * (Complex.exp (-(Complex.I * (Real.pi : ℂ) / 14))
          * Complex.exp (Complex.I * (Real.pi : ℂ) / 14))
        -
        (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ))^2
        * (Complex.exp (Complex.I * (Real.pi : ℂ) / 14)
          * Complex.exp (-(Complex.I * (Real.pi : ℂ) / 14))) := by ring
  rw [target_lhs, h_exp_id, h_exp_id']
  rw [div_pow, show Complex.I ^ 2 = -1 from Complex.I_sq, h_sqrt2_sq]
  ring

/-! ## 6. Eigenvector for `H_SU · T_RR5` and infinite-order witness -/

/-- The eigenvector for `M := H_SU·T_RR5` at eigenvalue `lam_RR5`. -/
noncomputable def v_RR5 : Fin 2 → ℂ := fun j =>
  if j = (0 : Fin 2) then (H_SU.val * T_RR5.val) ⟨0, by decide⟩ ⟨1, by decide⟩
  else lam_RR5 - (H_SU.val * T_RR5.val) ⟨0, by decide⟩ ⟨0, by decide⟩

private lemma v_RR5_apply_0 :
    v_RR5 (0 : Fin 2) = (H_SU.val * T_RR5.val) ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  simp [v_RR5]

private lemma v_RR5_apply_1 :
    v_RR5 (1 : Fin 2) = lam_RR5 - (H_SU.val * T_RR5.val) ⟨0, by decide⟩ ⟨0, by decide⟩ := by
  simp [v_RR5]

lemma v_RR5_ne_zero : v_RR5 ≠ 0 := by
  intro h
  have h0 := congr_fun h (0 : Fin 2)
  rw [v_RR5_apply_0] at h0
  apply H_SU_T_RR5_apply_0_1_ne_zero
  show (H_SU_mat * T_RR5_mat) ⟨0, by decide⟩ ⟨1, by decide⟩ = 0
  exact h0

/-- The eigenvalue equation `M · v = λ · v` for `M := H_SU·T_RR5`. -/
theorem H_SU_mul_T_RR5_eigen :
    (H_SU.val * T_RR5.val : Matrix (Fin 2) (Fin 2) ℂ).mulVec v_RR5
      = lam_RR5 • v_RR5 := by
  set a := (H_SU.val * T_RR5.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨0, by decide⟩ ⟨0, by decide⟩ with ha
  set b := (H_SU.val * T_RR5.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨0, by decide⟩ ⟨1, by decide⟩ with hb
  set c := (H_SU.val * T_RR5.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨1, by decide⟩ ⟨0, by decide⟩ with hc
  set d := (H_SU.val * T_RR5.val : Matrix (Fin 2) (Fin 2) ℂ) ⟨1, by decide⟩ ⟨1, by decide⟩ with hd
  have h_tr : a + d = (2 * α_RR5 : ℂ) := by
    show (H_SU_mat * T_RR5_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
        + (H_SU_mat * T_RR5_mat) ⟨1, by decide⟩ ⟨1, by decide⟩ = (2 * α_RR5 : ℂ)
    exact H_SU_T_RR5_trace_eq
  have h_det : a * d - b * c = 1 := by
    show (H_SU_mat * T_RR5_mat) ⟨0, by decide⟩ ⟨0, by decide⟩
       * (H_SU_mat * T_RR5_mat) ⟨1, by decide⟩ ⟨1, by decide⟩
       - (H_SU_mat * T_RR5_mat) ⟨0, by decide⟩ ⟨1, by decide⟩
       * (H_SU_mat * T_RR5_mat) ⟨1, by decide⟩ ⟨0, by decide⟩ = 1
    exact H_SU_T_RR5_det_eq
  have h_char : lam_RR5 ^ 2 = (a + d) * lam_RR5 - 1 := by
    rw [h_tr]
    exact lambda_RR5_sq
  ext i
  fin_cases i
  · show (H_SU.val * T_RR5.val : Matrix (Fin 2) (Fin 2) ℂ).mulVec v_RR5 (0 : Fin 2)
        = (lam_RR5 • v_RR5) (0 : Fin 2)
    rw [Matrix.mulVec, Matrix.vec2_dotProduct, v_RR5_apply_0, v_RR5_apply_1]
    show a * b + b * (lam_RR5 - a) = (lam_RR5 • v_RR5) (0 : Fin 2)
    rw [Pi.smul_apply, smul_eq_mul, v_RR5_apply_0]
    show a * b + b * (lam_RR5 - a) = lam_RR5 * b
    ring
  · show (H_SU.val * T_RR5.val : Matrix (Fin 2) (Fin 2) ℂ).mulVec v_RR5 (1 : Fin 2)
        = (lam_RR5 • v_RR5) (1 : Fin 2)
    rw [Matrix.mulVec, Matrix.vec2_dotProduct, v_RR5_apply_0, v_RR5_apply_1]
    show c * b + d * (lam_RR5 - a) = (lam_RR5 • v_RR5) (1 : Fin 2)
    rw [Pi.smul_apply, smul_eq_mul, v_RR5_apply_1]
    show c * b + d * (lam_RR5 - a) = lam_RR5 * (lam_RR5 - a)
    have h_char' : lam_RR5^2 - a*lam_RR5 - d*lam_RR5 + 1 = 0 := by
      rw [h_char]; ring
    have h_bc : c * b - a * d = -1 := by linear_combination -h_det
    linear_combination -h_char' + h_bc

theorem H_SU_mul_T_RR5_infinite_order :
    ¬ IsOfFinOrder (H_SU * T_RR5) := by
  apply not_finOrder_of_eigenvalue_not_rootOfUnity
    (H_SU * T_RR5) v_RR5 v_RR5_ne_zero lam_RR5
  · show ((H_SU * T_RR5 : Matrix.specialUnitaryGroup (Fin 2) ℂ).val).mulVec v_RR5
        = lam_RR5 • v_RR5
    have h_coe : ((H_SU * T_RR5 : Matrix.specialUnitaryGroup (Fin 2) ℂ).val
                : Matrix (Fin 2) (Fin 2) ℂ) = H_SU.val * T_RR5.val := rfl
    rw [h_coe]
    exact H_SU_mul_T_RR5_eigen
  · exact lambda_RR5_not_root_of_unity

/-! ## 7. Lift to `H_of_G readRezayiK5GeneratingSet` -/

theorem H_SU_mul_T_RR5_pow_injective :
    Function.Injective (fun n : ℕ => (H_SU * T_RR5) ^ n) :=
  injective_pow_iff_not_isOfFinOrder.mpr H_SU_mul_T_RR5_infinite_order

theorem H_SU_mul_T_RR5_pow_range_infinite :
    (Set.range (fun n : ℕ => (H_SU * T_RR5) ^ n)).Infinite := by
  exact Set.infinite_range_of_injective H_SU_mul_T_RR5_pow_injective

/-- **Headline: `H_of_G readRezayiK5GeneratingSet` is infinite (as a set).** -/
theorem H_of_G_readRezayiK5_isInfinite :
    (H_of_G readRezayiK5GeneratingSet
      : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).Infinite := by
  apply Set.Infinite.mono _ H_SU_mul_T_RR5_pow_range_infinite
  rintro _ ⟨n, rfl⟩
  exact (H_of_G readRezayiK5GeneratingSet).pow_mem
    ((H_of_G readRezayiK5GeneratingSet).mul_mem
      H_SU_mem_H_of_G_RR5 T_RR5_mem_H_of_G_RR5) n

/-! ## 8. The T-B.5.2 headline: accumulation at the identity -/

/-- **HEADLINE: `1` is an accumulation point of `H_of_G readRezayiK5`.**

This is the load-bearing fact consumed by the substantive discharge of
`rr5_v4_witness_tracked` (Track T-B.5.2). -/
theorem rr5_accPt_one_unconditional :
    AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (Filter.principal (H_of_G readRezayiK5GeneratingSet : Set _)) :=
  one_accPt_of_infinite_closed_subgroup
    (H_of_G readRezayiK5GeneratingSet)
    (H_of_G_isClosed readRezayiK5GeneratingSet)
    H_of_G_readRezayiK5_isInfinite

end SKEFTHawking.FKLW.GenericSU2
