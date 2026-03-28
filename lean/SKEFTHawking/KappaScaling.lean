import SKEFTHawking.Basic
import SKEFTHawking.HawkingUniversality
import SKEFTHawking.WKBAnalysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Kappa-Scaling Test: EFT Predictions

## Overview

This module formalizes the kappa-scaling predictions for analog Hawking
radiation in BEC systems. When the surface gravity κ is varied while
holding BEC material properties (ξ, c_s, γ₁, γ₂) fixed, the dispersive
and dissipative EFT corrections scale with different powers of κ:

  - Dispersive: |δ_disp(κ)| = (π/6) · (ξκ/c_s)²  ∝  κ²
  - Dissipative: δ_diss(κ) = (γ₁+γ₂) · κ / c_s²   ∝  κ

The different scaling exponents (2 vs 1) provide an experimental
discriminant. At the crossover κ_cross = 6(γ₁+γ₂)/(πξ²), the two
corrections are equal in magnitude. Below κ_cross dissipation dominates;
above κ_cross dispersion dominates.

## Physical Significance

The κ-scaling test is the most accessible experimental test of the SK-EFT
framework because:

1. It requires only varying the flow velocity (potential step height),
   not changing the BEC atomic species or interaction strength.
2. The prediction (quadratic vs linear) is a qualitative signature,
   not just a quantitative correction factor.
3. The crossover κ_cross is a sharp prediction that can be compared
   against measurement.

## References

- Biondi, arXiv:2504.08833 (2025), §5.3
- Phase 5, Wave 1A of SK-EFT research program
-/

namespace SKEFTHawking.KappaScaling

open Real

/-!
## Material Parameters

BEC material properties that are independent of the surface gravity κ.
These are held fixed during a κ-scaling sweep.
-/

/-- BEC material parameters for a κ-scaling test.
    These are properties of the condensate itself, independent of the
    flow geometry that determines κ.

    - `xi`: healing length ξ = ℏ/(mc_s) [m]
    - `cs`: speed of sound c_s = √(gn/m) [m/s]
    - `gamma_1`, `gamma_2`: first-order SK-EFT transport coefficients [m²/s]

    All are strictly positive (or non-negative for transport coefficients). -/
structure MaterialParams where
  xi : ℝ
  cs : ℝ
  gamma_1 : ℝ
  gamma_2 : ℝ
  xi_pos : 0 < xi
  cs_pos : 0 < cs
  gamma_1_nonneg : 0 ≤ gamma_1
  gamma_2_nonneg : 0 ≤ gamma_2

/-!
## Correction Definitions

The EFT corrections as explicit functions of κ at fixed material parameters.
-/

/-- Dispersive correction as a function of κ.
    δ_disp(κ) = -(π/6) · (ξ·κ/c_s)²

    This is negative (blue-shift) and quadratic in κ. -/
noncomputable def dispersiveCorrection (mat : MaterialParams) (kappa : ℝ) : ℝ :=
  -(π / 6) * (mat.xi * kappa / mat.cs) ^ 2

/-- Dissipative correction as a function of κ.
    δ_diss(κ) = (γ₁ + γ₂) · κ / c_s²

    This is non-negative and linear in κ. -/
noncomputable def dissipativeCorrection (mat : MaterialParams) (kappa : ℝ) : ℝ :=
  (mat.gamma_1 + mat.gamma_2) * kappa / mat.cs ^ 2

/-- Crossover surface gravity.
    κ_cross = 6 · (γ₁ + γ₂) / (π · ξ²)

    At this value, |δ_disp(κ)| = δ_diss(κ). -/
noncomputable def crossoverKappa (mat : MaterialParams) : ℝ :=
  6 * (mat.gamma_1 + mat.gamma_2) / (π * mat.xi ^ 2)

/-!
## Scaling Law Theorems

These theorems establish the functional form of the corrections
and verify the scaling exponents.
-/

/-- The dispersive correction factors as A · κ² where A depends only on
    material properties, establishing the quadratic scaling law.

    Specifically: δ_disp(κ) = A · κ² with A = -(π/6)(ξ/c_s)².
    The factored form makes the κ² dependence manifest.

    PROVIDED SOLUTION
    Unfold `dispersiveCorrection`. The LHS is -(π/6) * (mat.xi * kappa / mat.cs) ^ 2.
    The RHS is (-(π/6) * (mat.xi / mat.cs) ^ 2) * kappa ^ 2.
    These are equal by `ring` since (a * b / c)² = (a/c)² * b². -/
theorem kappa_scaling_dispersive_quadratic (mat : MaterialParams) (kappa : ℝ) :
    dispersiveCorrection mat kappa =
      (-(π / 6) * (mat.xi / mat.cs) ^ 2) * kappa ^ 2 := by
  unfold dispersiveCorrection
  ring

/-- The dissipative correction factors as B · κ where B depends only on
    material properties, establishing the linear scaling law.

    Specifically: δ_diss(κ) = B · κ with B = (γ₁+γ₂)/c_s².
    The factored form makes the κ¹ dependence manifest.

    PROVIDED SOLUTION
    Unfold `dissipativeCorrection`. The LHS is (mat.gamma_1 + mat.gamma_2) * kappa / mat.cs ^ 2.
    The RHS is ((mat.gamma_1 + mat.gamma_2) / mat.cs ^ 2) * kappa.
    These are equal by `ring` since (a * b) / c = (a / c) * b. -/
theorem kappa_scaling_dissipative_linear (mat : MaterialParams) (kappa : ℝ) :
    dissipativeCorrection mat kappa =
      ((mat.gamma_1 + mat.gamma_2) / mat.cs ^ 2) * kappa := by
  unfold dissipativeCorrection
  ring

/-- The dispersive correction is non-positive for all κ (blue-shift).

    PROVIDED SOLUTION
    Unfold `dispersiveCorrection`. We need -(π/6) * (ξκ/c_s)² ≤ 0.
    Since (ξκ/c_s)² ≥ 0 (by `sq_nonneg`) and π/6 > 0 (from `pi_pos`),
    we have (π/6) * (ξκ/c_s)² ≥ 0, so its negation is ≤ 0.
    Use `neg_nonpos_of_nonneg` with `mul_nonneg` applied to
    `div_nonneg pi_pos.le (by norm_num : (0:ℝ) ≤ 6)` and `sq_nonneg`. -/
theorem dispersive_nonpos (mat : MaterialParams) (kappa : ℝ) :
    dispersiveCorrection mat kappa ≤ 0 := by
  unfold dispersiveCorrection
  apply mul_nonpos_of_nonpos_of_nonneg
  · linarith [Real.pi_pos]
  · exact sq_nonneg _

/-- The dissipative correction is non-negative for non-negative κ (red-shift).

    PROVIDED SOLUTION
    Unfold `dissipativeCorrection`. We need (γ₁+γ₂)·κ/c_s² ≥ 0.
    γ₁ ≥ 0, γ₂ ≥ 0 (by `gamma_1_nonneg`, `gamma_2_nonneg`), so γ₁+γ₂ ≥ 0.
    κ ≥ 0 (by `hk`), c_s² > 0 (from `cs_pos`).
    Use `div_nonneg (mul_nonneg (add_nonneg mat.gamma_1_nonneg mat.gamma_2_nonneg) hk) (sq_nonneg mat.cs)`. -/
theorem dissipative_nonneg (mat : MaterialParams) (kappa : ℝ) (hk : 0 ≤ kappa) :
    0 ≤ dissipativeCorrection mat kappa := by
  unfold dissipativeCorrection
  apply div_nonneg
  · exact mul_nonneg (add_nonneg mat.gamma_1_nonneg mat.gamma_2_nonneg) hk
  · exact sq_nonneg _

/-- The dispersive correction is strictly negative for positive κ.

    PROVIDED SOLUTION
    Unfold `dispersiveCorrection`. We need -(π/6) * (ξκ/c_s)² < 0.
    Since κ > 0, ξ > 0 (by `xi_pos`), c_s > 0 (by `cs_pos`),
    we have ξκ/c_s > 0, so (ξκ/c_s)² > 0. Then π/6 > 0 gives
    (π/6) * (ξκ/c_s)² > 0, and negating gives < 0.
    Use `neg_neg_of_pos` with `mul_pos` on `div_pos pi_pos (by norm_num)`
    and `sq_pos_of_pos (div_pos (mul_pos mat.xi_pos hk) mat.cs_pos)`. -/
theorem dispersive_neg (mat : MaterialParams) (kappa : ℝ) (hk : 0 < kappa) :
    dispersiveCorrection mat kappa < 0 := by
  unfold dispersiveCorrection
  apply mul_neg_of_neg_of_pos
  · linarith [Real.pi_pos]
  · exact sq_pos_of_pos (div_pos (mul_pos mat.xi_pos hk) mat.cs_pos)

/-- The crossover kappa is non-negative.

    PROVIDED SOLUTION
    Unfold `crossoverKappa`. We need 6(γ₁+γ₂)/(πξ²) ≥ 0.
    Numerator: 6 ≥ 0, γ₁+γ₂ ≥ 0, so 6(γ₁+γ₂) ≥ 0.
    Denominator: π > 0, ξ² > 0, so πξ² > 0.
    Use `div_nonneg` with `mul_nonneg` and positivity of the denominator. -/
theorem crossover_nonneg (mat : MaterialParams) :
    0 ≤ crossoverKappa mat := by
  unfold crossoverKappa
  apply div_nonneg
  · exact mul_nonneg (by norm_num : (0:ℝ) ≤ 6) (add_nonneg mat.gamma_1_nonneg mat.gamma_2_nonneg)
  · exact mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg _)

/-!
## Crossover Theorem

The central result: at κ = κ_cross, the corrections balance exactly.
-/

/-- At the crossover point, |δ_disp| = δ_diss exactly.

    This is the key prediction of the κ-scaling test:
    |δ_disp(κ_cross)| = δ_diss(κ_cross)

    PROVIDED SOLUTION
    Unfold all definitions. LHS becomes:
      |-(π/6) * (ξ · (6(γ₁+γ₂)/(πξ²)) / c_s)²|
    = (π/6) * ξ² * 36(γ₁+γ₂)² / (π²ξ⁴ · c_s²)
    = 6(γ₁+γ₂)² / (πξ² · c_s²)

    RHS becomes:
      (γ₁+γ₂) · 6(γ₁+γ₂)/(πξ²) / c_s²
    = 6(γ₁+γ₂)² / (πξ² · c_s²)

    These are equal. Use `unfold`, `simp [abs_of_nonpos, dispersive_nonpos]`,
    then `field_simp` and `ring`. Need `mat.cs_pos.ne'` and
    `(mul_pos pi_pos (sq_pos_of_pos mat.xi_pos)).ne'` for `field_simp`. -/
theorem kappa_scaling_crossover_balance (mat : MaterialParams)
    (hgamma : 0 < mat.gamma_1 + mat.gamma_2) :
    |dispersiveCorrection mat (crossoverKappa mat)| =
      dissipativeCorrection mat (crossoverKappa mat) := by
  have hle := dispersive_nonpos mat (crossoverKappa mat)
  rw [abs_of_nonpos hle]
  unfold dispersiveCorrection dissipativeCorrection crossoverKappa
  have hcs : mat.cs ≠ 0 := ne_of_gt mat.cs_pos
  have hxi : mat.xi ≠ 0 := ne_of_gt mat.xi_pos
  have hpi : π ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-- The crossover formula: κ_cross = 6(γ₁+γ₂)/(πξ²).
    This is just the unfolding of the definition, but stated explicitly
    for reference from the Python layer. -/
theorem crossover_formula (mat : MaterialParams) :
    crossoverKappa mat = 6 * (mat.gamma_1 + mat.gamma_2) / (π * mat.xi ^ 2) := by
  rfl

/-!
## Regime Classification

Below κ_cross, dissipation dominates. Above κ_cross, dispersion dominates.
-/

/-- Below the crossover, the dissipative correction dominates.
    For 0 < κ < κ_cross: δ_diss(κ) > |δ_disp(κ)|.

    **Audit note:** `hgamma : 0 < mat.gamma_1 + mat.gamma_2` was removed —
    when `gamma_1 + gamma_2 = 0`, `crossoverKappa = 0`, making
    `hk_pos` and `hk_below` contradictory (0 < kappa < 0). -/
theorem dissipative_dominates_below (mat : MaterialParams)
    (kappa : ℝ) (hk_pos : 0 < kappa) (hk_below : kappa < crossoverKappa mat) :
    |dispersiveCorrection mat kappa| < dissipativeCorrection mat kappa := by
  rw [abs_of_nonpos] <;> norm_num [crossoverKappa, dispersiveCorrection, dissipativeCorrection] at *
  · rw [lt_div_iff₀ (mul_pos Real.pi_pos (sq_pos_of_pos mat.xi_pos))] at *
    field_simp [mul_comm, mul_assoc, mul_left_comm] at *
    gcongr
    exact sq_pos_of_pos mat.cs_pos
  · positivity

/-- Above the crossover, the dispersive correction dominates.
    For κ > κ_cross: |δ_disp(κ)| > δ_diss(κ).

    **Audit note:** `hgamma : 0 < mat.gamma_1 + mat.gamma_2` was removed —
    when `gamma_1 + gamma_2 = 0`, `crossoverKappa = 0`, so `hk_above`
    gives `0 < kappa`, `dissipativeCorrection = 0`, and `|dispersiveCorrection| > 0`. -/
theorem dispersive_dominates_above (mat : MaterialParams)
    (kappa : ℝ) (hk_above : crossoverKappa mat < kappa) :
    dissipativeCorrection mat kappa < |dispersiveCorrection mat kappa| := by
  rw [abs_of_nonpos (SKEFTHawking.KappaScaling.dispersive_nonpos mat kappa)]
  unfold crossoverKappa at hk_above
  rw [div_lt_iff₀ (mul_pos Real.pi_pos (sq_pos_of_pos mat.xi_pos))] at hk_above
  unfold dissipativeCorrection dispersiveCorrection
  rw [div_lt_iff₀ (sq_pos_of_pos mat.cs_pos)]
  ring_nf
  norm_num [ne_of_gt mat.cs_pos]
  have hkappa_pos : 0 < kappa := by
    by_contra h; push_neg at h
    have h1 := mul_nonpos_of_nonpos_of_nonneg h (mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg mat.xi))
    linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 6) (add_nonneg mat.gamma_1_nonneg mat.gamma_2_nonneg)]
  nlinarith [mul_nonneg (add_nonneg mat.gamma_1_nonneg mat.gamma_2_nonneg) (le_of_lt hkappa_pos)]

/-- Uniqueness of the crossover: κ_cross is the ONLY positive value where
    the corrections balance.

    **Audit note:** `hgamma : 0 < mat.gamma_1 + mat.gamma_2` was removed —
    when `gamma_1 + gamma_2 = 0`, `diss = 0` and `|disp| > 0` for `kappa > 0`,
    so `hbal` is contradictory. -/
theorem crossover_unique (mat : MaterialParams)
    (kappa : ℝ) (hk_pos : 0 < kappa)
    (hbal : |dispersiveCorrection mat kappa| = dissipativeCorrection mat kappa) :
    kappa = crossoverKappa mat := by
  unfold dispersiveCorrection dissipativeCorrection crossoverKappa at *
  rw [abs_of_nonpos] at hbal
  · rw [eq_div_iff] at *
    · field_simp at hbal
      rw [← hbal, mul_div_cancel_right₀ _ (ne_of_gt mat.cs_pos)]; ring
    · exact ne_of_gt (sq_pos_of_pos mat.cs_pos)
    · exact mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 mat.xi_pos.ne')
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (sq_nonneg _)

end SKEFTHawking.KappaScaling
