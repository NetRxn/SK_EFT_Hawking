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

    This is negative (blue-shift) and quadratic in κ.

    ⚠️ **`π/6` IS A DECLARED PROJECT NORMALIZATION, NOT A DERIVED CONSTANT.**
    Everything downstream — `crossoverKappa` (whose `6/π` is this coefficient
    inverted), `dispersive_correction_bound`, `kappa_scaling_dispersive_quadratic`,
    `HawkingUniversality.universalEffectiveTemp`, `GrapheneHawking`, and the
    δ_disp numbers printed in papers E1, E2 and D1 — is a statement about THIS
    DEFINITION, and moves if this number moves.

    What is established, and what is not:

    * The **D² scaling** is supported. Coutant–Weinfurtner (PRD 2017) obtain
      analytic expressions in the KdV approximation and find the leading
      correction to the effective temperature is O(ξ²κ²/c_s²) = O(D²) in the
      adiabatic regime. That is a *parametric* O(·) result.
    * The **coefficient is not derived anywhere, and no universal value exists.**
      A near-horizon Hamilton–Jacobi computation shows why: with
      ω = (v(x)+c_s)k + (c_sξ²/8)k³ and the inverse-profile series x(u) = Σ cᵖₙuⁿ,
      the tunneling exponent is 2π·Res_{k=0}[x dk] and only n ≡ 1 (mod 3) survives,
      giving ω·(cᵖ₁ − 4β cᵖ₄ ω² + 21β² cᵖ₇ ω⁴ + …) with β = c_sξ²/8. The leading
      term cᵖ₁ = 1/κ gives T_H = κ/2π exactly; the first dispersive term is
      −4β cᵖ₄ ω³, cubic in ω (a non-thermal distortion, not a temperature
      rescaling) with magnitude set by cᵖ₄ — a fourth-order datum of the velocity
      profile. Coutant–Parentani (PRD 90, 121501(R), 2014) prove the same by full
      mode calculation: β_ω = e^{−πω/κ}α_ω exactly for a locally linear profile,
      with a correction appearing only from the profile's non-linear part. Del
      Porro–Liberati–Schneider (arXiv:2406.14603) get (3/8)α² for a specific tanh
      profile and say the coefficient "depends crucially on the specific geometry".
    * **Do not attribute π/6 to Corley–Jacobson 1996** (numerical; fitted powers
      whose exponent is itself profile-dependent — p ≈ 3, 2, 1 across profiles;
      no D² law, no π/6) **or to Finazzi–Parentani 2012** (their D = κL/Λ is a
      different parameter, and their analytic coefficients there are 1/6 and
      3√3/8 multiplying D linearly).

    Canonical Python home: `src/core/formulas.DISPERSIVE_C1`; standing recorded in
    `PARAMETER_PROVENANCE['EFT.DISPERSIVE_C1']`; see
    `papers/AutomatedReviews/2026-08-15-dispersive-coefficient-normalization/`. -/
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
## Corrections vs. the adiabaticity parameter

`HawkingUniversality.adiabaticityParam κ c_s Λ = κ/(c_s·Λ)` is the dimensionless
control parameter of the universality expansion. For a BEC the EFT cutoff momentum
is the inverse healing length, Λ = 1/ξ, so

  D = adiabaticityParam κ c_s (1/ξ) = κ·ξ/c_s = T_H/T_max,

which is 0.02–0.04 in current experiments. The two theorems below re-express the
`dispersiveCorrection` / `dissipativeCorrection` definitions above in terms of D and
of the transport coefficients — they are the statements `src/core/formulas.py` cites.
-/

/-- **Dispersive correction bound.**

    The dispersive correction is exactly `−(π/6)·D²` in the adiabaticity parameter
    `D = adiabaticityParam κ c_s (1/ξ)`, hence bounded in magnitude by `(π/6)·D²`
    and nonzero for every `κ > 0`:

      δ_disp(κ) = −(π/6)·D²,  |δ_disp(κ)| ≤ (π/6)·D²,  δ_disp(κ) ≠ 0.

    **Nothing here is existentially quantified.** The bounded quantity is
    `dispersiveCorrection`, the project's definition of δ_disp (the quantity
    `src/core/formulas.py::dispersive_correction(D)` computes), and the bounding
    constant is the explicit number π/6 — so a witness cannot be chosen to
    satisfy the inequality. The bound is sharp, by the first conjunct.

    ⚠️ This theorem was previously headed "(Corley–Jacobson 1996;
    Coutant–Parentani 2014)". That attribution is withdrawn: neither paper
    contains a `D²` law or the constant π/6, and π/6 is a DECLARED PROJECT
    NORMALIZATION of an O(1) profile-dependent coefficient — see
    `dispersiveCorrection` for the standing and the sources that do apply.

    Companion of `kappa_scaling_dispersive_quadratic`, which fixes the same
    correction's κ-dependence at fixed material parameters. -/
theorem dispersive_correction_bound (mat : MaterialParams) (kappa : ℝ)
    (hkappa : 0 < kappa) :
    dispersiveCorrection mat kappa
        = -(π / 6) * HawkingUniversality.adiabaticityParam kappa mat.cs (1 / mat.xi) ^ 2 ∧
      |dispersiveCorrection mat kappa|
        ≤ π / 6 * HawkingUniversality.adiabaticityParam kappa mat.cs (1 / mat.xi) ^ 2 ∧
      dispersiveCorrection mat kappa ≠ 0 := by
  -- D = κ/(c_s·(1/ξ)) = ξκ/c_s, so δ_disp = −(π/6)·(ξκ/c_s)² = −(π/6)·D².
  have hD : HawkingUniversality.adiabaticityParam kappa mat.cs (1 / mat.xi)
      = mat.xi * kappa / mat.cs := by
    unfold HawkingUniversality.adiabaticityParam
    field_simp
  have hid : dispersiveCorrection mat kappa
      = -(π / 6) * HawkingUniversality.adiabaticityParam kappa mat.cs (1 / mat.xi) ^ 2 := by
    rw [hD]
    unfold dispersiveCorrection
    ring
  have hneg : dispersiveCorrection mat kappa < 0 := dispersive_neg mat kappa hkappa
  refine ⟨hid, ?_, ne_of_lt hneg⟩
  rw [abs_of_nonpos hneg.le, hid]
  linarith

/-- **Dissipative correction: vanishing criterion (core SK-EFT result).**

    The dissipative correction `dissipativeCorrection` vanishes exactly when both
    first-order transport coefficients vanish, and is *strictly positive* (a genuine
    red-shift, not merely nonzero) as soon as either is positive:

      γ₁ = γ₂ = 0  →  δ_diss(κ) = 0,     0 < γ₁ ∨ 0 < γ₂  →  0 < δ_diss(κ).

    Together the two implications characterise the zero set of δ_diss, because
    `γ₁, γ₂ ≥ 0` on `MaterialParams`.

    **Nothing here is existentially quantified**: the subject is the defined
    correction `δ_diss(κ) = (γ₁+γ₂)·κ/c_s²` (the quantity
    `src/core/formulas.py::dissipative_correction` computes as `Γ_H/κ`), not a
    witness. Historical name retained — `ARISTOTLE_THEOREMS`, `formulas.py` and the
    Phase-5 roadmaps cite it — although the statement is now a characterisation
    rather than an existence claim. -/
theorem dissipative_correction_existence (mat : MaterialParams) (kappa : ℝ)
    (hkappa : 0 < kappa) :
    ((mat.gamma_1 = 0 ∧ mat.gamma_2 = 0) → dissipativeCorrection mat kappa = 0) ∧
      ((0 < mat.gamma_1 ∨ 0 < mat.gamma_2) → 0 < dissipativeCorrection mat kappa) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold dissipativeCorrection
    rw [h.1, h.2]
    ring
  · unfold dissipativeCorrection
    have hg : 0 < mat.gamma_1 + mat.gamma_2 := by
      rcases h with h | h
      · linarith [mat.gamma_2_nonneg]
      · linarith [mat.gamma_1_nonneg]
    exact div_pos (mul_pos hg hkappa) (pow_pos mat.cs_pos 2)

/-- **The universality theorem's correction fields ARE the definitions above.**

    `HawkingUniversality.universalEffectiveTemp` — the dressed temperature
    `HawkingUniversality.hawking_universality` is stated about — carries
    `δ_disp = −(π/6)·D²` and `δ_diss = (γ₁+γ₂)·κ/c_s²` as *defined* fields. Under the
    BEC identification of the EFT cutoff with the inverse healing length, `Λ = 1/ξ`,
    and with the transport coefficients of `DissipativeCoeffs` and `MaterialParams`
    identified, those two fields are literally `dispersiveCorrection` and
    `dissipativeCorrection` evaluated at the horizon's surface gravity.

    This is the link the universality theorem cannot state itself: `KappaScaling`
    imports `HawkingUniversality`, so the correction definitions are not in scope
    there. It is the same identification `dispersive_correction_bound` uses, and it
    is what makes `hawking_universality` a statement about the project's corrections
    rather than about two ad-hoc expressions. -/
theorem universalEffectiveTemp_corrections_eq (mat : MaterialParams)
    (mdr : HawkingUniversality.ModifiedDispersion) (coeffs : DissipativeCoeffs)
    {bg : FluidBackground} (h : SonicHorizon bg)
    (hcs : mdr.cs = mat.cs) (hcut : mdr.cutoff = 1 / mat.xi)
    (hg1 : coeffs.gamma_1 = mat.gamma_1) (hg2 : coeffs.gamma_2 = mat.gamma_2) :
    (HawkingUniversality.universalEffectiveTemp mdr coeffs h).delta_disp
        = dispersiveCorrection mat h.surfaceGravity ∧
      (HawkingUniversality.universalEffectiveTemp mdr coeffs h).delta_diss
        = dissipativeCorrection mat h.surfaceGravity := by
  constructor
  · show -(π / 6) * HawkingUniversality.adiabaticityParam h.surfaceGravity mdr.cs mdr.cutoff ^ 2
        = dispersiveCorrection mat h.surfaceGravity
    rw [hcs, hcut]
    exact ((dispersive_correction_bound mat h.surfaceGravity h.surfaceGravity_pos).1).symm
  · show (coeffs.gamma_1 + coeffs.gamma_2) * h.surfaceGravity / mdr.cs ^ 2
        = dissipativeCorrection mat h.surfaceGravity
    rw [hcs, hg1, hg2]
    rfl

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
