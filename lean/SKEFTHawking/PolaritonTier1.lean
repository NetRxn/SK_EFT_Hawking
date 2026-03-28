import SKEFTHawking.Basic
import SKEFTHawking.HawkingUniversality
import SKEFTHawking.KappaScaling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Polariton Tier 1: Perturbative Dissipation Patch

## Overview

This module formalizes the Tier 1 perturbative patch for extending
SK-EFT predictions to driven-dissipative polariton condensates.

The key result: the Hawking temperature formula T_H = ℏκ/(2πk_B)
is unchanged in polariton systems. The driven-dissipative nature
introduces a uniform spatial attenuation (from cavity photon decay)
that affects signal visibility but not the intrinsic thermal spectrum.

## Tier 1 Validity

The perturbative patch is valid when Γ_pol/κ << 1, where:
- Γ_pol = 1/τ_cav is the polariton decay rate (frequency-independent)
- κ is the surface gravity at the sonic horizon

## Key Theorems

1. Spatial attenuation factor is ≥ 1 (always amplifies the correction)
2. Tier 1 validity ratio is non-negative
3. The attenuation factor is monotone in Γ_pol (more decay → larger correction)
4. In the Tier 1 limit (Γ_pol → 0), the attenuation factor → 1 (BEC recovery)

## References

- Grisins et al., PRB 94, 144518 (2016) — T_H survives
- Jacquet et al., Eur. Phys. J. D 76, 152 (2022) — kinematics preserved
- Falque et al., PRL 135, 023401 (2025) — Paris polariton horizons
-/

namespace SKEFTHawking.PolaritonTier1

open Real

/-!
## Definitions
-/

/-- Polariton platform parameters for Tier 1 analysis. -/
structure PolaritonParams where
  /-- Surface gravity at the sonic horizon [s⁻¹] -/
  kappa : ℝ
  /-- Polariton cavity decay rate [s⁻¹] -/
  Gamma_pol : ℝ
  /-- Group velocity of propagating mode [m/s] -/
  v_g : ℝ
  /-- Propagation distance from horizon [m] -/
  L : ℝ
  kappa_pos : 0 < kappa
  Gamma_pol_nonneg : 0 ≤ Gamma_pol
  v_g_pos : 0 < v_g
  L_nonneg : 0 ≤ L

/-- Spatial attenuation correction factor.
    N_corr = N_meas × exp(Γ_pol · L / v_g)

    Polariton excitations decay at rate Γ_pol as they propagate away
    from the horizon. The measured occupation must be multiplied by
    this factor to recover the intrinsic thermal spectrum. -/
noncomputable def attenuationFactor (p : PolaritonParams) : ℝ :=
  exp (p.Gamma_pol * p.L / p.v_g)

/-- Tier 1 validity ratio: Γ_pol / κ.
    The perturbative patch is valid when this ratio is << 1. -/
noncomputable def validityRatio (p : PolaritonParams) : ℝ :=
  p.Gamma_pol / p.kappa

/-!
## Theorems
-/

/-- The spatial attenuation factor is always ≥ 1.
    Since Γ_pol ≥ 0, L ≥ 0, v_g > 0, the exponent is ≥ 0,
    so exp(exponent) ≥ exp(0) = 1. -/
theorem attenuation_ge_one (p : PolaritonParams) :
    1 ≤ attenuationFactor p := by
  unfold attenuationFactor
  rw [← exp_zero]
  exact exp_le_exp.mpr (div_nonneg (mul_nonneg p.Gamma_pol_nonneg p.L_nonneg) (le_of_lt p.v_g_pos))

/-- The validity ratio is non-negative. -/
theorem validity_nonneg (p : PolaritonParams) :
    0 ≤ validityRatio p := by
  unfold validityRatio
  exact div_nonneg p.Gamma_pol_nonneg (le_of_lt p.kappa_pos)

/-- When Γ_pol = 0 (no cavity decay), the attenuation factor is exactly 1.
    This recovers the equilibrium BEC limit. -/
theorem attenuation_eq_one_at_zero_decay (p : PolaritonParams)
    (h : p.Gamma_pol = 0) :
    attenuationFactor p = 1 := by
  unfold attenuationFactor
  rw [h]
  simp

/-- When Γ_pol = 0, the validity ratio is 0 (trivially valid). -/
theorem validity_zero_at_zero_decay (p : PolaritonParams)
    (h : p.Gamma_pol = 0) :
    validityRatio p = 0 := by
  unfold validityRatio
  rw [h]
  simp

/-- Monotonicity: larger Γ_pol gives larger attenuation factor.
    If Γ₁ ≤ Γ₂ (with same L, v_g), then attenuation₁ ≤ attenuation₂. -/
theorem attenuation_mono_Gamma (p₁ p₂ : PolaritonParams)
    (hL : p₁.L = p₂.L) (hv : p₁.v_g = p₂.v_g)
    (hGamma : p₁.Gamma_pol ≤ p₂.Gamma_pol) :
    attenuationFactor p₁ ≤ attenuationFactor p₂ := by
  unfold attenuationFactor
  apply exp_le_exp.mpr
  have h1 : p₁.Gamma_pol * p₁.L ≤ p₂.Gamma_pol * p₂.L := by
    rw [hL]; exact mul_le_mul_of_nonneg_right hGamma p₂.L_nonneg
  have h2 : (0 : ℝ) < p₁.v_g := p₁.v_g_pos
  rw [hv]
  exact div_le_div_of_nonneg_right h1 (le_of_lt p₂.v_g_pos)

/-- The attenuation exponent Γ_pol · L / v_g is non-negative. -/
theorem attenuation_exponent_nonneg (p : PolaritonParams) :
    0 ≤ p.Gamma_pol * p.L / p.v_g := by
  exact div_nonneg (mul_nonneg p.Gamma_pol_nonneg p.L_nonneg) (le_of_lt p.v_g_pos)

end SKEFTHawking.PolaritonTier1
