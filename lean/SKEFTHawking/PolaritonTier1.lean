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

/-!
## Wave 6v.4: Penn TMD nanocavity polariton scope demarcation

The UPenn nanocavity exciton-polariton platform of Wang, Kim, Zhen, He
(PRL 136, 146901 (2026); arXiv:2411.16635) is a charge-tunable MoSe₂
monolayer in a planar photonic-crystal nanocavity. The device's
measured lower-polariton linewidth is γ_LP = 1.8 meV, corresponding to
a polariton decoherence rate

    Γ_LP = γ_LP / ℏ = (1.8 meV) / ℏ ≈ 2.7347 × 10¹² s⁻¹.

The platform is NOT itself an analog-horizon device — it forms no
sonic horizon. The theorem below establishes that even pairing this
Γ_LP against the *most generous* analog-horizon surface gravity ever
demonstrated in the polariton family (the Falque-LKB steep-horizon
maximum κ = 1.1 × 10¹¹ s⁻¹, FALQUE_STEEP_HORIZON_KAPPA in
src/core/constants.py), the validity ratio is

    Γ_LP / κ_max ≈ 24.86

which exceeds the SK-EFT Tier-1 perturbative-patch validity threshold
0.1 by a factor of nearly 250. This is a positive scope demarcation
for the E1 (Paris-LKB polariton) bundle: Tier 1 covers GaAs / Paris-
LKB long-lifetime polariton fluids in the smooth-horizon regime; it
does NOT cover ultrafast TMD-polariton nanocavities. No new axiom is
introduced; the result follows from `validityRatio` and `norm_num`
discharge of the numerical inequality.

Numerical-encoding choice: the Lean parameters use exact rationals
`Gamma_pol := 27347 * 10^8` and `kappa := 11 * 10^10`, equal to
`2.7347 × 10¹² s⁻¹` and `1.1 × 10¹¹ s⁻¹` respectively. The Γ_LP
rational uses 4-digit precision matching the Python provenance entry
`Penn_TMD_MoSe2.Gamma_pol = 2.7347e12` in
`src/core/provenance.py`.
-/

/-- The UPenn nanocavity TMD-polariton MoSe₂ platform parameters
    (Wang, Kim, Zhen, He, PRL 136, 146901 (2026); arXiv:2411.16635),
    paired with the Falque-LKB steep-horizon maximum κ as the
    *most generous* analog-horizon surface gravity. The `v_g` and
    `L` fields are not used by the `validityRatio` predicate. -/
noncomputable def pennTmdPolaritonParams : PolaritonParams where
  kappa     := 11 * 10^10        -- 1.1 × 10¹¹ s⁻¹ = FALQUE_STEEP_HORIZON_KAPPA
  Gamma_pol := 27347 * 10^8      -- 2.7347 × 10¹² s⁻¹ = γ_LP / ℏ (γ_LP = 1.8 meV)
  v_g       := 4 * 10^5          -- 4 × 10⁵ m/s (Falque c_s baseline; placeholder)
  L         := 0                  -- not used in validityRatio
  kappa_pos        := by norm_num
  Gamma_pol_nonneg := by norm_num
  v_g_pos          := by norm_num
  L_nonneg         := by norm_num

/-- Wave 6v.4 scope-demarcation theorem.

    The UPenn nanocavity TMD-polariton platform's validity ratio
    Γ_pol / κ is ≥ 1/10 = 0.1 even at the *most generous* polariton-
    family surface gravity (Falque-LKB steep-horizon κ = 1.1×10¹¹ s⁻¹).
    Consequently the Tier-1 perturbative-dissipation patch — defined
    by the strict inequality `validityRatio < 0.1` — does NOT hold.

    Quantitatively the ratio is ≈ 24.86, exceeding the threshold by
    a factor of nearly 250. This is a positive scope demarcation for
    the E1 bundle: Tier 1 covers GaAs / Paris-LKB long-lifetime
    polariton fluids in the smooth-horizon regime, NOT ultrafast
    TMD-polariton nanocavities. -/
theorem polariton_tier1_fails_tmds :
    (1 / 10 : ℝ) ≤ validityRatio pennTmdPolaritonParams := by
  unfold validityRatio pennTmdPolaritonParams
  norm_num

/-- Companion: the Tier-1 perturbative-dissipation predicate
    (`validityRatio p < 1/10`) does NOT hold on the UPenn nanocavity
    TMD-polariton platform. Direct contrapositive of
    `polariton_tier1_fails_tmds`. -/
theorem polariton_tier1_predicate_fails_tmds :
    ¬ (validityRatio pennTmdPolaritonParams < (1 / 10 : ℝ)) :=
  not_lt.mpr polariton_tier1_fails_tmds

end SKEFTHawking.PolaritonTier1
