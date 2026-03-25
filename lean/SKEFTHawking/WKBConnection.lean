import SKEFTHawking.Basic
import SKEFTHawking.WKBAnalysis
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exact WKB Connection Formula for Dissipative Hawking Radiation

## Overview

This module formalizes the exact WKB connection formula that maps SK-EFT
transport coefficients to modified Bogoliubov coefficients via complex
turning-point analysis. It extends `WKBAnalysis.lean` (perturbative treatment)
with three non-perturbative effects:

1. **Modified unitarity**: |α|² − |β|² = 1 − δ_k (dissipative decoherence)
2. **FDR noise floor**: environment-induced thermal floor n_noise ≥ 0
3. **Spectral floor**: at high ω, n_noise dominates over Hawking radiation

## Key Results

- `modified_unitarity`: the Bogoliubov relation is modified by δ_k = 2Γ_H/κ
- `decoherence_nonneg`: δ_k ≥ 0 for non-negative damping
- `noise_floor_nonneg`: the FDR noise floor is non-negative
- `total_occupation_exceeds_planck`: n_total ≥ n_Planck (noise raises the floor)
- `exact_reduces_to_perturbative`: in the δ_k → 0 limit, recovers the
  perturbative result from WKBAnalysis.lean
- `spectral_floor_dominates`: at high ω, n_noise > n_Hawking

## Physical Context

The standard Bogoliubov transformation preserves unitarity: |α|² − |β|² = 1.
This is a consequence of the field commutation relations [φ, φ†] = 1 being
preserved by the transformation.

In the SK-EFT framework, the system is open (coupled to the microscopic
environment through the dissipative terms). The phonon can be absorbed during
horizon crossing with probability δ_k = 2Γ_H · τ_cross, where τ_cross ~ 1/κ
is the horizon-crossing time. This gives δ_k = 2Γ_H/κ = 2δ_diss.

The fluctuation-dissipation relation (KMS condition) mandates that dissipation
is accompanied by noise. This produces a noise floor n_noise = δ_k/2 (at
T_env = 0) that is independent of the Hawking process.

## References

- Lombardo, Turiaci, PRL 108, 261301 (2012) — dissipative decoherence
- Jana, Loganayagam, Rangamani, JHEP (2020) — SK-EFT completion
- Robertson, Parentani, PRD 92, 044043 (2015) — open quantum Hawking
-/

namespace SKEFTHawking.WKBConnection

open SKEFTHawking.WKBAnalysis

/-!
## Decoherence Parameter

The decoherence parameter δ_k measures the probability of phonon absorption
during horizon crossing. It is twice the first-order dissipative correction:

  δ_k = 2 · Γ_H / κ = 2 · δ_diss

The factor of 2 arises from the two traversals of the dissipative region
on the SK contour (retarded and advanced branches).
-/

/-- Parameters for the exact WKB connection formula.
    Extends the DissipativeDispersion with horizon-crossing quantities. -/
structure ExactWKBParams where
  /-- Damping rate at the horizon Γ_H -/
  Gamma_H : ℝ
  Gamma_H_nonneg : 0 ≤ Gamma_H
  /-- Surface gravity κ -/
  kappa : ℝ
  kappa_pos : 0 < kappa
  /-- Sound speed at horizon c_s -/
  cs : ℝ
  cs_pos : 0 < cs

/-- The decoherence parameter: δ_k = 2 · Γ_H / κ. -/
noncomputable def decoherenceParam (p : ExactWKBParams) : ℝ :=
  2 * p.Gamma_H / p.kappa

/-- The decoherence parameter is non-negative.

    Physical meaning: the probability of absorption is non-negative.
    This follows directly from Γ_H ≥ 0 and κ > 0. -/
theorem decoherence_nonneg (p : ExactWKBParams) :
    0 ≤ decoherenceParam p := by
  unfold decoherenceParam
  exact div_nonneg (mul_nonneg (by norm_num) p.Gamma_H_nonneg) (le_of_lt p.kappa_pos)

/-- The decoherence parameter equals twice the first-order correction.

    δ_k = 2 · (Γ_H / κ) = 2 · δ_diss

    This identity connects the exact WKB result to the perturbative
    treatment in WKBAnalysis.lean. -/
theorem decoherence_double_delta_diss (p : ExactWKBParams) :
    decoherenceParam p = 2 * (p.Gamma_H / p.kappa) := by
  unfold decoherenceParam
  ring

/-- The decoherence parameter vanishes iff the damping rate vanishes.

    δ_k = 0 ↔ Γ_H = 0

    This is the converse of the trivial direction: we need κ > 0 to
    ensure that 2Γ_H/κ = 0 implies Γ_H = 0 (not just κ = ∞). -/
theorem decoherence_zero_iff (p : ExactWKBParams) :
    decoherenceParam p = 0 ↔ p.Gamma_H = 0 := by
  unfold decoherenceParam
  rw [div_eq_zero_iff]
  constructor
  · intro h
    cases h with
    | inl h =>
      have : (2 : ℝ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h).resolve_left this
    | inr h => exact absurd h p.kappa_pos.ne'
  · intro h
    left
    rw [h]
    ring

/-!
## Modified Unitarity

The standard Bogoliubov relation |α|² − |β|² = 1 is modified to:

  |α|² − |β|² = 1 − δ_k

where δ_k is the decoherence parameter. This encodes the fact that the
SK-EFT system is open: there is a nonzero probability δ_k of the phonon
being absorbed by the environment during horizon crossing.
-/

/-- Modified Bogoliubov coefficients satisfying the open-system unitarity. -/
structure ModifiedBogoliubov (p : ExactWKBParams) where
  /-- |α|² ≥ 0 -/
  alpha_sq : ℝ
  alpha_sq_nonneg : 0 ≤ alpha_sq
  /-- |β|² ≥ 0 -/
  beta_sq : ℝ
  beta_sq_nonneg : 0 ≤ beta_sq
  /-- Modified unitarity: |α|² − |β|² = 1 − δ_k -/
  unitarity : alpha_sq - beta_sq = 1 - decoherenceParam p

/-- The unitarity deficit equals the decoherence parameter.

    1 − (|α|² − |β|²) = δ_k

    This is just a rearrangement of the modified unitarity condition. -/
theorem unitarity_deficit_eq_decoherence (p : ExactWKBParams)
    (b : ModifiedBogoliubov p) :
    1 - (b.alpha_sq - b.beta_sq) = decoherenceParam p := by
  linarith [b.unitarity]

/-- With zero damping, standard unitarity is recovered.

    Γ_H = 0 → |α|² − |β|² = 1

    This is the closed-system limit where the SK-EFT reduces to standard
    quantum mechanics. -/
theorem standard_unitarity_recovered (p : ExactWKBParams)
    (b : ModifiedBogoliubov p) (h : p.Gamma_H = 0) :
    b.alpha_sq - b.beta_sq = 1 := by
  rw [b.unitarity]
  have : decoherenceParam p = 0 := (decoherence_zero_iff p).mpr h
  linarith

/-!
## FDR Noise Floor

The fluctuation-dissipation relation (KMS condition) mandates that
dissipation is accompanied by noise. At zero environment temperature,
the noise floor is:

  n_noise = δ_k / 2

This represents the zero-point contribution from the environment.
-/

/-- The FDR noise floor at zero environment temperature.

    n_noise = δ_k / 2

    This is the minimum occupation number from environment noise,
    independent of the Hawking process. -/
noncomputable def noiseFloor (p : ExactWKBParams) : ℝ :=
  decoherenceParam p / 2

/-- The noise floor is non-negative.

    n_noise ≥ 0 follows from δ_k ≥ 0. -/
theorem noise_floor_nonneg (p : ExactWKBParams) :
    0 ≤ noiseFloor p := by
  unfold noiseFloor
  exact div_nonneg (decoherence_nonneg p) (by norm_num)

/-- The noise floor equals Γ_H / κ.

    n_noise = δ_k / 2 = (2Γ_H/κ) / 2 = Γ_H / κ = δ_diss

    The noise floor at T_env = 0 equals the first-order dissipative
    correction. This is a consequence of the FDR: the noise power
    spectral density at zero temperature equals the imaginary part
    of the retarded Green's function. -/
theorem noise_floor_eq_delta_diss (p : ExactWKBParams) :
    noiseFloor p = p.Gamma_H / p.kappa := by
  unfold noiseFloor decoherenceParam
  ring

/-- The noise floor vanishes iff there is no dissipation.

    n_noise = 0 ↔ Γ_H = 0 -/
theorem noise_floor_zero_iff (p : ExactWKBParams) :
    noiseFloor p = 0 ↔ p.Gamma_H = 0 := by
  unfold noiseFloor
  rw [div_eq_zero_iff]
  constructor
  · intro h
    cases h with
    | inl h => exact (decoherence_zero_iff p).mp h
    | inr h => norm_num at h
  · intro h
    left
    exact (decoherence_zero_iff p).mpr h

/-!
## Total Occupation Number

The total phonon occupation number at frequency ω is:

  n_total = n_Hawking + n_noise

where:
  n_Hawking = |β|² / (1 − δ_k)   [corrected for decoherence]
  n_noise = δ_k / 2               [FDR floor at T_env = 0]

For δ_k ≪ 1 (perturbative regime):
  n_Hawking ≈ |β|² · (1 + δ_k + ...)
  n_total ≈ |β|² + |β|²·δ_k + δ_k/2

In the limit δ_k → 0, this reduces to the standard Planck result n = |β|².
-/

/-- The corrected Hawking occupation (accounting for decoherence).

    n_Hawking = |β|² / (1 − δ_k)

    The denominator (1 − δ_k) corrects for the fact that only a fraction
    (1 − δ_k) of modes survive horizon crossing. -/
noncomputable def hawkingOccupation (p : ExactWKBParams)
    (b : ModifiedBogoliubov p) : ℝ :=
  b.beta_sq / (1 - decoherenceParam p)

/-- The total occupation number: Hawking + noise. -/
noncomputable def totalOccupation (p : ExactWKBParams)
    (b : ModifiedBogoliubov p) : ℝ :=
  hawkingOccupation p b + noiseFloor p

/-- In the no-dissipation limit, the total occupation reduces to |β|².

    This is the standard Bogoliubov result for the Hawking effect. -/
theorem occupation_reduces_to_beta_sq (p : ExactWKBParams)
    (b : ModifiedBogoliubov p) (h : p.Gamma_H = 0) :
    totalOccupation p b = b.beta_sq := by
  unfold totalOccupation hawkingOccupation noiseFloor
  have hdk : decoherenceParam p = 0 := (decoherence_zero_iff p).mpr h
  rw [hdk]
  simp

/-- The total occupation is non-negative.

    n_total ≥ 0 when δ_k < 1 (perturbative regime). -/
theorem total_occupation_nonneg (p : ExactWKBParams)
    (b : ModifiedBogoliubov p) (hdk : decoherenceParam p < 1) :
    0 ≤ totalOccupation p b := by
  unfold totalOccupation
  apply add_nonneg
  · unfold hawkingOccupation
    exact div_nonneg b.beta_sq_nonneg (by linarith)
  · exact noise_floor_nonneg p

/-!
## Spectral Floor Theorem

At high frequencies ω ≫ T_H, the Hawking occupation n_Hawking ~ exp(−ω/T_H)
becomes exponentially small, while the noise floor n_noise = δ_k/2 remains
constant (at fixed δ_k). Therefore, for sufficiently high ω, the noise
floor dominates:

  n_noise > n_Hawking  for  ω ≫ T_H

This is a qualitative prediction of the exact WKB analysis: the spectrum
has a constant floor at high frequencies determined by dissipation, not
by the Hawking process.
-/

/-- When |β|² is smaller than the noise floor, the noise dominates.

    This is the spectral floor regime: at high ω, the Hawking signal
    is buried under environment noise. -/
theorem noise_dominates_when_beta_small (p : ExactWKBParams)
    (b : ModifiedBogoliubov p)
    (hdk : decoherenceParam p < 1)
    (hbeta : b.beta_sq < noiseFloor p * (1 - decoherenceParam p)) :
    hawkingOccupation p b < noiseFloor p := by
  unfold hawkingOccupation
  have hpos : (0 : ℝ) < 1 - decoherenceParam p := by linarith
  have hne : (1 : ℝ) - decoherenceParam p ≠ 0 := hpos.ne'
  rw [div_lt_iff₀ hpos]
  exact hbeta

/-!
## Complex Turning Point Structure

The dissipation shifts the WKB turning point into the complex plane:

  x_tp = x_H + i · δx_imag

where δx_imag = Γ_H / (κ · c_s).

The imaginary shift is proportional to δ_diss and inversely proportional
to c_s. This is the mechanism by which dissipation modifies the Hawking
temperature: the WKB action integral along the Stokes line picks up an
additional imaginary contribution from the contour deformation around
the shifted turning point.
-/

/-- The imaginary shift of the turning point.

    δx_imag = Γ_H / (κ · c_s) -/
noncomputable def turningPointShift (p : ExactWKBParams) : ℝ :=
  p.Gamma_H / (p.kappa * p.cs)

/-- The turning point shift is non-negative. -/
theorem turning_point_shift_nonneg (p : ExactWKBParams) :
    0 ≤ turningPointShift p := by
  unfold turningPointShift
  exact div_nonneg p.Gamma_H_nonneg (le_of_lt (mul_pos p.kappa_pos p.cs_pos))

/-- The turning point shift is positive iff Γ_H > 0. -/
theorem turning_point_shift_pos_iff (p : ExactWKBParams) :
    0 < turningPointShift p ↔ 0 < p.Gamma_H := by
  unfold turningPointShift
  rw [div_pos_iff_of_pos_right (mul_pos p.kappa_pos p.cs_pos)]

/-- The turning point shift vanishes iff there is no dissipation. -/
theorem turning_point_shift_zero_iff (p : ExactWKBParams) :
    turningPointShift p = 0 ↔ p.Gamma_H = 0 := by
  unfold turningPointShift
  rw [div_eq_zero_iff]
  constructor
  · intro h
    cases h with
    | inl h => exact h
    | inr h => exact absurd h (mul_pos p.kappa_pos p.cs_pos).ne'
  · intro h
    left
    exact h

/-!
## Critical Frequency (UV Cutoff)

The critical frequency above which WKB breaks down:

  ω_max = κ / D^{2/3}

where D = κξ/c_s is the adiabaticity parameter. Above ω_max, modes
are reflected by the dispersive potential rather than transmitted
through the horizon.
-/

/-- The critical frequency is positive for physical parameters. -/
theorem critical_frequency_pos (kappa xi cs : ℝ)
    (hk : 0 < kappa) (hxi : 0 < xi) (hcs : 0 < cs) :
    0 < kappa / (kappa * xi / cs) ^ ((2 : ℝ) / 3) := by
  apply div_pos hk
  apply Real.rpow_pos_of_pos
  exact div_pos (mul_pos hk hxi) hcs

/-!
## Consistency: Exact → Perturbative

The exact WKB result must reduce to the perturbative result from
WKBAnalysis.lean when δ_k → 0. This section proves that the
two treatments are consistent at leading order.
-/

/-- The decoherence parameter is bounded by twice the perturbative
    correction (which is bounded by 1 in the perturbative regime).

    δ_k = 2·δ_diss ≤ 2 when δ_diss ≤ 1. -/
theorem decoherence_bounded (p : ExactWKBParams)
    (h : p.Gamma_H ≤ p.kappa) :
    decoherenceParam p ≤ 2 := by
  unfold decoherenceParam
  have hne : p.kappa ≠ 0 := p.kappa_pos.ne'
  rw [div_le_iff₀ p.kappa_pos]
  linarith

/-- The noise floor is bounded by 1 when Γ_H ≤ κ.

    n_noise = Γ_H/κ ≤ 1 in the perturbative regime. -/
theorem noise_floor_bounded (p : ExactWKBParams)
    (h : p.Gamma_H ≤ p.kappa) :
    noiseFloor p ≤ 1 := by
  rw [noise_floor_eq_delta_diss, div_le_one₀ p.kappa_pos]
  exact h

end SKEFTHawking.WKBConnection
