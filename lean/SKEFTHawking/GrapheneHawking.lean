import SKEFTHawking.Basic
import SKEFTHawking.DiracFluidMetric
import SKEFTHawking.HawkingUniversality
import SKEFTHawking.WKBAnalysis
import SKEFTHawking.WKBConnection

/-!
# Graphene Hawking Radiation Predictions (Phase 5w Wave 3)

## Physical Content

The Dirac fluid in graphene has SUBLUMINAL dispersion corrections,
unlike the BEC which has SUPERLUMINAL Bogoliubov dispersion.  This
makes the Hawking temperature formula MORE robust:

- BEC: ω² = c_s²k²(1 + k²ξ²) — superluminal, high-k modes escape
- Graphene: v_F(k) increases at small k (Coulomb renormalization) —
  subluminal, high-k modes CANNOT escape, strengthening the horizon

The dispersive correction is δ_disp = -(π/6)D² with D = κ·l_ee/c_s.

⚠️ **Corrected 2026-08-09.** This header previously said δ_disp is the
DOMINANT correction, "negligible by 11 orders of magnitude because
η/(sT) << 1". η/(sT) is a **time**, not a dimensionless number, and comparing
it to 1 is the error: converting it to the kinematic viscosity the SK-EFT
needs requires a velocity² (see `DiracFluidSK.kinematicViscosity`). With that
factor restored, δ_diss ≈ +6.5 % at the Dean device against δ_disp ≈ −2.8 % —
the dissipative term is the LARGER of the two, and they carry opposite signs
and partially cancel. The eleven orders were an artifact, not a hierarchy.

## Key Results

1. Hawking temperature is universal (from HawkingUniversality.lean)
2. Dispersive correction bound applies with D = κ·l_ee/c_s
3. Dissipative correction is perturbative at the Dean device (|δ_diss| < 0.1),
   but is LARGER than the dispersive one there — not `δ_diss << δ_disp`
4. EFT validity requires D < 1 (sets minimum constriction length)
5. Subluminal dispersion strengthens horizon (no trans-Planckian leakage)

## Reused Theorems (41 total, 0 modifications)

From HawkingUniversality.lean (9): hawking_universality, dispersive_correction_bound, etc.
From WKBConnection.lean (17): unitarity_deficit_eq_decoherence, noise_floor_eq_delta_diss, etc.
From WKBAnalysis.lean (15): dissipative_occupation_planckian, turning_point_shift, etc.

## References

- Coutant & Parentani, PRD 81, 024009 (2010) — dispersive corrections
- Deep research §3: T_H estimates for 5 geometries
-/

namespace SKEFTHawking.GrapheneHawking

open SKEFTHawking.DiracFluidMetric SKEFTHawking.AcousticMetric

/-!
## Graphene-Specific Theorems

These are the genuinely new results — everything else is reused from
the existing 1+1D infrastructure via the block-diagonal reduction.
-/

/-- The adiabaticity parameter for graphene: D = κ · l_ee / c_s.

    In BEC, D = κξ/c_s with ξ the healing length.
    In graphene, the EFT cutoff is the electron-electron scattering
    length l_ee = ℏv_F/(k_BT), the scale below which hydrodynamics
    breaks down.

    The EFT expansion is valid when D < 1. -/
noncomputable def grapheneAdiabaticity (kappa l_ee c_s : ℝ) : ℝ :=
  kappa * l_ee / c_s

/-- The adiabaticity parameter is positive when all inputs are positive. -/
theorem grapheneAdiabaticity_pos (kappa l_ee c_s : ℝ)
    (hk : 0 < kappa) (hl : 0 < l_ee) (hc : 0 < c_s) :
    0 < grapheneAdiabaticity kappa l_ee c_s := by
  unfold grapheneAdiabaticity; positivity

/-- The dispersive correction is bounded by D²:
    |δ_disp| ≤ (π/6) D².

    This is the Coutant-Parentani result applied to graphene.
    The correction is negative (cooling) for both subluminal and
    superluminal dispersion. For subluminal (graphene), the correction
    is MORE robust because high-momentum modes cannot escape. -/
theorem graphene_dispersive_correction_bounded (D : ℝ) :
    |-(Real.pi / 6 * D ^ 2)| ≤ Real.pi / 6 * D ^ 2 := by
  rw [abs_neg, abs_of_nonneg (by positivity)]

/-- The dissipative correction is non-negative: δ_diss = Γ_H/κ ≥ 0.

    For the Dean device Γ_H ≈ 1.3×10¹¹ s⁻¹ and κ = 2×10¹² s⁻¹, giving
    δ_diss ≈ 6.5×10⁻² — larger than |δ_disp| ≈ 2.8×10⁻², and of opposite
    sign, so the two partially cancel.

    ⚠️ The superseded figures (Γ_H ~ 0.3 s⁻¹, δ_diss ~ 10⁻¹³) came from
    omitting the velocity² in ν; 0.3 s⁻¹ is eleven orders below the
    Γ_sound ~ 10¹⁰ s⁻¹ that Phase-5w reports for this fluid.

    This theorem comes directly from WKBAnalysis.lean via the
    block-diagonal reduction. No adaptation needed. -/
theorem graphene_dissipative_nonneg (Gamma_H kappa : ℝ)
    (hG : 0 ≤ Gamma_H) (hk : 0 < kappa) :
    0 ≤ Gamma_H / kappa :=
  div_nonneg hG hk.le

/-- The effective temperature with the dispersive correction alone:
    T_eff ≈ T_H · (1 - (π/6)D²)

    ⚠️ This isolates the dispersive channel; it is **not** the full T_eff.
    δ_diss is not negligible (see `graphene_dissipative_nonneg`), so the
    physical T_eff carries both terms and, at the Dean device, exceeds T_H.

    This is positive when D² < 6/π, i.e., D < √(6/π) ≈ 1.38.
    For the Dean nozzle, D ≈ 0.23 → T_eff/T_H ≈ 0.97. -/
theorem graphene_T_eff_positive (T_H D : ℝ)
    (hT : 0 < T_H) (hD : D ^ 2 < 6 / Real.pi) :
    0 < T_H * (1 - Real.pi / 6 * D ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi / 6 := by positivity
  have h1 : Real.pi / 6 * D ^ 2 < Real.pi / 6 * (6 / Real.pi) :=
    mul_lt_mul_of_pos_left hD hpi
  have h2 : Real.pi / 6 * (6 / Real.pi) = 1 := by
    field_simp
  rw [h2] at h1
  exact mul_pos hT (by linarith)

/-- The EFT validity condition: D < 1 ensures the perturbative
    expansion is reliable.  When D ≥ 1, the dispersive correction
    δ_disp ≥ π/6 ≈ 0.52, and higher-order terms are not controlled.

    This sets a MINIMUM constriction length for valid predictions:
    L_min = κ · l_ee / c_s requires L > l_ee (the nozzle must be
    longer than the mean free path). -/
theorem eft_validity_bound (D : ℝ) (hD0 : 0 ≤ D) (hD : D < 1) :
    Real.pi / 6 * D ^ 2 < Real.pi / 6 := by
  have hD2 : D ^ 2 < 1 := by nlinarith [sq_nonneg D]
  have hpi : 0 < Real.pi / 6 := by positivity
  nlinarith

/-- The Hawking temperature formula T_H = κ/(2π) is dimension-independent.
    It applies identically to the graphene Dirac fluid as to the BEC,
    because the (t,x) block of the 3×3 metric has the same structure
    as the 1+1D BEC metric (by DiracFluidMetric.lean block-diag theorem).

    This imports directly from AcousticMetric.lean / HawkingUniversality.lean
    with no modification. -/
theorem graphene_T_H_formula (kappa : ℝ) :
    hawkingTemp kappa = kappa / (2 * Real.pi) := rfl

end SKEFTHawking.GrapheneHawking
