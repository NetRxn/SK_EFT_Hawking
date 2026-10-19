/-!
Phase5w Wave10b: supplied quasi-1D envelopes and infrared algebra.

T1 bounds the defined scalar4*c_R*v/(c_R+v)^2 by0 and1; equality means
c_R=v, not a step-horizon limit. The physical source is Anderson,
Balbinot,Fabbri,Parentani, PRD90,104044(2014), arXiv1404.3224v3,
Eq36, in its specified BEC infrared setting. It does not derive bilayer
transmission or a finite-band/nozzle response.

T2/T3/T5 assume actual surface/evanescent error envelopes as h_bound,
h_surf,h_evan. Algebra/positive exponentials alone do not prove those
physical hypotheses. T4 uses the supplied kappa2e12,l_ee51nm,c_s4.4e5
and proves D=51/220<1, not an O(D^4) remainder or device validity.

The two H_* definitions are parameterized propositions about caller-
supplied temperatures/cutoff/constants, not inhabited physical theorems.
Their BUILD requires a selected profile/mode/state/PDE analysis and error
bounds, not merely future Mathlib support. Original quantitative objectives
remain owed. For the adopted quadratic cutoff law,
(omega_max/omega_H)^2=4*pi^2/D and rolloff at4*omega_H is4D/pi^2,
about9.4percent at literal D=51/220. Neither flat transmission nor
a physical safety band follows. The separate supplied envelope evaluation
roughly1.8percent is not a measured/derived error certificate.

Python companions retain greybody_zero_freq,greybody_smooth_profile,
dispersive_uv_cutoff,dean_adiabaticity_parameter,quasi1d_correction_bound.
Finazzi-Parentani PRD83,084010(2011), Macher-Parentani PRD80,043601(2009)
and transverse-mode research are motivation with their own assumptions.
-/

import Mathlib

namespace SKEFTHawking
namespace QuasiOneDReduction

/-! ## 1. T1 — Zero-frequency greybody bounds -/

/-- **T1a (greybody_zero_freq_nonneg)**: Γ₀ = 4 c_R v / (c_R + v)² ≥ 0 for positive c_R, v. -/
theorem greybody_zero_freq_nonneg (c_R v : ℝ) (hc : c_R > 0) (hv : v > 0) :
    4 * c_R * v / (c_R + v)^2 ≥ 0 := by
  positivity

/-- **T1b (greybody_zero_freq_le_one)**: Γ₀ ≤ 1 for positive c_R, v.

    Follows from the AM-GM identity 4 c_R v ≤ (c_R + v)² which
    rearranges to 0 ≤ (c_R - v)². -/
theorem greybody_zero_freq_le_one (c_R v : ℝ) (hc : c_R > 0) (hv : v > 0) :
    4 * c_R * v / (c_R + v)^2 ≤ 1 := by
  have h_denom_pos : (c_R + v)^2 > 0 := by positivity
  rw [div_le_one h_denom_pos]
  have h : (c_R - v)^2 ≥ 0 := sq_nonneg _
  nlinarith [h]

/-- **T1c (greybody_zero_freq_eq_one)**: Γ₀ = 1 iff c_R = v, solely a scalar equality. -/
theorem greybody_zero_freq_eq_one (c_R v : ℝ) (hc : c_R > 0) (hv : v > 0) :
    4 * c_R * v / (c_R + v)^2 = 1 ↔ c_R = v := by
  have h_denom_pos : (c_R + v)^2 > 0 := by positivity
  rw [div_eq_one_iff_eq h_denom_pos.ne']
  constructor
  · intro h
    have h_sq : (c_R - v)^2 = 0 := by nlinarith [h]
    have : c_R - v = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h_sq
    linarith
  · intro h
    rw [h]; ring

/-! ## 2. T2 — Surface gravity correction bound (quasi-1D) -/

/--
Non-negativity of the algebraic upper bound `(l_ee/W)²` used in T2.
-/
theorem surface_gravity_coefficient_nonneg (l_ee W : ℝ) :
    0 ≤ (l_ee / W)^2 := sq_nonneg _

/-- Supplied error |delta_kappa/kappa|<=(l_ee/W)^2 implies the stated
    pair of inequalities under0<=l_ee<W. h_bound IS the physical bound,
    not a result of this proof. At literal51nm/1um its envelope is about
    0.0026; interpreting it as target0.26percent error needs an actual
    transverse-profile derivation and normalization. -/
theorem surface_gravity_correction_bound
    (δκ_over_κ l_ee W : ℝ) (hW : W > 0) (h_lee_lt_W : l_ee < W) (h_lee : 0 ≤ l_ee)
    (h_bound : |δκ_over_κ| ≤ (l_ee / W)^2) :
    |δκ_over_κ| ≤ (l_ee / W)^2 ∧ |δκ_over_κ| < 1 := by
  refine ⟨h_bound, ?_⟩
  -- l_ee/W < 1 since 0 ≤ l_ee < W, so (l_ee/W)^2 < 1^2 = 1
  have h_ratio_nonneg : 0 ≤ l_ee / W := div_nonneg h_lee hW.le
  have h_ratio_lt_one : l_ee / W < 1 := (div_lt_one hW).mpr h_lee_lt_W
  have h_sq_lt_one : (l_ee / W)^2 < 1 := by
    have : (l_ee / W)^2 < 1^2 := sq_lt_sq' (by linarith) h_ratio_lt_one
    simpa using this
  linarith [h_bound]

/-! ## 3. T3 — Evanescent transverse-mode bound -/

/--
Non-negativity of the algebraic upper bound used in T3.
-/
theorem evanescent_coefficient_nonneg (ω ω_perp L W : ℝ) :
    0 ≤ (ω / ω_perp)^2 * Real.exp (-2 * Real.pi * L / W) := by
  have h_exp : Real.exp (-2 * Real.pi * L / W) > 0 := Real.exp_pos _
  positivity

/--
The evanescent suppression factor `exp(-2π · L / W)` is strictly less
than1 under the supplied L>0,W>0. This algebra does not derive a
physical transverse-mode decay law, its normalization or threshold.
-/
theorem evanescent_factor_lt_one (L W : ℝ) (hW : W > 0) (hL : 0 < L) :
    Real.exp (-2 * Real.pi * L / W) < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_num_neg : -2 * Real.pi * L < 0 := by nlinarith [h_pi_pos, hL]
  exact div_neg_of_neg_of_pos h_num_neg hW

/-- Consequences of supplied |delta_Gamma/Gamma|<=
    (omega/omega_perp)^2*exp(-2*pi*L/W). The physical mode/Helmholtz
    decay, threshold domain and amplitude normalization are h_bound,
    not derived from exp positivity. Historical0.06,0.284 and about
    1.5percent are illustrative envelope evaluations, not target errors. -/
theorem evanescent_bound
    (δΓ_over_Γ ω ω_perp L W : ℝ) (_hωp : ω_perp > 0) (hW : W > 0)
    (hL : 0 < L)
    (h_bound : |δΓ_over_Γ| ≤ (ω / ω_perp)^2 * Real.exp (-2 * Real.pi * L / W)) :
    |δΓ_over_Γ| ≤ (ω / ω_perp)^2 * Real.exp (-2 * Real.pi * L / W) ∧
      |δΓ_over_Γ| ≤ (ω / ω_perp)^2 := by
  refine ⟨h_bound, ?_⟩
  -- exp(-2πL/W) ≤ 1, so (ω/ω_⊥)² · exp(..) ≤ (ω/ω_⊥)² · 1 = (ω/ω_⊥)²
  have h_exp_lt_one : Real.exp (-2 * Real.pi * L / W) < 1 :=
    evanescent_factor_lt_one L W hW hL
  have h_exp_le_one : Real.exp (-2 * Real.pi * L / W) ≤ 1 := le_of_lt h_exp_lt_one
  have h_sq_nonneg : 0 ≤ (ω / ω_perp)^2 := sq_nonneg _
  have h_scale : (ω / ω_perp)^2 * Real.exp (-2 * Real.pi * L / W) ≤ (ω / ω_perp)^2 := by
    calc (ω / ω_perp)^2 * Real.exp (-2 * Real.pi * L / W)
        ≤ (ω / ω_perp)^2 * 1 := by
          exact mul_le_mul_of_nonneg_left h_exp_le_one h_sq_nonneg
      _ = (ω / ω_perp)^2 := by ring
  linarith

/-! ## 4. T4 — Dean graphene nozzle adiabaticity -/

/-- The literal supplied kappa=2e12s^-1,l_ee=51nm,c_s=4.4e5m/s
    gives D=51/220<1. This rational inequality does not prove
    H_AdiabaticRegimeCorrection, physical adiabaticity or a useful band. -/
theorem dean_adiabatic :
    (2 * 10^12 : ℝ) * (51 * 10^(-9 : ℤ)) / (4.4 * 10^5) < 1 := by
  norm_num

/-! ## 5. T5 — Combined quasi-1D validity bound -/

/--
Non-negativity of the combined algebraic upper bound used in T5.
-/
theorem quasi1D_coefficient_nonneg (ω ω_perp L W l_ee : ℝ) :
    0 ≤ (l_ee / W)^2 + (ω / ω_perp)^2 * Real.exp (-2 * Real.pi * L / W) := by
  have h1 : 0 ≤ (l_ee / W)^2 := sq_nonneg _
  have h2 : 0 ≤ (ω / ω_perp)^2 * Real.exp (-2 * Real.pi * L / W) :=
    evanescent_coefficient_nonneg ω ω_perp L W
  linarith

/-- Add the two supplied physical envelope hypotheses h_surf,h_evan.
    No target2D-to1D theorem or relative-error identification is derived.
    The historical51nm,1um,200nm/roughly1.8percent evaluation is
    conditional on those hypotheses and their actual frequency domain. -/
theorem quasi1D_validity_bound
    (δκ_over_κ δΓ_over_Γ_evan ω ω_perp L W l_ee : ℝ)
    (_hωp : ω_perp > 0) (_hW : W > 0) (_hL : 0 < L)
    (h_surf : |δκ_over_κ| ≤ (l_ee / W)^2)
    (h_evan : |δΓ_over_Γ_evan| ≤ (ω / ω_perp)^2 * Real.exp (-2 * Real.pi * L / W)) :
    |δκ_over_κ| + |δΓ_over_Γ_evan| ≤
        (l_ee / W)^2 + (ω / ω_perp)^2 * Real.exp (-2 * Real.pi * L / W) := by
  linarith

/-! ## 6. Tracked hypotheses for PDE-analysis content -/

/-- A parameterized proposition asserting a C_const*D^4 deviation for
    the supplied T_H_exact,T_H_leading and positive inputs.
    The bound is not constructed, inhabited or established for bilayer
    physics. A caller must derive it for an actual profile/state/mode/
    error regime. Missing Mathlib infrastructure is cost, not route closure.
    Existing finite-order physical research obligations remain BUILD. -/
def H_AdiabaticRegimeCorrection
    (kappa c_s l_ee C_const T_H_exact T_H_leading : ℝ) : Prop :=
  kappa > 0 → c_s > 0 → l_ee > 0 → C_const > 0 → T_H_leading > 0 →
    |T_H_exact - T_H_leading| / T_H_leading ≤
      C_const * (kappa * l_ee / c_s)^4

/-- A parameterized proposition asserting10percent agreement between
    supplied omega_max and C*sqrt(kappa*c_s/l_ee). No target cutoff,
    subluminal BdG spectrum or C calibration is derived. At the adopted
    C=1 model, the reference ratio is2*pi/sqrt(D), about13 for literal
    D=51/220; actual device safety/error matching remains BUILD. -/
def H_DispersiveUVCutoff
    (kappa c_s l_ee ω_max C : ℝ) : Prop :=
  kappa > 0 → c_s > 0 → l_ee > 0 → C > 0 → ω_max > 0 →
    |ω_max - C * Real.sqrt (kappa * c_s / l_ee)| /
      (C * Real.sqrt (kappa * c_s / l_ee)) ≤ (1 / 10 : ℝ)

/-! ## 7. Module summary -/

/-!
Module summary: T1 scalar infrared bounds; T2/T3/T5 consequences of
supplied physical envelopes; T4 literal D<1; two unproved parameterized
physical H_* obligations. These are not a flat finite band, a calibrated
bilayer theorem, an O(D^4) remainder or a physical detection certificate.
-/
end QuasiOneDReduction
end SKEFTHawking
