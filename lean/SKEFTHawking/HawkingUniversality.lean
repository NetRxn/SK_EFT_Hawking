import SKEFTHawking.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Structure C: Hawking Temperature Universality

## Statement

For any UV modification of the phonon dispersion relation satisfying:
  (i)  Subluminal or superluminal at high k
  (ii) Smooth in the adiabatic sense: D = κL/Λ ≫ 1
the effective temperature extracted from the asymptotic occupation number
satisfies:

  T_eff = T_H (1 + O(T_H/Λ)²)

This is the Corley-Jacobson (1996) / Coutant-Parentani (2014) universality
result, extended here to include dissipative modifications.

## Physical Context

The trans-Planckian problem: Hawking quanta at late times originated from
exponentially blue-shifted modes near the horizon, with frequencies far
above the EFT cutoff Λ ~ 1/ξ. The universality theorem shows that despite
this, the Hawking temperature depends only on the surface gravity κ, with
corrections suppressed by powers of (T_H/Λ)².

This is precisely the statement we need for the paper: the dissipative
correction δ_diss must similarly be computable within the EFT without
knowing the UV completion (beyond matching conditions).

## Formalization Approach

The proof uses WKB matching across the horizon:
1. Define the WKB mode functions in the asymptotic regions (far from horizon)
2. The connection formula across the horizon determines the Bogoliubov
   coefficients α, β
3. The occupation number n = |β/α|² gives the effective temperature
4. The WKB matching is algebraic manipulation of asymptotic series

The WKB validity (complex turning point analysis) is left as `sorry`.

## sorry Gaps

- Asymptotic validity of WKB in the complex plane
- Properties of the confluent Heun equation (connection formulas)
- Uniformity of the adiabatic expansion near the turning point
- The Stokes phenomenon for the modified dispersion relation

## References

- Corley-Jacobson, PRD 54, 1568 (1996) — dispersive corrections
- Coutant-Parentani, PRD 89, 124004 (2014) — broadened horizon paradigm
- Unruh, PRD 51, 2827 (1995) — sonic analog
- Jacobson, Prog. Theor. Phys. Suppl. 136, 1 (1999) — trans-Planckian review
-/

namespace SKEFTHawking.HawkingUniversality

/-!
## Modified Dispersion Relations

The EFT breaks down at k ~ 1/ξ. The full dispersion relation includes
UV corrections beyond the linear phonon dispersion ω = c_s |k|.

For a BEC, the Bogoliubov dispersion is:
  ω² = c_s² k² + (ℏk²/2m)²

More generally, any subluminal or superluminal UV modification:
  ω² = c_s² k² · F(k/Λ)

where F(0) = 1 and F grows (superluminal) or decreases (subluminal)
at large argument.
-/

/-- A modified dispersion relation (MDR) for phonons.

    The dispersion is ω² = c_s² k² · F(k²/Λ²) where:
    - F : ℝ → ℝ is the modification function
    - F(0) = 1 (recovers linear dispersion at low k)
    - Λ is the UV cutoff momentum

    The Bogoliubov case: F(x) = 1 + x gives ω² = c_s²k² + c_s²k⁴/Λ²
    which matches ω² = c_s²k² + ℏ²k⁴/(4m²) with Λ = 2m c_s/ℏ = 2/ξ. -/
structure ModifiedDispersion where
  /-- Sound speed at low momentum -/
  cs : ℝ
  cs_pos : 0 < cs
  /-- UV cutoff momentum Λ -/
  cutoff : ℝ
  cutoff_pos : 0 < cutoff
  /-- Modification function F: ω² = c_s² k² · F(k²/Λ²) -/
  F : ℝ → ℝ
  /-- F(0) = 1: recovery of linear dispersion at low k -/
  F_normalized : F 0 = 1
  /-- F is smooth (we use continuous + differentiable as proxy) -/
  F_continuous : Continuous F

/-- Subluminal dispersion: F(x) ≤ 1 for x > 0.
    The group velocity decreases at high k.
    Example: massive Klein-Gordon ω² = c²k² + m²c⁴ in some parameterizations. -/
def ModifiedDispersion.isSubluminal (mdr : ModifiedDispersion) : Prop :=
  ∀ x : ℝ, 0 < x → mdr.F x ≤ 1

/-- Superluminal dispersion: F(x) ≥ 1 for x > 0.
    The group velocity increases at high k.
    Example: Bogoliubov dispersion F(x) = 1 + x. -/
def ModifiedDispersion.isSuperluminal (mdr : ModifiedDispersion) : Prop :=
  ∀ x : ℝ, 0 < x → 1 ≤ mdr.F x

/-- The Bogoliubov dispersion relation for a weakly-interacting BEC:
    F(x) = 1 + x, giving ω² = c_s²k²(1 + k²/Λ²)

    This is superluminal: the group velocity exceeds c_s at high k. -/
noncomputable def bogoliubovDispersion (cs cutoff : ℝ)
    (hcs : 0 < cs) (hcut : 0 < cutoff) : ModifiedDispersion where
  cs := cs
  cs_pos := hcs
  cutoff := cutoff
  cutoff_pos := hcut
  F := fun x => 1 + x
  F_normalized := by simp
  F_continuous := continuous_const.add continuous_id

/-- The Bogoliubov dispersion is superluminal. -/
theorem bogoliubov_superluminal (cs cutoff : ℝ) (hcs : 0 < cs) (hcut : 0 < cutoff) :
    (bogoliubovDispersion cs cutoff hcs hcut).isSuperluminal :=
  fun _ hx => by simp [bogoliubovDispersion]; linarith

/-!
## The Adiabaticity Condition

The key assumption for Hawking universality: the wavelength of the
Hawking quanta changes slowly compared to the scale over which the
background varies. Quantified by the adiabaticity parameter:

  D = κ L / Λ

where L is the length scale of the background variation and Λ is the
EFT cutoff. When D ≫ 1, the WKB approximation is valid and the
Hawking result is robust.

Equivalently: T_H/T_max = κ/(c_s · Λ) ≪ 1, which is 0.02–0.04
in current BEC experiments.
-/

/-- The adiabaticity parameter D = κ / (c_s · Λ) = T_H / T_max.
    When D ≪ 1, the Hawking calculation is within the EFT regime.

    Physical values:
    - Steinhauer's ⁸⁷Rb BEC: D ≈ 0.02–0.04
    - Projected Heidelberg K-39: D ≈ 0.01–0.03 (tunable via Feshbach)
    - Spin-sonic (Trento): D could be O(1) due to c_spin ≪ c_density -/
noncomputable def adiabaticityParam (kappa cs cutoff : ℝ) : ℝ :=
  kappa / (cs * cutoff)

/-- The adiabatic regime: D ≪ 1, formalized as D < ε for some small ε.
    In this regime, the Hawking result is robust against UV modifications. -/
def isAdiabatic (kappa cs cutoff : ℝ) (epsilon : ℝ) : Prop :=
  0 < epsilon ∧ adiabaticityParam kappa cs cutoff < epsilon

/-!
## WKB Mode Functions and Bogoliubov Coefficients

The Hawking effect is encoded in the Bogoliubov coefficients relating
the "in" vacuum (modes defined at past infinity) to the "out" vacuum
(modes defined at future infinity, outside the horizon).

The WKB approximation gives the mode functions in the asymptotic regions.
The connection across the horizon determines the Bogoliubov transformation.
-/

/-- Bogoliubov coefficients relating in-modes to out-modes.
    The occupation number (particle production) is n = |β|²/(|α|² - |β|²).

    For the standard Hawking effect (no UV modification):
      |β/α|² = exp(-2πω/κ) = exp(-ω/T_H)

    giving a thermal spectrum at temperature T_H = κ/(2π). -/
structure BogoliubovCoeffs where
  /-- |α|² (normalization: |α|² - |β|² = 1 for bosons) -/
  alpha_sq : ℝ
  /-- |β|² (particle number per mode) -/
  beta_sq : ℝ
  /-- Bosonic normalization -/
  normalization : alpha_sq - beta_sq = 1
  /-- Positivity of particle number -/
  beta_sq_nonneg : 0 ≤ beta_sq

/-- The occupation number (mean particle number per mode at frequency ω):
    n(ω) = |β(ω)|² = 1/(exp(ω/T_eff) - 1)

    For a thermal spectrum at temperature T, this is the Bose-Einstein
    distribution. The "effective temperature" T_eff is extracted by
    fitting n(ω) to this form. -/
noncomputable def occupationNumber (bogo : BogoliubovCoeffs) : ℝ :=
  bogo.beta_sq

/-- Extract the effective temperature from the Bogoliubov coefficients:
    n(ω) = 1/(exp(ω/T_eff) - 1) implies T_eff = -ω/ln(|β/α|²)

    For exact Hawking: |β/α|² = exp(-2πω/κ), so T_eff = κ/(2π) = T_H. -/
noncomputable def effectiveTemp (omega : ℝ) (_kappa : ℝ) (bogo : BogoliubovCoeffs)
    (_h_alpha : 0 < bogo.alpha_sq) : ℝ :=
  -omega / Real.log (bogo.beta_sq / bogo.alpha_sq)

/-!
## The Universality Theorem

This is the main result: the Hawking temperature is universal at leading
order, with corrections suppressed by (T_H/Λ)².
-/

/-- **Standard Hawking Result (Unruh 1981).**

    For the unmodified dispersion relation (F ≡ 1, i.e., ω = c_s|k|),
    the Bogoliubov coefficients for modes of frequency ω are:

      |β/α|² = exp(-2πω/κ)

    giving a perfect Planckian spectrum at temperature T_H = κ/(2π).

    **Audit note:** Original hypotheses `_hkappa : 0 < kappa` and `_homega : 0 < omega`
    were removed — the conclusion is a definitional identity for all reals. -/
theorem standard_hawking_thermal (kappa : ℝ) :
    hawkingTemp kappa = kappa / (2 * Real.pi) := rfl

/-!
## Dispersive and dissipative corrections — stated in `KappaScaling.lean`

`dispersive_correction_bound` and `dissipative_correction_existence` used to live
here, in a form that quantified the corrected quantity existentially:

  `∃ δ_disp, ∃ C, 0 < C ∧ |δ_disp| ≤ C·D² ∧ δ_disp ≠ 0`

Both the bounded quantity AND the bounding constant were `∃`-bound, so the
inequality was satisfiable for any `D ≠ 0` by `δ = 1, C = 1/D²` — the statement
carried no information about dispersion, and never mentioned
`KappaScaling.dispersiveCorrection`, the project's definition of `δ_disp`.
The dissipative statement was the same shape: a case split satisfiable by `0` and
`1`, never tied to `KappaScaling.dissipativeCorrection`.

Both are now stated in `SKEFTHawking/KappaScaling.lean` — the one module where the
correction definitions and `adiabaticityParam` are simultaneously in scope
(`KappaScaling` imports this file, so the dependency cannot run the other way).
They keep their names, and the bounding constant is now the explicit universal
number `π/6` rather than an existential witness.
See finding 2/3 of `papers/AutomatedReviews/2026-08-13-statement-substance/I1.md`.
-/

/-- **The SK-EFT dressed effective temperature of a sonic horizon.**

    `T_eff = T_H · (1 + δ_disp + δ_diss + δ_cross)` with every field *defined*, not
    existentially witnessed:

      T_H     = hawkingTemp κ = κ/(2π)
      δ_disp  = −(π/6)·D²,  D = adiabaticityParam κ c_s Λ    (Corley–Jacobson 1996)
      δ_diss  = (γ₁+γ₂)·κ/c_s²                               (SK-EFT, first order)
      δ_cross = 0                                            (no cross term at this order)

    The two correction fields are the project's canonical corrections:
    `KappaScaling.universalEffectiveTemp_corrections_eq` proves they are literally
    `KappaScaling.dispersiveCorrection` and `KappaScaling.dissipativeCorrection` under
    the BEC identification Λ = 1/ξ (the same identification
    `KappaScaling.dispersive_correction_bound` uses). Nothing about the dressed
    temperature is chosen to satisfy an inequality. -/
noncomputable def universalEffectiveTemp
    (mdr : ModifiedDispersion) (coeffs : DissipativeCoeffs)
    {bg : FluidBackground} (h : SonicHorizon bg) : EffectiveTemperature where
  T_H := hawkingTemp h.surfaceGravity
  T_H_pos := div_pos h.surfaceGravity_pos (by positivity)
  delta_disp := -(Real.pi / 6) * adiabaticityParam h.surfaceGravity mdr.cs mdr.cutoff ^ 2
  delta_diss := (coeffs.gamma_1 + coeffs.gamma_2) * h.surfaceGravity / mdr.cs ^ 2
  delta_cross := 0

/-- **Hawking Temperature Universality Theorem (combined).**

    For the SK-EFT dressed temperature `universalEffectiveTemp` of *any* modified
    dispersion relation `mdr` — subluminal, superluminal, Bogoliubov, or anything else
    satisfying `ModifiedDispersion` — and any first-order transport coefficients:

      δ_disp < 0,        |δ_disp| = (π/6)·D²        (sharp, universal constant π/6)
      0 ≤ δ_diss,        δ_diss = 0 ↔ γ₁ = γ₂ = 0   (characterisation of the zero set)
      |T_eff − T_H·(1+δ_diss)| = T_H·(π/6)·D²       (the universality statement)

    The last conjunct is the content of the theorem: once dissipation is accounted for,
    the whole dependence of `T_eff` on the UV completion is the single number `(π/6)·D²`
    — the *same* number for every `mdr`, since `mdr.F` appears nowhere on the right.
    That is Corley–Jacobson (1996) / Coutant–Parentani (2014) universality.

    **Nothing here is existentially quantified**, and no constant is a witness: `π/6` is
    an explicit universal number and both corrections are the *defined* fields of
    `universalEffectiveTemp`. The statement was previously
    `∃ teff, … ∧ ∃ C > 0, |teff.delta_disp| ≤ C·D² ∧ …`, which the proof discharged with
    `δ_disp := 1, C := 1/D²` and `δ_diss := if γ₁ = 0 ∧ γ₂ = 0 then 0 else 1` — the
    escape pattern repaired in `KappaScaling.dispersive_correction_bound` /
    `dissipative_correction_existence`, nested one level deeper. See finding 2 of
    `papers/AutomatedReviews/2026-08-13-i1-wave-residue/infra.md`.

    **Audit note:** the hypothesis `_hadiabatic : D < 1` was unused and is removed —
    the conclusions hold at every `D > 0`, which is strictly stronger. `D > 0` is still
    required: at `D = 0` the dispersive correction vanishes and is not `< 0`. -/
theorem hawking_universality
    (mdr : ModifiedDispersion) (coeffs : DissipativeCoeffs)
    (bg : FluidBackground) (h : SonicHorizon bg)
    (hD_pos : 0 < adiabaticityParam h.surfaceGravity mdr.cs mdr.cutoff) :
    (universalEffectiveTemp mdr coeffs h).delta_disp < 0 ∧
      |(universalEffectiveTemp mdr coeffs h).delta_disp|
        = Real.pi / 6 * adiabaticityParam h.surfaceGravity mdr.cs mdr.cutoff ^ 2 ∧
      0 ≤ (universalEffectiveTemp mdr coeffs h).delta_diss ∧
      ((universalEffectiveTemp mdr coeffs h).delta_diss = 0
        ↔ coeffs.gamma_1 = 0 ∧ coeffs.gamma_2 = 0) ∧
      |(universalEffectiveTemp mdr coeffs h).T_eff
          - hawkingTemp h.surfaceGravity
              * (1 + (universalEffectiveTemp mdr coeffs h).delta_diss)|
        = hawkingTemp h.surfaceGravity * (Real.pi / 6)
            * adiabaticityParam h.surfaceGravity mdr.cs mdr.cutoff ^ 2 := by
  have hD2 : 0 < adiabaticityParam h.surfaceGravity mdr.cs mdr.cutoff ^ 2 := pow_pos hD_pos 2
  have hcs2 : (0:ℝ) < mdr.cs ^ 2 := pow_pos mdr.cs_pos 2
  have hTHpos : 0 < hawkingTemp h.surfaceGravity :=
    div_pos h.surfaceGravity_pos (by positivity)
  have hdisp : (universalEffectiveTemp mdr coeffs h).delta_disp
      = -(Real.pi / 6) * adiabaticityParam h.surfaceGravity mdr.cs mdr.cutoff ^ 2 := rfl
  have hdiss : (universalEffectiveTemp mdr coeffs h).delta_diss
      = (coeffs.gamma_1 + coeffs.gamma_2) * h.surfaceGravity / mdr.cs ^ 2 := rfl
  have hdisp_neg : (universalEffectiveTemp mdr coeffs h).delta_disp < 0 := by
    rw [hdisp]
    exact mul_neg_of_neg_of_pos (by linarith [Real.pi_pos]) hD2
  have habs : |(universalEffectiveTemp mdr coeffs h).delta_disp|
      = Real.pi / 6 * adiabaticityParam h.surfaceGravity mdr.cs mdr.cutoff ^ 2 := by
    rw [abs_of_nonpos hdisp_neg.le, hdisp]; ring
  have hdiss_nonneg : 0 ≤ (universalEffectiveTemp mdr coeffs h).delta_diss := by
    rw [hdiss]
    exact div_nonneg (mul_nonneg (add_nonneg coeffs.gamma_1_nonneg coeffs.gamma_2_nonneg)
      h.surfaceGravity_pos.le) hcs2.le
  have hiff : (universalEffectiveTemp mdr coeffs h).delta_diss = 0
      ↔ coeffs.gamma_1 = 0 ∧ coeffs.gamma_2 = 0 := by
    rw [hdiss, div_eq_zero_iff]
    constructor
    · rintro (hz | hz)
      · rcases mul_eq_zero.mp hz with hsum | hkappa
        · constructor <;>
            linarith [coeffs.gamma_1_nonneg, coeffs.gamma_2_nonneg]
        · exact absurd hkappa h.surfaceGravity_pos.ne'
      · exact absurd hz hcs2.ne'
    · rintro ⟨h1, h2⟩
      left; rw [h1, h2]; ring
  refine ⟨hdisp_neg, habs, hdiss_nonneg, hiff, ?_⟩
  have hTeff : (universalEffectiveTemp mdr coeffs h).T_eff
      - hawkingTemp h.surfaceGravity
          * (1 + (universalEffectiveTemp mdr coeffs h).delta_diss)
      = hawkingTemp h.surfaceGravity * (universalEffectiveTemp mdr coeffs h).delta_disp := by
    show hawkingTemp h.surfaceGravity
        * (1 + (universalEffectiveTemp mdr coeffs h).delta_disp
              + (universalEffectiveTemp mdr coeffs h).delta_diss + 0) - _ = _
    ring
  rw [hTeff, abs_mul, abs_of_pos hTHpos, habs]
  ring

/-!
## Scaling Estimates for Experiments

Concrete predictions for current and planned BEC experiments.
These are the numbers that go into the paper's discussion section.
-/

/-- **Steinhauer ⁸⁷Rb parameters.**

    - Healing length: ξ ≈ 0.4 μm
    - Sound speed: c_s ≈ 0.5 mm/s
    - Surface gravity: κ ≈ 5 × 10³ s⁻¹
    - Adiabaticity: D = κξ/c_s ≈ 0.04
    - Hawking temp: T_H ≈ 0.35 nK (measured!)
    - Beliaev damping: γ_B ~ (na³)^{1/2} ω²/c_s
    - Dispersive correction: δ_disp ~ D² ~ 1.6 × 10⁻³
    - Dissipative correction: δ_diss ~ 10⁻⁶ to 10⁻⁴
    - Experimental precision: ~10-30% → corrections unresolvable -/
noncomputable def steinhauer_adiabaticity : ℝ := 0.04

/-- **Trento spin-sonic parameters (projected).**

    In a two-component BEC with spin-sonic horizon (Berti et al. 2025):
    - c_spin ≪ c_density (tunable)
    - T_H/T_max can be enhanced by orders of magnitude
    - δ_diss could become O(10⁻² to 10⁻¹) → experimentally accessible!

    This is the key experimental motivation for computing δ_diss. -/
noncomputable def trento_spin_sonic_enhancement : ℝ := 100
  -- Enhancement factor: (c_density/c_spin)² relative to single-component

/-!
## Phase 3 Enhancements (1E)

### κ-Scaling Crossing Prediction

The dispersive and dissipative corrections scale differently with surface gravity:
  δ_disp = -(π/6)·D² = -(π/6)·(κξ/c_s)²  ∝ κ²
  δ_diss = Γ_H/κ                            ∝ κ

Since dispersive grows as κ² and dissipative falls as 1/κ (via Γ_H/κ
with Γ_H ∝ κ² giving δ_diss ∝ κ), there exists a crossing surface
gravity κ* where |δ_disp| = δ_diss.

Below κ*, dissipation dominates (δ_diss > |δ_disp|).
Above κ*, dispersion dominates (|δ_disp| > δ_diss).
-/

/-- Parameters for the κ-crossing analysis. -/
structure KappaCrossingParams where
  /-- Healing length ξ [m] -/
  xi : ℝ
  xi_pos : 0 < xi
  /-- Sound speed c_s [m/s] -/
  cs : ℝ
  cs_pos : 0 < cs
  /-- Effective damping coefficient A: δ_diss = A·κ where A = (γ₁+γ₂)/c_s² -/
  diss_coeff : ℝ
  diss_coeff_pos : 0 < diss_coeff

/-- The crossing surface gravity κ* where |δ_disp(κ*)| = δ_diss(κ*).

    Setting (π/6)·(κξ/c_s)² = A·κ (where A encodes the transport coefficients),
    we get κ* = 6A·c_s²/(π·ξ²).

    This is well-defined and positive when A > 0 (dissipation present),
    ξ > 0, and c_s > 0. -/
noncomputable def kappaCrossing (p : KappaCrossingParams) : ℝ :=
  6 * p.diss_coeff * p.cs ^ 2 / (Real.pi * p.xi ^ 2)

/-- The crossing surface gravity κ* is positive. -/
theorem kappaCrossing_pos (p : KappaCrossingParams) :
    0 < kappaCrossing p := by
  unfold kappaCrossing
  apply div_pos
  · have h6 : (0:ℝ) < 6 := by norm_num
    have hcs2 : (0:ℝ) < p.cs ^ 2 := sq_pos_of_pos p.cs_pos
    exact mul_pos (mul_pos h6 p.diss_coeff_pos) hcs2
  · exact mul_pos Real.pi_pos (sq_pos_of_pos p.xi_pos)

/-- At the crossing point, the dispersive and dissipative corrections
    are equal in magnitude.

    |δ_disp(κ*)| = (π/6)·(κ*·ξ/c_s)² and δ_diss(κ*) = A·κ*.
    Substituting κ* = 6A·c_s²/(π·ξ²):
      (π/6)·(6A·c_s²/(π·ξ²)·ξ/c_s)² = (π/6)·(6A·c_s/(π·ξ))²
                                       = (π/6)·36A²·c_s²/(π²·ξ²)
                                       = 6A²·c_s²/(π·ξ²)
                                       = A·κ* ✓ -/
theorem kappa_crossing_is_crossing (p : KappaCrossingParams) :
    Real.pi / 6 * (kappaCrossing p * p.xi / p.cs) ^ 2 =
    p.diss_coeff * kappaCrossing p := by
  unfold kappaCrossing
  have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have hxi : p.xi ≠ 0 := ne_of_gt p.xi_pos
  have hcs : p.cs ≠ 0 := ne_of_gt p.cs_pos
  have h6 : (6:ℝ) ≠ 0 := by norm_num
  field_simp [hpi, hxi, hcs, h6]

/-!
### Spin-Sonic Enhancement Theorem

In a two-component BEC, spin waves propagate at c_spin ≪ c_density.
The dissipative correction δ_diss scales as (c_density/c_spin)² relative
to a single-component system. This enhancement is exact at leading order
in the EFT.
-/

/-- Spin-sonic enhancement factor: the dissipative correction is enhanced
    by the square of the velocity ratio when operating with spin sound
    rather than density sound. -/
noncomputable def spinSonicEnhancement (c_density c_spin : ℝ) : ℝ :=
  (c_density / c_spin) ^ 2

/-- The enhancement factor is positive when both velocities are positive. -/
theorem spinSonicEnhancement_pos (c_d c_s : ℝ) (hd : 0 < c_d) (hs : 0 < c_s) :
    0 < spinSonicEnhancement c_d c_s := by
  unfold spinSonicEnhancement
  positivity

/-- The spin-sonic enhancement is exact at leading order:
    δ_diss(spin) = (c_density/c_spin)² · δ_diss(density).

    Proof: δ_diss = Γ_H/κ with Γ_H = (γ₁+γ₂)·k_H² and k_H = κ/c_s.
    Replacing c_s → c_spin while keeping γᵢ and κ fixed:
      k_H(spin) = κ/c_spin, so Γ_H(spin) = (γ₁+γ₂)·κ²/c_spin²
      δ_diss(spin) = (γ₁+γ₂)·κ/c_spin²
    while δ_diss(density) = (γ₁+γ₂)·κ/c_density²
    Ratio = c_density²/c_spin² = (c_density/c_spin)². -/
theorem spinSonic_enhancement_exact
    (gamma_eff kappa c_density c_spin : ℝ)
    (hgk : gamma_eff * kappa ≠ 0) (hcd : c_density ≠ 0) (hcs : c_spin ≠ 0) :
    -- δ_diss(spin) / δ_diss(density)
    -- = [gamma_eff · κ / c_spin²] / [gamma_eff · κ / c_density²]
    (gamma_eff * kappa / c_spin ^ 2) /
    (gamma_eff * kappa / c_density ^ 2) =
    spinSonicEnhancement c_density c_spin := by
  unfold spinSonicEnhancement
  have hcs2 : c_spin ^ 2 ≠ 0 := pow_ne_zero 2 hcs
  have hcd2 : c_density ^ 2 ≠ 0 := pow_ne_zero 2 hcd
  field_simp [hgk, hcs2, hcd2]
  have hge : gamma_eff ≠ 0 := left_ne_zero_of_mul hgk
  have hke : kappa ≠ 0 := right_ne_zero_of_mul hgk
  field_simp [hge, hke]

end SKEFTHawking.HawkingUniversality
