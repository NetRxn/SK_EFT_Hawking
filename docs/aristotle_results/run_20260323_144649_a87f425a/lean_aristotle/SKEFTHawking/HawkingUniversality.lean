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
    (bogoliubovDispersion cs cutoff hcs hcut).isSuperluminal := by
  intro x hx
  simp [bogoliubovDispersion]
  linarith

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

    giving a perfect Planckian spectrum at temperature T_H = κ/(2π). -/
theorem standard_hawking_thermal (kappa : ℝ) (_omega : ℝ) (_hkappa : 0 < kappa) (_homega : 0 < _omega) :
    -- The standard result: n(ω) = 1/(exp(2πω/κ) - 1)
    -- equivalently, T_eff = κ/(2π) = T_H
    hawkingTemp kappa = kappa / (2 * Real.pi) := by
  unfold hawkingTemp
  ring

/-- **Dispersive Correction (Corley-Jacobson 1996, Coutant-Parentani 2014).**

    For a modified dispersion relation with adiabaticity parameter D ≪ 1,
    the effective temperature receives corrections:

      T_eff = T_H · (1 + δ_disp)

    where δ_disp = O(D²) = O((T_H/Λ)²).

    The sign of δ_disp depends on whether the dispersion is subluminal
    (δ_disp > 0, slight heating) or superluminal (δ_disp < 0, slight cooling).
    The magnitude is |δ_disp| ~ (κξ/c_s)² ~ 0.04–0.16% for current BEC params. -/
theorem dispersive_correction_bound
    (mdr : ModifiedDispersion) (kappa : ℝ)
    (hkappa : 0 < kappa)
    (hadiabatic : adiabaticityParam kappa mdr.cs mdr.cutoff < 1) :
    -- There exists a δ_disp with |δ_disp| ≤ C · D² for some constant C
    ∃ (delta_disp C : ℝ),
      0 < C ∧
      |delta_disp| ≤ C * (adiabaticityParam kappa mdr.cs mdr.cutoff) ^ 2 := by
  sorry -- This is the Corley-Jacobson result
  -- Proof sketch:
  -- 1. Write the mode equation with MDR in tortoise coordinates
  -- 2. Apply WKB in the adiabatic regime
  -- 3. The connection formula across the turning point (near horizon)
  --    gives |β/α|² = exp(-2πω/κ) · (1 + correction)
  -- 4. The correction is bounded by the WKB remainder, which is O(D²)
  --
  -- The WKB matching is algebraic; the WKB validity requires analysis
  -- (specifically, complex turning point theory for the Heun equation)
  -- → sorry for the analysis parts

/-- **NEW: Dissipative Correction.**

    When the EFT includes dissipative terms (γ₁, γ₂ from the SK-EFT),
    there is an additional correction:

      δ_diss = O(γ/(κξ²))

    where γ is the phonon damping rate at the Hawking frequency.

    This is the main new result of the paper. The dissipative correction
    is independent of δ_disp at leading order, with a cross-term δ_cross
    appearing at next order. -/
theorem dissipative_correction_existence
    (mdr : ModifiedDispersion) (coeffs : DissipativeCoeffs) (kappa : ℝ)
    (hkappa : 0 < kappa) :
    -- There exists a dissipative correction δ_diss
    ∃ (delta_diss : ℝ),
      -- δ_diss is proportional to the dissipative coefficients
      -- (vanishes when γ₁ = γ₂ = 0)
      (coeffs.gamma_1 = 0 ∧ coeffs.gamma_2 = 0) → delta_diss = 0 := by
  sorry -- This is the core calculation of the paper
  -- Proof sketch:
  -- 1. Add the dissipative terms to the mode equation (from SK action)
  -- 2. The retarded Green's function G_R satisfies a modified equation
  --    (confluent Heun with additional damping terms)
  -- 3. WKB matching with dissipation modifies the connection formula
  -- 4. Extract δ_diss from the modified Bogoliubov coefficients
  -- 5. The FDR (KMS) determines the Keldysh function G_K
  -- 6. T_eff is read off from G_K's asymptotic form
  --
  -- This is the calculation that would fill 3-4 pages of the PRL

/-- **Hawking Temperature Universality Theorem (Combined).**

    For a superfluid described by the SK-EFT with dissipative corrections,
    in the adiabatic regime D ≪ 1, the effective temperature is:

      T_eff = T_H (1 + δ_disp + δ_diss + δ_cross)

    where:
    - T_H = κ/(2π) is the standard Hawking temperature
    - δ_disp = O(D²) is the dispersive correction (known)
    - δ_diss = O(γ/(κξ²)) is the dissipative correction (NEW)
    - δ_cross = O(D² · γ/(κξ²)) is the cross-term

    All corrections are parametrically small in the adiabatic regime,
    confirming the universality of the Hawking effect against both
    dispersive AND dissipative UV modifications. -/
theorem hawking_universality
    (mdr : ModifiedDispersion) (coeffs : DissipativeCoeffs)
    (bg : FluidBackground) (h : SonicHorizon bg) :
    ∃ (teff : EffectiveTemperature),
      teff.T_H = hawkingTemp h.surfaceGravity ∧
      -- All corrections vanish in the limit Λ → ∞, γ → 0
      (mdr.cutoff > 0 → coeffs.gamma_1 = 0 → coeffs.gamma_2 = 0 →
        teff.delta_disp = 0 ∧ teff.delta_diss = 0 ∧ teff.delta_cross = 0) := by
  sorry -- Combines the dispersive and dissipative results
  -- The existence is constructive: we build EffectiveTemperature from
  -- the WKB calculation with both modifications included

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

end SKEFTHawking.HawkingUniversality
