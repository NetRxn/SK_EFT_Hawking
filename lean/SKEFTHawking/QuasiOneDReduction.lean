/-
Phase 5w Wave 10b: Quasi-1D Reduction + Realistic Greybody Bounds

Formalizes the algebraic content of the quasi-1D approximation for the
graphene de Laval nozzle Hawking radiation.  The PDE-analysis content
(smooth profile existence, ω_max derivation from subluminal dispersion,
Coutant-Parentani spectral robustness) is captured as two tracked `Prop`
hypotheses pending future formalization — matching the precedent set by
`CenterFunctor.lean` (`H_CF1_center_functor`, `H_CF2_center_equivalence`)
and `CenterFunctorZ2Equiv.lean` (`H_CFZ2_sq_e`, `H_CFZ2_sq_a`).

## Main results

- **T1 `greybody_zero_freq_bounds`**: the profile-independent
  zero-frequency greybody `Γ₀ = 4 c_R v / (c_R + v)²` satisfies
  `0 ≤ Γ₀ ≤ 1` for positive c_R, v, with equality Γ₀ = 1 iff c_R = v
  (step-horizon limit). Derived by AM-GM: `4 c_R v ≤ (c_R + v)²`.
- **T2 `surface_gravity_correction_bound`**: the quasi-1D surface-gravity
  correction is bounded by `(l_ee / W)²`. Stated as the algebraic bound
  assuming the transverse flow-profile monotonicity hypothesis.
- **T3 `evanescent_bound`**: the transverse-mode evanescent leakage
  correction is bounded by `(ω / ω_⊥)² · exp(-2π·L/W)`. Follows from
  the Helmholtz equation for a sub-threshold transverse mode.
- **T4 `dean_adiabatic`**: the Dean graphene nozzle adiabaticity
  parameter `D = κ·l_ee/c_s < 1` for the specific Dean values
  (κ = 2e12, l_ee = 51 nm, c_s = 4.4e5) — `norm_num` over rationals.
- **T5 `quasi1D_validity_bound`**: the combined bound adds T2 and T3.

## Tracked hypotheses (PDE gaps)

- `H_AdiabaticRegimeCorrection`: the dispersive correction to T_H in the
  adiabatic regime D ≪ 1 is O(D⁴). Requires Finazzi-Parentani ODE
  perturbation theory not currently in Mathlib.
- `H_DispersiveUVCutoff`: the UV cutoff scales as `ω_max ~ √(κ·c_s/l_ee)`.
  Requires the subluminal BdG dispersion relation treated as a PDE
  spectral problem.

## References

- Deep research: `Lit-Search/Phase-5w/Greybody Factor and Quasi-1D
  Validity for the Graphene de Laval Nozzle.md` Blocks 1-2, §4.2.
- Anderson, Balbinot, Fabbri, Parentani, PRD 87, 124018 (2013).
- Finazzi & Parentani, PRD 83, 084010 (2011).
- Macher & Parentani, PRD 80, 043601 (2009).
- Dudley, Anderson, Balbinot, Fabbri — transverse mode structure.

## Python companions

- `src.core.formulas.greybody_zero_freq`
- `src.core.formulas.greybody_smooth_profile`
- `src.core.formulas.dispersive_uv_cutoff`
- `src.core.formulas.dean_adiabaticity_parameter`
- `src.core.formulas.quasi1d_correction_bound`
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

/-- **T1c (greybody_zero_freq_eq_one)**: Γ₀ = 1 iff c_R = v (step-horizon limit). -/
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

/--
**T2 (surface_gravity_correction_bound)**: the fractional surface-gravity
correction from the quasi-1D approximation is upper-bounded by `(l_ee/W)²`.

Parameterized over an abstract `δκ_over_κ : ℝ` representing the actual
deviation. The PDE content — that transverse averaging of a Poiseuille
profile yields this bound with an O(1) prefactor — is taken as a load-bearing
hypothesis `h_bound`. The theorem strengthens the bound to also give
`|δκ/κ| < 1` in the hydrodynamic regime `l_ee < W`, showing that the
correction never saturates the trivial upper bound.

For the Dean device (`l_ee = 51 nm`, `W = 1 μm`) the coefficient is
`(51/1000)² ≈ 2.6·10⁻³`, giving `δκ/κ ≤ 0.26%`.

See Block 2 §2.2 of the deep research for the Poiseuille flow derivation.
-/
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
than 1 whenever the channel is longer than zero (`L > 0`). This encodes
the physical exponential decay of sub-threshold transverse modes.
-/
theorem evanescent_factor_lt_one (L W : ℝ) (hW : W > 0) (hL : 0 < L) :
    Real.exp (-2 * Real.pi * L / W) < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_num_neg : -2 * Real.pi * L < 0 := by nlinarith [h_pi_pos, hL]
  exact div_neg_of_neg_of_pos h_num_neg hW

/--
**T3 (evanescent_bound)**: for sub-threshold transverse modes (`ω < ω_⊥`),
the correction to the greybody factor from evanescent leakage is
upper-bounded by `(ω / ω_⊥)² · exp(-2π · L / W)`.

Parameterized over an abstract `δΓ_over_Γ : ℝ`. The PDE content — that a
Helmholtz mode below cutoff decays exponentially over a channel of length
L with decay rate 2π/W — is taken as a load-bearing hypothesis `h_bound`.
The theorem strengthens the bound by pointing out that the decaying
factor makes the full bound strictly less than `(ω/ω_⊥)²` when `L > 0`.

For the Dean device at `ω = ω_H`, `(ω_H/ω_⊥)² ≈ 0.06` and
`exp(-2π L / W) ≈ 0.284`, giving δΓ/Γ ≤ 1.5%.

See Block 2 §2.3 of the deep research.
-/
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

/--
**T4 (dean_adiabatic)**: the Dean graphene nozzle adiabaticity parameter
`D = κ · l_ee / c_s` is strictly less than 1.

Uses the Dean-specific values: κ = 2×10¹² s⁻¹, l_ee = 51 nm = 5.1×10⁻⁸ m,
c_s = 4.4×10⁵ m/s. Yields D = 0.23181... < 1 via `norm_num`.

This places the Dean device in the adiabatic regime, supporting the
`O(D⁴)` dispersive correction claim tracked as
`H_AdiabaticRegimeCorrection`.
-/
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

/--
**T5 (quasi1D_validity_bound)**: the total fractional error in the
greybody factor from quasi-1D approximation, `|δΓ_2D - δΓ_1D|/Γ_1D`, is
upper-bounded by the sum of the surface-gravity correction (T2) and
evanescent leakage (T3) bounds:

    |δΓ_2D - δΓ_1D| / Γ_1D  ≤  (l_ee/W)²  +  (ω/ω_⊥)² · exp(-2π·L/W)

Per the deep research Block 2 §2.3, for the Dean nozzle
(`l_ee = 51 nm`, `W = 1 μm`, `L = 200 nm`, `ω_⊥ ≈ 4.46·ω_H`) this sum
evaluates to ≈ 0.0026 + 0.015 ≈ **1.8% at ω = ω_H**, bounded by
(1 + e^{-2π}) ≈ 1.002 (trivial bound from coefficient decomposition) and
tighter at smaller ω.

The theorem takes the component bounds from T2 and T3 as load-bearing
hypotheses and produces the combined bound by triangle inequality.
-/
theorem quasi1D_validity_bound
    (δκ_over_κ δΓ_over_Γ_evan ω ω_perp L W l_ee : ℝ)
    (_hωp : ω_perp > 0) (_hW : W > 0) (_hL : 0 < L)
    (h_surf : |δκ_over_κ| ≤ (l_ee / W)^2)
    (h_evan : |δΓ_over_Γ_evan| ≤ (ω / ω_perp)^2 * Real.exp (-2 * Real.pi * L / W)) :
    |δκ_over_κ| + |δΓ_over_Γ_evan| ≤
        (l_ee / W)^2 + (ω / ω_perp)^2 * Real.exp (-2 * Real.pi * L / W) := by
  linarith

/-! ## 6. Tracked hypotheses for PDE-analysis content -/

/--
**Tracked hypothesis (PDE gap)**: for a specific device configuration
— i.e., specific physical Hawking temperatures `T_H_exact` and
`T_H_leading` produced by the full Bogoliubov-de Gennes spectral
problem and its leading-order approximation — the fractional deviation
is bounded by `C_const · D⁴` where `D = κ · l_ee / c_s` is the
adiabaticity parameter. Requires Finazzi-Parentani ODE perturbation
theory (PRD 83, 084010 §III) not currently in Mathlib.

**Parameterization discipline.** `T_H_exact`, `T_H_leading`, and
`C_const` are **parameters** of the Prop, not universally-quantified
inside it. Universal quantification over `T_H` values would produce a
vacuously false Prop: given any small `D`, choose `T_H_exact = 1`,
`T_H_leading = 0.1` → `|diff| / T_H_leading = 9 ≰ C · D⁴`. The caller
supplies the specific pair `(T_H_exact, T_H_leading)` produced by
their device and asserts the bound for that specific pair.

Eliminable once Mathlib acquires the BdG eigenvalue perturbation
machinery. Zero downstream dependencies — only Paper 16's quantitative
Dean-specific T_H correction claim cites it.
-/
def H_AdiabaticRegimeCorrection
    (kappa c_s l_ee C_const T_H_exact T_H_leading : ℝ) : Prop :=
  kappa > 0 → c_s > 0 → l_ee > 0 → C_const > 0 → T_H_leading > 0 →
    |T_H_exact - T_H_leading| / T_H_leading ≤
      C_const * (kappa * l_ee / c_s)^4

/--
**Tracked hypothesis (PDE gap)**: for a specific device-determined UV
cutoff frequency `ω_max` and a specific theoretical scale constant `C`,
the cutoff matches the Macher-Parentani scaling `ω_max ≈ C ·
√(κ·c_s/l_ee)` to within 10%. Requires the subluminal quartic BdG
dispersion relation treated as a PDE spectral problem
(Macher-Parentani, PRD 80, 043601).

**Parameterization discipline.** `ω_max` and `C` are **parameters** of
the Prop, not universally-quantified inside it. Universal
quantification over `ω_max` with an inner `∃C` absorption would make
the Prop vacuous for any positive `ω_max` (just pick `C := ω_max /
√(κ·c_s/l_ee)`). The caller supplies the specific pair `(ω_max, C)`
produced by their PDE analysis and asserts the 10% agreement.

Eliminable once Mathlib acquires the BdG spectral formalism for
quartic dispersion. Zero downstream dependencies — only Paper 16's
quantitative ω_max/ω_H ≈ 13.4 detection-band-safety claim cites it.
-/
def H_DispersiveUVCutoff
    (kappa c_s l_ee ω_max C : ℝ) : Prop :=
  kappa > 0 → c_s > 0 → l_ee > 0 → C > 0 → ω_max > 0 →
    |ω_max - C * Real.sqrt (kappa * c_s / l_ee)| /
      (C * Real.sqrt (kappa * c_s / l_ee)) ≤ (1 / 10 : ℝ)

/-! ## 7. Module summary -/

/--
Summary theorem for the Quasi-1D Reduction module. Records the fact that
we have 5 formalized algebraic bounds (T1 three parts + T2 + T3 + T4 + T5)
plus 2 tracked hypotheses (H_AdiabaticRegimeCorrection,
H_DispersiveUVCutoff) for the PDE-analysis content.

Paper-claim mapping:
  - "Γ₀ ≈ 0.9994" → T1b + numerical evaluation in Python
  - "Γ(ω) remains ≈ Γ₀ across detection band" → T1b + T3 + H_DispersiveUVCutoff
  - "Dean nozzle in adiabatic regime (D < 1)" → T4
  - "Quasi-1D correction ≤ few percent" → T5 + Python-evaluated numerics
  - "Dispersive T_H correction is O(D⁴)" → H_AdiabaticRegimeCorrection
-/
theorem quasi_one_d_reduction_summary : True := trivial

end QuasiOneDReduction
end SKEFTHawking
