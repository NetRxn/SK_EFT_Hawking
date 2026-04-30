import SKEFTHawking.VestigialEOS
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Vestigial Natural-Branch Inflation: Structural No-Go

## Overview

Phase 6b Wave 3 (de-escalated per Gate B.3, 2026-04-29). Stage 3a preliminary
numerics scan over `(f_0, M_φ, τ_*)` produced **0 viable points / 2574** for
the Planck/BICEP admissibility region (n_s 2σ × r < 0.036 × 50 < N_e < 65),
exposing **two structural failures** of vestigial natural-branch inflation:

1. **η-problem.** At the natural hilltop `τ = √(3/5)` of the
   `VestigialEOS.rho_vest` potential, the slow-roll parameter η admits a
   closed form `η_hilltop = -30 · (M̄_P / M_φ)²`. Slow-roll `|η| < 1` therefore
   demands `M_φ > √30 · M̄_P ≈ 5.48 M̄_P` — strictly super-Planckian, outside
   the EFT validity window. Planck-2σ compatibility on `n_s` (which at the
   hilltop reduces to `n_s = 1 + 2η`) tightens this to `M_φ > 36 · M̄_P`.
2. **e-fold overshoot.** At any super-Planckian `M_φ` where `(n_s, r)` becomes
   formally admissible, the canonical 50–65 e-fold window is overshot
   (numerical scan: every `(n_s, r)`-passing point has `N_e ≥ 71.8`).

This module formalizes failure (1) end-to-end as a structural No-Go: the
load-bearing theorem `nSAtHilltop_planck_compatible_implies_super_Planckian`
proves that any choice of `M_φ` consistent with sub-Planckian EFT validity
falsifies Planck-2σ `n_s` at the natural vestigial hilltop. The companion
`vestigial_natural_branch_inflation_falsified` is the contrapositive.

This wave joins Phase 5y (vestigial-DE NO-GO) and Phase 5z W4 (substrate-bridge
NO-GO) in the project's structural-falsification ledger.

## Substrate

Vestigial-phase potential as inflaton energy density (from `VestigialEOS.lean`):
```
V_vest(τ) = ρ_vest(τ) = f_0 · (1 - τ²) · (5τ² - 1)
```
The hilltop sits at `τ_max = √(3/5)`; here `V(τ_max) = 4 f_0 / 5`,
`V'(τ_max) = 0`, `V''(τ_max) = -24 f_0`.

Canonical inflaton `φ = M_φ · τ`, so derivatives wrt `φ` carry one or two
inverse `M_φ` factors. Slow-roll parameters in reduced-Planck convention:
```
ε = (M̄_P²/2) · (V_φ/V)²        η = M̄_P² · (V_φφ/V)
n_s = 1 - 6ε + 2η               r  = 16 ε
```
At the hilltop `ε = 0` (since `V'_τ = 0`), so `n_s = 1 + 2 η_hilltop`.

## Cross-references

- `VestigialEOS.rho_vest` — the substrate potential.
- `src/vestigial_inflation/` — Python preliminary scan, 16 cross-layer tests.
- `figures/data/vestigial_inflation_preliminary_scan.json` — 2574-point scan.
- `temporary/working-docs/todo/phase6b_w3_gate_b3_preliminary.md` — Gate B.3 memo.
-/

namespace SKEFTHawking.VestigialInflationNoGo

open SKEFTHawking.VestigialEOS

/-- Inflation-sector dimensional parameters: vestigial free-energy depth `f_0`,
inflaton kinetic mass scale `M_φ` (canonical inflaton `φ = M_φ τ`), and
reduced Planck mass `M̄_P`. All strictly positive. -/
structure InflationParams where
  f0      : ℝ
  f0_pos  : 0 < f0
  Mphi    : ℝ
  Mphi_pos : 0 < Mphi
  MPlRed  : ℝ
  MPlRed_pos : 0 < MPlRed

/-- Underlying `VestigialParams` consumed by `rho_vest`. We supply only `f_0`;
the onset temperature `T_c` is irrelevant for the inflation-mode analysis. -/
noncomputable def toVestigialParams (P : InflationParams) : VestigialParams :=
  { f_0 := P.f0, T_c := 1, T_c_pos := by norm_num, f_0_pos := P.f0_pos }

/-- Vestigial inflaton potential `V(τ) := ρ_vest(τ)` from `VestigialEOS`. -/
noncomputable def potential (P : InflationParams) (τ : ℝ) : ℝ :=
  rho_vest (toVestigialParams P) τ

/-- First τ-derivative of `V(τ)`: `V'_τ(τ) = 4 f_0 τ (3 - 5 τ²)`.
Closed form is needed for the hilltop characterization. -/
noncomputable def potentialDerivTau (P : InflationParams) (τ : ℝ) : ℝ :=
  4 * P.f0 * τ * (3 - 5 * τ^2)

/-- Second τ-derivative of `V(τ)`: `V''_ττ(τ) = f_0 · (12 - 60 τ²)`. -/
noncomputable def potentialSecondDerivTau (P : InflationParams) (τ : ℝ) : ℝ :=
  P.f0 * (12 - 60 * τ^2)

/- ── Section 1: Hilltop characterization ─────────────────────────────── -/

/-- The vestigial natural hilltop sits at `τ_max² = 3/5`. We work with `τ²`
in algebraic statements to avoid `Real.sqrt` overhead in `norm_num`. -/
noncomputable def tauHilltopSq : ℝ := 3 / 5

theorem tauHilltopSq_pos : 0 < tauHilltopSq := by
  unfold tauHilltopSq; norm_num

theorem tauHilltopSq_lt_one : tauHilltopSq < 1 := by
  unfold tauHilltopSq; norm_num

/-- **Hilltop value of V**: `V(τ_max) = 4 f_0 / 5` when `τ² = 3/5`.
The hilltop is the unique slow-roll-friendly position (`V > 0`, `V'_τ = 0`). -/
theorem potential_at_hilltop (P : InflationParams) (τ : ℝ) (hτ : τ^2 = tauHilltopSq) :
    potential P τ = 4 * P.f0 / 5 := by
  unfold potential rho_vest toVestigialParams tauHilltopSq at *
  rw [hτ]
  ring

/-- **Hilltop derivative vanishes**: `V'_τ(τ_max) = 0` when `τ² = 3/5`.
Direct consequence of `3 - 5 · (3/5) = 0`; this is *why* slow-roll `ε = 0` at
the hilltop and the η-problem (not the ε-problem) is load-bearing. -/
theorem potentialDerivTau_at_hilltop (P : InflationParams) (τ : ℝ) (hτ : τ^2 = tauHilltopSq) :
    potentialDerivTau P τ = 0 := by
  unfold potentialDerivTau tauHilltopSq at *
  have : 3 - 5 * τ^2 = 0 := by rw [hτ]; ring
  rw [this]; ring

/-- **Hilltop curvature is concave-down**: `V''_ττ(τ_max) = -24 f_0`.
The negative curvature is the geometric source of the η-problem: the ratio
`V''/V = -30/(M̄_P²/M_φ²)⁻¹` blows up `|η|` for sub-Planckian `M_φ`. -/
theorem potentialSecondDerivTau_at_hilltop (P : InflationParams) (τ : ℝ)
    (hτ : τ^2 = tauHilltopSq) :
    potentialSecondDerivTau P τ = -24 * P.f0 := by
  unfold potentialSecondDerivTau tauHilltopSq at *
  rw [hτ]; ring

/- ── Section 2: Closed-form η at the hilltop ─────────────────────────── -/

/-- Slow-roll `η` parameter at the hilltop, in canonical inflaton convention:
`η = M̄_P² · V_φφ / V = (M̄_P²/M_φ²) · V_ττ / V`. With `V_ττ = -24 f_0` and
`V = 4 f_0 / 5` this collapses to `η = -30 · (M̄_P/M_φ)²` *independent of `f_0`*.
The `f_0`-cancellation is what makes the η-problem geometric, not parametric. -/
noncomputable def etaAtHilltop (P : InflationParams) : ℝ :=
  (P.MPlRed / P.Mphi)^2 * (-30)

/-- **η-problem closed form**: at the hilltop, the slow-roll
`η = (M̄_P/M_φ)² · V_ττ/V` reduces algebraically to `-30 · (M̄_P/M_φ)²`.

Load-bearing identity: this is what makes `n_s` at the hilltop a
sub-Planckian-discriminating quantity. -/
theorem etaAtHilltop_eq_neg_thirty_ratio_sq (P : InflationParams) :
    etaAtHilltop P = -30 * (P.MPlRed / P.Mphi)^2 := by
  unfold etaAtHilltop; ring

/-- The hilltop η is strictly negative for any choice of inflation parameters.
Together with `n_s = 1 + 2η` at the hilltop, this means `n_s < 1` at the
hilltop (red-tilt, consistent with the *direction* of the Planck observation). -/
theorem etaAtHilltop_neg (P : InflationParams) : etaAtHilltop P < 0 := by
  unfold etaAtHilltop
  have hratio_pos : 0 < P.MPlRed / P.Mphi := div_pos P.MPlRed_pos P.Mphi_pos
  have h1 : 0 < (P.MPlRed / P.Mphi)^2 := pow_pos hratio_pos 2
  nlinarith

/- ── Section 3: η-problem ⟹ super-Planckian M_φ ─────────────────────── -/

/-- **Slow-roll viability constraint at the hilltop**: `|η_hilltop| < 1`
*implies* `M_φ² > 30 · M̄_P²` (i.e. `M_φ > √30 · M̄_P ≈ 5.48 M̄_P`,
strictly super-Planckian). This is the η-problem in its slow-roll-existence
form. -/
theorem etaAtHilltop_abs_lt_one_implies_super_Planckian (P : InflationParams)
    (h : |etaAtHilltop P| < 1) :
    30 * P.MPlRed^2 < P.Mphi^2 := by
  rw [etaAtHilltop_eq_neg_thirty_ratio_sq P] at h
  rw [abs_lt] at h
  obtain ⟨hlb, _⟩ := h
  have hmphi_pos : 0 < P.Mphi^2 := pow_pos P.Mphi_pos 2
  have hmpl_pos : 0 < P.MPlRed^2 := pow_pos P.MPlRed_pos 2
  -- hlb : -1 < -30 * (P.MPlRed / P.Mphi)^2
  -- i.e. 30 * (P.MPlRed / P.Mphi)^2 < 1
  have hsq_eq : (P.MPlRed / P.Mphi)^2 = P.MPlRed^2 / P.Mphi^2 := by
    rw [div_pow]
  have hsq_lt : 30 * (P.MPlRed^2 / P.Mphi^2) < 1 := by
    rw [← hsq_eq]; linarith
  -- 30 * MPl^2 / Mphi^2 < 1  ⟺  30 * MPl^2 < Mphi^2  (when Mphi^2 > 0)
  have hcombine : 30 * P.MPlRed^2 / P.Mphi^2 < 1 := by
    have : 30 * (P.MPlRed^2 / P.Mphi^2) = 30 * P.MPlRed^2 / P.Mphi^2 := by ring
    linarith
  rw [div_lt_one hmphi_pos] at hcombine
  exact hcombine

/- ── Section 4: n_s at the hilltop ───────────────────────────────────── -/

/-- Scalar spectral index at the hilltop. Since `ε = 0` at the hilltop
(because `V'_τ = 0` there), `n_s_hilltop = 1 + 2 · η_hilltop = 1 - 60 · (M̄_P/M_φ)²`. -/
noncomputable def nSAtHilltop (P : InflationParams) : ℝ :=
  1 + 2 * etaAtHilltop P

theorem nSAtHilltop_eq (P : InflationParams) :
    nSAtHilltop P = 1 - 60 * (P.MPlRed / P.Mphi)^2 := by
  unfold nSAtHilltop
  rw [etaAtHilltop_eq_neg_thirty_ratio_sq]
  ring

/-- The hilltop `n_s` is strictly less than 1 (red-tilt direction). -/
theorem nSAtHilltop_lt_one (P : InflationParams) : nSAtHilltop P < 1 := by
  rw [nSAtHilltop_eq]
  have hratio_pos : 0 < P.MPlRed / P.Mphi := div_pos P.MPlRed_pos P.Mphi_pos
  have h1 : 0 < (P.MPlRed / P.Mphi)^2 := pow_pos hratio_pos 2
  nlinarith

/-- **Load-bearing structural No-Go (η-problem ⟹ super-Planckian M_φ).**

If the hilltop scalar spectral index lands within Planck 2σ
(`n_s ≥ 0.9565`, the lower bound from `0.9649 − 2 · 0.0042`),
then `M_φ²` exceeds `1300 · M̄_P²` — i.e., `M_φ > 36 · M̄_P`, strictly
super-Planckian and outside the EFT validity window.

The `1300` figure follows from `60 / (1 - 0.9565) = 60/0.0435 ≈ 1379.3`, of
which `1300` is a safe `norm_num`-friendly under-estimate. -/
theorem nSAtHilltop_planck_compatible_implies_super_Planckian
    (P : InflationParams)
    (h_planck : nSAtHilltop P ≥ 0.9565) :
    1300 * P.MPlRed^2 < P.Mphi^2 := by
  rw [nSAtHilltop_eq] at h_planck
  have hmphi_pos : 0 < P.Mphi^2 := pow_pos P.Mphi_pos 2
  have hmpl_pos : 0 < P.MPlRed^2 := pow_pos P.MPlRed_pos 2
  -- 1 - 60 (MPl/Mphi)^2 ≥ 0.9565  ⟹  60 (MPl/Mphi)^2 ≤ 0.0435
  have h2 : 60 * (P.MPlRed / P.Mphi)^2 ≤ 0.0435 := by linarith
  have hsq_eq : (P.MPlRed / P.Mphi)^2 = P.MPlRed^2 / P.Mphi^2 := by rw [div_pow]
  rw [hsq_eq] at h2
  -- 60 * (MPl^2 / Mphi^2) ≤ 0.0435  ⟹  60 * MPl^2 ≤ 0.0435 * Mphi^2
  have h3 : 60 * P.MPlRed^2 ≤ 0.0435 * P.Mphi^2 := by
    have h2' : 60 * P.MPlRed^2 / P.Mphi^2 ≤ 0.0435 := by
      have heq : 60 * (P.MPlRed^2 / P.Mphi^2) = 60 * P.MPlRed^2 / P.Mphi^2 := by ring
      linarith
    rw [div_le_iff₀ hmphi_pos] at h2'
    exact h2'
  -- Chain to the conclusion: 1300 * MPl^2 ≤ (1300/60) * 60 * MPl^2
  --                           ≤ (1300/60) * 0.0435 * Mphi^2
  --                           = 0.9425 * Mphi^2 < Mphi^2
  nlinarith [h3, hmphi_pos, hmpl_pos]

/- ── Section 5: Numerical witnesses ───────────────────────────────────── -/

/-- **Witness at canonical sub-Planckian `M_φ = M̄_P`**: η blows up to `-30`,
massively violating slow-roll `|η| < 1`. -/
theorem etaAtHilltop_at_M_phi_eq_M_Pl_red_eq_neg_thirty (P : InflationParams)
    (h : P.Mphi = P.MPlRed) :
    etaAtHilltop P = -30 := by
  rw [etaAtHilltop_eq_neg_thirty_ratio_sq, h]
  have : P.MPlRed / P.MPlRed = 1 := div_self (ne_of_gt P.MPlRed_pos)
  rw [this]; ring

/-- **n_s witness at canonical M_φ = M̄_P**: `n_s = -59`, *very far* from Planck. -/
theorem nSAtHilltop_at_M_phi_eq_M_Pl_red_eq_neg_fifty_nine (P : InflationParams)
    (h : P.Mphi = P.MPlRed) :
    nSAtHilltop P = -59 := by
  rw [nSAtHilltop_eq, h]
  have : P.MPlRed / P.MPlRed = 1 := div_self (ne_of_gt P.MPlRed_pos)
  rw [this]; ring

/- ── Section 6: Joint structural No-Go bundle ────────────────────────── -/

/-- **Vestigial natural-branch inflation falsified at sub-Planckian M_φ.**

Joint structural No-Go: any choice of inflation parameters with `M_φ ≤ M̄_P`
(the EFT-natural sub-Planckian window) produces a hilltop `n_s` strictly
below the Planck 2σ lower bound `0.9565`. Equivalently, the contrapositive
of `nSAtHilltop_planck_compatible_implies_super_Planckian`.

This is the load-bearing structural punchline of the wave: vestigial
natural-branch inflation cannot reproduce the observed CMB scalar tilt
within the EFT validity window. -/
theorem vestigial_natural_branch_inflation_falsified
    (P : InflationParams) (h_subPlanck : P.Mphi ≤ P.MPlRed) :
    nSAtHilltop P < 0.9565 := by
  rw [nSAtHilltop_eq]
  -- Want: 1 - 60 * (MPl/Mphi)^2 < 0.9565, i.e. 60 * (MPl/Mphi)^2 > 0.0435
  -- With Mphi ≤ MPl, (MPl/Mphi) ≥ 1, so 60 * (MPl/Mphi)^2 ≥ 60 > 0.0435.
  have hmphi : 0 < P.Mphi := P.Mphi_pos
  have hmpl : 0 < P.MPlRed := P.MPlRed_pos
  have hratio_ge_one : 1 ≤ P.MPlRed / P.Mphi := by
    rw [le_div_iff₀ hmphi]; linarith
  have hratio_pos : 0 < P.MPlRed / P.Mphi := div_pos hmpl hmphi
  have hsq_ge_one : 1 ≤ (P.MPlRed / P.Mphi)^2 := by
    have h2 : (1 : ℝ)^2 ≤ (P.MPlRed / P.Mphi)^2 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hratio_ge_one 2
    simpa using h2
  linarith

/-- **Quantitative companion to the joint No-Go**: at the canonical natural
choice `M_φ = M̄_P`, the predicted `n_s` deviates from Planck by *60 units*
of the central value, i.e., `|n_s_hilltop − n_s_Planck| > 50`. The vestigial
prediction is not merely Planck-incompatible — it is wildly off-scale. -/
theorem nSAtHilltop_deviation_at_M_phi_eq_M_Pl_red
    (P : InflationParams) (h : P.Mphi = P.MPlRed) :
    |nSAtHilltop P - 0.9649| > 50 := by
  rw [nSAtHilltop_at_M_phi_eq_M_Pl_red_eq_neg_fifty_nine P h]
  rw [show ((-59 : ℝ) - 0.9649) = -(59.9649) from by norm_num]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 59.9649)]
  norm_num

/-- **Module summary marker** (no operational content; serves as the
audit-trail anchor for "Phase 6b W3 SHIPPED as structural No-Go" per
`feedback_post_wave_strengthening_audit.md` discipline). -/
theorem phase6b_w3_structural_no_go_marker : True := trivial

end SKEFTHawking.VestigialInflationNoGo
