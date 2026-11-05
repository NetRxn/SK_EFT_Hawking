import SKEFTHawking.Basic
import SKEFTHawking.Curvature
import SKEFTHawking.EinsteinTensor
import SKEFTHawking.EnergyConditions
import SKEFTHawking.LinearizedEFE
import SKEFTHawking.KerrSchild
import SKEFTHawking.RiemannCoordinate
import SKEFTHawking.RiemannDifferentialBianchi
import Mathlib

/-!
# Phase 6f Wave 4 — Exact Solutions of the Einstein Field Equations

## Overview

Phase 6f Wave 4. Catalogues four canonical exact solutions of the
Einstein field equations as named consumers of the Phase 6f.1 +
Phase 6f.2 + Phase 6f.3 algebraic infrastructure:

1. **Minkowski** — the K = 0, Λ = 0 vacuum solution. Unique constant-
   curvature space with vanishing Einstein tensor (biconditional).
2. **de Sitter (dS₄)** — the K > 0 maximally symmetric vacuum-with-
   cosmological-constant solution. Λ = 3K, Hubble² = K, Hawking
   horizon at r = H⁻¹, Hawking temperature T_H = H/(2π).
3. **Anti-de Sitter (AdS₄)** — the K < 0 solution. Λ = 3K < 0,
   AdS length scale ℓ = 1/√(-K).
4. **Schwarzschild** — the M > 0 spherically-symmetric vacuum
   solution. Kerr-Schild form `g = η + (2M/r)·l⊗l`. Horizon at
   r = 2M; surface gravity κ = 1/(4M); Hawking temperature
   T_H = 1/(8πM); Bekenstein-Hawking entropy S_BH = 4πM².

## Scoping mode

This module ships at the **algebraic / point-wise** level, following
the precedent of Waves 6f.1+6f.2+6f.3 (audit §3E first formalization).
Each "exact solution" is a named specialization of the constant-K
Riemann witness (6f.1) with the appropriate sign of K (where
applicable), or an explicit Kerr-Schild form (Schwarzschild),
combined with the algebraic Einstein-equation verification from 6f.2
and the BH thermodynamics cross-bridges from Phase 6a Wave 5.

The full Lorentzian-manifold version (g(x) as a metric field on a
globally hyperbolic spacetime, derived from coordinates with full
Christoffel symbols and ∂_μ machinery) is deferred to Phase 6g.1+.
**Status (2026-04-29 catch-up):** Bonn's `CovariantDerivative` HAS
landed in pinned commit `8850ed93`, but Mathlib still lacks
Riemann/Ricci/scalar curvature on a connection — those are
SK-EFT-owned per the audit. For Schwarzschild specifically, the
vacuum-Ricci verification `Ric(g_Schw) = 0` outside r = 2M
intrinsically requires Lorentzian-metric infrastructure +
Ricci-from-connection (both built in 6g.1+) and is **not** encoded
here as a tracked Prop (per 6f.2 lesson on rejecting vacuous tracked
Props with trivial discharge); it will ship as substantive content
in 6g.1 or a follow-on wave.

## References

- R.M. Wald, *General Relativity* (1984) §6.1 (Schwarzschild),
  §5.2 (de Sitter / FLRW).
- S. Carroll, *Spacetime and Geometry* (2004) §5.1 (Schwarzschild),
  §8.3 (de Sitter).
- C. Misner, K. Thorne, J. Wheeler, *Gravitation* (1973) §17.2
  (de Sitter); §31 (Schwarzschild).
- G.W. Gibbons & S.W. Hawking, *Phys. Rev. D* **15**, 2738 (1977)
  (de Sitter Hawking radiation: T_H = H/2π).
- J.M. Bardeen, B. Carter, S.W. Hawking, *Commun. Math. Phys.*
  **31**, 161 (1973) (Schwarzschild T_H = κ/2π = 1/8πM).

## Cross-system landscape

Per the Phase 6f audit §3E + extensions, no proof assistant — Lean
(Mathlib4 + Bonn + PhysLean) / Coq / Isabelle/AFP / HOL Light /
HOL4 / Mizar / Agda — has formalized the canonical exact solutions
as named consumers of an algebraic curvature tensor with chain
implications, Λ-cosmological-constant biconditional, and
Hawking-Unruh quantitative cross-bridges to BH thermodynamics.
This wave plausibly continues the first-formalization claim from
6f.1+6f.2+6f.3.
-/

namespace SKEFTHawking.ExactSolutions

open SKEFTHawking.Curvature
open SKEFTHawking.EinsteinTensor
open SKEFTHawking.LinearizedEFE

/-! ## §1 — Minkowski as the K = 0 vacuum solution -/

/--
**Minkowski as the unique Λ = 0 vacuum among constant-curvature
spaces.** For the constant-K Riemann witness on Minkowski metric η,
the Λ = 0 vacuum equation `G + 0·η = 0` is satisfied iff K = 0.

This is the **uniqueness** content: among the one-parameter family
of constant-curvature spaces (parameterized by K), Minkowski is the
**only** one with vanishing cosmological constant. Forward direction
uses 6f.2's `constantSectional_lambda_vacuum_iff` (specialized at
Λ = 0 with the explicit non-degeneracy `η 0 0 = -1 ≠ 0`); backward
direction substitutes K = 0 (giving Ric = 0, R = 0, G = 0, so the
Λ = 0 equation reduces to `0 = 0`).
-/
theorem minkowski_lambda_zero_iff_K_zero (K : ℝ) :
    (∀ μ ν : Fin 4, einsteinTensor (ricciOf (constantSectionalRiemann K η))
        (scalarOf (ricciOf (constantSectionalRiemann K η)) η) η μ ν
          + (0 : ℝ) * η μ ν = 0) ↔ K = 0 := by
  have h_dim4 : sumFin4 (fun μ => sumFin4 (fun ν => η μ ν * η μ ν)) = 4 :=
    minkowski_dim_contraction
  have h_g00 : η 0 0 ≠ 0 := by rw [η_zero_zero]; norm_num
  have h_iff := constantSectional_lambda_vacuum_iff K (0 : ℝ) η η h_dim4 0 0 h_g00
  rw [h_iff]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ## §2 — de Sitter (K > 0) -/

/--
**de Sitter scalar curvature: `R = 12K`.** Named specialization of
6f.2's `constantSectional_scalarOf_eq` to η, using the load-bearing
4D contraction identity `Σ_{μν} η^{μν} η_{μν} = 4`.

For physical de Sitter at Hubble parameter H, R = 12 H² > 0.
The dimension factor n(n-1) = 4·3 = 12 is the 4D specialization.
-/
theorem deSitter_scalar_eq (K : ℝ) :
    scalarOf (ricciOf (constantSectionalRiemann K η)) η = 12 * K := by
  exact constantSectional_scalarOf_eq K η η minkowski_dim_contraction

/--
**de Sitter Einstein tensor: `G = -3K η`.** Named specialization of
6f.2's `constantSectional_einsteinTensor_eq` to η. The signature
`G_00 = +3K`, `G_ii = -3K` (for K > 0) reflects the de Sitter
"timelike compression / spacelike expansion" pattern.
-/
theorem deSitter_einsteinTensor_eq (K : ℝ) (μ ν : Fin 4) :
    einsteinTensor (ricciOf (constantSectionalRiemann K η))
      (scalarOf (ricciOf (constantSectionalRiemann K η)) η) η μ ν
        = -3 * K * η μ ν :=
  constantSectional_einsteinTensor_eq K η η minkowski_dim_contraction μ ν

/--
**de Sitter Λ-vacuum biconditional (sign-agnostic, η-specialized).**
The Λ-vacuum equation `G_μν + Λ η_μν = 0` is satisfied iff Λ = 3K.

Cross-bridge: 6f.2's `constantSectional_lambda_vacuum_iff`
specialized to η using the explicit non-degeneracy
`η 0 0 = -1 ≠ 0`. Removing the abstract non-degeneracy hypothesis
tightens the result for downstream consumers.

Note: this biconditional is sign-agnostic in K, so it serves as the
shared headline result for both de Sitter (K > 0) and Anti-de Sitter
(K < 0) — see `ads_lambda_eq_neg_three_over_ell_sq` below for the
AdS-specific quantitative consumer.
-/
theorem deSitter_lambda_vacuum_iff (K Λ : ℝ) :
    (∀ μ ν : Fin 4, einsteinTensor (ricciOf (constantSectionalRiemann K η))
        (scalarOf (ricciOf (constantSectionalRiemann K η)) η) η μ ν
          + Λ * η μ ν = 0) ↔ Λ = 3 * K :=
  constantSectional_lambda_vacuum_iff K Λ η η minkowski_dim_contraction
    0 0 (by rw [η_zero_zero]; norm_num)

/--
**de Sitter quantitative anchor: `Λ_dS = 3 H²`.** For physical
de Sitter at Hubble parameter H (with K = H²), the cosmological
constant is Λ = 3H² > 0.

Numerical anchor: the observed Λ ≃ 1.1 × 10⁻⁵² m⁻² gives
H = √(Λ/3) ≃ 1.9 × 10⁻²⁶ m⁻¹, matching the measured H₀ ≃ 67.4
km/s/Mpc to 1-2 σ precision.

This theorem is the **load-bearing quantitative bridge** from
6f.4's algebraic content to physical Hubble-Λ phenomenology.
-/
theorem deSitter_lambda_eq_three_H_squared (H : ℝ) :
    (∀ μ ν : Fin 4, einsteinTensor (ricciOf (constantSectionalRiemann (H ^ 2) η))
        (scalarOf (ricciOf (constantSectionalRiemann (H ^ 2) η)) η) η μ ν
          + (3 * H ^ 2) * η μ ν = 0) :=
  (deSitter_lambda_vacuum_iff (H ^ 2) (3 * H ^ 2)).mpr (by ring)

/-- **de Sitter cosmological horizon (Hubble) radius**:
    `r_H(H) = 1/H`. For dS₄ at Hubble parameter H > 0, the
    cosmological horizon is at proper radius r_H = 1/H = 1/√K.
    Gibbons-Hawking 1977 §III. -/
noncomputable def deSitterHubbleRadius (H : ℝ) : ℝ := 1 / H

/-- **de Sitter surface gravity**: `κ_dS(H) = H`. The dS Hubble
    parameter doubles as the surface gravity at the cosmological
    horizon. -/
noncomputable def deSitterKappa (H : ℝ) : ℝ := H

/-- **de Sitter Hawking temperature**: `T_H_dS(H) = H / (2π)`.
    Gibbons-Hawking 1977: a static observer in dS₄ at Hubble
    parameter H detects thermal radiation at temperature H/(2π). -/
noncomputable def deSitterHawkingTemp (H : ℝ) : ℝ := H / (2 * Real.pi)

/--
**de Sitter T_H = κ/(2π) (Hawking-Unruh dS specialization).**
For dS₄ at Hubble parameter H > 0, the universal Hawking-Unruh
relation `T_H = κ/(2π)` reads `T_H_dS = H/(2π)` because
κ_dS = H. Gibbons-Hawking 1977 + Hawking-Unruh universal.

Substantive: this is the **dS specialization of the universal
T_H = κ/(2π) relation**, and it provides the named-quantity
identity `2π · T_H_dS = κ_dS` that mirrors
`schwarzschild_T_H_eq_kappa_over_2pi` in the Schwarzschild section.
The shared κ-T_H structure is the algebraic basis for treating
both dS and Schwarzschild as "BH-class" thermodynamic objects.
-/
theorem deSitter_T_H_eq_kappa_over_2pi (H : ℝ) (hH : 0 < H) :
    2 * Real.pi * deSitterHawkingTemp H = deSitterKappa H := by
  unfold deSitterHawkingTemp deSitterKappa
  have h_pi : 0 < Real.pi := Real.pi_pos
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

/-! ## §3 — Anti-de Sitter (K < 0) -/

/--
**AdS quantitative anchor: `Λ_AdS = -3 / ℓ²`.** Setting K = -1/ℓ²
for AdS radius ℓ > 0, the cosmological constant is Λ = -3/ℓ² < 0.

Cross-bridge to AdS holography literature: AdS₅ × S⁵ has
ℓ_AdS = (4πg_s N α'²)^{1/4}, so the AdS₅ cosmological constant
encodes the 't Hooft coupling.

Substantive: the K < 0 specialization of `deSitter_lambda_vacuum_iff`
giving the explicit AdS-radius-to-Λ relation.
-/
theorem ads_lambda_eq_neg_three_over_ell_sq (ℓ : ℝ) (hℓ : 0 < ℓ) :
    let K : ℝ := -1 / (ℓ ^ 2)
    (∀ μ ν : Fin 4, einsteinTensor (ricciOf (constantSectionalRiemann K η))
        (scalarOf (ricciOf (constantSectionalRiemann K η)) η) η μ ν
          + (-3 / (ℓ ^ 2)) * η μ ν = 0) := by
  intro K
  have hℓ_sq_ne : (ℓ ^ 2 : ℝ) ≠ 0 := by positivity
  apply (deSitter_lambda_vacuum_iff K (-3 / (ℓ ^ 2))).mpr
  show (-3 / (ℓ ^ 2) : ℝ) = 3 * (-1 / (ℓ ^ 2))
  field_simp

/-! ## §4 — Schwarzschild infrastructure (Kerr-Schild form)

Kerr-Schild form: `g_μν = η_μν + φ(r) l_μ l_ν` with `φ = 2M/r` and
`l = (1, x/r, y/r, z/r)`. Wave 4 contributes substantive content on
top of `KerrSchild.lean`: the horizon-location biconditional, three
g_tt signature theorems characterizing the timelike/null/spacelike
character of the t-direction across the horizon, named
Schwarzschild thermodynamic quantities (κ, T_H, A, S_BH), and BH
thermodynamics cross-bridges to Phase 6a Wave 5
`BHThermodynamicsFourLaws`.
-/

/-- **Schwarzschild horizon radius**: `r_H(M) = 2M`. The unique
    radius at which the Schwarzschild Killing horizon is located. -/
noncomputable def schwarzschildHorizonRadius (M : ℝ) : ℝ := 2 * M

/-- **Schwarzschild surface gravity**: `κ(M) = 1 / (4M)`.
    Bardeen-Carter-Hawking 1973. Geometrically tractable
    horizon-quantity that determines the Hawking temperature via
    the universal Hawking-Unruh formula T_H = κ/(2π). -/
noncomputable def schwarzschildKappa (M : ℝ) : ℝ := 1 / (4 * M)

/-- **Schwarzschild Hawking temperature**: `T_H(M) = 1 / (8πM)`.
    Hawking 1975. Cross-bridge to Phase 6a Wave 5 BH
    thermodynamics regime classifier. -/
noncomputable def schwarzschildHawkingTemp (M : ℝ) : ℝ := 1 / (8 * Real.pi * M)

/-- **Schwarzschild event-horizon area**: `A(M) = 4π · r_H²`.
    The horizon is a topological 2-sphere of radius r_H = 2M. -/
noncomputable def schwarzschildArea (M : ℝ) : ℝ :=
  4 * Real.pi * (schwarzschildHorizonRadius M) ^ 2

/-- **Schwarzschild Bekenstein-Hawking entropy**: `S_BH(M) = A / 4`.
    Bekenstein 1973, Hawking 1976. -/
noncomputable def schwarzschildBHEntropy (M : ℝ) : ℝ :=
  (schwarzschildArea M) / 4


/--
**Schwarzschild horizon biconditional: `φ = 1 ↔ r = 2M`.**
Strengthens the existing `KerrSchild.schwarzschild_horizon`
(forward direction `r = 2M ⇒ φ = 1`) to a biconditional, making
the horizon-location claim falsifiable rather than just informative.

The biconditional is non-trivial: it asserts the Schwarzschild
scalar `φ(r) = 2M/r` reaches the value 1 at exactly **one** radius
r = 2M.
-/
theorem schwarzschild_horizon_iff
    (M r : ℝ) (hM : 0 < M) (hr : 0 < r) :
    2 * M / r = 1 ↔ r = 2 * M := by
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp

/--
**Schwarzschild g_tt outside horizon: `g_tt = -1 + 2M/r < 0`.**
For r > 2M (outside horizon), the time-time metric component is
strictly negative, confirming the t-coordinate is timelike outside
the horizon (signature `−+++`).

Quantitative identity: `g_tt(r) = -(1 - 2M/r)` is the load-bearing
algebraic structure of static Schwarzschild coordinates.
-/
theorem schwarzschild_g_tt_outside_horizon_neg
    (M r : ℝ) (hM : 0 < M) (h_outside : 2 * M < r) :
    -1 + 2 * M / r < 0 := by
  have hr_pos : 0 < r := lt_trans (by linarith : (0 : ℝ) < 2 * M) h_outside
  have h_phi_lt_one : 2 * M / r < 1 := by
    rw [div_lt_one hr_pos]; exact h_outside
  linarith

/--
**Schwarzschild g_tt at horizon: `g_tt(2M) = 0`.** The t-direction
degenerates to null at the horizon. Algebraic basis for the
Killing-vector-character-flip locus of the timelike Killing vector
∂_t.
-/
theorem schwarzschild_g_tt_at_horizon_zero (M : ℝ) (hM : 0 < M) :
    -1 + 2 * M / (2 * M) = 0 := by
  have h2M_ne : (2 * M : ℝ) ≠ 0 := by positivity
  field_simp; ring

/--
**Schwarzschild g_tt inside horizon: `g_tt > 0`.** For 0 < r < 2M
(inside horizon), the time-time metric component is **positive**,
confirming the t-coordinate is **spacelike** inside the horizon.
The famous Schwarzschild "r↔t character flip."

Substantive: the strict-positivity claim is non-trivial — requires
both r > 0 (for division) and r < 2M (for the sign). Note that
M > 0 is **derived** from `hr : 0 < r` and `h_inside : r < 2*M`
via positivity, so we omit it from the signature; the hypotheses
in the signature are exactly the load-bearing inputs to the proof.
-/
theorem schwarzschild_g_tt_inside_horizon_pos
    (M r : ℝ) (hr : 0 < r) (h_inside : r < 2 * M) :
    0 < -1 + 2 * M / r := by
  have h_phi_gt_one : 1 < 2 * M / r := by
    rw [lt_div_iff₀ hr]; linarith
  linarith

/--
**Schwarzschild surface-gravity-times-4M identity: `κ · 4M = 1`
for M > 0.** The product of surface gravity and 4M is a universal
constant (= 1) independent of M, encoding the inverse-mass
scaling κ ∝ 1/M.

Bardeen-Carter-Hawking 1973. The `rfl` definitional unfold
`schwarzschildKappa M = 1/(4M)` is captured at the def level (not
shipped as a separate theorem per the 6f.4 strengthening discipline:
pure-rfl theorems are CUT in favor of their named-quantity
substantive consumer).
-/
theorem schwarzschild_kappa_times_4M (M : ℝ) (hM : 0 < M) :
    schwarzschildKappa M * (4 * M) = 1 := by
  unfold schwarzschildKappa
  have h4M_ne : (4 * M : ℝ) ≠ 0 := by positivity
  field_simp

/--
**Schwarzschild T_H · M = 1/(8π) (mass-independent product).**
The product of Hawking temperature and mass equals the universal
constant 1/(8π), independent of M. Encodes T_H ∝ 1/M.

Cross-bridge: load-bearing for Phase 6a Wave 5
`BHThermodynamicsFourLaws` regime classifier prediction
T_H = 1/(8πM) for Schwarzschild-class BHs.
-/
theorem schwarzschild_T_H_times_M (M : ℝ) (hM : 0 < M) :
    schwarzschildHawkingTemp M * M = 1 / (8 * Real.pi) := by
  unfold schwarzschildHawkingTemp
  have h_pi : 0 < Real.pi := Real.pi_pos
  have h8piM_ne : (8 * Real.pi * M : ℝ) ≠ 0 := by positivity
  have h8pi_ne : (8 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

/--
**Schwarzschild T_H = κ/(2π) (Hawking-Unruh universal relation).**
For Schwarzschild, T_H = 1/(8πM) and κ = 1/(4M), so
2π · T_H = 2π · 1/(8πM) = 1/(4M) = κ.

This is the load-bearing **κ ↔ T_H connection**, making the
Schwarzschild Hawking temperature derivable from the surface
gravity (a tractable horizon-geometric quantity, not a quantum-
thermal one). Bardeen-Carter-Hawking 1973 + Hawking 1975.
-/
theorem schwarzschild_T_H_eq_kappa_over_2pi (M : ℝ) (hM : 0 < M) :
    2 * Real.pi * schwarzschildHawkingTemp M = schwarzschildKappa M := by
  unfold schwarzschildHawkingTemp schwarzschildKappa
  have h_pi : 0 < Real.pi := Real.pi_pos
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have h8piM_ne : (8 * Real.pi * M : ℝ) ≠ 0 := by positivity
  have h4M_ne : (4 * M : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/--
**Schwarzschild event-horizon area: `A_H = 16π M²`.** Substantive
named identity tying the `schwarzschildArea` definition to the
Hawking-Bekenstein closed form. Cross-bridge to BH thermodynamics.
-/
theorem schwarzschild_area_eq_16pi_M_sq (M : ℝ) :
    schwarzschildArea M = 16 * Real.pi * M ^ 2 := by
  unfold schwarzschildArea schwarzschildHorizonRadius
  ring

/-- The area derivative along a curve of Schwarzschild geometric masses. -/
theorem schwarzschildArea_profile_deriv
    {m : ℝ → ℝ} {t dm : ℝ} (hm : HasDerivAt m dm t) :
    HasDerivAt (fun s ↦ schwarzschildArea (m s)) (32 * Real.pi * m t * dm) t := by
  simp_rw [schwarzschild_area_eq_16pi_M_sq]
  convert (hm.fun_pow 2).const_mul (16 * Real.pi) using 1 <;> first | rfl | ring

private theorem schwarzschild_area_term
    {G m dm : ℝ} (hG : G ≠ 0) (hm : m ≠ 0) :
    schwarzschildKappa m / (8 * Real.pi * G) * (32 * Real.pi * m * dm) = dm / G := by
  unfold schwarzschildKappa
  field_simp [hG, hm, Real.pi_ne_zero]
  ring

/-- Fixed-coupling Schwarzschild first law with geometric mass G times physical mass. -/
theorem schwarzschild_fixed_G_firstLaw
    {mass : ℝ → ℝ} {G t dM : ℝ}
    (hG : 0 < G) (hM : 0 < mass t) (hMass : HasDerivAt mass dM t) :
    let dA := 32 * Real.pi * (G * mass t) * (G * dM)
    HasDerivAt (fun s ↦ schwarzschildArea (G * mass s)) dA t ∧
      dM = schwarzschildKappa (G * mass t) / (8 * Real.pi * G) * dA := by
  dsimp only
  refine ⟨schwarzschildArea_profile_deriv (hMass.const_mul G), ?_⟩
  rw [schwarzschild_area_term (ne_of_gt hG) (ne_of_gt (mul_pos hG hM))]
  field_simp [ne_of_gt hG]

/-- Varying-coupling control within the algebraic Schwarzschild family. -/
theorem schwarzschild_varying_G_area_control
    {coupling mass : ℝ → ℝ} {t dG dM : ℝ}
    (hG : 0 < coupling t) (hM : 0 < mass t)
    (hCoupling : HasDerivAt coupling dG t) (hMass : HasDerivAt mass dM t) :
    let dA := 32 * Real.pi * (coupling t * mass t) * (dG * mass t + coupling t * dM)
    HasDerivAt (fun s ↦ schwarzschildArea (coupling s * mass s)) dA t ∧
      schwarzschildKappa (coupling t * mass t) / (8 * Real.pi * coupling t) * dA =
        dM + mass t * dG / coupling t := by
  dsimp only
  refine ⟨schwarzschildArea_profile_deriv (hCoupling.fun_mul hMass), ?_⟩
  rw [schwarzschild_area_term (ne_of_gt hG) (ne_of_gt (mul_pos hG hM))]
  field_simp [ne_of_gt hG]
  ring

section SphericalExterior

open Filter Set
open scoped Topology

/-- The reduced spherical vacuum ODE makes the radial mass function constant. -/
theorem spherical_massFunction_eq_at_radius
    (F : ℝ → ℝ) {a r₀ : ℝ} (hr₀ : a < r₀)
    (hF : ∀ r > a, DifferentiableAt ℝ F r)
    (hVac : ∀ r > a, r * deriv F r + F r - 1 = 0) :
    EqOn (fun r ↦ r * (1 - F r)) (fun _ ↦ r₀ * (1 - F r₀)) (Ioi a) := by
  have hMass (r : ℝ) (hr : a < r) :
      HasDerivAt (fun s ↦ s * (1 - F s)) 0 r := by
    have hsub := (hasDerivAt_const r (1 : ℝ)).sub (hF r hr).hasDerivAt
    have hzero : 1 * (1 - F r) + r * (0 - deriv F r) = 0 := by
      linarith [hVac r hr]
    rw [← hzero]
    exact (hasDerivAt_id' (x := r)).fun_mul hsub
  refine isOpen_Ioi.eqOn_of_deriv_eq (convex_Ioi a).isPreconnected ?_ ?_ ?_ hr₀ rfl
  · intro r hr
    exact (hMass r hr).differentiableAt.differentiableWithinAt
  · exact differentiableOn_const _
  · intro r hr
    exact (hMass r hr).deriv.trans
      (hasDerivAt_const r (r₀ * (1 - F r₀))).deriv.symm

/-- The weak-field normalization fixes the unique spherical lapse on the exterior. -/
theorem spherical_normalized_lapse
    (F : ℝ → ℝ) {a C : ℝ} (ha : 0 ≤ a)
    (hF : ∀ r > a, DifferentiableAt ℝ F r)
    (hVac : ∀ r > a, r * deriv F r + F r - 1 = 0)
    (hTail : Tendsto (fun r ↦ r * (1 - F r)) atTop (𝓝 C)) :
    ∀ r > a, F r = 1 - C / r := by
  let r₀ : ℝ := a + 1
  have hr₀ : a < r₀ := by dsimp [r₀]; linarith
  have hconst := spherical_massFunction_eq_at_radius F hr₀ hF hVac
  have hevent :
      (fun r ↦ r * (1 - F r)) =ᶠ[atTop] (fun _ ↦ r₀ * (1 - F r₀)) :=
    (eventually_gt_atTop a).mono fun r hr ↦ hconst hr
  have hC : C = r₀ * (1 - F r₀) :=
    tendsto_nhds_unique (hTail.congr' hevent) tendsto_const_nhds
  intro r hr
  have hrne : r ≠ 0 := ne_of_gt (lt_of_le_of_lt ha hr)
  have hmass : r * (1 - F r) = C := (hconst hr).trans hC.symm
  have hdiv : C / r = 1 - F r := (div_eq_iff hrne).2 (by
    simpa only [mul_comm r] using hmass.symm)
  rw [hdiv]
  ring

/-- With the normalized ingoing chart conventions, the unique zero gives the
Schwarzschild sphere area and half-lapse-slope profile. The radial interval
must contain the candidate horizon. -/
theorem spherical_normalized_horizon_profiles
    (F : ℝ → ℝ) {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) (hinside : a < 2 * m)
    (hF : ∀ r > a, DifferentiableAt ℝ F r)
    (hVac : ∀ r > a, r * deriv F r + F r - 1 = 0)
    (hTail : Tendsto (fun r ↦ r * (1 - F r)) atTop (𝓝 (2 * m))) :
    (∀ r > a, F r = 0 ↔ r = schwarzschildHorizonRadius m) ∧
    4 * Real.pi * (2 * m) ^ 2 = schwarzschildArea m ∧
    deriv F (2 * m) / 2 = schwarzschildKappa m := by
  have hFexact := spherical_normalized_lapse F ha hF hVac hTail
  have hzero (r : ℝ) (hr : a < r) :
      F r = 0 ↔ r = schwarzschildHorizonRadius m := by
    have hrne : r ≠ 0 := ne_of_gt (lt_of_le_of_lt ha hr)
    unfold schwarzschildHorizonRadius
    rw [hFexact r hr]
    constructor
    · intro hz
      have hq : 2 * m / r = 1 := by linarith
      simpa using ((div_eq_iff hrne).1 hq).symm
    · rintro rfl
      simp [hrne]
  refine ⟨hzero, rfl, ?_⟩
  have hz : F (2 * m) = 0 := (hzero (2 * m) hinside).2 rfl
  have hmne : m ≠ 0 := ne_of_gt hm
  have h2m : (2 : ℝ) * m ≠ 0 := mul_ne_zero (by norm_num) hmne
  have hd : deriv F (2 * m) = 1 / (2 * m) := (eq_div_iff h2m).2 (by
    have hODE := hVac (2 * m) hinside
    rw [hz] at hODE
    nlinarith)
  rw [hd]
  unfold schwarzschildKappa
  field_simp [hmne]
  ring

end SphericalExterior

section IngoingChart

open Filter
open scoped Topology

open SKEFTHawking.RiemannianConnection

/-- Ingoing chart with coordinates ordered v,r,θ,φ and round angular block. -/
noncomputable def ingoingSphericalMetric (F : ℝ → ℝ) (r θ : ℝ) : MetricMatrix :=
  ![![-F r, 1, 0, 0], ![1, 0, 0, 0],
    ![0, 0, r ^ 2, 0], ![0, 0, 0, r ^ 2 * Real.sin θ ^ 2]]

/-- The radial block has inverse even at a zero of F. Angular poles are excluded. -/
noncomputable def ingoingSphericalInverse (F : ℝ → ℝ) (r θ : ℝ) : MetricMatrix :=
  ![![0, 1, 0, 0], ![1, F r, 0, 0],
    ![0, 0, 1 / r ^ 2, 0], ![0, 0, 0, 1 / (r ^ 2 * Real.sin θ ^ 2)]]

theorem ingoingSpherical_inverse (F : ℝ → ℝ) {r θ : ℝ}
    (hr : r ≠ 0) (hθ : Real.sin θ ≠ 0) (i j : Fin 4) :
    sumFin4 (fun k ↦ ingoingSphericalMetric F r θ i k *
      ingoingSphericalInverse F r θ k j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [sumFin4, ingoingSphericalMetric,
      ingoingSphericalInverse, hr]
  field_simp [hr, hθ]

/-- Radial nondegeneracy requires no condition on the lapse. -/
theorem ingoingSpherical_radial_det (F : ℝ → ℝ) (r θ : ℝ) :
    ingoingSphericalMetric F r θ 0 0 * ingoingSphericalMetric F r θ 1 1 -
      ingoingSphericalMetric F r θ 0 1 * ingoingSphericalMetric F r θ 1 0 = -1 := by
  norm_num [ingoingSphericalMetric]

/-- Metric components at a chart point; they are independent of v and φ. -/
noncomputable def ingoingChartMetric (F : ℝ → ℝ) (x : Fin 4 → ℝ) : MetricMatrix :=
  ingoingSphericalMetric F (x 1) (x 2)

/-- Actual coordinate partials used in the Koszul Christoffel formula. -/
noncomputable def ingoingMetricPartial (F : ℝ → ℝ) (x : Fin 4 → ℝ) : MetricPartial :=
  fun d i j ↦ deriv (fun s ↦ ingoingChartMetric F (Function.update x d s) i j) (x d)

theorem ingoingMetricPartial_v (F : ℝ → ℝ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    ingoingMetricPartial F x 0 i j = 0 := by
  simp [ingoingMetricPartial, ingoingChartMetric, Function.update]

theorem ingoingMetricPartial_vv (F : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hF : DifferentiableAt ℝ F (x 1)) (d : Fin 4) :
    ingoingMetricPartial F x d 0 0 = if d = 1 then -deriv F (x 1) else 0 := by
  by_cases hd : d = 1
  · subst d
    have hline : (fun s ↦ ingoingChartMetric F (Function.update x 1 s) 0 0) =
        fun s ↦ -F s := by
      funext s
      simp [ingoingChartMetric, ingoingSphericalMetric]
    unfold ingoingMetricPartial
    rw [hline, if_pos rfl]
    exact hF.hasDerivAt.neg.deriv
  · simp [ingoingMetricPartial, ingoingChartMetric, ingoingSphericalMetric,
      Function.update, hd, Ne.symm hd]

/-- Components of the stationary coordinate generator ∂v. -/
def ingoingK (i : Fin 4) : ℝ := if i = 0 then 1 else 0

theorem ingoingK_nonzero : ingoingK 0 ≠ 0 := by norm_num [ingoingK]

theorem ingoingK_norm (F : ℝ → ℝ) (r θ : ℝ) :
    sumFin4 (fun i ↦ sumFin4 (fun j ↦
      ingoingSphericalMetric F r θ i j * ingoingK i * ingoingK j)) = -F r := by
  simp (config := {decide := true}) [sumFin4, ingoingSphericalMetric, ingoingK]

/-- At a lapse zero the inverse-column identities encode the null normal dr
and its raised vector ∂v on the regular chart of `ingoingSpherical_inverse`. -/
theorem ingoing_horizon_normal (F : ℝ → ℝ) {r θ : ℝ} (hz : F r = 0) :
    ingoingSphericalInverse F r θ 1 1 = 0 ∧
      (∀ i, ingoingSphericalInverse F r θ i 1 = ingoingK i) := by
  refine ⟨?_, ?_⟩
  · simp [ingoingSphericalInverse, hz]
  · intro i
    fin_cases i <;> norm_num [ingoingSphericalInverse, ingoingK, hz]

/-- Stationarity and the actual partial of g_vv give the radial inverse column
in the covariant acceleration of the constant coordinate generator. -/
theorem ingoing_christoffel_vv (F : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hF : DifferentiableAt ℝ F (x 1)) (i : Fin 4) :
    christoffelKoszul (ingoingSphericalInverse F (x 1) (x 2))
      (ingoingMetricPartial F x) i 0 0 =
      (deriv F (x 1) / 2) * ingoingSphericalInverse F (x 1) (x 2) i 1 := by
  simp [christoffelKoszul, sumFin4, ingoingMetricPartial_v,
    ingoingMetricPartial_vv F x hF]
  ring

/-- The horizon generator has nonaffinity F′/2 in the fixed ingoing chart
scale. Interpret the connection on the regular chart of `ingoingSpherical_inverse`. -/
theorem ingoing_horizon_nonaffinity (F : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hF : DifferentiableAt ℝ F (x 1)) (hz : F (x 1) = 0) (i : Fin 4) :
    christoffelKoszul (ingoingSphericalInverse F (x 1) (x 2))
      (ingoingMetricPartial F x) i 0 0 = (deriv F (x 1) / 2) * ingoingK i := by
  rw [ingoing_christoffel_vv F x hF, (ingoing_horizon_normal F hz).2 i]

/-- The normalized lapse gives the Schwarzschild nonaffinity at the chart horizon. -/
theorem ingoing_normalized_horizon_nonaffinity
    (F : ℝ → ℝ) (x : Fin 4 → ℝ) {a m : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hinside : a < 2 * m) (hx : x 1 = 2 * m)
    (hF : ∀ r > a, DifferentiableAt ℝ F r)
    (hVac : ∀ r > a, r * deriv F r + F r - 1 = 0)
    (hTail : Tendsto (fun r ↦ r * (1 - F r)) atTop (𝓝 (2 * m))) (i : Fin 4) :
    christoffelKoszul (ingoingSphericalInverse F (x 1) (x 2))
      (ingoingMetricPartial F x) i 0 0 = schwarzschildKappa m * ingoingK i := by
  obtain ⟨hzero, _, hκ⟩ := spherical_normalized_horizon_profiles F ha hm hinside hF hVac hTail
  have hxinside : a < x 1 := hx.symm ▸ hinside
  have hz : F (x 1) = 0 := (hzero (x 1) hxinside).2 hx
  rw [ingoing_horizon_nonaffinity F x (hF (x 1) hxinside) hz, hx, hκ]

open SKEFTHawking.RiemannCoordinate

noncomputable def ingoingChartChristoffel (F : ℝ → ℝ) (x : Fin 4 → ℝ) : Christoffel :=
  christoffelKoszul (ingoingSphericalInverse F (x 1) (x 2)) (ingoingMetricPartial F x)

noncomputable def ingoingChartChristoffelPartial
    (F : ℝ → ℝ) (x : Fin 4 → ℝ) : ChristoffelPartial :=
  fun d i j k ↦ deriv (fun s ↦ ingoingChartChristoffel F (Function.update x d s) i j k) (x d)

private noncomputable def ingoingPartialTable
    (F : ℝ → ℝ) (r θ : ℝ) : MetricPartial :=
  fun d i j ↦ match d.val, i.val, j.val with
    | 1, 0, 0 => -deriv F r
    | 1, 2, 2 => 2 * r
    | 1, 3, 3 => 2 * r * Real.sin θ ^ 2
    | 2, 3, 3 => r ^ 2 * (2 * Real.sin θ * Real.cos θ)
    | _, _, _ => 0

private theorem ingoingMetricPartial_eq_table (F : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hF : DifferentiableAt ℝ F (x 1)) :
    ingoingMetricPartial F x = ingoingPartialTable F (x 1) (x 2) := by
  have hrr : deriv (fun s : ℝ ↦ s ^ 2) (x 1) = 2 * x 1 := by
    simp
  have hrrφ : deriv (fun s : ℝ ↦ s ^ 2 * Real.sin (x 2) ^ 2) (x 1) =
      2 * x 1 * Real.sin (x 2) ^ 2 := by
    simp
  have hθφ : deriv (fun s : ℝ ↦ x 1 ^ 2 * Real.sin s ^ 2) (x 2) =
      x 1 ^ 2 * (2 * Real.sin (x 2) * Real.cos (x 2)) := by
    simp
  have hn : deriv (fun s ↦ -F s) (x 1) = -deriv F (x 1) := hF.hasDerivAt.neg.deriv
  funext d i j
  fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [ingoingMetricPartial, ingoingChartMetric,
      ingoingSphericalMetric, ingoingPartialTable, Function.update, hrr, hrrφ, hθφ, hn]

private noncomputable def ingoingChristoffelTable
    (F : ℝ → ℝ) (r θ : ℝ) : Christoffel :=
  fun i j k ↦ match i.val, j.val, k.val with
    | 0, 0, 0 => deriv F r / 2
    | 1, 0, 0 => F r * deriv F r / 2
    | 1, 0, 1 | 1, 1, 0 => -(deriv F r / 2)
    | 0, 2, 2 => -r
    | 1, 2, 2 => -r * F r
    | 0, 3, 3 => -r * Real.sin θ ^ 2
    | 1, 3, 3 => -r * F r * Real.sin θ ^ 2
    | 2, 1, 2 | 2, 2, 1 | 3, 1, 3 | 3, 3, 1 => 1 / r
    | 2, 3, 3 => -Real.sin θ * Real.cos θ
    | 3, 2, 3 | 3, 3, 2 => Real.cos θ / Real.sin θ
    | _, _, _ => 0

private theorem ingoingChartChristoffel_eq_table (F : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hθ : Real.sin (x 2) ≠ 0)
    (hF : DifferentiableAt ℝ F (x 1)) :
    ingoingChartChristoffel F x = ingoingChristoffelTable F (x 1) (x 2) := by
  unfold ingoingChartChristoffel
  rw [ingoingMetricPartial_eq_table F x hF]
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp (config := {decide := true}) [christoffelKoszul, sumFin4,
      ingoingSphericalInverse, ingoingPartialTable, ingoingChristoffelTable] <;>
    field_simp [hr, hθ]

private theorem ingoingChartChristoffelPartial_eq_table_deriv
    (F : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hθ : Real.sin (x 2) ≠ 0)
    (hF : DifferentiableAt ℝ F (x 1))
    (hNear : ∀ᶠ s in 𝓝 (x 1), DifferentiableAt ℝ F s) (d i j k : Fin 4) :
    ingoingChartChristoffelPartial F x d i j k =
      deriv (fun s ↦ ingoingChristoffelTable F
        (Function.update x d s 1) (Function.update x d s 2) i j k) (x d) := by
  apply Filter.EventuallyEq.deriv_eq
  have hrNear : ∀ᶠ s : ℝ in 𝓝 (x 1), s ≠ 0 := isOpen_ne.mem_nhds hr
  have hθNear : ∀ᶠ s : ℝ in 𝓝 (x 2), Real.sin s ≠ 0 :=
    Real.continuous_sin.continuousAt.eventually_ne hθ
  fin_cases d
  · exact Eventually.of_forall fun s ↦ congrFun (congrFun (congrFun
      (ingoingChartChristoffel_eq_table F (Function.update x 0 s)
        (by simpa using hr) (by simpa using hθ) (by simpa using hF)) i) j) k
  · filter_upwards [hrNear, hNear] with s hsr hsF
    exact congrFun (congrFun (congrFun
      (ingoingChartChristoffel_eq_table F (Function.update x 1 s)
        (by simpa using hsr) (by simpa using hθ) (by simpa using hsF)) i) j) k
  · filter_upwards [hθNear] with s hsθ
    exact congrFun (congrFun (congrFun
      (ingoingChartChristoffel_eq_table F (Function.update x 2 s)
        (by simpa using hr) (by simpa using hsθ) (by simpa using hF)) i) j) k
  · exact Eventually.of_forall fun s ↦ congrFun (congrFun (congrFun
      (ingoingChartChristoffel_eq_table F (Function.update x 3 s)
        (by simpa using hr) (by simpa using hθ) (by simpa using hF)) i) j) k

/-- The angular Ricci component of the actual ingoing-chart metric. -/
theorem ingoing_spherical_ricci_theta_theta
    (F : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hθ : Real.sin (x 2) ≠ 0)
    (hF : DifferentiableAt ℝ F (x 1))
    (hNear : ∀ᶠ s in 𝓝 (x 1), DifferentiableAt ℝ F s) :
    ricciOf (riemannCoord (ingoingChartChristoffel F x)
      (ingoingChartChristoffelPartial F x)) 2 2 = 1 - F (x 1) - x 1 * deriv F (x 1) := by
  have hrad : deriv (fun s ↦ s * F s) (x 1) = F (x 1) + x 1 * deriv F (x 1) := by
    simpa using ((hasDerivAt_id' (x := x 1)).fun_mul hF.hasDerivAt).deriv
  have hcot : deriv (fun s ↦ Real.cos s / Real.sin s) (x 2) =
      -(1 / Real.sin (x 2) ^ 2) := by
    rw [((Real.hasDerivAt_cos (x 2)).fun_div (Real.hasDerivAt_sin (x 2)) hθ).deriv]
    field_simp [hθ]
    nlinarith [Real.sin_sq_add_cos_sq (x 2)]
  simp only [ricciOf, riemannCoord, riemannLinearTerm, riemannQuadraticTerm, sumFin4]
  simp_rw [ingoingChartChristoffelPartial_eq_table_deriv F x hr hθ hF hNear,
    ingoingChartChristoffel_eq_table F x hr hθ hF]
  simp (config := {decide := true}) [ingoingChristoffelTable, Function.update, hrad, hcot]
  field_simp [hr, hθ]
  have hcos : Real.cos (x 2) ^ 2 = 1 - Real.sin (x 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x 2)]
  ring_nf
  simp only [hcos]
  ring

/-- Angular vacuum Ricci implies the reduced radial equation. -/
theorem ingoing_spherical_reducedVacuum_of_ricci_theta_theta
    (F : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hθ : Real.sin (x 2) ≠ 0)
    (hF : DifferentiableAt ℝ F (x 1))
    (hNear : ∀ᶠ s in 𝓝 (x 1), DifferentiableAt ℝ F s)
    (hVac : ricciOf (riemannCoord (ingoingChartChristoffel F x)
      (ingoingChartChristoffelPartial F x)) 2 2 = 0) :
    x 1 * deriv F (x 1) + F (x 1) - 1 = 0 := by
  rw [ingoing_spherical_ricci_theta_theta F x hr hθ hF hNear] at hVac
  linarith

/-- Independent components of the Ricci tensor in the stationary ingoing chart. -/
noncomputable def ingoingSphericalRicciTable
    (f f₁ f₂ r θ : ℝ) : RicciTensor :=
  let q := f₂ / 2 + f₁ / r
  let w := 1 - f - r * f₁
  ![![f * q, -q, 0, 0], ![-q, 0, 0, 0],
    ![0, 0, w, 0], ![0, 0, 0, w * Real.sin θ ^ 2]]

set_option maxHeartbeats 600000 in
/-- Full coordinate Ricci tensor. Only the radial second derivative is needed. -/
theorem ingoing_spherical_fullRicci
    (F : ℝ → ℝ) (x : Fin 4 → ℝ) {f₂ : ℝ}
    (hr : x 1 ≠ 0) (hθ : Real.sin (x 2) ≠ 0)
    (hF : DifferentiableAt ℝ F (x 1))
    (hNear : ∀ᶠ s in 𝓝 (x 1), DifferentiableAt ℝ F s)
    (h₂ : HasDerivAt (deriv F) f₂ (x 1)) :
    ricciOf (riemannCoord (ingoingChartChristoffel F x)
      (ingoingChartChristoffelPartial F x)) =
      ingoingSphericalRicciTable (F (x 1)) (deriv F (x 1)) f₂ (x 1) (x 2) := by
  have hid := hasDerivAt_id' (x := x 1)
  have hfr := hid.fun_mul hF.hasDerivAt
  have hrad : deriv (fun s ↦ s * F s) (x 1) = F (x 1) + x 1 * deriv F (x 1) := by
    simpa using hfr.deriv
  have hradφ : deriv (fun s ↦ s * F s * Real.sin (x 2) ^ 2) (x 1) =
      (F (x 1) + x 1 * deriv F (x 1)) * Real.sin (x 2) ^ 2 := by
    simpa only [one_mul] using (hfr.mul_const (Real.sin (x 2) ^ 2)).deriv
  have hfrd : deriv (fun s ↦ F s * deriv F s / 2) (x 1) =
      (deriv F (x 1) * deriv F (x 1) + F (x 1) * f₂) / 2 :=
    ((hF.hasDerivAt.fun_mul h₂).div_const 2).deriv
  have hhalf : deriv (fun s ↦ deriv F s / 2) (x 1) = f₂ / 2 :=
    (h₂.div_const 2).deriv
  have hcot : deriv (fun s ↦ Real.cos s / Real.sin s) (x 2) =
      -(1 / Real.sin (x 2) ^ 2) := by
    rw [((Real.hasDerivAt_cos (x 2)).fun_div (Real.hasDerivAt_sin (x 2)) hθ).deriv]
    field_simp [hθ]
    nlinarith [Real.sin_sq_add_cos_sq (x 2)]
  have hsc : deriv (fun s ↦ Real.sin s * Real.cos s) (x 2) =
      Real.cos (x 2) ^ 2 - Real.sin (x 2) ^ 2 := by
    rw [((Real.hasDerivAt_sin (x 2)).fun_mul (Real.hasDerivAt_cos (x 2))).deriv]
    ring
  have hcos : Real.cos (x 2) ^ 2 = 1 - Real.sin (x 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x 2)]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [ricciOf, riemannCoord, riemannLinearTerm, riemannQuadraticTerm, sumFin4] <;>
    simp_rw [ingoingChartChristoffelPartial_eq_table_deriv F x hr hθ hF hNear,
      ingoingChartChristoffel_eq_table F x hr hθ hF] <;>
    simp (config := {decide := true}) [ingoingChristoffelTable, ingoingSphericalRicciTable,
      Function.update, hrad, hradφ, hfrd, hhalf, hcot, hsc] <;>
    field_simp [hr, hθ] <;> ring_nf <;> simp only [hcos] <;> ring

/-- At a point, angular vacuum and the differentiated radial condition are independent. -/
theorem ingoing_spherical_ricciFlat_iff
    (F : ℝ → ℝ) (x : Fin 4 → ℝ) {f₂ : ℝ}
    (hr : x 1 ≠ 0) (hθ : Real.sin (x 2) ≠ 0)
    (hF : DifferentiableAt ℝ F (x 1))
    (hNear : ∀ᶠ s in 𝓝 (x 1), DifferentiableAt ℝ F s)
    (h₂ : HasDerivAt (deriv F) f₂ (x 1)) :
    (∀ i j, ricciOf (riemannCoord (ingoingChartChristoffel F x)
      (ingoingChartChristoffelPartial F x)) i j = 0) ↔
      (x 1 * deriv F (x 1) + F (x 1) - 1 = 0 ∧
        x 1 * f₂ + 2 * deriv F (x 1) = 0) := by
  rw [ingoing_spherical_fullRicci F x hr hθ hF hNear h₂]
  constructor
  · intro h
    have hω := h 2 2
    have hq := h 0 1
    simp [ingoingSphericalRicciTable] at hω hq
    field_simp [hr] at hq
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hω, hq⟩ i j
    have hq' : f₂ / 2 + deriv F (x 1) / x 1 = 0 := by
      field_simp [hr]
      linarith
    have hω' : 1 - F (x 1) - x 1 * deriv F (x 1) = 0 := by linarith
    fin_cases i <;> fin_cases j <;> simp [ingoingSphericalRicciTable, hω', hq']

/-- On a neighborhood, the reduced vacuum equation implies full pointwise Ricci-flatness. -/
theorem ingoing_spherical_ricciFlat_of_local_reducedVacuum
    (F : ℝ → ℝ) (x : Fin 4 → ℝ) {f₂ : ℝ}
    (hr : x 1 ≠ 0) (hθ : Real.sin (x 2) ≠ 0)
    (hF : DifferentiableAt ℝ F (x 1))
    (hNear : ∀ᶠ s in 𝓝 (x 1), DifferentiableAt ℝ F s)
    (h₂ : HasDerivAt (deriv F) f₂ (x 1))
    (hVac : (fun s ↦ s * deriv F s + F s - 1) =ᶠ[𝓝 (x 1)] fun _ ↦ 0) :
    ∀ i j, ricciOf (riemannCoord (ingoingChartChristoffel F x)
      (ingoingChartChristoffelPartial F x)) i j = 0 := by
  apply (ingoing_spherical_ricciFlat_iff F x hr hθ hF hNear h₂).2
  refine ⟨hVac.eq_of_nhds, ?_⟩
  have hD := (((hasDerivAt_id' (x := x 1)).fun_mul h₂).add hF.hasDerivAt).sub_const 1
  have hz := hVac.deriv_eq
  change deriv (fun s ↦ s * deriv F s + F s - 1) (x 1) = _ at hz
  have hDval : deriv (fun s ↦ s * deriv F s + F s - 1) (x 1) = _ := hD.deriv
  rw [hDval, deriv_const] at hz
  linarith

section IngoingVariationalCompatibility

open SKEFTHawking.RiemannDifferentialBianchi
open SKEFTHawking.RiemannDifferentialBianchi.EHChart

private theorem ingoing_det_exact (F : ℝ → ℝ) (r θ : ℝ) :
    Matrix.det (ingoingSphericalMetric F r θ : Matrix (Fin 4) (Fin 4) ℝ) =
      -(r ^ 4 * Real.sin θ ^ 2) := by
  let M : Matrix (Fin 4) (Fin 4) ℝ := ingoingSphericalMetric F r θ
  change M.det = _
  have h0 : (M.submatrix (0 : Fin 4).succAbove Fin.succ).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero (0 : Fin 3)
    intro j
    fin_cases j <;> rfl
  have h1 : (M.submatrix (1 : Fin 4).succAbove Fin.succ).det =
      r ^ 4 * Real.sin θ ^ 2 := by
    rw [Matrix.det_fin_three]
    change 1 * r ^ 2 * (r ^ 2 * Real.sin θ ^ 2) - 1 * 0 * 0 -
      0 * 0 * (r ^ 2 * Real.sin θ ^ 2) + 0 * 0 * 0 + 0 * 0 * 0 -
      0 * r ^ 2 * 0 = _
    ring
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_four, h0, h1]
  have h10 : M 1 0 = 1 := rfl
  have h20 : M 2 0 = 0 := rfl
  have h30 : M 3 0 = 0 := rfl
  simp [h10, h20, h30]

private theorem ingoing_inverse_exact (F : ℝ → ℝ) (r θ : ℝ)
    (hr : r ≠ 0) (hθ : Real.sin θ ≠ 0) :
    @Inv.inv (Matrix (Fin 4) (Fin 4) ℝ) Matrix.inv (ingoingSphericalMetric F r θ) =
      ingoingSphericalInverse F r θ := by
  apply Matrix.inv_eq_right_inv
  ext i j
  simpa only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four, sumFin4] using
    ingoingSpherical_inverse F hr hθ i j

private theorem ingoing_weight_exact (F : ℝ → ℝ) (r θ : ℝ)
    (hr : 0 < r) (hθ : 0 < Real.sin θ) :
    Real.sqrt |Matrix.det
      (ingoingSphericalMetric F r θ : Matrix (Fin 4) (Fin 4) ℝ)| =
      r ^ 2 * Real.sin θ := by
  rw [ingoing_det_exact, abs_neg, abs_of_nonneg (by positivity :
    0 ≤ r ^ 4 * Real.sin θ ^ 2)]
  rw [show r ^ 4 * Real.sin θ ^ 2 = (r ^ 2 * Real.sin θ) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

private theorem spatialLineDeriv_eq_update (f : Chart → ℝ) (x : Chart) (a : Fin 4) :
    spatialLineDeriv f x a =
      deriv (fun t => f (Function.update x a t)) (x a) := by
  have hline (t : ℝ) : x + t • (Pi.single a 1 : Chart) =
      Function.update x a (x a + t) := by
    funext i
    by_cases h : i = a
    · subst i
      simp
    · simp [Function.update, h]
  unfold spatialLineDeriv
  simp_rw [hline]
  simpa only [add_zero] using
    deriv_comp_const_add (fun t => f (Function.update x a t)) (x a) (0 : ℝ)

private theorem update_line_continuous (x : Chart) (a i : Fin 4) :
    Continuous (fun t : ℝ => Function.update x a t i) := by
  by_cases h : i = a
  · subst i
    simp only [Function.update_self]
    change Continuous (id : ℝ → ℝ)
    exact continuous_id
  · simpa [Function.update, h] using (continuous_const : Continuous (fun _ : ℝ => x i))

private theorem update_line_regular (x : Chart) (a : Fin 4)
    (hr : 0 < x 1) (hθ : 0 < Real.sin (x 2)) :
    ∀ᶠ t in 𝓝 (x a), 0 < Function.update x a t 1 ∧
      0 < Real.sin (Function.update x a t 2) := by
  have h₁ : 0 < Function.update x a (x a) 1 := by simpa only [Function.update_eq_self] using hr
  have h₂ : 0 < Real.sin (Function.update x a (x a) 2) := by
    simpa only [Function.update_eq_self] using hθ
  exact (continuous_const.continuousAt.eventually_lt
      (update_line_continuous x a 1).continuousAt h₁).and
    (continuous_const.continuousAt.eventually_lt
      (Real.continuous_sin.comp (update_line_continuous x a 2)).continuousAt h₂)

/-- The ingoing spherical background is symmetric in all metric indices. -/
theorem ingoing_chart_baseSymmetric (F : ℝ → ℝ) :
    ∀ y i j, ingoingChartMetric F y i j = ingoingChartMetric F y j i := by
  intro y i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Continuity of the parameterized metric preserves nondegeneracy near
the ingoing base, including points where the lapse profile vanishes. -/
theorem ingoing_path_eventually_nondegenerate (g : MetricPath) (F : ℝ → ℝ) (x : Chart)
    (hBase : g 0 = ingoingChartMetric F)
    (hr : x 1 ≠ 0) (hθ : Real.sin (x 2) ≠ 0)
    (hcont : ContinuousAt (fun s => g s x) 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      Matrix.det (g s x : Matrix (Fin 4) (Fin 4) ℝ) ≠ 0 := by
  have hdet : Matrix.det (g 0 x : Matrix (Fin 4) (Fin 4) ℝ) ≠ 0 := by
    rw [hBase]
    change Matrix.det (ingoingSphericalMetric F (x 1) (x 2)) ≠ 0
    rw [ingoing_det_exact]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hθ))
  have hdetCont : ContinuousAt
      (fun s => Matrix.det (g s x : Matrix (Fin 4) (Fin 4) ℝ)) 0 :=
    (continuous_id.matrix_det.continuousAt).comp hcont
  exact hdetCont.eventually_ne hdet

private theorem ingoing_metricConnection_eq (g : MetricPath) (F : ℝ → ℝ) (x : Chart)
    (hBase : g 0 = ingoingChartMetric F) (hr : x 1 ≠ 0) (hθ : Real.sin (x 2) ≠ 0) :
    metricConnection g 0 x = ingoingChartChristoffel F x := by
  have hInv : metricInverse g 0 x = ingoingSphericalInverse F (x 1) (x 2) := by
    unfold metricInverse
    rw [hBase]
    exact ingoing_inverse_exact F (x 1) (x 2) hr hθ
  unfold metricConnection ingoingChartChristoffel ingoingMetricPartial
  simp_rw [hInv, hBase, spatialLineDeriv_eq_update]

/-- On a regular ingoing chart, the Ricci tensor used by the actual
Einstein–Hilbert density agrees with the ingoing-coordinate calculation. -/
theorem ingoing_metricRicci_eq (g : MetricPath) (F : ℝ → ℝ) (x : Chart)
    (hBase : g 0 = ingoingChartMetric F)
    (hr : 0 < x 1) (hθ : 0 < Real.sin (x 2)) :
    metricRicci g 0 x = ricciOf (riemannCoord (ingoingChartChristoffel F x)
      (ingoingChartChristoffelPartial F x)) := by
  have hPartial : metricConnectionPartial g 0 x = ingoingChartChristoffelPartial F x := by
    funext a i j k
    unfold metricConnectionPartial ingoingChartChristoffelPartial
    rw [spatialLineDeriv_eq_update]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [update_line_regular x a hr hθ] with t ht
    rw [ingoing_metricConnection_eq g F _ hBase ht.1.ne' ht.2.ne']
  rw [metricRicci, ingoing_metricConnection_eq g F x hBase hr.ne' hθ.ne', hPartial]

/-- The local reduced vacuum equation makes the actual chart Ricci tensor
vanish at the base of an arbitrary metric path on the regular patch. -/
theorem ingoing_metricRicci_eq_zero_of_local_reducedVacuum
    (g : MetricPath) (F : ℝ → ℝ) (x : Chart) {f₂ : ℝ}
    (hBase : g 0 = ingoingChartMetric F)
    (hr : 0 < x 1) (hθ : 0 < Real.sin (x 2))
    (hF : DifferentiableAt ℝ F (x 1))
    (hNear : ∀ᶠ s in 𝓝 (x 1), DifferentiableAt ℝ F s)
    (h₂ : HasDerivAt (deriv F) f₂ (x 1))
    (hVac : (fun s ↦ s * deriv F s + F s - 1) =ᶠ[𝓝 (x 1)] fun _ ↦ 0) :
    ∀ i j, metricRicci g 0 x i j = 0 := by
  rw [ingoing_metricRicci_eq g F x hBase hr hθ]
  exact ingoing_spherical_ricciFlat_of_local_reducedVacuum F x hr.ne' hθ.ne' hF hNear h₂ hVac

private noncomputable def ingoingInversePartialTable
    (F : ℝ → ℝ) (r θ : ℝ) : Fin 4 → MetricMatrix :=
  fun a i j => match a.val, i.val, j.val with
    | 1, 1, 1 => deriv F r
    | 1, 2, 2 => -(2 / r ^ 3)
    | 1, 3, 3 => -(2 / (r ^ 3 * Real.sin θ ^ 2))
    | 2, 3, 3 => -(2 * Real.cos θ / (r ^ 2 * Real.sin θ ^ 3))
    | _, _, _ => 0

private theorem ingoing_inverse_update_derivative (F : ℝ → ℝ) (x : Chart)
    (hr : x 1 ≠ 0) (hθ : Real.sin (x 2) ≠ 0) (a i j : Fin 4) :
    deriv (fun s => ingoingSphericalInverse F (Function.update x a s 1)
      (Function.update x a s 2) i j) (x a) =
      ingoingInversePartialTable F (x 1) (x 2) a i j := by
  have h22 : deriv (fun r : ℝ => 1 / r ^ 2) (x 1) = -(2 / x 1 ^ 3) := by
    rw [((hasDerivAt_const (x 1) (1 : ℝ)).fun_div
      (hasDerivAt_pow 2 (x 1)) (pow_ne_zero _ hr)).deriv]
    field_simp [hr] <;> ring
  have hrInv : deriv (fun r : ℝ => (r ^ 2)⁻¹) (x 1) = -(2 / x 1 ^ 3) := by
    simpa only [one_div] using h22
  have hθInv : deriv (fun θ : ℝ => (Real.sin θ ^ 2)⁻¹) (x 2) =
      -(2 * Real.cos (x 2) / Real.sin (x 2) ^ 3) := by
    have h := (((Real.hasDerivAt_sin (x 2)).fun_pow 2).inv (pow_ne_zero _ hθ)).deriv
    change deriv (fun θ => (Real.sin θ ^ 2)⁻¹) (x 2) = _ at h
    rw [h]
    field_simp [hθ] <;> ring
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [ingoingSphericalInverse, Function.update,
      ingoingInversePartialTable, hrInv, hθInv] <;>
    field_simp [hr, hθ] <;> ring

private theorem ingoing_weight_update_derivative (x : Chart) (a : Fin 4) :
    deriv (fun s => (Function.update x a s 1) ^ 2 *
      Real.sin (Function.update x a s 2)) (x a) =
      (![0, 2 * x 1 * Real.sin (x 2), x 1 ^ 2 * Real.cos (x 2), 0] : Fin 4 → ℝ) a := by
  have hr := ((hasDerivAt_pow 2 (x 1)).mul_const (Real.sin (x 2))).deriv
  have hθ := ((Real.hasDerivAt_sin (x 2)).const_mul (x 1 ^ 2)).deriv
  fin_cases a <;> simp (config := {decide := true}) [Function.update, hr, hθ]

set_option maxHeartbeats 1200000 in
/-- The two Palatini compatibility identities for an arbitrary family
with the selected ingoing spherical base. They concern only s=0 and
place no symmetry restrictions on the perturbation away from s=0. -/
theorem ingoing_background_variational_compatibility
    (g : MetricPath) (F : ℝ → ℝ) (x : Chart)
    (hBase : g 0 = ingoingChartMetric F)
    (hr : 0 < x 1) (hθ : 0 < Real.sin (x 2)) (hF : DifferentiableAt ℝ F (x 1)) :
    inverseMetricCompatiblePartial (metricConnection g 0 x) (metricInverse g 0 x)
      (inversePartial g x) ∧
    densityCompatiblePartial (metricConnection g 0 x) (metricWeight g 0 x)
      (weightPartial g x) := by
  have hInv (y : Chart) (hy₁ : 0 < y 1) (hy₂ : 0 < Real.sin (y 2)) :
      metricInverse g 0 y = ingoingSphericalInverse F (y 1) (y 2) := by
    unfold metricInverse
    rw [hBase]
    exact ingoing_inverse_exact F (y 1) (y 2) hy₁.ne' hy₂.ne'
  have hW (y : Chart) (hy₁ : 0 < y 1) (hy₂ : 0 < Real.sin (y 2)) :
      metricWeight g 0 y = y 1 ^ 2 * Real.sin (y 2) := by
    unfold metricWeight
    rw [hBase]
    exact ingoing_weight_exact F (y 1) (y 2) hy₁ hy₂
  have hΓ : metricConnection g 0 x = ingoingChristoffelTable F (x 1) (x 2) := by
    rw [ingoing_metricConnection_eq g F x hBase hr.ne' hθ.ne',
      ingoingChartChristoffel_eq_table F x hr.ne' hθ.ne' hF]
  have hdB (a i j : Fin 4) : inversePartial g x a i j =
      ingoingInversePartialTable F (x 1) (x 2) a i j := by
    unfold inversePartial
    rw [spatialLineDeriv_eq_update, ← ingoing_inverse_update_derivative F x hr.ne' hθ.ne']
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [update_line_regular x a hr hθ] with s hs
    exact congrArg (fun M : MetricMatrix => M i j) (hInv _ hs.1 hs.2)
  have hdW (a : Fin 4) : weightPartial g x a =
      (![0, 2 * x 1 * Real.sin (x 2), x 1 ^ 2 * Real.cos (x 2), 0] : Fin 4 → ℝ) a := by
    unfold weightPartial
    rw [spatialLineDeriv_eq_update, ← ingoing_weight_update_derivative x a]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [update_line_regular x a hr hθ] with s hs
    exact hW _ hs.1 hs.2
  constructor
  · intro a i j
    rw [hdB, hΓ, hInv x hr hθ]
    fin_cases a <;> fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [sumFin4, ingoingChristoffelTable,
        ingoingSphericalInverse, ingoingInversePartialTable] <;>
      field_simp [hr.ne', hθ.ne'] <;> ring
  · intro a
    rw [hdW, hΓ, hW x hr hθ]
    fin_cases a <;>
      simp (config := {decide := true}) [sumFin4, ingoingChristoffelTable] <;>
      field_simp [hr.ne', hθ.ne'] <;> ring

end IngoingVariationalCompatibility

end IngoingChart

/--
**Schwarzschild Bekenstein-Hawking entropy: `S_BH = 4π M²`.**
Substantive named identity tying the `schwarzschildBHEntropy`
definition (= A/4) to the closed form 4πM². Bekenstein 1973,
Hawking 1976. Cross-bridge to Phase 6a Wave 5 BH thermodynamics
regime classifier and Phase 6a Wave 3 BH entropy from MTC counting.
-/
theorem schwarzschild_S_BH_eq_4pi_M_sq (M : ℝ) :
    schwarzschildBHEntropy M = 4 * Real.pi * M ^ 2 := by
  unfold schwarzschildBHEntropy schwarzschildArea schwarzschildHorizonRadius
  ring

/-! ## §5 — Module summary -/

/--
**Phase 6f Wave 4 module summary marker.** This module ships the
catalogue of canonical exact solutions of the Einstein field
equations as algebraic-level specializations of the Phase
6f.1+6f.2+6f.3 infrastructure plus BH thermodynamics
cross-bridges to Phase 6a Wave 5:

1. **Minkowski (K = 0, Λ = 0):** `minkowski_lambda_zero_iff_K_zero`
   (substantive uniqueness biconditional).
2. **de Sitter (K > 0):** `deSitter_scalar_eq` /
   `deSitter_einsteinTensor_eq` / `deSitter_lambda_vacuum_iff` /
   `deSitter_lambda_eq_three_H_squared` /
   `deSitter_T_H_eq_kappa_over_2pi` (5 theorems; the last is
   the Gibbons-Hawking 1977 dS Hawking-Unruh relation, consuming
   the named defs `deSitterHubbleRadius` / `deSitterKappa` /
   `deSitterHawkingTemp`). The `deSitter_Ricci_eq` rename was
   CUT in the post-Phase-6f-closure strengthening pass — pure
   forwarding to `constantSectional_minkowski_Ricci_eq`, no
   substantive content beyond the rename. Downstream consumers
   call the 6f.1 generic theorem directly.
3. **Anti-de Sitter (K < 0):** `ads_lambda_eq_neg_three_over_ell_sq`
   (1 theorem; AdS-radius anchor).
4. **Schwarzschild (Kerr-Schild form):**
   `schwarzschild_horizon_iff` (1 biconditional) /
   `schwarzschild_g_tt_outside_horizon_neg` /
   `schwarzschild_g_tt_at_horizon_zero` /
   `schwarzschild_g_tt_inside_horizon_pos` (3 signature theorems
   characterizing the t-direction across the horizon) /
   `schwarzschild_kappa_times_4M` /
   `schwarzschild_T_H_times_M` /
   `schwarzschild_T_H_eq_kappa_over_2pi` /
   `schwarzschild_area_eq_16pi_M_sq` /
   `schwarzschild_S_BH_eq_4pi_M_sq` (5 BH-thermo cross-bridges
   consuming the named defs `schwarzschildHorizonRadius` /
   `schwarzschildKappa` / `schwarzschildHawkingTemp` /
   `schwarzschildArea` / `schwarzschildBHEntropy`).

Total: **16 substantive theorems + 1 marker**, 0 sorry, 0 new
axioms (verified `propext, Classical.choice, Quot.sound` only).

**Strengthening discipline metric: 2 retroactive cuts** (post-
Phase-6f-closure audit added cut of `deSitter_Ricci_eq` rename)
(`schwarzschild_kappa_eq`, a pure `rfl` definitional unfold; the
substantive content κ = 1/(4M) lives in the `schwarzschildKappa`
def itself, consumed by the substantive `schwarzschild_kappa_times_4M`
M-independent product). Trend: 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4,
6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3, 6c.2=2, 6e.1=2, 6e.2=1, 6e.3=2,
6e.4=3, 6e.5=0, 6e.6=2, 6b.2=0, 6f.1=5 (regression), 6f.2=0,
6f.3=0 (Lean-side; backfill added 11 helpers + 38 tests + 1 fig
post-hoc), **6f.4=1** (small regression vs 6f.2/6e.5/6b.2 baseline,
caught by the 6f.1-carry-forward question + ruthless post-wave
audit; the named-quantity definition pattern made most of the
P3-trivial-discharge content into substantive named-API rather
than rfl-rename theorems, so the cut surface area was small).

**Anti-pattern audit (preemptive-strengthening discipline +
6f.1 carry-forward):**
- P1 (∃-absorption): no — all witnesses concrete.
- P2 (bundle redundancy): the dS pack of 4 (Ric, scalar, Einstein,
  Λ-iff) ships as **named API specializations** (each consumed by
  distinct downstream contexts), not redundant restatements.
- P3 (trivial-multiplication-as-physics): the 5 Schwarzschild
  thermodynamic identities (κ·4M = 1, T_H·M = 1/(8π),
  2π·T_H = κ, A = 16πM², S_BH = A/4) are `field_simp` + `ring`
  discharges but each carries **load-bearing quantitative content**
  (mass-independent invariants, universal Hawking-Unruh relation,
  Bekenstein-Hawking entropy formula).
- P4 (vacuous axioms): no new axioms.
- P5 (structural-tautology falsifiers): the three biconditionals
  (`minkowski_lambda_zero_iff_K_zero`, `deSitter_lambda_vacuum_iff`,
  `schwarzschild_horizon_iff`) each have non-trivial both-direction
  content. The `ads_lambda_vacuum_iff` rename was CUT
  (rename-only of `deSitter_lambda_vacuum_iff`); the AdS content
  ships only via the substantive `ads_lambda_eq_neg_three_over_ell_sq`
  quantitative consumer.
- P6 (cross-module bridge integrity): every dS/AdS theorem calls
  6f.1 (`constantSectional_minkowski_Ricci_eq`) or 6f.2
  (`constantSectional_scalarOf_eq`,
  `constantSectional_einsteinTensor_eq`,
  `constantSectional_lambda_vacuum_iff`,
  `minkowski_dim_contraction`) by name. Every Schwarzschild
  thermodynamic identity is a named cross-bridge to Phase 6a
  Wave 5.
- 6f.1-carry-forward: no zero-witness-trivial-plumbing. The
  Schwarzschild vacuum-Ricci tracked Prop was REJECTED at first-
  pass (would be vacuous tracked Prop with `True` body); the
  6g.1+ Lorentzian-metric + Ricci-from-connection infrastructure
  will ship the substantive vacuum-EFE verification.

**Cuts at first-pass (6f.2 best-practice, applied prospectively):**
- `ads_lambda_vacuum_iff` — pure rename of dS biconditional (CUT).
- `H_SchwarzschildRicciVanishesOutside` — vacuous tracked Prop
  (CUT; defer until 6g.1+ Lorentzian + connection-Ricci land).
- `schwarzschild_T_H_eq_inverse_eight_pi_M` — P3 trivial positivity
  (CUT; substantive content captured by `schwarzschild_T_H_times_M`).
-/
theorem _phase6f_w4_module_summary_marker : True := trivial

end SKEFTHawking.ExactSolutions
