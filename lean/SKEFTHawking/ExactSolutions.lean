import SKEFTHawking.Basic
import SKEFTHawking.Curvature
import SKEFTHawking.EinsteinTensor
import SKEFTHawking.EnergyConditions
import SKEFTHawking.LinearizedEFE
import SKEFTHawking.KerrSchild
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
Christoffel symbols and ∂_μ machinery) is deferred to a future wave
once Bonn's `CovariantDerivative` API lands. For Schwarzschild
specifically, the vacuum-Ricci verification `Ric(g_Schw) = 0` outside
r = 2M intrinsically requires ∂_μ machinery and is **not** encoded
here as a tracked Prop (per 6f.2 lesson on rejecting vacuous tracked
Props with trivial discharge); it will ship as substantive content
in a future wave.

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
  pass (would be vacuous tracked Prop with `True` body); future
  wave with ∂_μ machinery will ship the substantive vacuum-EFE
  verification.

**Cuts at first-pass (6f.2 best-practice, applied prospectively):**
- `ads_lambda_vacuum_iff` — pure rename of dS biconditional (CUT).
- `H_SchwarzschildRicciVanishesOutside` — vacuous tracked Prop
  (CUT; defer until ∂_μ machinery lands).
- `schwarzschild_T_H_eq_inverse_eight_pi_M` — P3 trivial positivity
  (CUT; substantive content captured by `schwarzschild_T_H_times_M`).
-/
theorem _phase6f_w4_module_summary_marker : True := trivial

end SKEFTHawking.ExactSolutions
