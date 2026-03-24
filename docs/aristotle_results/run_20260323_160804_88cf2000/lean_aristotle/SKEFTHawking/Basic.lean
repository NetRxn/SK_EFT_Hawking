import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.MetricSpace.Basic

/-!
# Basic Definitions for SK-EFT Hawking Formalization

Shared type definitions, notation, and foundational structures used across
all three formalization targets. These provide the mathematical vocabulary
for the acoustic metric, SK doubling, and Hawking universality theorems.

## Design Decisions

- We work over ℝ throughout (no complex analysis needed at the algebraic level).
- Spatial dimension is parametric but most results specialize to 1+1D.
- We separate the background fluid state (a record type) from the fluctuation
  fields (functions on spacetime) to match the physical EFT expansion.
- Transport coefficients are treated as abstract real parameters — their
  microscopic origin (Bogoliubov matching) is in the Python layer, not here.
-/

namespace SKEFTHawking

/-!
## Spacetime and Field Conventions

We work in 1+1 dimensions for the transonic problem.
Coordinates: (t, x) with t ∈ ℝ, x ∈ ℝ.
The sonic horizon is at x = x_H where v(x_H) = c_s(x_H).
-/

/-- A point in 1+1D spacetime. -/
structure Spacetime1D where
  t : ℝ
  x : ℝ
-- Note: `deriving Repr` removed because Real.instRepr is unsafe in Lean 4.28

/-- A scalar field on 1+1D spacetime. -/
def ScalarField := Spacetime1D → ℝ

/-!
## Fluid Background

The mean-field superfluid background is characterized by spatially varying
flow velocity v(x), sound speed c_s(x), and density ρ(x), subject to the
steady-state Euler and continuity equations.
-/

/-- Background fluid configuration for a steady 1D flow.
    All fields are functions of the spatial coordinate x only (steady state).

    **Physical interpretation:**
    - `velocity`: the superfluid flow velocity v(x)
    - `soundSpeed`: the local sound speed c_s(x) = √(∂P/∂ρ)
    - `density`: the number density ρ(x) = n(x)
    - `massCurrent`: the conserved mass current J = ρ·v (constant by continuity)

    The sonic horizon occurs where velocity(x_H) = soundSpeed(x_H). -/
structure FluidBackground where
  velocity : ℝ → ℝ
  soundSpeed : ℝ → ℝ
  density : ℝ → ℝ
  massCurrent : ℝ
  /-- Continuity equation: ρ(x) · v(x) = J for all x -/
  continuity : ∀ x : ℝ, density x * velocity x = massCurrent
  /-- Sound speed is strictly positive everywhere -/
  soundSpeed_pos : ∀ x : ℝ, 0 < soundSpeed x
  /-- Density is strictly positive everywhere -/
  density_pos : ∀ x : ℝ, 0 < density x

/-- A sonic horizon exists at position x_H where the flow speed equals the
    sound speed. The surface gravity κ characterizes the local gradient. -/
structure SonicHorizon (bg : FluidBackground) where
  /-- Position of the sonic horizon -/
  x_H : ℝ
  /-- At the horizon, flow speed equals sound speed -/
  horizon_condition : bg.velocity x_H = bg.soundSpeed x_H
  /-- Surface gravity: κ = |dv/dx + dc_s/dx| evaluated at x_H.
      This determines the Hawking temperature T_H = ℏκ/(2πk_B). -/
  surfaceGravity : ℝ
  /-- Surface gravity is strictly positive (non-degenerate horizon) -/
  surfaceGravity_pos : 0 < surfaceGravity

/-!
## Near-Horizon Expansion

Near the sonic horizon, the background fields admit a Taylor expansion
that determines the leading-order physics. This is where the Hawking
temperature emerges.
-/

/-- Near-horizon linear approximation to the fluid background.
    v(x) ≈ c_s + κ_v · (x - x_H),  c_s(x) ≈ c_s - κ_c · (x - x_H)
    where κ = κ_v + κ_c is the surface gravity.

    This parameterization follows Unruh (1981) and is the standard form
    used in all analog Hawking calculations. -/
structure NearHorizonExpansion (bg : FluidBackground) (h : SonicHorizon bg) where
  /-- Velocity gradient at horizon: dv/dx|_{x_H} -/
  kappa_v : ℝ
  /-- Sound speed gradient at horizon: -dc_s/dx|_{x_H} -/
  kappa_c : ℝ
  /-- Surface gravity decomposition: κ = κ_v + κ_c -/
  surfaceGravity_decomp : h.surfaceGravity = kappa_v + kappa_c

/-!
## EFT Parameters

The effective field theory is characterized by:
1. The equation of state P(X) where X = g^{μν} ∂_μψ ∂_νψ
2. Dissipative transport coefficients γ₁, γ₂ from the SK-EFT
3. The UV cutoff Λ (related to the healing length ξ)
-/

/-- The equation of state for a superfluid, parameterized as P(X).
    For a BEC: P(X) = (X - m²)²/(4λ) in the non-relativistic limit.

    We store the first three derivatives P, P', P'' at the background
    chemical potential μ, which fully determine the phonon sector. -/
structure EquationOfState where
  /-- Background chemical potential μ = √X₀ -/
  mu : ℝ
  mu_pos : 0 < mu
  /-- P(μ²): pressure at the background -/
  P_val : ℝ
  /-- P'(μ²): first derivative, determines the acoustic metric -/
  P_prime : ℝ
  P_prime_pos : 0 < P_prime
  /-- P''(μ²): second derivative, determines phonon interactions -/
  P_double_prime : ℝ

/-- Sound speed squared from the equation of state:
    c_s² = P'/(P' + 2μ²P'')
    This is Son's result for the superfluid EFT L = P(X). -/
noncomputable def EquationOfState.soundSpeedSq (eos : EquationOfState) : ℝ :=
  eos.P_prime / (eos.P_prime + 2 * eos.mu ^ 2 * eos.P_double_prime)

/-- Dissipative transport coefficients from the SK-EFT.

    These appear at first order in the derivative expansion beyond
    the ideal (Son) superfluid. They encode:
    - γ₁: bulk phonon damping (related to bulk viscosity)
    - γ₂: directional damping along the superfluid velocity

    Physical origin at T=0: Beliaev damping (phonon → two phonons),
    three-body losses, and quantum fluctuation effects.

    Reference: Endlich-Nicolis-Porto-Wang (PRD 2013) for first-order;
    Crossley-Glorioso-Liu (JHEP 2017) for full SK framework. -/
structure DissipativeCoeffs where
  gamma_1 : ℝ
  gamma_2 : ℝ
  /-- Positivity of imaginary part of SK action requires γ₁ ≥ 0 -/
  gamma_1_nonneg : 0 ≤ gamma_1
  /-- Positivity also requires γ₂ ≥ 0 -/
  gamma_2_nonneg : 0 ≤ gamma_2

/-- UV cutoff parameters for the EFT.

    The healing length ξ = ℏ/(m·c_s) sets the natural cutoff.
    The EFT is valid for k ≪ 1/ξ, i.e., ω ≪ c_s/ξ.

    The dimensionless parameter controlling corrections is
    κξ/c_s ∼ T_H/T_max, which is 0.02–0.04 in current BEC experiments
    (comfortably within the EFT regime). -/
structure UVCutoff where
  /-- Healing length ξ in natural units -/
  healingLength : ℝ
  healingLength_pos : 0 < healingLength
  /-- Cutoff momentum Λ ∼ 1/ξ -/
  cutoffMomentum : ℝ
  cutoffMomentum_pos : 0 < cutoffMomentum

/-!
## Hawking Temperature

The central physical quantity: T_H = ℏκ/(2π k_B), and its
dissipative correction T_eff = T_H(1 + δ_diss + δ_disp + δ_cross).
-/

/-- The standard (uncorrected) Hawking temperature in natural units (ℏ = k_B = 1):
    T_H = κ/(2π) -/
noncomputable def hawkingTemp (kappa : ℝ) : ℝ := kappa / (2 * Real.pi)

/-- The effective temperature with all corrections:
    T_eff = T_H · (1 + δ_diss + δ_disp + δ_cross)

    - δ_disp: dispersive correction ~ O((ξ/λ_H)²), known (Coutant-Parentani)
    - δ_diss: dissipative correction ~ O(γ/(κξ²)), NEW (this paper)
    - δ_cross: cross-term between dispersion and dissipation -/
structure EffectiveTemperature where
  T_H : ℝ
  T_H_pos : 0 < T_H
  delta_disp : ℝ
  delta_diss : ℝ
  delta_cross : ℝ
  /-- The full effective temperature -/
  T_eff : ℝ := T_H * (1 + delta_disp + delta_diss + delta_cross)

end SKEFTHawking
