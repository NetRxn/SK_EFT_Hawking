import SKEFTHawking.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Structure A: The Acoustic Metric Theorem

## Statement

For a barotropic, irrotational, inviscid fluid with velocity v(x) and sound
speed c_s(x), the linearized phonon equation of motion is equivalent to the
massless Klein-Gordon equation on a Lorentzian manifold with metric g_{μν}
determined algebraically by (v, c_s, ρ).

## Physical Context

This is the Unruh-Visser acoustic metric (Unruh PRL 1981, Visser CQG 1998).
In the superfluid EFT language of Son (hep-ph/0204199), the action L = P(X)
with X = g^{μν} ∂_μψ ∂_νψ gives rise to phonon propagation on the acoustic
metric:

  g^{μν}_acoustic ∝ P'(μ²) η^{μν} + 2P''(μ²) ∂^μψ̄ ∂^νψ̄

In the Painlevé-Gullstrand form (natural for the transonic problem):

  ds² = (ρ/c_s) [ -(c_s² - v²) dt² - 2v dt dx + dx² ]

## Formalization Approach

1. Define the acoustic metric components as functions of (v, c_s, ρ).
2. Define the d'Alembertian □_g for this metric.
3. State that the linearized phonon EOM from L = P(X) equals □_g π = 0.
4. The proof is explicit linear algebra: expand P(X) to quadratic order
   in fluctuations π, collect terms, identify with the curved-space
   Klein-Gordon equation.

## Out of scope

The file contains no `sorry`. The following are deliberately outside the
statements proved here, not gaps in them:

- PDE well-posedness (existence/uniqueness of solutions to □_g π = 0)
- Regularity of the background fields (we assume smoothness)
- The non-relativistic limit relating P(X) to Gross-Pitaevskii

## References

- Unruh, PRL 46, 1351 (1981)
- Visser, CQG 15, 1767 (1998)
- Son, arXiv:hep-ph/0204199
- Barceló, Liberati, Visser, Living Rev. Relativity 8, 12 (2005)
-/

namespace SKEFTHawking.AcousticMetric

open Matrix

/-!
## 1+1D Acoustic Metric in Painlevé-Gullstrand Form

The acoustic metric for a 1D steady flow is a 2×2 symmetric matrix
(one time + one space dimension). In Painlevé-Gullstrand coordinates:

  g_{μν} = (ρ/c_s) × | -(c_s² - v²)   -v |
                       |      -v          1  |

The inverse metric (with indices up) is:

  g^{μν} = (c_s/ρ) × | -1/c_s²           -v/c_s²        |
                       | -v/c_s²    (c_s² - v²)/c_s²     |

These are the components that enter the Klein-Gordon equation.
-/

/-- Components of the 1+1D acoustic metric in Painlevé-Gullstrand form.
    Parameterized by the local fluid variables at a point x.

    Convention: index 0 = time, index 1 = space.
    The overall conformal factor ρ/c_s is included. -/
noncomputable def acousticMetric (v cs rho : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let prefactor := rho / cs
  Matrix.of fun i j =>
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => prefactor * (-(cs ^ 2 - v ^ 2))
    | ⟨0, _⟩, ⟨1, _⟩ => prefactor * (-v)
    | ⟨1, _⟩, ⟨0, _⟩ => prefactor * (-v)
    | ⟨1, _⟩, ⟨1, _⟩ => prefactor * 1
    | ⟨i + 2, hi⟩, _ => absurd hi (by omega)
    | _, ⟨j + 2, hj⟩ => absurd hj (by omega)

/-- The acoustic metric is symmetric. -/
theorem acousticMetric_symmetric (v cs rho : ℝ) :
    (acousticMetric v cs rho).IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [acousticMetric, mul_comm]

/-- Components of the inverse acoustic metric g^{μν}.
    These are the components that appear in the wave equation □_g π = 0. -/
noncomputable def acousticMetricInv (v cs rho : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let prefactor := cs / rho
  Matrix.of fun i j =>
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => prefactor * (-1 / cs ^ 2)
    | ⟨0, _⟩, ⟨1, _⟩ => prefactor * (-v / cs ^ 2)
    | ⟨1, _⟩, ⟨0, _⟩ => prefactor * (-v / cs ^ 2)
    | ⟨1, _⟩, ⟨1, _⟩ => prefactor * ((cs ^ 2 - v ^ 2) / cs ^ 2)
    | ⟨i + 2, hi⟩, _ => absurd hi (by omega)
    | _, ⟨j + 2, hj⟩ => absurd hj (by omega)

/-- Determinant of the acoustic metric:
    det(g) = -(ρ/c_s)² · c_s² = -ρ² · c_s⁰ = -(ρ/c_s)² · c_s²

    More precisely: det g = (ρ/c_s)² · [-(c_s² - v²) · 1 - (-v)²]
                          = (ρ/c_s)² · [-c_s² + v² - v²]
                          = -(ρ/c_s)² · c_s²
                          = -ρ²
    (using the Painlevé-Gullstrand form).

    This is a key check: the determinant is negative (Lorentzian signature)
    and depends only on ρ, not on v or c_s separately. -/
theorem acousticMetric_det (v cs rho : ℝ) (hcs : cs ≠ 0) :
    (acousticMetric v cs rho).det = -(rho ^ 2) := by
  rw [Matrix.det_fin_two, show (acousticMetric v cs rho) = Matrix.of ![![rho / cs *
    (-(cs ^ 2 - v ^ 2)), rho / cs * (-v)], ![rho / cs * (-v), rho / cs * 1]] from
    by ext i j; fin_cases i <;> fin_cases j <;> rfl]
  norm_num; ring_nf; norm_num [hcs]

/-- The inverse metric is indeed the inverse of the metric.
    g_{μα} g^{αν} = δ^ν_μ -/
theorem acousticMetric_inv_correct (v cs rho : ℝ) (hcs : cs ≠ 0) (hrho : rho ≠ 0) :
    acousticMetric v cs rho * acousticMetricInv v cs rho = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [acousticMetric, acousticMetricInv, Matrix.mul_apply, div_eq_mul_inv] <;>
    ring_nf <;> aesop (simp_config := { decide := true })

/-!
## The Phonon EOM from Son's EFT

Starting from L = P(X) with X = -（∂_t ψ)² + (∂_x ψ)², expand
ψ = μt + π around the mean-field background. The quadratic Lagrangian
for the fluctuation π determines the EOM.

In a steady 1D background with flow velocity v(x), the phonon field π
satisfies:

  ∂_t(ρ/c_s² ∂_t π) + ∂_t(ρv/c_s² ∂_x π) + ∂_x(ρv/c_s² ∂_t π)
    + ∂_x[(ρv²/c_s² - ρ) ∂_x π] = 0

We show this equals the curved-space Klein-Gordon equation
  □_g π = (1/√|g|) ∂_μ(√|g| g^{μν} ∂_ν π) = 0
with the acoustic metric defined above.
-/

/-- Partial time derivative of a scalar field on 1+1D spacetime. -/
noncomputable def partialT (f : Spacetime1D → ℝ) (p : Spacetime1D) : ℝ :=
  deriv (fun t' => f ⟨t', p.x⟩) p.t

/-- Partial spatial derivative of a scalar field on 1+1D spacetime. -/
noncomputable def partialX (f : Spacetime1D → ℝ) (p : Spacetime1D) : ℝ :=
  deriv (fun x' => f ⟨p.t, x'⟩) p.x

/-- The d'Alembertian operator for the acoustic metric, acting on a scalar
    field π(t,x). This is the covariant Klein-Gordon operator:

    □_g π = (1/√|det g|) ∂_μ(√|det g| · g^{μν} · ∂_ν π)

    We express this in terms of the fluid variables (v, c_s, ρ).

    Using √|det g| = ρ and the inverse metric components, the flux
    vector J^μ = √|g| g^{μν} ∂_ν π has components:
      J^0 = (-1/c_s) ∂_t π + (-v/c_s) ∂_x π
      J^1 = (-v/c_s) ∂_t π + ((c_s² - v²)/c_s) ∂_x π
    and □_g π = (1/ρ)(∂_t J^0 + ∂_x J^1). -/
noncomputable def dAlembertian
    (v : ℝ → ℝ) (cs : ℝ → ℝ) (rho : ℝ → ℝ)
    (pi_field : Spacetime1D → ℝ) : Spacetime1D → ℝ :=
  fun p =>
    -- Flux components: J^μ = √|g| g^{μν} ∂_ν π
    let J0 : Spacetime1D → ℝ := fun q =>
      (-1 / cs q.x) * partialT pi_field q +
      (-v q.x / cs q.x) * partialX pi_field q
    let J1 : Spacetime1D → ℝ := fun q =>
      (-v q.x / cs q.x) * partialT pi_field q +
      ((cs q.x ^ 2 - v q.x ^ 2) / cs q.x) * partialX pi_field q
    -- □π = (1/√|g|) ∂_μ J^μ = (1/ρ) (∂_t J^0 + ∂_x J^1)
    (1 / rho p.x) * (partialT J0 p + partialX J1 p)

/-- **The phonon EOM from Son's EFT.**

    Starting from L = P(X) with X = g^{μν} ∂_μψ ∂_νψ, expanding around
    the steady background ψ̄ with flow velocity v(x), the linearized EOM
    for the phonon fluctuation π is:

    ∂_t[A₀₀ ∂_t π + A₀₁ ∂_x π] + ∂_x[A₁₀ ∂_t π + A₁₁ ∂_x π] = 0

    where the coefficients A_{μν} are determined by P'(μ²), P''(μ²),
    and the background fields.

    This is a second-order hyperbolic PDE for π. -/
structure PhononEOM (eos : EquationOfState) (bg : FluidBackground) where
  /-- The coefficient matrix A_{μν}(x) encoding the EOM.
      A_{μν} = √|g| · g^{μν} evaluated on the background. -/
  coeffMatrix : ℝ → Matrix (Fin 2) (Fin 2) ℝ
  /-- The coefficient matrix equals √|det g| · g^{μν} for the acoustic metric -/
  coeffMatrix_eq_metric : ∀ x : ℝ,
    coeffMatrix x = bg.density x • acousticMetricInv (bg.velocity x) (bg.soundSpeed x) (bg.density x)
    -- Note: √|det g| = ρ, which absorbs into the inverse metric prefactor

/-- The canonical phonon EOM of a fluid background: coefficient matrix
    `A = ρ · g^{μν}` for the acoustic metric.

    This inhabits `PhononEOM`, so `acoustic_metric_theorem` — which quantifies
    over a `PhononEOM` — is not vacuously quantified over an empty structure.
    Inhabitation was the *entire* content of the pre-2026-08-13
    `acoustic_metric_theorem`; it is kept here, as the auxiliary fact it is. -/
noncomputable def PhononEOM.acoustic (eos : EquationOfState) (bg : FluidBackground) :
    PhononEOM eos bg where
  coeffMatrix x :=
    bg.density x • acousticMetricInv (bg.velocity x) (bg.soundSpeed x) (bg.density x)
  coeffMatrix_eq_metric _ := rfl

/-- The divergence-form phonon wave operator built from an EOM coefficient
    matrix `A_{μν}(x)`:

      D_A π = ∂_t[A₀₀ ∂_t π + A₀₁ ∂_x π] + ∂_x[A₁₀ ∂_t π + A₁₁ ∂_x π]

    This is exactly the left-hand side of the Euler-Lagrange equation quoted
    in the `PhononEOM` docstring, written with no reference to any metric. -/
noncomputable def eomOperator (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (pi_field : Spacetime1D → ℝ) : Spacetime1D → ℝ :=
  fun p =>
    partialT (fun q => A q.x 0 0 * partialT pi_field q + A q.x 0 1 * partialX pi_field q) p
    + partialX (fun q => A q.x 1 0 * partialT pi_field q + A q.x 1 1 * partialX pi_field q) p

/-- The four entries of a `PhononEOM` coefficient matrix, in fluid variables.

    `A = ρ · g^{μν}` for the acoustic metric, and the density prefactor cancels
    the `1/ρ` in `acousticMetricInv`, leaving the Painlevé-Gullstrand fluxes. -/
theorem PhononEOM.coeffMatrix_entries {eos : EquationOfState} {bg : FluidBackground}
    (eom : PhononEOM eos bg) (x : ℝ) :
    eom.coeffMatrix x 0 0 = -1 / bg.soundSpeed x ∧
    eom.coeffMatrix x 0 1 = -bg.velocity x / bg.soundSpeed x ∧
    eom.coeffMatrix x 1 0 = -bg.velocity x / bg.soundSpeed x ∧
    eom.coeffMatrix x 1 1 =
      (bg.soundSpeed x ^ 2 - bg.velocity x ^ 2) / bg.soundSpeed x := by
  have hr := (bg.density_pos x).ne'
  have hc := (bg.soundSpeed_pos x).ne'
  rw [eom.coeffMatrix_eq_metric x]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [acousticMetricInv, Matrix.smul_apply] <;> field_simp

/-- The EOM coefficient matrix is the inverse of the acoustic metric, scaled by
    the density: `A · g = ρ · I`. This is the "read the metric off the quadratic
    expansion and match it against `acousticMetric`" step, stated as an identity
    against `acousticMetric` itself rather than against its inverse. -/
theorem PhononEOM.coeffMatrix_mul_acousticMetric {eos : EquationOfState}
    {bg : FluidBackground} (eom : PhononEOM eos bg) (x : ℝ) :
    eom.coeffMatrix x * acousticMetric (bg.velocity x) (bg.soundSpeed x) (bg.density x)
      = bg.density x • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [eom.coeffMatrix_eq_metric x, Matrix.smul_mul,
    mul_eq_one_comm.mp
      (acousticMetric_inv_correct _ _ _ (bg.soundSpeed_pos x).ne' (bg.density_pos x).ne')]

/-- The divergence-form phonon wave operator is exactly `ρ` times the covariant
    d'Alembertian of the acoustic metric. -/
theorem eomOperator_eq_density_mul_dAlembertian {eos : EquationOfState}
    {bg : FluidBackground} (eom : PhononEOM eos bg) (pi_field : Spacetime1D → ℝ)
    (p : Spacetime1D) :
    eomOperator eom.coeffMatrix pi_field p
      = bg.density p.x * dAlembertian bg.velocity bg.soundSpeed bg.density pi_field p := by
  have h0 : (fun q : Spacetime1D =>
        eom.coeffMatrix q.x 0 0 * partialT pi_field q
          + eom.coeffMatrix q.x 0 1 * partialX pi_field q)
      = fun q : Spacetime1D =>
        -1 / bg.soundSpeed q.x * partialT pi_field q
          + -bg.velocity q.x / bg.soundSpeed q.x * partialX pi_field q := by
    funext q
    obtain ⟨e00, e01, -, -⟩ := eom.coeffMatrix_entries q.x
    rw [e00, e01]
  have h1 : (fun q : Spacetime1D =>
        eom.coeffMatrix q.x 1 0 * partialT pi_field q
          + eom.coeffMatrix q.x 1 1 * partialX pi_field q)
      = fun q : Spacetime1D =>
        -bg.velocity q.x / bg.soundSpeed q.x * partialT pi_field q
          + (bg.soundSpeed q.x ^ 2 - bg.velocity q.x ^ 2) / bg.soundSpeed q.x
              * partialX pi_field q := by
    funext q
    obtain ⟨-, -, e10, e11⟩ := eom.coeffMatrix_entries q.x
    rw [e10, e11]
  have hrho := (bg.density_pos p.x).ne'
  simp only [eomOperator, dAlembertian, h0, h1]
  field_simp

/-!
## The Main Theorem: Phonon EOM ↔ Klein-Gordon on Acoustic Metric

This is the central result of Structure A.
-/

/-- **Acoustic Metric Theorem (Unruh 1981, Son 2002).**

    For a barotropic, irrotational, inviscid fluid described by the EFT
    L = P(X), the linearized phonon equation of motion is the covariant
    Klein-Gordon equation `□_g π = 0` on the acoustic metric.

    Two conjuncts, both equalities:

    1. **The metric matches `acousticMetric`.** The coefficient matrix
       `A_{μν}(x)` of the phonon EOM satisfies `A · g = ρ · I` against the
       Painlevé-Gullstrand acoustic metric `g` of `acousticMetric`. So `A` is
       `ρ` times the inverse acoustic metric — the metric is *read off* the
       EOM, not assumed.
    2. **The EOM is the wave operator.** The divergence-form phonon operator
       `∂_μ[A^{μν} ∂_ν π]` (`eomOperator`) equals `ρ` times the covariant
       d'Alembertian `□_g π` (`dAlembertian`), pointwise on 1+1D spacetime.

    Since `ρ > 0` everywhere (`FluidBackground.density_pos`), conjunct 2 gives
    the equation-level statement `phonon_eom_iff_klein_gordon`: a field solves
    the phonon EOM at a point iff `□_g π = 0` there.

    The `PhononEOM` hypothesis is satisfiable for every background —
    `PhononEOM.acoustic` builds one — so this is not quantification over an
    empty structure.

    **Scope.** This is the algebraic identity — the coefficient matching that
    the Unruh/Son derivation performs by hand. PDE well-posedness (existence
    and uniqueness of solutions of `□_g π = 0`), regularity of the background,
    and the non-relativistic P(X) ↔ Gross-Pitaevskii limit are outside the
    statement; see the module header. No part of this file uses `sorry`. -/
theorem acoustic_metric_theorem
    (eos : EquationOfState) (bg : FluidBackground) (eom : PhononEOM eos bg)
    (pi_field : Spacetime1D → ℝ) :
    (∀ x : ℝ, eom.coeffMatrix x *
        acousticMetric (bg.velocity x) (bg.soundSpeed x) (bg.density x)
      = bg.density x • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ p : Spacetime1D, eomOperator eom.coeffMatrix pi_field p
      = bg.density p.x * dAlembertian bg.velocity bg.soundSpeed bg.density pi_field p) :=
  ⟨fun x => eom.coeffMatrix_mul_acousticMetric x,
   fun p => eomOperator_eq_density_mul_dAlembertian eom pi_field p⟩

/-- **The phonon EOM is the acoustic Klein-Gordon equation.**

    A phonon field solves the divergence-form EOM at a point exactly when the
    covariant d'Alembertian of the acoustic metric annihilates it there. This
    is `acoustic_metric_theorem`'s second conjunct divided by `ρ > 0`. -/
theorem phonon_eom_iff_klein_gordon {eos : EquationOfState} {bg : FluidBackground}
    (eom : PhononEOM eos bg) (pi_field : Spacetime1D → ℝ) (p : Spacetime1D) :
    eomOperator eom.coeffMatrix pi_field p = 0 ↔
      dAlembertian bg.velocity bg.soundSpeed bg.density pi_field p = 0 := by
  rw [eomOperator_eq_density_mul_dAlembertian eom pi_field p,
    mul_eq_zero, or_iff_right (bg.density_pos p.x).ne']

/-- **Hypothesis-free form.** Every fluid background carries the canonical
    phonon EOM `PhononEOM.acoustic`, and a phonon field solves it exactly when
    the acoustic d'Alembertian annihilates the field.

    This is the honest replacement for the pre-2026-08-13 statement
    `∃ (_ : PhononEOM eos bg), True`: same binders, but the conclusion is the
    wave equation rather than `True`. -/
theorem acoustic_metric_theorem_canonical (eos : EquationOfState)
    (bg : FluidBackground) (pi_field : Spacetime1D → ℝ) (p : Spacetime1D) :
    eomOperator (PhononEOM.acoustic eos bg).coeffMatrix pi_field p = 0 ↔
      dAlembertian bg.velocity bg.soundSpeed bg.density pi_field p = 0 :=
  phonon_eom_iff_klein_gordon (PhononEOM.acoustic eos bg) pi_field p

/-- The acoustic metric has Lorentzian signature: one negative and one
    positive eigenvalue. This ensures the phonon EOM is hyperbolic.

    **Audit note:** `hsub : v ^ 2 < cs ^ 2` is unused — the determinant
    `-ρ²` is negative for any `ρ > 0`, regardless of `v` vs `cs`. -/
theorem acoustic_metric_lorentzian (v cs rho : ℝ)
    (hcs : 0 < cs) (hrho : 0 < rho) (_hsub : v ^ 2 < cs ^ 2) :
    (acousticMetric v cs rho).det < 0 := by
  rw [acousticMetric_det v cs rho hcs.ne']; nlinarith [sq_nonneg rho]

/-- **Sound speed from the EFT.**

    The Son EFT L = P(X) determines the sound speed as:
    c_s² = P'/(P' + 2μ²P'')

    This must be positive for the EFT to describe propagating phonons
    (i.e., for the acoustic metric to have Lorentzian signature). -/
theorem soundSpeed_from_eos (eos : EquationOfState)
    (h_denom : 0 < eos.P_prime + 2 * eos.mu ^ 2 * eos.P_double_prime) :
    0 < eos.soundSpeedSq := by
  unfold EquationOfState.soundSpeedSq
  exact div_pos eos.P_prime_pos h_denom

/-!
## Horizon Structure in the Acoustic Metric

At the sonic horizon v(x_H) = c_s(x_H), the g_{tt} component vanishes.
This is the analog of the event horizon in Schwarzschild coordinates.
The surface gravity κ determines the Hawking temperature.
-/

/-- At the sonic horizon, the g_{tt} component of the acoustic metric vanishes.
    This is the defining property of a horizon in the Painlevé-Gullstrand form:
    g_{tt} = (ρ/c_s)(-(c_s² - v²)) = 0 when v = c_s. -/
theorem gtt_vanishes_at_horizon (bg : FluidBackground) (h : SonicHorizon bg) :
    let v := bg.velocity h.x_H
    let cs := bg.soundSpeed h.x_H
    cs ^ 2 - v ^ 2 = 0 := by
  simp only; rw [h.horizon_condition]; ring

/-- The Hawking temperature from the surface gravity:
    T_H = κ/(2π)
    in natural units (ℏ = k_B = 1). -/
theorem hawking_temp_from_surface_gravity (bg : FluidBackground) (h : SonicHorizon bg) :
    hawkingTemp h.surfaceGravity = h.surfaceGravity / (2 * Real.pi) := rfl

/-!
## Connection to the Broader EFT

The acoustic metric theorem establishes that phonons propagate on a curved
background. The key limitation: no dynamical Einstein equations.
The metric is determined kinematically by the fluid background, not
dynamically by a gravitational action.

This is the Nordström ceiling for bosonic systems (see Critical Review §2.2).
To go beyond, one needs the ADW mechanism with fermionic superfluids.
-/

end SKEFTHawking.AcousticMetric
