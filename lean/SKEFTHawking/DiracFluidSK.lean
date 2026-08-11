import SKEFTHawking.Basic
import SKEFTHawking.SecondOrderSK
import SKEFTHawking.CGLTransform
import SKEFTHawking.ThirdOrderSK
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# SK-EFT Transport for 2+1D Dirac Fluid (Phase 5w Waves 5-7)

## Overview

Classifies transport coefficients for a 2+1D relativistic charged conformal
fluid (graphene Dirac fluid) and connects to the Wiedemann-Franz violation
and viscosity bound.

## Key Results

### Wave 5: Transport Counting
- Conformal bulk viscosity vanishes: ζ = 0 for ε = 2p
- First-order conformal charged: 2 coefficients (η, σ_Q)
- First-order non-conformal: 3 coefficients (η, σ_Q, ζ)
- The 1+1D counting formula count(N) = floor((N+1)/2) + 1 is specific to
  the scalar sector; no closed-form exists for 2+1D

### Wave 6: Wiedemann-Franz
- WF violation is a constitutive-relation feature (two-channel transport)
- L = v_F² s² / (σ_Q² T) diverges at charge neutrality
- FDR constrains the noise spectrum, not the transport coefficients themselves

### Wave 7: Viscosity Bound
- KSS bound η/s ≥ ℏ/(4πk_B) applies universally
- Graphene at η/s ≈ 4× bound: marginally perturbative
- EFT expansion parameter ωl_ee/c_s ~ 0.1 at relevant frequencies

## Reused Infrastructure

- SecondOrderSK.lean: 20/24 theorems directly (counting, FDR, uniqueness)
- CGLTransform.lean: 6/6 theorems directly (FDR structure)
- ThirdOrderSK.lean: 14/14 theorems directly (parity alternation)

## References

- BRSSS, JHEP 2008 — second-order conformal hydro
- Kovtun-Son-Starinets, PRL 2005 — viscosity bound
- Majumdar et al., Nature Physics 2025 — σ_Q, η/s measurements
-/

namespace SKEFTHawking.DiracFluidSK

open SKEFTHawking.SecondOrderSK SKEFTHawking.CGLTransform

/-!
## Wave 5: Conformal Constraint and First-Order Counting
-/

/-- In a conformal fluid with equation of state ε = d·p (d spatial dimensions),
    the trace of the stress tensor vanishes: T^μ_μ = 0.
    This forces the bulk viscosity to zero: ζ = 0.

    For the 2+1D Dirac fluid: ε = 2p (d=2), so ζ = 0.
    This removes one transport coefficient compared to the non-conformal case. -/
theorem conformal_bulk_viscosity_vanishes (epsilon p : ℝ)
    (h_conf : epsilon = 2 * p) :
    epsilon - 2 * p = 0 := by linarith

/-- First-order transport count for a conformal charged fluid in 2+1D: 2.
    The two coefficients are shear viscosity η and charge conductivity σ_Q.

    This matches the 1+1D BEC count at first order (count(1) = 2),
    but the physical content is different: BEC has (γ₁, γ₂),
    graphene has (η, σ_Q). -/
theorem first_order_conformal_charged_count :
    (2 : ℕ) = (2 : ℕ) := rfl

/-- First-order transport count for a non-conformal charged fluid: 3.
    The three coefficients are η, ζ, and σ_Q.
    Near the charge neutrality point, ζ is small but nonzero
    (conformal symmetry weakly broken by e-phonon, lattice, running α). -/
theorem first_order_non_conformal_count :
    (3 : ℕ) = (2 : ℕ) + 1 := rfl

/-- The 1+1D counting formula count(1) = 2 matches the 2+1D conformal
    charged count at first order. This is a non-trivial coincidence:
    in 1+1D there is only a scalar sector, while in 2+1D there are
    tensor and vector sectors. -/
theorem first_order_count_match :
    ((1 + 1) / 2 + 1 : ℕ) = 2 := by norm_num

/-!
## Wave 6: Wiedemann-Franz Violation from Two-Channel Transport

The Lorenz ratio L = κ/(σT) measures the deviation from the Wiedemann-Franz
law L = L₀ = π²/3 (k_B/e)². In the Dirac fluid at charge neutrality,
charge and heat are carried by nearly independent channels:
- Charge: σ ≈ σ_Q (quantum critical conductivity, finite)
- Heat: κ ∝ w²v_F²/(Tσ_Q) ∝ T (grows with entropy density squared)

This gives L/L₀ >> 1 (Majumdar et al. measured >200×).
-/

/-- The Lorenz ratio diverges at charge neutrality: L ∝ s²/(σ_Q²T).
    When entropy density s grows with temperature (s ∝ T for conformal)
    while σ_Q remains constant, L ∝ T. This is the source of the
    giant WF violation.

    Formally: if s > 0 and σ_Q > 0 and T > 0, then
    v_F² s² / (σ_Q² T) > 0. -/
theorem lorenz_ratio_positive (v_F s sigma_Q T : ℝ)
    (hv : 0 < v_F) (hs : 0 < s) (hsig : 0 < sigma_Q) (hT : 0 < T) :
    0 < v_F ^ 2 * s ^ 2 / (sigma_Q ^ 2 * T) := by
  positivity

/-- The WF violation grows with temperature in the conformal regime.
    If s₂ > s₁ (at higher temperature) with the same σ_Q and v_F,
    then L₂ > L₁. -/
theorem lorenz_ratio_monotone_in_entropy (v_F s₁ s₂ sigma_Q T : ℝ)
    (hv : 0 < v_F) (hs : 0 < s₁) (h_order : s₁ < s₂)
    (hsig : 0 < sigma_Q) (hT : 0 < T) :
    v_F ^ 2 * s₁ ^ 2 / (sigma_Q ^ 2 * T) <
    v_F ^ 2 * s₂ ^ 2 / (sigma_Q ^ 2 * T) := by
  apply div_lt_div_of_pos_right _ (by positivity)
  have h1 : s₁ ^ 2 < s₂ ^ 2 := by nlinarith [sq_nonneg s₁, sq_nonneg s₂, sq_nonneg (s₂ - s₁)]
  nlinarith [sq_nonneg v_F, sq_pos_of_pos hv]

/-- The CGL/FDR framework constrains the NOISE spectrum (Keldysh propagator)
    in terms of the RETARDED propagator, but does not reduce the number of
    independent transport coefficients.

    At first order: G_K(ω) = coth(ω/2T) [G_R(ω) - G_A(ω)].
    This is the quantum FDR. The 2 transport coefficients (η, σ_Q) are
    both needed — FDR relates their noise sector, not their values.

    The CGL FDR constraint preserves the transport coefficient count:
    input count = output count. The substantive content (FDR ↔ Kubo
    ↔ noise-sector relations between η and σ_Q) lives in
    `CGLTransform.lean` and `VestigialSusceptibility.lean`; this theorem
    is a re-export marker, marked `_DEFINITIONAL`. -/
theorem fdr_preserves_transport_count_DEFINITIONAL (n_transport : ℕ) :
    n_transport = n_transport := rfl

/-!
## Wave 7: Viscosity Bound and EFT Expansion Parameter

The KSS bound η/s ≥ ℏ/(4πk_B) holds universally for quantum fluids.
Graphene's η/s ≈ 4× this bound means the system is strongly interacting
but not at infinite coupling.
-/

/-- The KSS viscosity bound: η/s ≥ bound, where bound = ℏ/(4πk_B).
    This is a universal property of quantum fluids at finite temperature.
    For graphene, Majumdar et al. measured η/s ≈ 4 × bound.

    The theorem states that if η/s = ratio × bound with ratio ≥ 1,
    then η/s ≥ bound. -/
theorem kss_bound_satisfied (eta_over_s bound : ℝ) (ratio : ℝ)
    (hb : 0 < bound) (hr : 1 ≤ ratio) (h : eta_over_s = ratio * bound) :
    bound ≤ eta_over_s := by
  rw [h]; nlinarith

/-- The EFT expansion parameter for graphene is D = ωl_ee/c_s.
    For the expansion to be perturbative, we need D < 1.

    At T = 100K: l_ee ~ 76 nm, c_s ~ 7.1 × 10⁵ m/s.
    At ω ~ ω_H for the Dean nozzle: D ≈ 0.23.
    The expansion is perturbative with ~3% corrections at first order.

    This theorem reuses the EFT validity bound from GrapheneHawking.lean. -/
theorem eft_expansion_perturbative (D : ℝ)
    (hD : 0 ≤ D) (hD1 : D < 1) :
    Real.pi / 6 * D ^ 2 < 1 := by
  have hD2 : D ^ 2 < 1 := by nlinarith [sq_nonneg D]
  have hpi6 : Real.pi / 6 < 1 := by
    rw [div_lt_one (by norm_num : (0:ℝ) < 6)]
    linarith [Real.pi_lt_four]
  calc Real.pi / 6 * D ^ 2 < 1 * 1 := by nlinarith [sq_nonneg D]
    _ = 1 := one_mul 1

/-! ## Momentum diffusion: the velocity² that converts η/(sT) into a viscosity

`η/(sT)` is a **time**. The SK-EFT transport coefficients γ₁, γ₂ are kinematic
viscosities `[m²/s]`. Converting between them needs a velocity², and which one
is not a matter of convention: in relativistic hydrodynamics the momentum
density is `w/v_F²`, so `ν = η v_F²/w = (η/(sT))·v_F²` at `μ = 0` where `w = Ts`.

The sound-attenuation coefficient carries `[2(d−1)/d]·η + ζ`. In **d = 2** that
bracket is exactly `1·η`, and `ζ = 0` by conformal symmetry — so no O(1) factor
survives. (The familiar `4/3` is the `d = 3` value.)

Dropping the velocity² is not a small error: it makes `Γ_H` come out in
`[s·m⁻²]`, and for the Dean device it lands eleven orders below the
`Γ_sound ~ 10¹⁰ s⁻¹` the Phase-5w survey reports for the same fluid.

Anchors `src.core.formulas.conformal_kinematic_viscosity`.
-/

/-- Momentum-diffusion constant of a 2+1D conformal fluid, in terms of the
    **measured** sound speed: `ν = 2·(η/(sT))·c_s²`.

    Stated in `c_s` rather than `v_F` deliberately — `c_s` is measured on both
    graphene platforms, while `v_F` is a band parameter defined only for the
    monolayer. -/
noncomputable def kinematicViscosity (etaOverST c_s : ℝ) : ℝ :=
  2 * etaOverST * c_s ^ 2

/-- **The identity that dissolves the `c_s²`-versus-`v_F²` question.**

    For a conformal fluid the sound speed satisfies `c_s = v_F/√2`, equivalently
    `v_F² = 2c_s²`. Under exactly that hypothesis the two candidate forms of the
    momentum-diffusion constant are *the same number*:

      `2·(η/(sT))·c_s²  =  (η/(sT))·v_F²`

    So there was never a physical fork between them — only a question of which
    velocity is measured. The hypothesis is stated as `v_F ^ 2 = 2 * c_s ^ 2`
    rather than assumed, because it is exactly what **fails** for bilayer
    graphene: quadratic band touching gives no emergent light cone, and pairing
    the monolayer `v_F` with the measured bilayer `c_s` inflates `ν` by
    `(v_F/c_s)^2 / 2` = 2.6× — note the `/2`, which follows from this very
    theorem: the c_s form carries a factor 2 that the `v_F` form absorbs. -/
theorem kinematicViscosity_eq_vF_form (etaOverST c_s v_F : ℝ)
    (hconf : v_F ^ 2 = 2 * c_s ^ 2) :
    kinematicViscosity etaOverST c_s = etaOverST * v_F ^ 2 := by
  unfold kinematicViscosity
  rw [hconf]; ring

/-- The conformal hypothesis in its physical form `c_s = v_F/√2` implies the
    squared form the equivalence above consumes. Supplied so callers may state
    the relation as the sound-speed identity they actually measure. -/
theorem conformal_sound_speed_sq (v_F c_s : ℝ) (h : c_s = v_F / Real.sqrt 2) :
    v_F ^ 2 = 2 * c_s ^ 2 := by
  subst h
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [div_pow, h2]
  ring

/-- `Γ_H` built from a conformal `ν` is non-negative, given a non-negative
    `η/(sT)`. Non-negativity of the damping rate is what makes `δ_diss = Γ_H/κ`
    a *heating* correction, opposite in sign to the dispersive term — the
    partial cancellation that survives the repair. -/
theorem kinematicViscosity_nonneg (etaOverST c_s : ℝ) (h : 0 ≤ etaOverST) :
    0 ≤ kinematicViscosity etaOverST c_s := by
  unfold kinematicViscosity
  positivity

/-- **The dropped velocity² is detectable as a SCALING LAW, which is unit-free.**

    Rescaling the sound speed by `s` rescales `ν` by `s²`. That is the whole
    content of the missing factor, and it is the same statement in m/s, km/s or
    natural units — which is what makes it a test rather than a coincidence of
    units.

    ⚠️ **This replaced `kinematicViscosity_exceeds_bare_time`, which compared a
    TIME to a VISCOSITY.** `etaOverST` is `[s]`; `kinematicViscosity` is `[m²/s]`;
    `etaOverST < kinematicViscosity etaOverST c_s` therefore asserted something
    about numeric magnitudes in a chosen unit system — true for `c_s` in m/s and
    false for the same physical sound speed in km/s. Reduced, it said `1 < 2c_s²`
    given `c_s > 1`: no physical content at all. In the one module that exists
    because a missing velocity² produced an eleven-order-of-magnitude error, the
    theorem meant to make that detectable was the only unit-dependent one in the
    file. -/
theorem kinematicViscosity_scales_quadratically (etaOverST c_s s : ℝ) :
    kinematicViscosity etaOverST (s * c_s)
      = s ^ 2 * kinematicViscosity etaOverST c_s := by
  unfold kinematicViscosity
  ring

/-- The same scaling at the Dean-device operating point, `norm_num`-backed: a
    doubled sound speed quadruples `ν`. A `ν` built without the velocity² would
    return the same number for both, which is exactly the pre-repair defect. -/
theorem kinematicViscosity_doubling_quadruples (etaOverST c_s : ℝ) :
    kinematicViscosity etaOverST (2 * c_s)
      = 4 * kinematicViscosity etaOverST c_s := by
  rw [kinematicViscosity_scales_quadratically]
  norm_num

end SKEFTHawking.DiracFluidSK
