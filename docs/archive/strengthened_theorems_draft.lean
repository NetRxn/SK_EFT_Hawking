/-!
# Strengthened Theorem Statements — Draft for Review

These are proposed replacements for the five vacuous/unprovable theorems.
Review before patching into the actual Lean source files.

## Design Principles

1. Every conclusion must encode *real physics content*, not `True`
2. Existential witnesses must not be satisfiable by trivial (zero) values
3. Type restrictions must match the physical argument's domain
4. Proof sketches should guide Aristotle toward the real argument
-/

-- ═══════════════════════════════════════════════════════════════════
-- 1. fdr_from_kms  (SKDoubling.lean)
--
-- DIAGNOSIS: Conclusion was `True`. The FDR is an algebraic identity
-- on the coefficients of the SK quadratic action — it says the
-- Im (noise) coefficients are determined by the Re (dissipative)
-- coefficients and β. We can state this WITHOUT Fourier transforms
-- by working directly with the coefficient structure.
--
-- KEY INSIGHT: For firstOrderDissipativeAction, the Im part has
-- coefficients (γ₁/β, γ₂/β) and the Re part has coefficients (γ₁, γ₂).
-- The ratio Im_coeff / Re_coeff = 1/β is exactly the FDR at this order.
-- We encode this as: given any action satisfying KMS at temperature 1/β,
-- its noise-to-dissipation ratio at first order equals 1/β.
-- ═══════════════════════════════════════════════════════════════════

/-- Extract the "noise coefficient" from the Im part of an SK action.
    For a quadratic Im part of the form c₁·ψ_a² + c₂·(∂_t ψ_a)²,
    this extracts the coefficient of the ψ_a² term. -/
noncomputable def noiseCoeff_psi_a_sq (action : SKAction) : ℝ :=
  -- Evaluate Im L at ψ_a = 1, all other fields = 0
  -- This picks out the coefficient of ψ_a²
  (action.lagrangian ⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩).2

/-- Extract the "dissipative coefficient" from the Re part of an SK action.
    For a Re part containing γ·ψ_a·□ψ_r, this extracts the coefficient
    by evaluating at ψ_a = 1, □ψ_r = (dtt - dxx) = 1 (i.e., dtt=1, dxx=0). -/
noncomputable def dissipCoeff_box (action : SKAction) : ℝ :=
  -- Evaluate Re L at ψ_a = 1, dtt_psi_r = 1, all other = 0
  -- This picks out the coefficient of ψ_a · □ψ_r
  (action.lagrangian ⟨0, 1, 0, 0, 0, 0, 1, 0, 0⟩).1

/-- **The fluctuation-dissipation relation from KMS symmetry (algebraic form).**

    For the first-order dissipative SK action, KMS symmetry at temperature
    1/β forces the noise coefficient (Im part, ψ_a² term) to equal the
    dissipative coefficient (Re part, ψ_a·□ψ_r term) divided by β:

      noise_coeff = dissip_coeff / β

    This is the position-space, algebraic statement of the FDR:
      Σ_K(ω) = coth(βω/2) · [Σ_R(ω) - Σ_A(ω)]
    specialized to the leading (frequency-independent) term.

    We prove this concretely for `firstOrderDissipativeAction`. -/
theorem fdr_from_kms (coeffs : DissipativeCoeffs) (beta : ℝ) (hbeta : 0 < beta) :
    let action := firstOrderDissipativeAction coeffs beta
    -- The noise coefficient (Im, ψ_a² term) equals dissip coeff / β
    noiseCoeff_psi_a_sq action = dissipCoeff_box action / beta := by
  sorry -- Unfold firstOrderDissipativeAction, evaluate both sides:
  -- noiseCoeff_psi_a_sq: Im L at (0,1,0,0,0,0,0,0,0) = γ₁/β · 1² + γ₂/β · 0² = γ₁/β
  -- dissipCoeff_box:     Re L at (0,1,0,0,0,0,1,0,0) = γ₁·1·(1-0) + γ₂·1·1 = γ₁ + γ₂
  -- Hmm — this doesn't simplify to a clean ratio unless we separate the two terms.
  -- REVISED APPROACH: prove for each transport coefficient independently.
  -- See fdr_from_kms_gamma1 and fdr_from_kms_gamma2 below.

-- ALTERNATIVE (cleaner): prove the FDR for each coefficient separately
-- by isolating the γ₁ and γ₂ sectors.

/-- FDR for the γ₁ sector: the ψ_a² noise term has coefficient γ₁/β,
    which equals γ₁ · (1/β). This encodes coth(βω/2) → 1/β at leading order. -/
theorem fdr_from_kms_gamma1 (coeffs : DissipativeCoeffs) (beta : ℝ) (hbeta : 0 < beta) :
    let action := firstOrderDissipativeAction coeffs beta
    -- Evaluate Im L at the "pure ψ_a" point to extract γ₁/β
    (action.lagrangian ⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩).2 =
      coeffs.gamma_1 / beta := by
  sorry -- Unfold firstOrderDissipativeAction.lagrangian:
  -- im_part = (γ₁/β) · 1² + (γ₂/β) · 0² = γ₁/β  ✓
  -- This is a direct computation: simp + ring should close it.

/-- FDR for the γ₂ sector: the (∂_t ψ_a)² noise term has coefficient γ₂/β. -/
theorem fdr_from_kms_gamma2 (coeffs : DissipativeCoeffs) (beta : ℝ) (hbeta : 0 < beta) :
    let action := firstOrderDissipativeAction coeffs beta
    -- Evaluate Im L at the "pure ∂_t ψ_a" point to extract γ₂/β
    (action.lagrangian ⟨0, 0, 0, 0, 1, 0, 0, 0, 0⟩).2 =
      coeffs.gamma_2 / beta := by
  sorry -- Unfold firstOrderDissipativeAction.lagrangian:
  -- im_part = (γ₁/β) · 0² + (γ₂/β) · 1² = γ₂/β  ✓
  -- Direct computation.

/-- Combined FDR: the full noise sector of firstOrderDissipativeAction is
    determined by (γ₁, γ₂, β) with the relation Im_coeff = Re_coeff / β
    for each independent sector. -/
theorem fdr_from_kms_combined (coeffs : DissipativeCoeffs) (beta : ℝ) (hbeta : 0 < beta) :
    let action := firstOrderDissipativeAction coeffs beta
    -- For ALL field configurations, the Im part decomposes as (γ₁/β)·ψ_a² + (γ₂/β)·(∂_t ψ_a)²
    ∀ (f : SKFields),
      (action.lagrangian f).2 =
        (coeffs.gamma_1 / beta) * f.psi_a ^ 2 +
        (coeffs.gamma_2 / beta) * f.dt_psi_a ^ 2 := by
  sorry -- Unfold firstOrderDissipativeAction, the Im part is literally this expression.
  -- intro f; simp [firstOrderDissipativeAction]; ring

-- ═══════════════════════════════════════════════════════════════════
-- 2. firstOrder_uniqueness  (SKDoubling.lean)
--
-- DIAGNOSIS: Aristotle correctly identified the type-theoretic issue.
-- SKAction allows arbitrary functions, but uniqueness requires
-- restricting to polynomial Lagrangians at first derivative order.
--
-- APPROACH: Define `FirstOrderSKAction` as a 9-coefficient structure
-- (one per candidate monomial), then prove the axioms reduce
-- the 9 coefficients to 2 free parameters.
-- ═══════════════════════════════════════════════════════════════════

/-- A first-order polynomial SK action in 1+1D.

    The most general Lagrangian at first derivative order, with at least
    one factor of ψ_a (normalization), is a linear combination of 9
    monomials. We decompose into real and imaginary parts.

    Real (dissipative response) monomials:
      r₁: ψ_a · ∂_t² ψ_r      (bulk damping, temporal)
      r₂: ψ_a · ∂_x² ψ_r      (bulk damping, spatial)
      r₃: ψ_a · ∂_t∂_x ψ_r    (mixed damping)
      r₄: ψ_a · ∂_t ψ_r       (zeroth-order dissipation — forbidden by Lorentz)
      r₅: ψ_a · ∂_x ψ_r       (zeroth-order dissipation — forbidden by Lorentz)
      r₆: ψ_a · ψ_r            (mass-like — forbidden by shift symmetry)

    Imaginary (noise/fluctuation) monomials:
      i₁: ψ_a²                 (local noise)
      i₂: (∂_t ψ_a)²          (gradient noise, temporal)
      i₃: (∂_x ψ_a)²          (gradient noise, spatial)

    Total: 6 real + 3 imaginary = 9 candidate structures. -/
structure FirstOrderCoeffs where
  -- Real part coefficients
  r1 : ℝ  -- ψ_a · ∂_t² ψ_r
  r2 : ℝ  -- ψ_a · ∂_x² ψ_r
  r3 : ℝ  -- ψ_a · ∂_t∂_x ψ_r
  r4 : ℝ  -- ψ_a · ∂_t ψ_r
  r5 : ℝ  -- ψ_a · ∂_x ψ_r
  r6 : ℝ  -- ψ_a · ψ_r
  -- Imaginary part coefficients
  i1 : ℝ  -- ψ_a²
  i2 : ℝ  -- (∂_t ψ_a)²
  i3 : ℝ  -- (∂_x ψ_a)²

/-- Construct an SKAction from first-order polynomial coefficients. -/
noncomputable def firstOrderAction (c : FirstOrderCoeffs) : SKAction where
  lagrangian := fun f =>
    let re := c.r1 * f.psi_a * f.dtt_psi_r +
              c.r2 * f.psi_a * f.dxx_psi_r +
              c.r3 * f.psi_a * f.dtx_psi_r +
              c.r4 * f.psi_a * f.dt_psi_r +
              c.r5 * f.psi_a * f.dx_psi_r +
              c.r6 * f.psi_a * f.psi_r
    let im := c.i1 * f.psi_a ^ 2 +
              c.i2 * f.dt_psi_a ^ 2 +
              c.i3 * f.dx_psi_a ^ 2
    (re, im)

/-- **Uniqueness theorem (restricted to first-order polynomial actions).**

    Any first-order polynomial SK action satisfying normalization,
    positivity, and KMS is parameterized by exactly two coefficients
    that correspond to (γ₁, γ₂) of the dissipative action.

    The proof is finite-dimensional linear algebra on a 9-dim space:
    1. Normalization: automatically satisfied (every monomial has ψ_a)
    2. Positivity: i₁ ≥ 0, i₂ ≥ 0, i₃ ≥ 0 (diagonal quadratic form)
    3. KMS: ψ_a → ψ_a + β·∂_t ψ_r imposes:
       - r4 = r5 = r6 = 0 (no zeroth-derivative dissipation)
       - r3 = 0 (isotropy in 1+1D or parity)
       - i₁ = (r₁ + r₂)/β  (FDR for bulk sector)
       - Wait — need to be more careful here.
       Actually: KMS invariance equates L(f) = L(kms(f)) for all f.
       Expanding both sides as polynomials in the 9 field components and
       matching coefficients gives linear relations among the rᵢ and iⱼ.
       The result is: r₁ - r₂ = γ₁, r₁ + r₂ = related to γ₂,
       and i₁ = γ₁/β, i₂ = γ₂/β, i₃ = 0, r₃=r₄=r₅=r₆=0.
       Net: 2 free parameters. -/
theorem firstOrder_uniqueness_polynomial :
    ∀ (c : FirstOrderCoeffs) (beta : ℝ),
      0 < beta →
      satisfies_positivity (firstOrderAction c) →
      KMSSymmetry (firstOrderAction c) beta →
      ∃ (coeffs : DissipativeCoeffs),
        ∀ (f : SKFields),
          (firstOrderAction c).lagrangian f =
            (firstOrderDissipativeAction coeffs beta).lagrangian f := by
  sorry -- The proof is:
  -- 1. KMS invariance: for all f, firstOrderAction c (kms f) = firstOrderAction c f
  -- 2. Expand both sides. The kms transform sends:
  --    psi_a ↦ psi_a + β·dt_psi_r, dt_psi_a ↦ dt_psi_a + β·dtt_psi_r, etc.
  -- 3. Matching the coefficient of each independent monomial gives:
  --    From Re part: c.r4 = 0, c.r5 = 0, c.r6 = 0, c.r3 = 0
  --    From Im↔Re cross: c.i1 = c.r1/β (FDR for □ sector),
  --                       c.i2 = c.r2/β or similar (FDR for u·∂ sector)
  --    From Im part: c.i3 = 0 (no ∂_x ψ_a noise at this order)
  -- 4. Remaining free: c.r1 and c.r2 (or linear combos = γ₁, γ₂)
  -- 5. Construct DissipativeCoeffs from these, show equality.
  -- This is a 9-variable system with ~7 linear constraints → 2 free params.

-- ═══════════════════════════════════════════════════════════════════
-- 3. dispersive_correction_bound  (HawkingUniversality.lean)
--
-- DIAGNOSIS: Aristotle witnessed δ_disp = 0, C = 1. Need to require
-- that the correction is *non-trivial* when dispersion is present.
-- ═══════════════════════════════════════════════════════════════════

/-- **Dispersive correction bound (strengthened).**

    For a modified dispersion relation with adiabaticity parameter D,
    there exists a correction δ_disp with:
    - |δ_disp| ≤ C · D² for some C > 0  (the correction is O(D²))
    - When D > 0, the correction is non-zero (δ_disp ≠ 0)

    This encodes the Corley-Jacobson result that dispersion produces
    a *genuine* correction, not just that zero is a valid bound. -/
theorem dispersive_correction_bound_strong
    (mdr : ModifiedDispersion) (kappa : ℝ)
    (hkappa : 0 < kappa)
    (hadiabatic : adiabaticityParam kappa mdr.cs mdr.cutoff < 1)
    (hD_pos : 0 < adiabaticityParam kappa mdr.cs mdr.cutoff) :
    ∃ (delta_disp C : ℝ),
      0 < C ∧
      |delta_disp| ≤ C * (adiabaticityParam kappa mdr.cs mdr.cutoff) ^ 2 ∧
      delta_disp ≠ 0 := by
  sorry -- WKB connection formula across the turning point.
  -- The Bogoliubov coefficient |β/α|² = exp(-2πω/κ) · (1 + δ_disp)
  -- with δ_disp = -(π/6)(ω/κ)·D² + O(D⁴) for subluminal dispersion.
  -- The leading coefficient -(π/6)(ω/κ) is nonzero when D > 0.

-- ═══════════════════════════════════════════════════════════════════
-- 4. dissipative_correction_existence  (HawkingUniversality.lean)
--
-- DIAGNOSIS: Aristotle witnessed δ_diss = 0. Need to require that
-- dissipation produces a *genuine* correction when γ > 0.
-- ═══════════════════════════════════════════════════════════════════

/-- **Dissipative correction existence (strengthened).**

    When dissipative coefficients are non-zero, the correction is non-zero.
    This is the *core new result* of the paper. -/
theorem dissipative_correction_existence_strong
    (mdr : ModifiedDispersion) (coeffs : DissipativeCoeffs) (kappa : ℝ)
    (hkappa : 0 < kappa) :
    ∃ (delta_diss : ℝ),
      -- Vanishes when γ₁ = γ₂ = 0
      ((coeffs.gamma_1 = 0 ∧ coeffs.gamma_2 = 0) → delta_diss = 0) ∧
      -- Non-zero when either γ > 0 (the new content!)
      ((0 < coeffs.gamma_1 ∨ 0 < coeffs.gamma_2) → delta_diss ≠ 0) := by
  sorry -- This is the core calculation:
  -- The dissipative correction at leading order is:
  --   δ_diss = -(γ₁ + γ₂)/(2κ) · (ω_H/c_s)
  -- where ω_H is the Hawking frequency. When γ₁ > 0 or γ₂ > 0,
  -- this is strictly negative (dissipation slightly cools the spectrum).
  -- The sign is physical: dissipation removes energy from the modes.

-- ═══════════════════════════════════════════════════════════════════
-- 5. hawking_universality  (HawkingUniversality.lean)
--
-- DIAGNOSIS: Aristotle constructed T_H with all corrections = 0.
-- Need to require the full correction structure.
-- ═══════════════════════════════════════════════════════════════════

/-- **Hawking universality (strengthened).**

    The effective temperature decomposes into standard Hawking plus
    three correction terms, with the limit property AND the structure
    that corrections track their physical sources. -/
theorem hawking_universality_strong
    (mdr : ModifiedDispersion) (coeffs : DissipativeCoeffs)
    (bg : FluidBackground) (h : SonicHorizon bg) :
    ∃ (teff : EffectiveTemperature),
      -- T_H is the standard Hawking temperature
      teff.T_H = hawkingTemp h.surfaceGravity ∧
      -- Corrections vanish in the appropriate limits
      (coeffs.gamma_1 = 0 → coeffs.gamma_2 = 0 → teff.delta_diss = 0) ∧
      -- Dispersive correction is bounded
      (∃ C : ℝ, 0 < C ∧
        |teff.delta_disp| ≤ C * (adiabaticityParam h.surfaceGravity mdr.cs mdr.cutoff) ^ 2) ∧
      -- Cross term is higher order
      (coeffs.gamma_1 = 0 → coeffs.gamma_2 = 0 → teff.delta_cross = 0) := by
  sorry -- Combines the dispersive and dissipative results.
  -- Construct EffectiveTemperature from the WKB calculation with
  -- both dispersive and dissipative modifications included.
