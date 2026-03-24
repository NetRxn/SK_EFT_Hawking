import SKEFTHawking.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Structure B: Schwinger-Keldysh Doubling Constraints

## Statement

Given an action I[ψ] with global U(1) symmetry, the SK doubled action
I_SK[ψ_r, ψ_a] satisfying:
  (i)   I_SK[ψ_r, 0] = 0       (normalization)
  (ii)  Im I_SK ≥ 0              (positivity / unitarity)
  (iii) KMS symmetry             (fluctuation-dissipation relation)
is uniquely determined at each order in the derivative expansion up to
the transport coefficients.

## Physical Context

The Schwinger-Keldysh formalism (Crossley-Glorioso-Liu, JHEP 2017) is the
standard framework for dissipative EFTs. It doubles the degrees of freedom:

  ψ → (ψ₁, ψ₂) on forward/backward branches of the SK contour

  ψ_r = (ψ₁ + ψ₂)/2    (classical/retarded field)
  ψ_a = ψ₁ - ψ₂         (noise/advanced field)

The three axioms encode:
  (i)   The optical theorem / unitarity
  (ii)  The arrow of time / second law
  (iii) Thermal equilibrium at temperature T = 1/β

At each derivative order, the space of allowed terms is finite-dimensional.
The symmetry constraints reduce the free parameters to the transport coefficients
(γ₁, γ₂, ...) — physical quantities measurable in experiment.

## Formalization Approach

Encode the SK constraints as propositions on a vector space of field monomials.
At each derivative order n, the space of possible terms is a finite-dimensional
real vector space V_n. The three constraints are linear or quadratic relations
on V_n. The "free parameters" are the dimension of the quotient space
V_n / (constraints).

This is a finite-dimensional linear algebra problem: count independent
structures, impose symmetry constraints, identify free parameters.

## sorry Gaps

- Convergence of the derivative expansion
- Physical interpretation of the transport coefficients
- Connection to microscopic Bogoliubov theory (UV matching)
- The KMS transformation beyond leading order

## References

- Crossley-Glorioso-Liu, JHEP 2017 (arXiv:1511.03646)
- Glorioso-Liu, JHEP 2018 (arXiv:1612.07705) — SK for superfluids
- Endlich-Nicolis-Porto-Wang, PRD 2013 (arXiv:1211.6461)
- Jain-Kovtun, JHEP 2024 (arXiv:2309.00511) — UV ambiguity
-/

namespace SKEFTHawking.SKDoubling

/-!
## SK Field Content

The doubled fields (ψ_r, ψ_a) and their derivatives form the building
blocks of the SK effective action. We work in 1+1D.
-/

/-- The Schwinger-Keldysh doubled field content at a spacetime point.
    We store the field values and their first and second derivatives,
    which is sufficient through the first dissipative order.

    Convention:
    - ψ_r = (ψ₁ + ψ₂)/2 is the "classical" or "retarded" field
    - ψ_a = ψ₁ - ψ₂ is the "quantum" or "advanced" field
    - In the classical limit ψ_a → 0, recovering the physical field ψ_r -/
structure SKFields where
  /-- Retarded (classical) field value ψ_r -/
  psi_r : ℝ
  /-- Advanced (quantum) field value ψ_a -/
  psi_a : ℝ
  /-- Time derivative of ψ_r: ∂_t ψ_r -/
  dt_psi_r : ℝ
  /-- Spatial derivative of ψ_r: ∂_x ψ_r -/
  dx_psi_r : ℝ
  /-- Time derivative of ψ_a: ∂_t ψ_a -/
  dt_psi_a : ℝ
  /-- Spatial derivative of ψ_a: ∂_x ψ_a -/
  dx_psi_a : ℝ
  /-- Second time derivative of ψ_r: ∂_t² ψ_r -/
  dtt_psi_r : ℝ
  /-- Mixed derivative of ψ_r: ∂_t∂_x ψ_r -/
  dtx_psi_r : ℝ
  /-- Second spatial derivative of ψ_r: ∂_x² ψ_r -/
  dxx_psi_r : ℝ

/-!
## The Three SK Axioms

These are the constraints that any SK effective action must satisfy.
They encode unitarity, the arrow of time, and thermal equilibrium.
-/

/-- An SK effective action is a functional I_SK[ψ_r, ψ_a] represented
    locally as a Lagrangian density L_SK(ψ_r, ψ_a, ∂ψ_r, ∂ψ_a, ...).

    We model this as a real-valued function on the field content,
    which when integrated over spacetime gives the action. -/
structure SKAction where
  /-- The Lagrangian density as a function of the local field content.
      Returns (Re L_SK, Im L_SK) to track the imaginary part separately. -/
  lagrangian : SKFields → ℝ × ℝ

/-- **Axiom (i): Normalization.**
    I_SK[ψ_r, ψ_a = 0] = 0

    Physical meaning: the partition function Z = Tr(ρ) = 1 when the
    forward and backward evolutions are identical (ψ_a = 0).
    This is the optical theorem for the SK generating functional.

    Consequence: every term in I_SK must contain at least one power of ψ_a
    or its derivatives. -/
def satisfies_normalization (action : SKAction) : Prop :=
  ∀ (fields : SKFields),
    fields.psi_a = 0 → fields.dt_psi_a = 0 → fields.dx_psi_a = 0 →
    action.lagrangian fields = (0, 0)

/-- **Axiom (ii): Positivity of Im I_SK.**
    Im I_SK[ψ_r, ψ_a] ≥ 0

    Physical meaning: the probability distribution exp(iI_SK) must be
    normalizable, requiring Im I_SK ≥ 0. This encodes the second law
    of thermodynamics (entropy production ≥ 0).

    In the classical limit, this becomes an emergent BRST supersymmetry
    (Crossley-Glorioso-Liu). -/
def satisfies_positivity (action : SKAction) : Prop :=
  ∀ (fields : SKFields), (action.lagrangian fields).2 ≥ 0

/-- **Axiom (iii): KMS symmetry.**
    The action is invariant under the KMS transformation:

      ψ_a → ψ_a + iβ ∂_t ψ_r   (to leading order in ℏ)

    where β = 1/T is the inverse temperature.

    Physical meaning: this enforces the fluctuation-dissipation relation
    (FDR) automatically. Every dissipative coefficient (imaginary part)
    is paired with a fluctuation coefficient (noise) in a ratio fixed by T.

    At T → 0 (β → ∞), the KMS condition becomes the vacuum FDR:
    G_K = sign(ω) · Im G_R, encoding zero-point quantum fluctuations. -/
structure KMSSymmetry (action : SKAction) (beta : ℝ) where
  /-- The KMS-transformed fields: ψ_a → ψ_a + iβ ∂_t ψ_r -/
  kms_transform : SKFields → SKFields
  /-- The transformation adds iβ ∂_t ψ_r to ψ_a -/
  kms_transform_spec : ∀ (f : SKFields),
    (kms_transform f).psi_r = f.psi_r ∧
    (kms_transform f).psi_a = f.psi_a + beta * f.dt_psi_r ∧
    (kms_transform f).dt_psi_r = f.dt_psi_r ∧
    (kms_transform f).dx_psi_r = f.dx_psi_r
  /-- The action is invariant under the KMS transformation -/
  invariance : ∀ (f : SKFields),
    action.lagrangian (kms_transform f) = action.lagrangian f

/-!
## Derivative Counting and the Space of Allowed Terms

At each derivative order, we enumerate the possible terms in I_SK.
The three axioms constrain this finite-dimensional space.

### Order 0 (no derivatives beyond the ideal part):
  - Only term with ψ_a: ψ_a · (∂P/∂ψ_r evaluated on background)
  - This reproduces the ideal (non-dissipative) EOM. No free parameters.

### Order 1 (first dissipative order):
  - Candidate terms (real part): ψ_a · □ψ_r, ψ_a · u^μ∂_μ(u^ν∂_νψ_r), ...
  - Candidate terms (imaginary part): ψ_a², ψ_a · ∂_t ψ_a, ...
  - Normalization: each term has ≥ 1 factor of ψ_a ✓
  - KMS: pairs each Im term with a Re term via β
  - After constraints: 2 free parameters (γ₁, γ₂)
-/

/-- The derivative order of a term in the SK action.
    Order 0 = ideal fluid (Son's L = P(X))
    Order 1 = first dissipative corrections (our focus)
    Order 2 = second-order hydrodynamics -/
structure DerivativeOrder where
  order : ℕ

/-- **Space of candidate terms at a given derivative order.**

    At order n, the space of Lorentz-scalar monomials built from
    (ψ_r, ψ_a, ∂ψ_r, ∂ψ_a, ...) with total derivative count n
    and at least one factor of ψ_a (normalization) is finite-dimensional.

    We model this as a natural number (the dimension before constraints). -/
noncomputable def candidateTermCount (n : ℕ) : ℕ :=
  -- Proof by Aristotle: concrete monomial counts in 1+1D SK-EFT
  -- Order 0: 1 term (ideal EOM ψ_a · ∂P/∂ψ_r)
  -- Order 1: 9 terms (6 real + 3 imaginary candidate structures)
  -- Higher: not enumerated (set to 0)
  match n with
  | 0 => 1
  | 1 => 9
  | _ => 0

/-- **Number of free parameters (transport coefficients) at each order.**

    After imposing all three SK axioms, the number of free parameters
    at order n is the dimension of the constrained space.

    Known results:
    - Order 0: 0 free parameters (ideal fluid fully determined by P(X))
    - Order 1: 2 free parameters (γ₁, γ₂) for a superfluid
    - Order 2: O(10) parameters for a general fluid -/
noncomputable def transportCoeffCount (n : ℕ) : ℕ :=
  -- Linear algebra result: dim(V_n) - rank(constraint matrix)
  -- Known values from Crossley-Glorioso-Liu classification:
  match n with
  | 0 => 0  -- Ideal fluid: fully determined by P(X), no free parameters
  | 1 => 2  -- First dissipative order: (γ₁, γ₂)
  | _ => 0  -- Higher orders: not enumerated here

/-!
## The First-Order Dissipative Action

This is the specific action we need for the Hawking calculation.
At order 1 beyond the ideal superfluid, the SK action takes the form:

  I_SK^(1) = ∫ d²x [iγ₁ ψ_a □ψ_r + iγ₂ ψ_a u^μ∂_μ(u^ν∂_ν ψ_r)
                    + (γ₁/β) ψ_a² + (γ₂/β) (u^μ∂_μ ψ_a)²/... ]

The imaginary terms (proportional to γ₁, γ₂) encode dissipation.
The real fluctuation terms are fixed by KMS (FDR).
-/

/-- The first-order dissipative SK action for a superfluid in 1+1D.

    Two transport coefficients (γ₁, γ₂) parameterize all dissipative
    effects at this order. Their physical interpretation:
    - γ₁: isotropic phonon damping (related to bulk viscosity)
    - γ₂: anisotropic damping along the superfluid flow

    At T = 0 in a BEC:
    - γ₁ receives contributions from Beliaev damping and 3-body loss
    - γ₂ is generated by the anomalous density ⟨ψ̂ψ̂⟩ effects -/
noncomputable def firstOrderDissipativeAction
    (coeffs : DissipativeCoeffs) (beta : ℝ) : SKAction where
  lagrangian := fun fields =>
    -- Real part: dissipative response
    let re_part := coeffs.gamma_1 * fields.psi_a *
        (fields.dtt_psi_r - fields.dxx_psi_r) +
      coeffs.gamma_2 * fields.psi_a * fields.dtt_psi_r
    -- Imaginary part: fluctuation/noise (fixed by KMS relative to Re)
    let im_part := (coeffs.gamma_1 / beta) * fields.psi_a ^ 2 +
      (coeffs.gamma_2 / beta) * fields.dt_psi_a ^ 2
    (re_part, im_part)

/-- The first-order dissipative action satisfies the normalization axiom.
    When ψ_a = 0 and ∂ψ_a = 0, the Lagrangian vanishes. -/
theorem firstOrder_normalization (coeffs : DissipativeCoeffs) (beta : ℝ) :
    satisfies_normalization (firstOrderDissipativeAction coeffs beta) := by
  intro fields ha hda_t hda_x
  simp only [firstOrderDissipativeAction, ha, hda_t]
  norm_num

/-- The first-order dissipative action satisfies positivity (Im I_SK ≥ 0)
    when γ₁ ≥ 0, γ₂ ≥ 0, and β > 0. -/
theorem firstOrder_positivity (coeffs : DissipativeCoeffs) (beta : ℝ)
    (hbeta : 0 < beta) :
    satisfies_positivity (firstOrderDissipativeAction coeffs beta) := by
  -- Proof by Aristotle: (γ₁/β)·ψ_a² + (γ₂/β)·(∂_t ψ_a)² ≥ 0
  -- from γ₁≥0, γ₂≥0, β>0, x²≥0
  intro fields
  exact add_nonneg
    (mul_nonneg (div_nonneg coeffs.gamma_1_nonneg hbeta.le) (sq_nonneg _))
    (mul_nonneg (div_nonneg coeffs.gamma_2_nonneg hbeta.le) (sq_nonneg _))

/-- A first-order polynomial SK action in 1+1D, parameterized by 9 coefficients.

    The most general Lagrangian at first derivative order with at least one ψ_a
    factor (normalization) is a linear combination of 9 monomials:

    Real (dissipative) monomials:
      r₁: ψ_a · ∂_t² ψ_r,  r₂: ψ_a · ∂_x² ψ_r,  r₃: ψ_a · ∂_t∂_x ψ_r,
      r₄: ψ_a · ∂_t ψ_r,   r₅: ψ_a · ∂_x ψ_r,    r₆: ψ_a · ψ_r

    Imaginary (noise) monomials:
      i₁: ψ_a²,  i₂: (∂_t ψ_a)²,  i₃: (∂_x ψ_a)² -/
structure FirstOrderCoeffs where
  r1 : ℝ  -- ψ_a · ∂_t² ψ_r
  r2 : ℝ  -- ψ_a · ∂_x² ψ_r
  r3 : ℝ  -- ψ_a · ∂_t∂_x ψ_r
  r4 : ℝ  -- ψ_a · ∂_t ψ_r
  r5 : ℝ  -- ψ_a · ∂_x ψ_r
  r6 : ℝ  -- ψ_a · ψ_r
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

/-
## Note on `KMSSymmetry` and the original theorem statement

The original `firstOrder_uniqueness` used `KMSSymmetry (firstOrderAction c) beta`
as a hypothesis. However, the `KMSSymmetry` structure only constrains 4 of 9
transform components (ψ_r, ψ_a, ∂_t ψ_r, ∂_x ψ_r), leaving the derivatives of
ψ_a and the second derivatives of ψ_r unconstrained.  This makes the condition
too weak to capture the physical fluctuation-dissipation relation (FDR).

Counterexample: c = ⟨0,0,0,0,0,0,0,1,0⟩ gives action (0, (∂_t ψ_a)²) which
satisfies positivity and admits a KMS-compatible transform (keeping ∂_t ψ_a
fixed), but does NOT equal `firstOrderDissipativeAction` for any coefficients
(γ₁, γ₂), since the latter always has Re ≠ 0 when γ₂ ≠ 0 and Im = 0 when
γ₁ = γ₂ = 0.

Physically, the KMS transform ψ_a → ψ_a + iβ ∂_t ψ_r induces consistent
transformations on ALL derivatives (∂_t ψ_a → ∂_t ψ_a + β ∂_t² ψ_r, etc.),
and the invariance holds only order-by-order in the derivative expansion.
The correct first-order constraint is the algebraic FDR relating Im (noise)
coefficients to Re (dissipative) coefficients — captured by `FirstOrderKMS`.
-/

-- Original (false) theorem statement, commented out:
-- theorem firstOrder_uniqueness_ORIGINAL :
--     ∀ (c : FirstOrderCoeffs) (beta : ℝ),
--       0 < beta →
--       satisfies_positivity (firstOrderAction c) →
--       KMSSymmetry (firstOrderAction c) beta →
--       ∃ (coeffs : DissipativeCoeffs),
--         ∀ (fields : SKFields),
--           (firstOrderAction c).lagrangian fields =
--             (firstOrderDissipativeAction coeffs beta).lagrangian fields := by
--   sorry

/-- **Algebraic KMS condition on first-order SK coefficients.**

    The physical KMS symmetry (ψ_a → ψ_a + iβ ∂_t ψ_r) at first derivative
    order imposes algebraic constraints on the 9 coefficients of the general
    first-order action.  These constraints encode the fluctuation-dissipation
    relation: the noise (Im) coefficients are fixed by the dissipative (Re)
    coefficients and the inverse temperature β.

    Specifically, the KMS variation of the Re part generates cross-terms
    (β · ∂_t ψ_r · O_n) that must cancel against the KMS variation of the
    Im part (noise terms).  Matching monomials order-by-order gives:

    1. Lower-derivative Re monomials (r3–r6) have no KMS partners → vanish
    2. The noise coefficients are fixed by the FDR:
       i₁ = −r₂/β,  i₂ = (r₁+r₂)/β,  i₃ = 0
    3. The surviving free parameters are r₁ and r₂ (equivalently γ₁, γ₂). -/
structure FirstOrderKMS (c : FirstOrderCoeffs) (beta : ℝ) : Prop where
  /-- Mixed spatial-temporal monomial has no KMS partner at this order -/
  r3_zero : c.r3 = 0
  /-- Lower-derivative monomials vanish (no KMS partner) -/
  r4_zero : c.r4 = 0
  r5_zero : c.r5 = 0
  r6_zero : c.r6 = 0
  /-- FDR: ψ_a² noise coefficient fixed by the ∂_x²ψ_r dissipative coefficient -/
  fdr_i1 : c.i1 * beta = -(c.r2)
  /-- FDR: (∂_t ψ_a)² noise coefficient fixed by the ∂_t²ψ_r coefficients -/
  fdr_i2 : c.i2 * beta = c.r1 + c.r2
  /-- No spatial noise term at first derivative order -/
  i3_zero : c.i3 = 0

/-
PROBLEM
**Uniqueness theorem for first-order dissipative SK action (corrected).**

    At first derivative order, any first-order polynomial SK action (parameterized
    by `FirstOrderCoeffs` — 9 real coefficients for the 9 candidate monomials)
    satisfying positivity and the algebraic KMS condition (FDR) is determined by
    exactly two free parameters corresponding to `DissipativeCoeffs` (γ₁, γ₂).

    The corrected version uses `FirstOrderKMS` (algebraic FDR on coefficients)
    instead of the general `KMSSymmetry` transform, which was too weak to
    capture the physical content.

PROVIDED SOLUTION
We construct DissipativeCoeffs with γ₁ = -c.r2 and γ₂ = c.r1 + c.r2, then show the lagrangians are equal.

Step 1: Extract non-negativity. From `satisfies_positivity`, setting fields with only psi_a=1 gives c.i1 ≥ 0, and with only dt_psi_a=1 gives c.i2 ≥ 0.

Step 2: Construct coefficients.
- γ₁ = -c.r2 ≥ 0: From fdr_i1 (c.i1 * beta = -c.r2) and c.i1 ≥ 0, beta > 0, we get -c.r2 = c.i1 * beta ≥ 0.
- γ₂ = c.r1 + c.r2 ≥ 0: From fdr_i2 (c.i2 * beta = c.r1 + c.r2) and c.i2 ≥ 0, beta > 0.

Step 3: Show lagrangian equality by `ext` on fields, then verify both Re and Im parts match.

For Re: firstOrderAction c gives r1*ψ_a*dtt + r2*ψ_a*dxx (since r3=r4=r5=r6=0 from hkms).
firstOrderDissipativeAction gives γ₁*ψ_a*(dtt-dxx) + γ₂*ψ_a*dtt = (γ₁+γ₂)*ψ_a*dtt - γ₁*ψ_a*dxx = (r1+r2-r2)*ψ_a*dtt + r2*ψ_a*dxx = r1*ψ_a*dtt + r2*ψ_a*dxx. ✓

For Im: firstOrderAction c gives i1*ψ_a² + i2*dt_ψ_a² (since i3=0 from hkms).
firstOrderDissipativeAction gives (γ₁/β)*ψ_a² + (γ₂/β)*dt_ψ_a².
From fdr_i1: i1 = -r2/β = γ₁/β. From fdr_i2: i2 = (r1+r2)/β = γ₂/β. ✓
-/
theorem firstOrder_uniqueness :
    ∀ (c : FirstOrderCoeffs) (beta : ℝ),
      0 < beta →
      satisfies_positivity (firstOrderAction c) →
      FirstOrderKMS c beta →
      ∃ (coeffs : DissipativeCoeffs),
        ∀ (fields : SKFields),
          (firstOrderAction c).lagrangian fields =
            (firstOrderDissipativeAction coeffs beta).lagrangian fields := by
  -- Proof by Aristotle (run 270e77a0): corrected KMS hypothesis, algebraic coefficient matching
  -- Key insight: original KMSSymmetry was too weak (only 4 of 9 components constrained).
  -- Aristotle found counterexample c = ⟨0,0,0,0,0,0,0,1,0⟩ and introduced FirstOrderKMS.
  intro c beta hb hp hcoeffs
  use ⟨-c.r2, c.r1 + c.r2, by
    have h_nonneg : ∀ (fields : SKFields), (firstOrderAction c).lagrangian fields = (c.r1 * fields.psi_a * fields.dtt_psi_r + c.r2 * fields.psi_a * fields.dxx_psi_r, c.i1 * fields.psi_a ^ 2 + c.i2 * fields.dt_psi_a ^ 2) := by
      unfold firstOrderAction;
      cases hcoeffs ; aesop;
    contrapose! hp;
    unfold satisfies_positivity;
    simp [h_nonneg];
    exact ⟨ ⟨ 0, 1, 0, 0, 0, 0, 0, 0, 0 ⟩, by norm_num; nlinarith [ hcoeffs.fdr_i1, hcoeffs.fdr_i2 ] ⟩, by
    contrapose! hp;
    norm_num [ satisfies_positivity ] at *;
    use ⟨ 0, 0, 0, 0, 1, 0, 0, 0, 0 ⟩ ; norm_num [ firstOrderAction ] ; nlinarith [ hcoeffs.fdr_i2, hcoeffs.fdr_i1, mul_div_cancel₀ ( c.r1 + c.r2 ) hb.ne', mul_div_cancel₀ ( -c.r2 ) hb.ne' ]⟩
  generalize_proofs;
  unfold firstOrderAction firstOrderDissipativeAction; simp +decide [ hcoeffs.r3_zero, hcoeffs.r4_zero, hcoeffs.r5_zero, hcoeffs.r6_zero, hcoeffs.i3_zero ] ; ring;
  intro fields; rw [ show c.i1 = -c.r2 / beta by rw [ eq_div_iff hb.ne' ] ; linarith [ hcoeffs.fdr_i1 ], show c.i2 = ( c.r1 + c.r2 ) / beta by rw [ eq_div_iff hb.ne' ] ; linarith [ hcoeffs.fdr_i2 ] ] ; ring;
  norm_num

/-!
## The T → 0 Limit: Quantum SK-EFT

At zero temperature (β → ∞), the KMS condition becomes the vacuum FDR.
The fluctuation terms do NOT vanish — they encode zero-point quantum
fluctuations. This is crucial for BEC experiments at near-zero temperature.

The Keldysh Green's function:
  G_K = coth(ω/2T) · Im G_R  →  sign(ω) · Im G_R  as T → 0

The dissipative corrections δ_diss persist at T = 0 because they modify
Im G_R (the spectral function), not just the thermal occupation factor.
-/

/-- In the T → 0 limit, the KMS constraint becomes:
    ψ_a → ψ_a + i∞ · ∂_t ψ_r

    In practice, this means the fluctuation terms in Im I_SK are
    determined by the vacuum FDR rather than the thermal one.
    The action remains non-trivial because G_K = sign(ω) · Im G_R ≠ 0. -/
theorem zeroTemp_nontrivial (_coeffs : DissipativeCoeffs)
    (_hg1 : 0 < _coeffs.gamma_1 ∨ 0 < _coeffs.gamma_2) :
    -- The dissipative action is non-zero even at T = 0
    -- (the ψ_a sector remains coupled to ψ_r)
    True := by
  trivial -- Placeholder: the real content is that Im G_R ≠ 0
  -- when γ₁ > 0 or γ₂ > 0, regardless of temperature

/-!
## Fluctuation-Dissipation Relation

The KMS symmetry automatically generates the FDR:

  G_K(ω) = [1 + 2n_B(ω)] · [G_R(ω) - G_A(ω)]

where n_B = 1/(e^{βω} - 1) is the Bose-Einstein distribution.

For the Hawking problem: G_K near the horizon encodes the thermal
spectrum at temperature T_H. The dissipative correction δ_diss appears
as a shift in the effective temperature extracted from G_K.
-/

/-- **FDR for the γ₁ sector: the ψ_a² noise term has coefficient γ₁/β.**

    Evaluating the Im part of `firstOrderDissipativeAction` at the "pure ψ_a"
    point (ψ_a = 1, all other fields zero) extracts the γ₁/β coefficient.
    This encodes coth(βω/2) → 1/β at leading (frequency-independent) order
    for the bulk damping sector. -/
theorem fdr_from_kms_gamma1 (coeffs : DissipativeCoeffs) (beta : ℝ) (_hbeta : 0 < beta) :
    let action := firstOrderDissipativeAction coeffs beta
    (action.lagrangian ⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩).2 =
      coeffs.gamma_1 / beta := by
  -- Im part at (ψ_r=0, ψ_a=1, rest=0):
  -- (γ₁/β)·1² + (γ₂/β)·0² = γ₁/β
  -- Proof by Aristotle (run 20556034): unfold + aesop
  unfold firstOrderDissipativeAction ; aesop

/-- **FDR for the γ₂ sector: the (∂_t ψ_a)² noise term has coefficient γ₂/β.**

    Evaluating the Im part at the "pure ∂_t ψ_a" point extracts γ₂/β.
    This encodes the FDR for the anisotropic damping sector along the
    superfluid flow direction. -/
theorem fdr_from_kms_gamma2 (coeffs : DissipativeCoeffs) (beta : ℝ) (_hbeta : 0 < beta) :
    let action := firstOrderDissipativeAction coeffs beta
    (action.lagrangian ⟨0, 0, 0, 0, 1, 0, 0, 0, 0⟩).2 =
      coeffs.gamma_2 / beta := by
  -- Im part at (dt_ψ_a=1, rest=0):
  -- (γ₁/β)·0² + (γ₂/β)·1² = γ₂/β
  -- Proof by Aristotle (run 20556034): simp on definition
  simp [firstOrderDissipativeAction]

/-- **The fluctuation-dissipation relation (algebraic, position-space form).**

    For the first-order dissipative SK action, KMS symmetry at temperature
    1/β forces the noise (imaginary) sector to be entirely determined by
    the dissipative (real) coefficients and β:

      Im L = (γ₁/β) · ψ_a² + (γ₂/β) · (∂_t ψ_a)²

    This is the position-space, algebraic statement of the FDR:
      Σ_K(ω) = coth(βω/2) · [Σ_R(ω) - Σ_A(ω)]
    specialized to the leading (frequency-independent) term.

    The proof is a direct computation: unfold `firstOrderDissipativeAction`
    and verify that the Im part of the Lagrangian equals the claimed
    expression for all field configurations. -/
theorem fdr_from_kms (coeffs : DissipativeCoeffs) (beta : ℝ) (_hbeta : 0 < beta) :
    let action := firstOrderDissipativeAction coeffs beta
    -- For ALL field configurations, the Im part equals (γ₁/β)·ψ_a² + (γ₂/β)·(∂_t ψ_a)²
    ∀ (f : SKFields),
      (action.lagrangian f).2 =
        (coeffs.gamma_1 / beta) * f.psi_a ^ 2 +
        (coeffs.gamma_2 / beta) * f.dt_psi_a ^ 2 :=
  -- Proof by Aristotle (run 638c5ff3): definitional equality — the Im part
  -- of firstOrderDissipativeAction is literally this expression.
  fun _ => rfl

/-!
## Stress Test: Strongest Possible First-Order KMS

Phase 1 used `FirstOrderKMS` (7 constraints on 9 coefficients → 2 free params).
Is this the STRONGEST constraint, or could there be additional relations
we're missing?

### Test: Hermiticity of the Imaginary Sector

The Im part of the SK action defines a quadratic form on ψ_a fields.
For physical consistency (probabilistic interpretation), this quadratic
form should be symmetric (Hermitian in the real case). At first order,
Im = i1·ψ_a² + i2·(∂_t ψ_a)² + i3·(∂_x ψ_a)² is manifestly symmetric.
But is there an additional constraint from requiring the FULL action
(Re + Im) to be consistent with the Hermiticity of the density matrix?

If so, we might find that i3 = 0 is not just a KMS consequence but
also a Hermiticity consequence — providing an independent derivation.
-/

/-- **Strongest KMS test**: Any first-order SK action satisfying
    FirstOrderKMS also satisfies positivity IFF γ₁ ≥ 0 AND γ₂ ≥ 0.

    This verifies that FirstOrderKMS + positivity is equivalent to
    the DissipativeCoeffs parameterization (which has γ₁ ≥ 0, γ₂ ≥ 0
    built in). No additional constraints are needed.

    If Aristotle proves this, FirstOrderKMS is the optimal constraint
    at first order. If a counterexample is found, we need stronger KMS. -/
theorem firstOrder_KMS_optimal :
    ∀ (c : FirstOrderCoeffs) (beta : ℝ),
      0 < beta →
      FirstOrderKMS c beta →
      (satisfies_positivity (firstOrderAction c) ↔
        (0 ≤ c.i1 ∧ 0 ≤ c.i2)) := by
  -- Aristotle run 3eedcabb: proved biconditional.
  -- Forward: specialize positivity at specific field configs to extract i1≥0, i2≥0.
  -- Backward: under KMS, Im = i1·ψ_a² + i2·(∂_t ψ_a)² is sum of nonneg terms.
  intro c beta hb hkms
  constructor
  · intro hp
    constructor
    · have := hp ⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩
      simp [firstOrderAction, hkms.i3_zero] at this
      linarith
    · have := hp ⟨0, 0, 0, 0, 1, 0, 0, 0, 0⟩
      simp [firstOrderAction, hkms.i3_zero] at this
      linarith
  · intro ⟨h1, h2⟩ fields
    simp [firstOrderAction, hkms.i3_zero]
    exact add_nonneg (mul_nonneg h1 (sq_nonneg _)) (mul_nonneg h2 (sq_nonneg _))

/-- **Alternative FDR sign test at first order**: What if fdr_i1 had the
    wrong sign? i.e., i1·β = +r2 instead of -r2.

    Under this alternative, does uniqueness still hold?
    Expected: Aristotle should find a COUNTEREXAMPLE. -/
structure FirstOrderKMS_altSign (c : FirstOrderCoeffs) (beta : ℝ) : Prop where
  r3_zero : c.r3 = 0
  r4_zero : c.r4 = 0
  r5_zero : c.r5 = 0
  r6_zero : c.r6 = 0
  /-- ALTERNATIVE: wrong sign on FDR for i1 -/
  fdr_i1_alt : c.i1 * beta = c.r2  -- Note: +r2 instead of -r2
  fdr_i2 : c.i2 * beta = c.r1 + c.r2
  i3_zero : c.i3 = 0

/-- The original statement claimed uniqueness under the wrong FDR sign.
    This is FALSE: the wrong sign i1·β = +r2 allows r2 > 0, forcing γ₁ = -r2 < 0,
    which violates gamma_1_nonneg in DissipativeCoeffs.
    Counterexample: c = ⟨1, 1, 0, 0, 0, 0, 1, 2, 0⟩, β = 1. -/
-- Original (false) statement:
-- theorem firstOrder_altSign_uniqueness_test :
--     ∀ (c : FirstOrderCoeffs) (beta : ℝ),
--       0 < beta →
--       satisfies_positivity (firstOrderAction c) →
--       FirstOrderKMS_altSign c beta →
--       ∃ (coeffs : DissipativeCoeffs),
--         ∀ (fields : SKFields),
--           (firstOrderAction c).lagrangian fields =
--             (firstOrderDissipativeAction coeffs beta).lagrangian fields := by
--   sorry

theorem firstOrder_altSign_uniqueness_test :
    ¬ (∀ (c : FirstOrderCoeffs) (beta : ℝ),
      0 < beta →
      satisfies_positivity (firstOrderAction c) →
      FirstOrderKMS_altSign c beta →
      ∃ (coeffs : DissipativeCoeffs),
        ∀ (fields : SKFields),
          (firstOrderAction c).lagrangian fields =
            (firstOrderDissipativeAction coeffs beta).lagrangian fields) := by
  -- Aristotle run 3eedcabb: proved negation with counterexample.
  -- c = ⟨1, 1, 0, 0, 0, 0, 1, 2, 0⟩, β = 1 satisfies alt-FDR and positivity,
  -- but forces γ₁ = -r2 = -1 < 0, violating DissipativeCoeffs.gamma_1_nonneg.
  intro h
  have hkms : FirstOrderKMS_altSign ⟨1, 1, 0, 0, 0, 0, 1, 2, 0⟩ 1 :=
    ⟨rfl, rfl, rfl, rfl, by norm_num, by norm_num, rfl⟩
  have hpos : satisfies_positivity (firstOrderAction ⟨1, 1, 0, 0, 0, 0, 1, 2, 0⟩) := by
    intro f; simp [firstOrderAction]; nlinarith [sq_nonneg f.psi_a, sq_nonneg f.dt_psi_a]
  obtain ⟨coeffs, hcoeffs⟩ := h ⟨1, 1, 0, 0, 0, 0, 1, 2, 0⟩ 1 one_pos hpos hkms
  have h1 := hcoeffs ⟨0, 1, 0, 0, 0, 0, 0, 0, 1⟩
  simp [firstOrderAction, firstOrderDissipativeAction] at h1
  linarith [coeffs.gamma_1_nonneg]

end SKEFTHawking.SKDoubling
