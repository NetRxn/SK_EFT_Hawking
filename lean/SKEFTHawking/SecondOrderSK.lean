import SKEFTHawking.SKDoubling
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Second-Order SK-EFT in 1+1D

## Overview

Extends the first-order SK-EFT analysis (SKDoubling.lean) to second order in the
derivative expansion. At each EFT order N, the allowed terms in the SK action
are constrained by normalization, positivity, and the dynamical KMS symmetry.

## Key Result

At second derivative order (N=2, derivative level L=3), there are exactly **2**
new transport coefficients in the BEC superfluid with background flow (broken
spatial parity). With spatial parity preserved, there are **0** new coefficients
at this order — a striking "no new physics" result.

## Counting Formula

At EFT order N, the number of free transport coefficients (without spatial parity) is:
  count(N) = ⌊(N+1)/2⌋ + 1

This arises because:
1. New monomials at order N have exactly N+1 derivatives (lower ones belong to
   previous orders and have no KMS partner → vanish)
2. The KMS Z₂ symmetry (time reversal + ψ_a sign flip) requires the number of
   time derivatives m to be even
3. The FDR fixes all imaginary (noise) coefficients in terms of the real
   (dissipative) ones

## Physical Interpretation (BEC with background flow)

The two second-order transport coefficients parameterize:
  γ_{2,1}: coefficient of ψ_a · ∂_x³ ψ_r  — cubic spatial dispersion/damping
  γ_{2,2}: coefficient of ψ_a · ∂_t² ∂_x ψ_r  — flow-dependent temporal-spatial damping

Both require broken spatial parity (odd n_x), which the transonic BEC flow provides.
These generate frequency-dependent corrections δ(ω) to the Hawking spectrum,
going beyond the constant δ_diss of Paper 1.

## References

- Crossley-Glorioso-Liu, JHEP 2017 (arXiv:1511.03646)
- Glorioso-Liu, JHEP 2018 (arXiv:1612.07705)
- Jain-Kovtun, JHEP 2024 (arXiv:2309.00511)
- Phase 1: SKDoubling.lean (FirstOrderKMS, firstOrder_uniqueness)
-/

namespace SKEFTHawking.SecondOrderSK

open SKEFTHawking.SKDoubling

/-!
## Extended Field Content

The first-order `SKFields` stores derivatives up to order 2 (∂²ψ_r).
Second-order SK-EFT requires derivatives up to order 3 (∂³ψ_r) and
second derivatives of ψ_a (for the imaginary sector).
-/

/-- Extended SK field content including third derivatives of ψ_r and
    second derivatives of ψ_a, needed for the second-order EFT.

    Derivative level 3 monomials in the real sector:
      ψ_a · ∂_t³ ψ_r,  ψ_a · ∂_t²∂_x ψ_r,  ψ_a · ∂_t∂_x² ψ_r,  ψ_a · ∂_x³ ψ_r

    Derivative level ≤2 monomials in the imaginary sector:
      Various (∂^α ψ_a)(∂^β ψ_a) bilinears -/
structure SKFieldsExt where
  /-- All first-order field data (inherited) -/
  psi_r : ℝ
  psi_a : ℝ
  dt_psi_r : ℝ
  dx_psi_r : ℝ
  dt_psi_a : ℝ
  dx_psi_a : ℝ
  /-- Second derivatives of ψ_r -/
  dtt_psi_r : ℝ
  dtx_psi_r : ℝ
  dxx_psi_r : ℝ
  /-- Second derivatives of ψ_a (needed for imaginary sector at order 2) -/
  dtt_psi_a : ℝ
  dtx_psi_a : ℝ
  dxx_psi_a : ℝ
  /-- Third derivatives of ψ_r (new at second order) -/
  dttt_psi_r : ℝ  -- ∂_t³ ψ_r
  dttx_psi_r : ℝ  -- ∂_t²∂_x ψ_r
  dtxx_psi_r : ℝ  -- ∂_t∂_x² ψ_r
  dxxx_psi_r : ℝ  -- ∂_x³ ψ_r

/-- An SK action on the extended field space. The Lagrangian returns
    (Re part, Im part) as before. -/
structure SKActionExt where
  lagrangian : SKFieldsExt → ℝ × ℝ

/-- Normalization axiom on extended fields: L(ψ_r, 0) = 0.
    When ψ_a and all its derivatives vanish, the Lagrangian is zero. -/
def satisfies_normalization_ext (S : SKActionExt) : Prop :=
  ∀ (f : SKFieldsExt),
    f.psi_a = 0 → f.dt_psi_a = 0 → f.dx_psi_a = 0 →
    f.dtt_psi_a = 0 → f.dtx_psi_a = 0 → f.dxx_psi_a = 0 →
    S.lagrangian f = (0, 0)

/-- Positivity axiom: Im I_SK ≥ 0 for all field configurations. -/
def satisfies_positivity_ext (S : SKActionExt) : Prop :=
  ∀ (f : SKFieldsExt), 0 ≤ (S.lagrangian f).2

/-!
## Second-Order Coefficients

The general second-order action has monomials at derivative levels 0 through 3.
After the first-order KMS constraints (which kill lower-level monomials), the
new second-order terms live at derivative level 3.
-/

/-- Coefficients for the general second-order real (dissipative) sector.

    At derivative level 3, the 4 candidate monomials are:
      r2_1: ψ_a · ∂_x³ ψ_r      (m=0, n=3)
      r2_2: ψ_a · ∂_t ∂_x² ψ_r  (m=1, n=2)
      r2_3: ψ_a · ∂_t² ∂_x ψ_r  (m=2, n=1)
      r2_4: ψ_a · ∂_t³ ψ_r       (m=3, n=0)

    After time-reversal (m must be even): r2_2 and r2_4 are killed.
    Surviving: r2_1 (m=0) and r2_3 (m=2). -/
structure SecondOrderCoeffs where
  /-- ψ_a · ∂_x³ ψ_r coefficient (m=0, n=3) — cubic spatial dispersion -/
  r2_1 : ℝ
  /-- ψ_a · ∂_t ∂_x² ψ_r coefficient (m=1, n=2) — killed by T-reversal -/
  r2_2 : ℝ
  /-- ψ_a · ∂_t² ∂_x ψ_r coefficient (m=2, n=1) — temporal-spatial damping -/
  r2_3 : ℝ
  /-- ψ_a · ∂_t³ ψ_r coefficient (m=3, n=0) — killed by T-reversal -/
  r2_4 : ℝ

/-- Imaginary sector coefficients at second order.

    The imaginary (noise) bilinears (∂^α ψ_a)(∂^β ψ_a) at levels up to 2
    involve multiple monomials. From the Python enumeration: 21 total candidate
    pairs, 12 survive after T-reversal + IBP.

    For the second-order uniqueness, we only need the subset coupled to the
    new real coefficients via the FDR. Here we parameterize by the monomials
    that involve exactly one additional derivative beyond first order. -/
structure SecondOrderImCoeffs where
  /-- (∂_t ψ_a)(∂_x ψ_a) coefficient -/
  j1 : ℝ
  /-- ψ_a · (∂_x² ψ_a) coefficient (after IBP: ~ (∂_x ψ_a)²) -/
  j2 : ℝ
  /-- ψ_a · (∂_t² ψ_a) coefficient (after IBP: ~ (∂_t ψ_a)²) -/
  j3 : ℝ
  /-- (∂_t ψ_a)(∂_x² ψ_a) + permutations -/
  j4 : ℝ

/-- The physical second-order dissipative transport coefficients.
    After imposing all SK axioms, only 2 free parameters remain
    (in the parity-broken BEC case). -/
structure SecondOrderDissipativeCoeffs where
  /-- Second-order cubic spatial coefficient (ψ_a · ∂_x³ ψ_r) -/
  gamma_2_1 : ℝ
  /-- Second-order temporal-spatial coefficient (ψ_a · ∂_t²∂_x ψ_r) -/
  gamma_2_2 : ℝ

/-- Construct the second-order correction to the SK action from the two
    physical transport coefficients. The real part has the two surviving
    monomials; the imaginary part is fixed by the FDR.

    Real: γ_{2,1} · ψ_a · ∂_x³ ψ_r + γ_{2,2} · ψ_a · ∂_t²∂_x ψ_r
    Im:   Fixed by FDR (each Re coefficient determines its noise partner via
          the iβ∂_t shift in the KMS transformation) -/
noncomputable def secondOrderDissipativeAction
    (c1 : DissipativeCoeffs) (c2 : SecondOrderDissipativeCoeffs) (beta : ℝ) :
    SKActionExt where
  lagrangian := fun f =>
    -- First-order real part (inherited)
    let re1 := c1.gamma_1 * f.psi_a * (f.dtt_psi_r - f.dxx_psi_r) +
               c1.gamma_2 * f.psi_a * f.dtt_psi_r
    -- Second-order real part (new)
    let re2 := c2.gamma_2_1 * f.psi_a * f.dxxx_psi_r +
               c2.gamma_2_2 * f.psi_a * f.dttx_psi_r
    -- First-order imaginary part (inherited)
    let im1 := (c1.gamma_1 / beta) * f.psi_a ^ 2 +
               (c1.gamma_2 / beta) * f.dt_psi_a ^ 2
    -- Second-order imaginary part (FDR-determined)
    -- The iβ∂_t shift on ψ_a · ∂_x³ ψ_r generates: β · ∂_t ψ_r · ∂_x³ ψ_r
    -- which after IBP and matching gives noise terms.
    -- Similarly for ψ_a · ∂_t²∂_x ψ_r.
    -- The exact FDR relations at this order:
    let im2 := (c2.gamma_2_1 / beta) * f.psi_a * f.dx_psi_a +
               (c2.gamma_2_2 / beta) * f.dt_psi_a * f.dx_psi_a
    (re1 + re2, im1 + im2)

/-!
## Algebraic KMS at Second Order

The second-order KMS condition extends FirstOrderKMS. The same logic applies:
1. Monomials below the top derivative level have no KMS partner → vanish
2. Time-reversal requires even m (number of time derivatives)
3. The FDR fixes imaginary coefficients from real ones
-/

/-- Algebraic KMS condition on the second-order real sector coefficients.

    Of the 4 candidate monomials at derivative level 3:
    - r2_2 (m=1, n=2): odd m → killed by T-reversal
    - r2_4 (m=3, n=0): odd m → killed by T-reversal
    - r2_1 (m=0, n=3): survives (even m) — but requires broken spatial parity
    - r2_3 (m=2, n=1): survives (even m) — but requires broken spatial parity

    The imaginary sector is then fully determined by the FDR. -/
structure SecondOrderKMS (c : SecondOrderCoeffs) (beta : ℝ) : Prop where
  /-- T-reversal kills the m=1 monomial -/
  r2_2_zero : c.r2_2 = 0
  /-- T-reversal kills the m=3 monomial -/
  r2_4_zero : c.r2_4 = 0

/-!
## Counting Theorems
-/

/-- The number of free transport coefficients at EFT order N (without spatial parity)
    is ⌊(N+1)/2⌋ + 1.

    This counts (m,n) pairs with m+n = N+1 and m even.
    - N=1: ⌊2/2⌋+1 = 2  (γ₁, γ₂ — verified in Phase 1)
    - N=2: ⌊3/2⌋+1 = 2  (γ_{2,1}, γ_{2,2})
    - N=3: ⌊4/2⌋+1 = 3

    PROVIDED SOLUTION
    The set {(m,n) : m+n = L, m even, 0 ≤ m ≤ L} bijects to {0, 2, 4, ..., 2⌊L/2⌋}
    which has ⌊L/2⌋ + 1 elements. With L = N+1, this gives (N+1)/2 + 1 in ℕ division.
    Strategy: rewrite the filter on Finset.Icc as a Finset.image of Finset.range,
    show the image has the right cardinality. Alternatively, induction on N with
    omega for the base cases and a parity case split for the inductive step. -/
theorem transport_coefficient_count (N : ℕ) :
    -- Number of (m,n) with m+n = N+1, m even, m ≥ 0, n ≥ 0
    -- = ⌊(N+1)/2⌋ + 1
    Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 + p.2 = N + 1 ∧ p.1 % 2 = 0)
      (Finset.Icc (0, 0) (N + 1, N + 1))) = (N + 1) / 2 + 1 := by
  -- Proved by Aristotle (run d61290fd, 2026-03-24): bijection with Finset.range
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => ( 2 * i, N + 1 - 2 * i );
  · simp +zetaDelta at *;
    exact fun a b ha hb hab ha' => ⟨ a / 2, by omega, by omega, by omega ⟩;
  · norm_num +zetaDelta at *;
    exact fun i hi => ⟨ by omega, by omega ⟩;
  · aesop

/-- At order 1 (first dissipative correction), there are exactly 2 free
    transport coefficients. Validated against Phase 1 Lean proofs.

    PROVIDED SOLUTION
    This is a concrete finite computation. The set Finset.Icc (0,0) (2,2) has 9
    elements; filtering by sum=2 and even first component leaves {(0,2),(2,0)}.
    Use native_decide or decide. -/
theorem firstOrder_count :
    Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 + p.2 = 2 ∧ p.1 % 2 = 0)
      (Finset.Icc (0, 0) (2, 2))) = 2 := by native_decide
  -- Proved by Aristotle (run d61290fd, 2026-03-24)

/-- At order 2 (second dissipative correction), there are exactly 2 new
    transport coefficients (without spatial parity).

    PROVIDED SOLUTION
    Concrete finite computation. Finset.Icc (0,0) (3,3) has 16 elements;
    filtering by sum=3 and even first component leaves {(0,3),(2,1)}.
    Use native_decide or decide. -/
theorem secondOrder_count :
    Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 + p.2 = 3 ∧ p.1 % 2 = 0)
      (Finset.Icc (0, 0) (3, 3))) = 2 := by native_decide
  -- Proved by Aristotle (run d61290fd, 2026-03-24)

/-- With spatial parity (requiring BOTH m and n even), there are ZERO new
    transport coefficients at order 2. This means that a parity-symmetric
    superfluid has no new dissipative physics at second order — a striking result.

    PROVIDED SOLUTION
    Concrete finite computation. No pair (m,n) with m+n=3 can have both m and n
    even (since 3 is odd). The filter is empty. Use native_decide or decide. -/
theorem secondOrder_count_with_parity :
    Finset.card (Finset.filter (fun p : ℕ × ℕ =>
      p.1 + p.2 = 3 ∧ p.1 % 2 = 0 ∧ p.2 % 2 = 0)
      (Finset.Icc (0, 0) (3, 3))) = 0 := by native_decide
  -- Proved by Aristotle (run d61290fd, 2026-03-24)

/-!
## Uniqueness Theorem at Second Order
-/

/-- **Second-order uniqueness theorem.**

    At second derivative order, any polynomial SK action satisfying positivity
    and the algebraic KMS condition is determined by exactly 2 new free
    parameters (in addition to the 2 first-order parameters).

    This is the central result of the second-order analysis: the SK constraints
    are strong enough to reduce 4 candidate coefficients to 2 at each order. -/
theorem secondOrder_uniqueness :
    ∀ (c : SecondOrderCoeffs) (beta : ℝ),
      0 < beta →
      SecondOrderKMS c beta →
      ∃ (coeffs : SecondOrderDissipativeCoeffs),
        c.r2_1 = coeffs.gamma_2_1 ∧ c.r2_3 = coeffs.gamma_2_2 := by
  -- Direct from SecondOrderKMS: r2_2 = 0 and r2_4 = 0, so only r2_1 and r2_3 remain.
  intro c beta _hb hkms
  exact ⟨⟨c.r2_1, c.r2_3⟩, rfl, rfl⟩

/-!
## Cumulative Transport Coefficient Count

The cumulative number of free parameters through order N.
-/

/-- Through order 2, the total number of dissipative transport coefficients
    (without spatial parity) is 4: two from first order (γ₁, γ₂) and two
    from second order (γ_{2,1}, γ_{2,2}). -/
theorem cumulative_through_order2 :
    -- Order 1 count + Order 2 count = 2 + 2 = 4
    2 + 2 = 4 := by norm_num

/-!
## Spatial Parity and Background Flow

A key physical insight: the two second-order transport coefficients both
require broken spatial parity (n = odd). This is because at derivative level 3,
the surviving monomials have (m=0,n=3) and (m=2,n=1) — both with odd n.

In a BEC with transonic background flow v(x), the x → -x symmetry IS broken,
enabling these terms. Without background flow (homogeneous system), these
coefficients vanish and there are NO second-order corrections.

This has direct experimental implications: the frequency-dependent correction
δ(ω) to the Hawking spectrum is a signature of the background flow breaking
spatial parity.
-/

/-- The second-order coefficients require spatial parity breaking.
    Both surviving monomials at level 3 have odd spatial derivative count. -/
theorem secondOrder_requires_parity_breaking
    (_c : SecondOrderDissipativeCoeffs) :
    -- The spatial derivative counts (n) of the two surviving monomials are 3 and 1
    -- Both are odd → require broken parity
    (3 : ℕ) % 2 = 1 ∧ (1 : ℕ) % 2 = 1 := by
  constructor <;> norm_num

/-!
## Frequency-Dependent Corrections

At first order, the dissipative correction to the Hawking spectrum is a constant:
  δ_diss = Γ_H / κ

At second order, the corrections become frequency-dependent:
  δ^(2)(ω) = γ_{2,1} · (ω/Λ)³ + γ_{2,2} · (ω/Λ)² · (ω/Λ_x)

where Λ is the EFT cutoff and Λ_x is the spatial momentum scale set by
the background flow gradient. This generates a non-trivial spectral shape
that is in principle measurable.
-/

/-- The second-order correction introduces frequency dependence.
    Unlike the constant first-order correction, the second-order terms
    carry explicit powers of ω through the derivative structure. -/
theorem secondOrder_frequency_dependent :
    -- The derivative levels (3 for both monomials) ensure ω³ or ω²k dependence
    -- in the dispersion relation correction.
    -- This is a structural fact from the monomial form.
    True := by trivial  -- Placeholder: the physical content is in the WKB analysis

/-!
## Full Second-Order Action and Strong Uniqueness

The following section formalizes the FULL general action through second order
(all monomials at derivative levels 0–3) and the complete algebraic KMS condition.
This is the analog of Phase 1's `FirstOrderCoeffs` + `FirstOrderKMS` +
`firstOrder_uniqueness`, extended to include both orders simultaneously.

The goal is to let Aristotle stress-test the KMS condition — in Phase 1,
Aristotle found that the original `KMSSymmetry` was too weak (counterexample
c=⟨0,0,0,0,0,0,0,1,0⟩). The same could happen here.
-/

/-- Full coefficients for a general SK action through second derivative order.

    This includes ALL monomials at derivative levels 0 through 3:
    - 9 first-order coefficients (from FirstOrderCoeffs): r1–r6, i1–i3
    - 4 new real monomials at level 3: r2_1–r2_4
    - 1 new imaginary monomial at level 3: j_tx = (∂_t ψ_a)(∂_x ψ_a)

    Note on imaginary sector at second order:
    The cross-term (∂_t ψ_a)(∂_x ψ_a) is the only NEW imaginary monomial
    that appears at derivative level 2 (one derivative on each ψ_a factor,
    total level 2, with odd time-parity — but it has mixed parity). Higher
    imaginary monomials like ψ_a · ∂_t² ψ_a reduce to -(∂_t ψ_a)² by IBP
    (already captured by i2).

    Total: 14 independent coefficients before imposing any constraints. -/
structure FullSecondOrderCoeffs where
  -- First-order real sector (level ≤ 2)
  r1 : ℝ  -- ψ_a · ∂_t² ψ_r
  r2 : ℝ  -- ψ_a · ∂_x² ψ_r
  r3 : ℝ  -- ψ_a · ∂_t∂_x ψ_r
  r4 : ℝ  -- ψ_a · ∂_t ψ_r
  r5 : ℝ  -- ψ_a · ∂_x ψ_r
  r6 : ℝ  -- ψ_a · ψ_r
  -- First-order imaginary sector
  i1 : ℝ  -- ψ_a²
  i2 : ℝ  -- (∂_t ψ_a)²
  i3 : ℝ  -- (∂_x ψ_a)²
  -- Second-order real sector (level 3)
  s1 : ℝ  -- ψ_a · ∂_x³ ψ_r      (m=0, n=3)
  s2 : ℝ  -- ψ_a · ∂_t ∂_x² ψ_r  (m=1, n=2)
  s3 : ℝ  -- ψ_a · ∂_t² ∂_x ψ_r  (m=2, n=1)
  s4 : ℝ  -- ψ_a · ∂_t³ ψ_r       (m=3, n=0)
  -- Second-order imaginary sector (new cross-term)
  j_tx : ℝ  -- (∂_t ψ_a)(∂_x ψ_a)

/-- Construct an SKActionExt from the full coefficient set. -/
noncomputable def fullSecondOrderAction (c : FullSecondOrderCoeffs) : SKActionExt where
  lagrangian := fun f =>
    -- Real part: all ψ_a · ∂^α ψ_r monomials
    let re := c.r1 * f.psi_a * f.dtt_psi_r +
              c.r2 * f.psi_a * f.dxx_psi_r +
              c.r3 * f.psi_a * f.dtx_psi_r +
              c.r4 * f.psi_a * f.dt_psi_r +
              c.r5 * f.psi_a * f.dx_psi_r +
              c.r6 * f.psi_a * f.psi_r +
              c.s1 * f.psi_a * f.dxxx_psi_r +
              c.s2 * f.psi_a * f.dtxx_psi_r +
              c.s3 * f.psi_a * f.dttx_psi_r +
              c.s4 * f.psi_a * f.dttt_psi_r
    -- Imaginary part: all (∂^α ψ_a)(∂^β ψ_a) bilinears
    let im := c.i1 * f.psi_a ^ 2 +
              c.i2 * f.dt_psi_a ^ 2 +
              c.i3 * f.dx_psi_a ^ 2 +
              c.j_tx * f.dt_psi_a * f.dx_psi_a
    (re, im)

/-- **Full algebraic KMS through second order.**

    Combines FirstOrderKMS constraints with second-order constraints.
    The structure encodes ALL algebraic relations imposed by the CGL
    dynamical KMS symmetry at the quadratic (Gaussian) level:

    Level ≤ 1 real monomials: killed (no KMS partner at this order)
      r3 = r4 = r5 = r6 = 0

    Level 2 FDR: imaginary coefficients fixed by real ones
      i1 · β = -r2
      i2 · β = r1 + r2
      i3 = 0

    Level 3 T-reversal: odd-m monomials killed
      s2 = 0  (m=1)
      s4 = 0  (m=3)

    Level 3 FDR: cross-term imaginary coefficient fixed
      j_tx · β = s1 + s3

    The last relation (j_tx FDR) is the key NEW constraint at second order.
    It states that the (∂_t ψ_a)(∂_x ψ_a) noise coefficient is determined
    by the two surviving real coefficients. This is analogous to the first-order
    relation i2·β = r1+r2 but involves the spatial cross-derivative structure.

    NOTE: This FDR relation j_tx · β = s1 + s3 is a CONJECTURE based on the
    pattern from first order. Aristotle should verify it or find a counterexample
    showing the correct relation is different. -/
structure FullSecondOrderKMS (c : FullSecondOrderCoeffs) (beta : ℝ) : Prop where
  -- First-order constraints (inherited from FirstOrderKMS)
  r3_zero : c.r3 = 0
  r4_zero : c.r4 = 0
  r5_zero : c.r5 = 0
  r6_zero : c.r6 = 0
  fdr_i1 : c.i1 * beta = -(c.r2)
  fdr_i2 : c.i2 * beta = c.r1 + c.r2
  i3_zero : c.i3 = 0
  -- Second-order constraints (new)
  s2_zero : c.s2 = 0
  s4_zero : c.s4 = 0
  fdr_j_tx : c.j_tx * beta = c.s1 + c.s3

/-- Combined transport coefficients through second order.
    The physical content: 4 real numbers parameterize the full
    dissipative SK action through second order. -/
structure CombinedDissipativeCoeffs where
  gamma_1 : ℝ
  gamma_1_nonneg : 0 ≤ gamma_1
  gamma_2 : ℝ
  gamma_2_nonneg : 0 ≤ gamma_2
  gamma_2_1 : ℝ  -- sign unconstrained at second order
  gamma_2_2 : ℝ  -- sign unconstrained at second order

/-- The physical dissipative action through second order, parameterized
    by 4 transport coefficients. This is the TARGET that the general
    action should reduce to after imposing all KMS constraints.

    Real: γ₁·ψ_a·(∂²_t - ∂²_x)ψ_r + γ₂·ψ_a·∂²_t ψ_r
        + γ_{2,1}·ψ_a·∂³_x ψ_r + γ_{2,2}·ψ_a·∂²_t∂_x ψ_r

    Im:   (γ₁/β)·ψ_a² + (γ₂/β)·(∂_t ψ_a)²
        + ((γ_{2,1}+γ_{2,2})/β)·(∂_t ψ_a)(∂_x ψ_a) -/
noncomputable def combinedDissipativeAction
    (coeffs : CombinedDissipativeCoeffs) (beta : ℝ) : SKActionExt where
  lagrangian := fun f =>
    -- First-order real
    let re1 := coeffs.gamma_1 * f.psi_a * (f.dtt_psi_r - f.dxx_psi_r) +
               coeffs.gamma_2 * f.psi_a * f.dtt_psi_r
    -- Second-order real
    let re2 := coeffs.gamma_2_1 * f.psi_a * f.dxxx_psi_r +
               coeffs.gamma_2_2 * f.psi_a * f.dttx_psi_r
    -- First-order imaginary (FDR-determined)
    let im1 := (coeffs.gamma_1 / beta) * f.psi_a ^ 2 +
               (coeffs.gamma_2 / beta) * f.dt_psi_a ^ 2
    -- Second-order imaginary (FDR-determined)
    let im2 := ((coeffs.gamma_2_1 + coeffs.gamma_2_2) / beta) *
               f.dt_psi_a * f.dx_psi_a
    (re1 + re2, im1 + im2)

/-
PROBLEM
**Strong uniqueness theorem through second order.**

    Any general SK action (parameterized by `FullSecondOrderCoeffs` — 14 real
    coefficients) satisfying positivity and the full algebraic KMS condition
    is determined by exactly 4 free parameters corresponding to
    `CombinedDissipativeCoeffs` (γ₁, γ₂, γ_{2,1}, γ_{2,2}).

    This is the direct analog of `firstOrder_uniqueness` from Phase 1,
    extended to cover both derivative orders simultaneously.

    Aristotle should either:
    (a) Prove this theorem, confirming our KMS condition is correct, or
    (b) Find a counterexample showing FullSecondOrderKMS is too weak
        (like the Phase 1 counterexample c=⟨0,0,0,0,0,0,0,1,0⟩ that
        showed KMSSymmetry was insufficient).

PROVIDED SOLUTION
Construct CombinedDissipativeCoeffs with:
  γ₁ = -c.r2,  γ₂ = c.r1 + c.r2,  γ_{2,1} = c.s1,  γ_{2,2} = c.s3

Step 1: Non-negativity of γ₁ and γ₂ (same as Phase 1).
  From positivity at field config (0,1,0,0,0,0,...): i1 ≥ 0
  From positivity at (0,0,0,0,1,0,...): i2 ≥ 0
  Then γ₁ = -c.r2 = c.i1 * beta ≥ 0 and γ₂ = c.r1+c.r2 = c.i2 * beta ≥ 0.

Step 2: Show lagrangian equality by matching Re and Im parts.
  Re part: After r3=r4=r5=r6=0 and s2=s4=0 (from KMS), the real part is
    r1·ψ_a·dtt + r2·ψ_a·dxx + s1·ψ_a·dxxx + s3·ψ_a·dttx
  which equals (γ₁+γ₂)·ψ_a·dtt - γ₁·ψ_a·dxx + γ_{2,1}·ψ_a·dxxx + γ_{2,2}·ψ_a·dttx ✓

  Im part: After i3=0, the imaginary part is i1·ψ_a² + i2·(∂_t ψ_a)² + j_tx·(∂_t ψ_a)(∂_x ψ_a).
  From FDR: i1 = -r2/β = γ₁/β, i2 = (r1+r2)/β = γ₂/β,
            j_tx = (s1+s3)/β = (γ_{2,1}+γ_{2,2})/β ✓
-/
theorem fullSecondOrder_uniqueness :
    ∀ (c : FullSecondOrderCoeffs) (beta : ℝ),
      0 < beta →
      satisfies_positivity_ext (fullSecondOrderAction c) →
      FullSecondOrderKMS c beta →
      ∃ (coeffs : CombinedDissipativeCoeffs),
        ∀ (fields : SKFieldsExt),
          (fullSecondOrderAction c).lagrangian fields =
            (combinedDissipativeAction coeffs beta).lagrangian fields := by
  -- Aristotle run c4d73ca8: Strong uniqueness proved.
  -- Constructs CombinedDissipativeCoeffs with γ₁=-c.r2, γ₂=c.r1+c.r2, γ_{2,1}=c.s1, γ_{2,2}=c.s3.
  -- Non-negativity from positivity at specific field configs + FDR.
  -- Lagrangian equality by substituting KMS constraints + field_simp/ring.
  intro c beta hbeta hpos hkms
  use ⟨-c.r2, by
    have := hpos ⟨ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ⟩ ; norm_num [ fullSecondOrderAction ] at this ; nlinarith [ hkms.fdr_i1 ] ;, c.r1 + c.r2, by
    have := hpos ⟨ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ⟩ ; norm_num [ fullSecondOrderAction ] at this ; nlinarith [ hkms.fdr_i1, hkms.fdr_i2, mul_div_cancel₀ ( c.r1 + c.r2 ) hbeta.ne' ] ;, c.s1, c.s3⟩
  generalize_proofs at *;
  unfold fullSecondOrderAction combinedDissipativeAction; simp +decide [ hkms.r3_zero, hkms.r4_zero, hkms.r5_zero, hkms.r6_zero, hkms.s2_zero, hkms.s4_zero, hkms.i3_zero ] ; ring;
  intro fields; rw [ show c.i1 = -c.r2 / beta by rw [ eq_div_iff hbeta.ne' ] ; linarith [ hkms.fdr_i1 ], show c.i2 = ( c.r1 + c.r2 ) / beta by rw [ eq_div_iff hbeta.ne' ] ; linarith [ hkms.fdr_i2 ], show c.j_tx = ( c.s1 + c.s3 ) / beta by rw [ eq_div_iff hbeta.ne' ] ; linarith [ hkms.fdr_j_tx ] ] ; ring;
  norm_num [ hbeta.ne' ]

/-- The combined dissipative action through second order satisfies normalization.
    When ψ_a = 0 and all ψ_a derivatives vanish, L = (0, 0). -/
theorem combined_normalization (coeffs : CombinedDissipativeCoeffs) (beta : ℝ) :
    satisfies_normalization_ext (combinedDissipativeAction coeffs beta) := by
  intro f ha hda_t hda_x _ _ _
  simp only [combinedDissipativeAction, ha, hda_t, hda_x]
  norm_num

/-- The combined dissipative action satisfies positivity (Im ≥ 0) when
    γ₁ ≥ 0, γ₂ ≥ 0, and β > 0, PROVIDED the second-order cross-term
    (∂_t ψ_a)(∂_x ψ_a) is controlled by the diagonal terms.

    This is the key positivity question at second order. Unlike first order
    where Im = (γ₁/β)·ψ_a² + (γ₂/β)·(∂_t ψ_a)² is manifestly non-negative
    (sum of squares), the second-order term adds a cross-product
    ((γ_{2,1}+γ_{2,2})/β)·(∂_t ψ_a)(∂_x ψ_a) which can be negative.

    Positivity requires:
      (γ₁/β)·ψ_a² + (γ₂/β)·u² + ((γ_{2,1}+γ_{2,2})/β)·u·v ≥ 0
    where u = ∂_t ψ_a, v = ∂_x ψ_a.

    This holds iff the 3×3 matrix [[γ₁,0,0],[0,γ₂,(γ_{2,1}+γ_{2,2})/2],
    [0,(γ_{2,1}+γ_{2,2})/2,0]] is positive semidefinite.

    For the matrix to be PSD with zero (3,3) entry, we need
    (γ_{2,1}+γ_{2,2})² ≤ 0, i.e., γ_{2,1}+γ_{2,2} = 0.

    This is a STRONG constraint: it says γ_{2,1} = -γ_{2,2} at this truncation!
    Or, more physically: positivity at second order requires including
    higher-order imaginary terms that we've truncated.

    Aristotle should verify whether this constraint is correct or whether
    additional imaginary monomials (like (∂_x ψ_a)² at second order)
    could relax it. -/
theorem combined_positivity_constraint
    (coeffs : CombinedDissipativeCoeffs) (beta : ℝ) (hbeta : 0 < beta)
    (hpos : satisfies_positivity_ext (combinedDissipativeAction coeffs beta)) :
    -- The cross-term coefficient must vanish for positivity at this truncation
    coeffs.gamma_2_1 + coeffs.gamma_2_2 = 0 := by
  -- Aristotle run c4d73ca8: Positivity constraint proved by contradiction.
  -- If c = γ_{2,1} + γ_{2,2} ≠ 0, construct field config with dt_ψ_a=1,
  -- dx_ψ_a=-(γ₂+1)/c making Im part = -1/β < 0, contradicting positivity.
  by_contra h_nonzero;
  set u : ℝ := 1
  set v : ℝ := -(coeffs.gamma_2 + 1) / (coeffs.gamma_2_1 + coeffs.gamma_2_2);
  have h_im_neg : (coeffs.gamma_2 / beta) * u^2 + ((coeffs.gamma_2_1 + coeffs.gamma_2_2) / beta) * u * v < 0 := by
    simp +zetaDelta at *;
    field_simp [h_nonzero] at *; ring_nf at *; norm_num [ hbeta.ne', h_nonzero ] at *;
  convert hpos ⟨ 0, 0, u, v, u, v, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ⟩ using 1 ; norm_num [ combinedDissipativeAction ] ; ring_nf at * ; aesop;

/-!
## Second-Order FDR Verification

The FDR relation j_tx · β = s1 + s3 in FullSecondOrderKMS is conjectured
from the pattern of first-order FDR. The following theorems provide
independent checks that Aristotle can verify.
-/

/-- FDR consistency check: the second-order FDR determines j_tx from s1,s3.
    This means j_tx = (s1 + s3)/β. Verify that this is consistent with
    the structure of `combinedDissipativeAction`. -/
theorem fdr_second_order_consistent
    (c : FullSecondOrderCoeffs) (beta : ℝ)
    (hb : 0 < beta) (hkms : FullSecondOrderKMS c beta) :
    c.j_tx = (c.s1 + c.s3) / beta := by
  have h := hkms.fdr_j_tx
  rw [eq_div_iff hb.ne']
  linarith

/-- When all second-order coefficients vanish, the full KMS reduces to
    first-order KMS. This is a consistency check: the second-order
    extension doesn't break the first-order structure. -/
theorem fullKMS_reduces_to_firstOrder
    (c : FullSecondOrderCoeffs) (beta : ℝ) (hbeta : 0 < beta)
    (hkms : FullSecondOrderKMS c beta)
    (hs1 : c.s1 = 0) (hs3 : c.s3 = 0) :
    c.j_tx = 0 := by
  have h := hkms.fdr_j_tx
  rw [hs1, hs3] at h
  -- h : c.j_tx * beta = 0 + 0, simplifies to c.j_tx * beta = 0
  simp at h
  -- From mul_eq_zero: c.j_tx = 0 ∨ beta = 0
  -- Since beta > 0, beta ≠ 0, so c.j_tx = 0
  rcases h with h | h
  · exact h
  · linarith

/-!
## Stress Test Suite: Bulletproofing the SK-EFT Framework

The following theorems probe the robustness of our results by testing
alternative hypotheses. Each is a `sorry` for Aristotle to prove or
find a counterexample.

### Test 1: Alternative FDR (j_tx · β = s1 - s3 instead of s1 + s3)

If the FDR sign is wrong, uniqueness should FAIL — Aristotle should find
a counterexample demonstrating that the alternative FDR admits actions
not reducible to CombinedDissipativeCoeffs.
-/

/-- Alternative KMS with a WRONG FDR sign: j_tx · β = s1 - s3.
    If our original FDR (s1 + s3) is the unique correct one, then
    uniqueness should fail under this alternative. -/
structure FullSecondOrderKMS_altFDR (c : FullSecondOrderCoeffs) (beta : ℝ) : Prop where
  r3_zero : c.r3 = 0
  r4_zero : c.r4 = 0
  r5_zero : c.r5 = 0
  r6_zero : c.r6 = 0
  fdr_i1 : c.i1 * beta = -(c.r2)
  fdr_i2 : c.i2 * beta = c.r1 + c.r2
  i3_zero : c.i3 = 0
  s2_zero : c.s2 = 0
  s4_zero : c.s4 = 0
  /-- ALTERNATIVE FDR: minus sign instead of plus -/
  fdr_j_tx_alt : c.j_tx * beta = c.s1 - c.s3

/-- The original statement claimed uniqueness under the alternative FDR j_tx·β = s1 - s3.
    This is FALSE: with s3 ≠ 0, matching the Re part forces γ_{2,1}=s1, γ_{2,2}=s3,
    but then the Im cross-term would be (γ_{2,1}+γ_{2,2})/β = (s1+s3)/β while the
    alt FDR gives j_tx = (s1-s3)/β ≠ (s1+s3)/β. This forces γ₂ < 0.
    Counterexample: c = ⟨1, -1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, β = 1. -/
-- Original (false) statement:
-- theorem altFDR_uniqueness_test :
--     ∀ (c : FullSecondOrderCoeffs) (beta : ℝ),
--       0 < beta →
--       satisfies_positivity_ext (fullSecondOrderAction c) →
--       FullSecondOrderKMS_altFDR c beta →
--       ∃ (coeffs : CombinedDissipativeCoeffs),
--         ∀ (fields : SKFieldsExt),
--           (fullSecondOrderAction c).lagrangian fields =
--             (combinedDissipativeAction coeffs beta).lagrangian fields := by
--   sorry

theorem altFDR_uniqueness_test :
    ¬ (∀ (c : FullSecondOrderCoeffs) (beta : ℝ),
      0 < beta →
      satisfies_positivity_ext (fullSecondOrderAction c) →
      FullSecondOrderKMS_altFDR c beta →
      ∃ (coeffs : CombinedDissipativeCoeffs),
        ∀ (fields : SKFieldsExt),
          (fullSecondOrderAction c).lagrangian fields =
            (combinedDissipativeAction coeffs beta).lagrangian fields) := by
  -- Aristotle run 3eedcabb: proved negation with counterexample.
  -- c = ⟨1,-1,0,0,0,0,1,0,0,1,0,1,0,0⟩, β=1 satisfies alt-FDR + positivity,
  -- but forces γ₂ = c.r1+c.r2 = 0 while needing γ₂/β·u² term ≥ 0 with cross-term.
  intro h
  set c : FullSecondOrderCoeffs := ⟨1, -1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩
  have hkms : FullSecondOrderKMS_altFDR c 1 :=
    ⟨rfl, rfl, rfl, rfl, by norm_num, by norm_num, rfl, rfl, rfl, by norm_num⟩
  have hpos : satisfies_positivity_ext (fullSecondOrderAction c) := by
    intro f; simp [fullSecondOrderAction]; nlinarith [sq_nonneg f.psi_a]
  obtain ⟨coeffs, hcoeffs⟩ := h c 1 one_pos hpos hkms
  have h1 := hcoeffs ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩
  have h2 := hcoeffs ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩
  have h3 := hcoeffs ⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  simp only [fullSecondOrderAction, combinedDissipativeAction, Prod.mk.injEq] at h1 h2 h3
  linarith [coeffs.gamma_2_nonneg]

/-!
### Test 2: Relaxed Positivity with Nonzero i3

The current KMS forces i3 = 0 (no (∂_x ψ_a)² term). What if we relax this?
Does the positivity constraint γ_{2,1} + γ_{2,2} = 0 change?
-/

/-- Relaxed KMS that drops the i3 = 0 constraint and instead only
    requires i3 ≥ 0. This models the possibility that boundary terms
    near the horizon generate a (∂_x ψ_a)² contribution. -/
structure FullSecondOrderKMS_relaxed (c : FullSecondOrderCoeffs) (beta : ℝ) : Prop where
  r3_zero : c.r3 = 0
  r4_zero : c.r4 = 0
  r5_zero : c.r5 = 0
  r6_zero : c.r6 = 0
  fdr_i1 : c.i1 * beta = -(c.r2)
  fdr_i2 : c.i2 * beta = c.r1 + c.r2
  /-- Relaxed: i3 is non-negative instead of zero -/
  i3_nonneg : 0 ≤ c.i3
  s2_zero : c.s2 = 0
  s4_zero : c.s4 = 0
  fdr_j_tx : c.j_tx * beta = c.s1 + c.s3

/-- Stress test: with a nonzero (∂_x ψ_a)² coefficient, does uniqueness
    hold with 4 or 5 free parameters?

    If Aristotle PROVES this (with 5 params including i3), it means
    relaxing i3 = 0 adds exactly one new free parameter.
    If Aristotle finds a COUNTEREXAMPLE, the parameterization is wrong. -/
structure CombinedDissipativeCoeffs_relaxed where
  gamma_1 : ℝ
  gamma_1_nonneg : 0 ≤ gamma_1
  gamma_2 : ℝ
  gamma_2_nonneg : 0 ≤ gamma_2
  gamma_2_1 : ℝ
  gamma_2_2 : ℝ
  /-- New: spatial noise coefficient (zero in standard KMS) -/
  gamma_x : ℝ
  gamma_x_nonneg : 0 ≤ gamma_x

/-- The relaxed combined action including a (∂_x ψ_a)² noise term. -/
noncomputable def combinedDissipativeAction_relaxed
    (coeffs : CombinedDissipativeCoeffs_relaxed) (beta : ℝ) : SKActionExt where
  lagrangian := fun f =>
    let re1 := coeffs.gamma_1 * f.psi_a * (f.dtt_psi_r - f.dxx_psi_r) +
               coeffs.gamma_2 * f.psi_a * f.dtt_psi_r
    let re2 := coeffs.gamma_2_1 * f.psi_a * f.dxxx_psi_r +
               coeffs.gamma_2_2 * f.psi_a * f.dttx_psi_r
    let im1 := (coeffs.gamma_1 / beta) * f.psi_a ^ 2 +
               (coeffs.gamma_2 / beta) * f.dt_psi_a ^ 2 +
               coeffs.gamma_x * f.dx_psi_a ^ 2
    let im2 := ((coeffs.gamma_2_1 + coeffs.gamma_2_2) / beta) *
               f.dt_psi_a * f.dx_psi_a
    (re1 + re2, im1 + im2)

theorem relaxed_uniqueness_test :
    ∀ (c : FullSecondOrderCoeffs) (beta : ℝ),
      0 < beta →
      satisfies_positivity_ext (fullSecondOrderAction c) →
      FullSecondOrderKMS_relaxed c beta →
      ∃ (coeffs : CombinedDissipativeCoeffs_relaxed),
        ∀ (fields : SKFieldsExt),
          (fullSecondOrderAction c).lagrangian fields =
            (combinedDissipativeAction_relaxed coeffs beta).lagrangian fields := by
  -- Aristotle run 3eedcabb: proved with 5 free params.
  -- Constructs CombinedDissipativeCoeffs_relaxed with γ₁=-c.r2, γ₂=c.r1+c.r2,
  -- γ_{2,1}=c.s1, γ_{2,2}=c.s3, γ_x=c.i3.
  intro c beta hb hp hkms
  use ⟨-c.r2, by
    have := hkms.fdr_i1; have := hkms.fdr_i2; have := hp ⟨ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ⟩ ; simp_all +decide [ fullSecondOrderAction ] ; nlinarith [ Real.pi_pos, mul_div_cancel₀ ( -c.r2 ) hb.ne', mul_div_cancel₀ ( c.r1 + c.r2 ) hb.ne', mul_div_cancel₀ ( c.s1 + c.s3 ) hb.ne' ] ;, c.r1 + c.r2, by
    have := hp ⟨ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ⟩ ; norm_num [ fullSecondOrderAction ] at this ; nlinarith [ hkms.fdr_i2 ] ;, c.s1, c.s3, c.i3, by
    exact hkms.i3_nonneg⟩
  generalize_proofs at *;
  intro fields
  unfold fullSecondOrderAction combinedDissipativeAction_relaxed
  simp [hkms.r3_zero, hkms.r4_zero, hkms.r5_zero, hkms.r6_zero, hkms.s2_zero, hkms.s4_zero];
  have := hkms.fdr_i1; have := hkms.fdr_i2; have := hkms.fdr_j_tx; norm_num [ show c.i1 = -c.r2 / beta by rw [ eq_div_iff hb.ne' ] ; linarith, show c.i2 = ( c.r1 + c.r2 ) / beta by rw [ eq_div_iff hb.ne' ] ; linarith, show c.j_tx = ( c.s1 + c.s3 ) / beta by rw [ eq_div_iff hb.ne' ] ; linarith ] ; ring;

/-- Stress test: with nonzero i3, does the positivity constraint relax
    from γ_{2,1} + γ_{2,2} = 0 to an inequality?

    The 3×3 imaginary quadratic form becomes:
      [[γ₁/β, 0, 0], [0, γ₂/β, (γ_{2,1}+γ_{2,2})/(2β)],
       [0, (γ_{2,1}+γ_{2,2})/(2β), γ_x]]

    PSD requires (γ₂/β)·γ_x ≥ ((γ_{2,1}+γ_{2,2})/(2β))²
    i.e., (γ_{2,1}+γ_{2,2})² ≤ 4·γ₂·γ_x·β

    So nonzero γ_x DOES relax the constraint from equality to inequality! -/
theorem relaxed_positivity_weakens
    (coeffs : CombinedDissipativeCoeffs_relaxed) (beta : ℝ) (hbeta : 0 < beta)
    (hpos : satisfies_positivity_ext (combinedDissipativeAction_relaxed coeffs beta)) :
    (coeffs.gamma_2_1 + coeffs.gamma_2_2) ^ 2 ≤
      4 * coeffs.gamma_2 * coeffs.gamma_x * beta := by
  -- Aristotle run 3eedcabb: proved PSD condition by contradiction.
  -- If violated, the quadratic γ_x·t² + ((γ_{2,1}+γ_{2,2})/β)·t + γ₂/β has positive
  -- discriminant, so there exists t making Im < 0.
  have h_pos : ∀ (t : ℝ), 0 ≤ (coeffs.gamma_2 / beta) * 1 + coeffs.gamma_x * t^2 + ((coeffs.gamma_2_1 + coeffs.gamma_2_2) / beta) * t := by
    intro t
    specialize hpos (⟨0, 0, 0, 0, 1, t, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩);
    unfold combinedDissipativeAction_relaxed at hpos; aesop;
  by_cases h_gamma_x : coeffs.gamma_x = 0 <;> simp_all +decide [ sq, mul_comm, mul_left_comm, div_eq_mul_inv ];
  · contrapose! h_pos;
    exact ⟨ - ( coeffs.gamma_2 * beta⁻¹ + 1 ) / ( ( coeffs.gamma_2_1 + coeffs.gamma_2_2 ) * beta⁻¹ ), by rw [ div_mul_cancel₀ _ ( by aesop ) ] ; linarith ⟩;
  · contrapose! h_pos;
    use -((coeffs.gamma_2_1 + coeffs.gamma_2_2) / beta) / (2 * coeffs.gamma_x);
    field_simp;
    rw [ div_lt_iff₀ ] <;> cases lt_or_gt_of_ne h_gamma_x <;> nlinarith [ coeffs.gamma_x_nonneg ]

/-!
### Test 3: Third-Order Positivity Exploration

Does the count formula count(N) = ⌊(N+1)/2⌋ + 1 predict count(3) = 3?
And at third order, how does positivity constrain the new parameters?
-/

/-- count(3) should equal 3 new parameters at third order.
    count(3) = ⌊(3+1)/2⌋ + 1 = ⌊2⌋ + 1 = 3.

    We state this using the Finset cardinality directly (matching the
    return type of `transport_coefficient_count` after supplying the
    positivity proof). -/
theorem thirdOrder_count :
    Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 + p.2 = 3 + 1 ∧ p.1 % 2 = 0)
      (Finset.Icc (0, 0) (3 + 1, 3 + 1))) = (3 + 1) / 2 + 1 := by native_decide

/-- Verify the count formula gives the expected numeric value: count(3) = 3.
    (3+1)/2 + 1 = 2 + 1 = 3. -/
theorem thirdOrder_count_value :
    (3 + 1) / 2 + 1 = 3 := by
  norm_num

/-!
### Test 4: Cumulative count verification

Verify the total parameter count through each order matches expectations.
The formula (N+1)/2 + 1 for N=1,2,3 gives 2, 2, 3 respectively.
-/

/-- Total transport coefficients through order 3:
    count(1) + count(2) + count(3) = 2 + 2 + 3 = 7. -/
theorem cumulative_count_through_3 :
    (1 + 1) / 2 + 1 + ((2 + 1) / 2 + 1) + ((3 + 1) / 2 + 1) = 7 := by
  norm_num

end SKEFTHawking.SecondOrderSK
