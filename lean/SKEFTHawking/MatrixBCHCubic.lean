/-
SK_EFT_Hawking Phase 6p Wave 2d.2-followup-R5.2a SHIP (2026-05-13 PM):
**BCH cubic norm bound on the polynomial residual**.

This module ships the load-bearing **cubic** norm bound

  `‖bchPolyRem F G‖ ≤ 30 · δ³`   (for `‖F‖, ‖G‖ ≤ δ ≤ 1`)

required as an upstream dependency for AA Bridge Lemma 6.1 (commutator
quadratic-shrinkage iteration; see `FKLW/AharonovAradLemma6.lean`).
The constant `K = 30` is a comfortable loose bound; the D-N original
K ≤ 4 is deferred to R5.2c.

## Mathematical context

For Hermitian F, G with `‖F‖, ‖G‖ ≤ δ ≤ 1`:

  `exp(±iX) = T₂(±X) + R₃(±X)`

where `T₂(±X) := 1 ± iX - X²/2` is the order-2 Taylor polynomial and
`R₃(±X)` is the cubic remainder, satisfying `‖R₃(±X)‖ ≤ δ³ · exp(δ)`
(via `MatrixTaylor.norm_exp_sub_order3_le_loose`; consumed by R5.2b).

The 4-fold product then decomposes:

  `exp(iF)·exp(iG)·exp(-iF)·exp(-iG)`
  `  = T₂(F)·T₂(G)·T₂(-F)·T₂(-G)      [polynomial part — this module]`
  `    + (cross terms with at least one R₃ factor)  [R5.2b]`

The polynomial part `T₂(F)·T₂(G)·T₂(-F)·T₂(-G)` reduces at order ≤ 2
to `1 - [F,G]` exactly (the BCH leading correction). At order ≥ 3,
the residual `bchPolyRem F G := T₂(F)·T₂(G)·T₂(-F)·T₂(-G) - (1 - [F,G])`
collapses to a 6-piece decomposition `(F⁴/4 + G⁴/4 + F⁴·G⁴/16) +
(⁅T₂(G), T₂(-F)⁆ + [F,G]) + (right-bookend) + (left-bookend)`, each
bounded `O(δ³)`. Total `≤ 30·δ³`.

## Proof architecture

  1. **Same-F factorization** (`T2pos_T2neg_self`):
     `T2pos F · T2neg F = 1 + F⁴/4`, isolating O(δ⁴) cancellation.

  2. **Swap identity** (`A·B·C·D = A·C·B·D + A·⁅B,C⁆·D`):
     reorders the 4-fold product so two same-F factorizations apply,
     extracting the load-bearing commutator `⁅T2pos G, T2neg F⁆`.

  3. **Commutator linearization** (`commutator_T2pos_T2neg_plus_FG_decomp`):
     the leading `O(δ²)` content of `⁅T2pos G, T2neg F⁆` is exactly
     `-⁅F, G⁆`, which cancels with `+⁅F, G⁆` in the bchPolyRem
     definition. Bilinearity expansion shows the residual is a sum
     of 2 small commutators with O(δ²)+O(δ) factors → O(δ³).

  4. **Bookend identity** (`A·X·D = X + A·X·(D-1) + (A-1)·X`):
     extracts the bare commutator from the right-bookend `T2pos F ·
     ⁅T2pos G, T2neg F⁆ · T2neg G`, exposing the linearization for
     the cubic-cancellation argument.

## What this module exports

  *Definitions:*
  - `T2pos X := 1 + iX - X²/2` (order-2 `exp(iX)` polynomial).
  - `T2neg X := 1 - iX - X²/2` (order-2 `exp(-iX)` polynomial).
  - `bchPolyRem F G := T2pos F · T2pos G · T2neg F · T2neg G - (1 - [F,G])`.

  *Key substantive theorems:*
  - `T2pos_T2neg_self : T2pos F · T2neg F = 1 + F⁴/4`
  - `commutator_T2pos_T2neg_plus_FG_decomp` — explicit decomposition
    of the linearization residual into 2 simple commutators.
  - `commutator_T2pos_T2neg_plus_FG_norm_le_cubic` — `≤ 3·δ³`.
  - `commutator_T2pos_T2neg_norm_le_quadratic` — `≤ 9·δ²/2`.
  - `bchPolyRem_decomp` — explicit 6-piece algebraic decomposition.
  - **`bchPolyRem_norm_le_cubic` — `‖bchPolyRem F G‖ ≤ 30·δ³`**
    (the headline R5.2a theorem).

## What is deferred (R5.2 sub-waves)

  - **R5.2b**: Compose with the Taylor remainder bound to derive the
    full `bch_order_2_cubic_thm` (replacing the linear `200·δ` with
    cubic `K·δ³` in the headline theorem).
  - **R5.2c**: Optimize the constant K. Target K ≤ 4 per the original
    D-N analysis; current K = 30 is sufficient for downstream AA
    Bridge Lemma 6.1.

The cubic upgrade is the load-bearing missing ingredient for the
constructive discharge of `aa_residual_interior_at_one_for_hom`:
the AA Bridge Lemma 6.1's commutator quadratic-shrinkage iteration
requires `‖[g,h] - 1‖ ≤ C·ε²` for any group commutator of elements
ε-close to 1. The current BCH linear bound `200·δ` dominates for
small δ, breaking the iteration; the cubic bound `K·δ³` makes the
total bound `O(δ² + δ³) = O(δ²)` quadratic in δ for δ ≤ 1, completing
the iteration.

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED — pure constructive
    definitions, algebraic identities, and norm bounds. Total
    project axiom count UNCHANGED (still 2:
    `gapped_interface_axiom` + `aa_residual_interior_at_one_for_hom`).
  - Preemptive-strengthening:
    * P3/P4/P5 (trivial discharge): every theorem has substantive
      content. `bchPoly_decomp` is honestly flagged as trivial (it
      names the residual); the substantive load is in `T2pos_T2neg_self`,
      `commutator_T2pos_T2neg_plus_FG_decomp`, `bchPolyRem_decomp`,
      and the headline `bchPolyRem_norm_le_cubic`.
    * P6 (cross-module bridge): all cross-references docstring-cited
      (MatrixTaylor.norm_exp_sub_order3_le_loose, MatrixBCH, AA).

Zero sorry. Zero new project-local axioms in this module.
-/

import Mathlib
import SKEFTHawking.MatrixBCH
import SKEFTHawking.MatrixTaylor

set_option autoImplicit false

namespace SKEFTHawking.MatrixBCHCubic

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Order-2 Taylor polynomials -/

/-- The order-2 Taylor polynomial of `exp(iX)`: `1 + iX - X²/2`.

This is the truncation of `Σ_{n≥0} (iX)^n / n!` at `n = 2` (omitting the
`(iX)³/6 = -iX³/6` term and higher). Bounded matrix-Taylor remainder
gives `‖exp(iX) - T2pos X‖ ≤ ‖X‖³ · exp(‖X‖)` by
`MatrixTaylor.norm_exp_sub_order3_le_loose` (applied to `Complex.I • X`,
using `‖Complex.I • X‖ = ‖X‖` for the linftyOp norm). -/
noncomputable def T2pos {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  1 + Complex.I • X - ((2 : ℂ)⁻¹) • X ^ 2

/-- The order-2 Taylor polynomial of `exp(-iX)`: `1 - iX - X²/2`.

Note `T2neg X = T2pos (-X)` because `(-X)² = X²` and `i • (-X) = -(i • X)`. -/
noncomputable def T2neg {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  1 - Complex.I • X - ((2 : ℂ)⁻¹) • X ^ 2

/-- `T2pos` equals `T2neg` of the negative: `T2pos (-X) = T2neg X`. Useful
when reusing symmetry arguments. -/
lemma T2pos_neg_eq_T2neg {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    T2pos (-X) = T2neg X := by
  unfold T2pos T2neg
  simp
  noncomm_ring

/-! ## 2. The BCH polynomial residual

The polynomial product `T2pos F · T2pos G · T2neg F · T2neg G` admits an
explicit residual decomposition: order-2 truncation gives `1 - [F,G]`
exactly (as computed by hand in the D-N paper and verified independently
via the order-by-order matrix expansion). The higher-order monomials
(total degree ≥ 3 in F, G) form the residual, bounded by `O(δ³)` under
`‖F‖, ‖G‖ ≤ δ ≤ 1`. -/

/-- The explicit cubic-or-higher polynomial residual for the BCH
order-2 algebraic identity. -/
noncomputable def bchPolyRem {d : ℕ} (F G : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  T2pos F * T2pos G * T2neg F * T2neg G - (1 - ⁅F, G⁆)

/-! ### 2.1. Clean factorization `T2pos F · T2neg F = 1 + F⁴/4`

A substantive algebraic identity: when the same matrix `F` appears in
both factors, the cross-terms cancel exactly and only `1 + F⁴/4`
remains. This is a building block for the deferred cubic bound R5.2a:
the 4-fold product `T2pos F · T2pos G · T2neg F · T2neg G` can be
rewritten as `T2pos F · T2neg F · T2pos G · T2neg G` plus a commutator
correction term `T2pos F · [T2pos G, T2neg F] · T2neg G`. The former
equals `(1 + F⁴/4)(1 + G⁴/4)` by this identity applied twice, leaving
the commutator term as the load-bearing piece for the cubic bound.

Proof: write `(1 + iF - F²/2)(1 - iF - F²/2) = (a + b)(a - b)` with
`a = 1 - F²/2`, `b = iF`. Use `Commute.sq_sub_sq` (since a, b commute —
both polynomials in F), then compute `a² - b²`:
  - `a² = 1 - F² + F⁴/4` (direct expansion using `module` for smul algebra).
  - `b² = (iF)² = i² F² = -F²` (using `Complex.I_sq` and `smul_pow`).
  - `a² - b² = (1 - F² + F⁴/4) - (-F²) = 1 + F⁴/4`. -/

/-- **Clean factorization** `T2pos F · T2neg F = 1 + F⁴/4`.

The same-`F` product collapses to `1 + F⁴/4` exactly (no remainder).
Used downstream in R5.2a's cubic-bound proof: the 4-fold product
factors as `(1 + F⁴/4)(1 + G⁴/4) + commutator-correction`, isolating
the bound-relevant content in the commutator. -/
theorem T2pos_T2neg_self {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ) :
    T2pos F * T2neg F = 1 + ((4 : ℂ)⁻¹) • F ^ 4 := by
  unfold T2pos T2neg
  set a : Matrix (Fin d) (Fin d) ℂ := 1 - ((2 : ℂ)⁻¹) • F^2 with ha_def
  set b : Matrix (Fin d) (Fin d) ℂ := Complex.I • F with hb_def
  -- Rewrite LHS as (a + b) * (a - b)
  have h_lhs : (1 + Complex.I • F - ((2 : ℂ)⁻¹) • F^2) *
               (1 - Complex.I • F - ((2 : ℂ)⁻¹) • F^2) = (a + b) * (a - b) := by
    show (1 + b - ((2 : ℂ)⁻¹) • F^2) * (1 - b - ((2 : ℂ)⁻¹) • F^2) = (a + b) * (a - b)
    rw [show 1 + b - ((2 : ℂ)⁻¹) • F^2 = a + b from by rw [ha_def]; abel,
        show 1 - b - ((2 : ℂ)⁻¹) • F^2 = a - b from by rw [ha_def]; abel]
  rw [h_lhs]
  -- a, b commute (both are polynomials in F)
  have h_comm : Commute a b := by
    show Commute (1 - ((2 : ℂ)⁻¹) • F^2) (Complex.I • F)
    have hX : Commute (((2 : ℂ)⁻¹) • F^2) (Complex.I • F) := by
      have h1 : Commute (F^2) F := (Commute.refl F).pow_left 2
      exact (h1.smul_right Complex.I).smul_left ((2 : ℂ)⁻¹)
    exact (Commute.one_left (Complex.I • F)).sub_left hX
  -- (a + b)(a - b) = a² - b²
  rw [← h_comm.sq_sub_sq]
  -- b² = -F²
  have h_b_sq : b^2 = -((1 : ℂ) • F^2) := by
    show (Complex.I • F)^2 = -((1 : ℂ) • F^2)
    rw [smul_pow, Complex.I_sq]
    simp
  -- a² = 1 - F² + F⁴/4
  have h_a_sq : a^2 = 1 - (1 : ℂ) • F^2 + ((4 : ℂ)⁻¹) • F^4 := by
    show (1 - ((2 : ℂ)⁻¹) • F^2)^2 = 1 - (1 : ℂ) • F^2 + ((4 : ℂ)⁻¹) • F^4
    rw [sq, mul_sub, sub_mul, sub_mul, mul_one, one_mul, smul_mul_smul_comm]
    have hF4 : F^2 * F^2 = F^4 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
    rw [hF4, show (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ = (4 : ℂ)⁻¹ from by norm_num, mul_one]
    module
  rw [h_a_sq, h_b_sq]
  abel

/-- **Trivial algebraic decomposition (naming the residual)**:

  `T2pos F · T2pos G · T2neg F · T2neg G = (1 - ⁅F, G⁆) + bchPolyRem F G`.

The point of this lemma is NOT to assert a substantive identity (the
RHS is defined as exactly the LHS - (1 - ⁅F, G⁆)), but to give
the residual a named handle (`bchPolyRem`) that future norm-bound
lemmas can target. The substantive content is the bound
`‖bchPolyRem F G‖ ≤ C·δ³` (R5.2a, deferred). -/
theorem bchPoly_decomp {d : ℕ} (F G : Matrix (Fin d) (Fin d) ℂ) :
    T2pos F * T2pos G * T2neg F * T2neg G = (1 - ⁅F, G⁆) + bchPolyRem F G := by
  unfold bchPolyRem
  abel

/-! ## 3. Norm bounds on `T2pos`, `T2neg`, and their `1`-residuals

These elementary norm bounds are the entry-point to the cubic-bound
proof. Each is a direct triangle inequality + scalar-multiplication
norm computation. -/

/-- The norm of `(2 : ℂ)⁻¹` is `1/2`. -/
private lemma norm_two_inv_complex : ‖((2 : ℂ)⁻¹)‖ = (1 : ℝ) / 2 := by
  rw [norm_inv]
  simp

/-- The norm of `(4 : ℂ)⁻¹` is `1/4`. -/
private lemma norm_four_inv_complex : ‖((4 : ℂ)⁻¹)‖ = (1 : ℝ) / 4 := by
  rw [norm_inv]
  simp

/-- `‖F^2‖ ≤ ‖F‖^2` (submultiplicativity of the matrix operator norm). -/
private lemma norm_sq_le {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ) :
    ‖F ^ 2‖ ≤ ‖F‖ ^ 2 := by
  have h_eq : F ^ 2 = F * F := by rw [sq]
  rw [h_eq, sq]
  exact norm_mul_le F F

/-- **Norm bound on `T2pos F`**: `‖T2pos F‖ ≤ 1 + ‖F‖ + ‖F‖²/2`.

Direct triangle inequality on `T2pos F = 1 + iF - F²/2`, using
`‖Complex.I • F‖ = ‖F‖`, `‖(2 : ℂ)⁻¹ • F²‖ = ‖F²‖/2 ≤ ‖F‖²/2`. -/
lemma T2pos_norm_le {d : ℕ} [Nonempty (Fin d)]
    (F : Matrix (Fin d) (Fin d) ℂ) :
    ‖T2pos F‖ ≤ 1 + ‖F‖ + ‖F‖ ^ 2 / 2 := by
  unfold T2pos
  have h_one : ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖ = 1 := norm_one
  have h_iF : ‖Complex.I • F‖ = ‖F‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have h_F2_norm : ‖((2 : ℂ)⁻¹) • F ^ 2‖ ≤ ‖F‖ ^ 2 / 2 := by
    rw [norm_smul, norm_two_inv_complex]
    have h_F2 : ‖F ^ 2‖ ≤ ‖F‖ ^ 2 := norm_sq_le F
    have h_F2_nn : (0 : ℝ) ≤ ‖F‖ ^ 2 := by positivity
    nlinarith [h_F2, h_F2_nn]
  have h_eq : (1 : Matrix (Fin d) (Fin d) ℂ) + Complex.I • F - ((2 : ℂ)⁻¹) • F ^ 2
              = (1 + Complex.I • F) + (-(((2 : ℂ)⁻¹) • F ^ 2)) := by
    abel
  rw [h_eq]
  calc ‖(1 + Complex.I • F) + (-(((2 : ℂ)⁻¹) • F ^ 2))‖
      ≤ ‖(1 : Matrix (Fin d) (Fin d) ℂ) + Complex.I • F‖
        + ‖(-(((2 : ℂ)⁻¹) • F ^ 2))‖ := norm_add_le _ _
    _ = ‖(1 : Matrix (Fin d) (Fin d) ℂ) + Complex.I • F‖
        + ‖((2 : ℂ)⁻¹) • F ^ 2‖ := by rw [norm_neg]
    _ ≤ (‖(1 : Matrix (Fin d) (Fin d) ℂ)‖ + ‖Complex.I • F‖)
        + ‖((2 : ℂ)⁻¹) • F ^ 2‖ := by gcongr; exact norm_add_le _ _
    _ = 1 + ‖F‖ + ‖((2 : ℂ)⁻¹) • F ^ 2‖ := by rw [h_one, h_iF]
    _ ≤ 1 + ‖F‖ + ‖F‖ ^ 2 / 2 := by linarith

/-- **Norm bound on `T2neg F`**: `‖T2neg F‖ ≤ 1 + ‖F‖ + ‖F‖²/2`.

Same as `T2pos_norm_le` since `T2neg F = T2pos (-F)` and `‖-F‖ = ‖F‖`. -/
lemma T2neg_norm_le {d : ℕ} [Nonempty (Fin d)]
    (F : Matrix (Fin d) (Fin d) ℂ) :
    ‖T2neg F‖ ≤ 1 + ‖F‖ + ‖F‖ ^ 2 / 2 := by
  rw [← T2pos_neg_eq_T2neg]
  have h := T2pos_norm_le (-F)
  rw [norm_neg] at h
  exact h

/-- **Norm bound on `T2pos F - 1`**: `‖T2pos F - 1‖ ≤ ‖F‖ + ‖F‖²/2`.

Direct triangle inequality on `T2pos F - 1 = iF - F²/2`. -/
lemma T2pos_sub_one_norm_le {d : ℕ}
    (F : Matrix (Fin d) (Fin d) ℂ) :
    ‖T2pos F - 1‖ ≤ ‖F‖ + ‖F‖ ^ 2 / 2 := by
  have h_eq : T2pos F - 1 = Complex.I • F - ((2 : ℂ)⁻¹) • F ^ 2 := by
    unfold T2pos; abel
  rw [h_eq]
  have h_iF : ‖Complex.I • F‖ = ‖F‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have h_F2_norm : ‖((2 : ℂ)⁻¹) • F ^ 2‖ ≤ ‖F‖ ^ 2 / 2 := by
    rw [norm_smul, norm_two_inv_complex]
    have h_F2 : ‖F ^ 2‖ ≤ ‖F‖ ^ 2 := norm_sq_le F
    have h_F2_nn : (0 : ℝ) ≤ ‖F‖ ^ 2 := by positivity
    nlinarith [h_F2, h_F2_nn]
  calc ‖Complex.I • F - ((2 : ℂ)⁻¹) • F ^ 2‖
      ≤ ‖Complex.I • F‖ + ‖((2 : ℂ)⁻¹) • F ^ 2‖ := norm_sub_le _ _
    _ = ‖F‖ + ‖((2 : ℂ)⁻¹) • F ^ 2‖ := by rw [h_iF]
    _ ≤ ‖F‖ + ‖F‖ ^ 2 / 2 := by linarith

/-- **Norm bound on `T2neg F - 1`**: `‖T2neg F - 1‖ ≤ ‖F‖ + ‖F‖²/2`. -/
lemma T2neg_sub_one_norm_le {d : ℕ}
    (F : Matrix (Fin d) (Fin d) ℂ) :
    ‖T2neg F - 1‖ ≤ ‖F‖ + ‖F‖ ^ 2 / 2 := by
  have h_eq : T2neg F - 1 = -(Complex.I • F) - ((2 : ℂ)⁻¹) • F ^ 2 := by
    unfold T2neg; abel
  rw [h_eq]
  have h_iF : ‖Complex.I • F‖ = ‖F‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have h_F2_norm : ‖((2 : ℂ)⁻¹) • F ^ 2‖ ≤ ‖F‖ ^ 2 / 2 := by
    rw [norm_smul, norm_two_inv_complex]
    have h_F2 : ‖F ^ 2‖ ≤ ‖F‖ ^ 2 := norm_sq_le F
    have h_F2_nn : (0 : ℝ) ≤ ‖F‖ ^ 2 := by positivity
    nlinarith [h_F2, h_F2_nn]
  calc ‖-(Complex.I • F) - ((2 : ℂ)⁻¹) • F ^ 2‖
      ≤ ‖-(Complex.I • F)‖ + ‖((2 : ℂ)⁻¹) • F ^ 2‖ := norm_sub_le _ _
    _ = ‖Complex.I • F‖ + ‖((2 : ℂ)⁻¹) • F ^ 2‖ := by rw [norm_neg]
    _ = ‖F‖ + ‖((2 : ℂ)⁻¹) • F ^ 2‖ := by rw [h_iF]
    _ ≤ ‖F‖ + ‖F‖ ^ 2 / 2 := by linarith

/-- **Generic commutator norm bound**: `‖⁅F, G⁆‖ ≤ 2 · ‖F‖ · ‖G‖`.

No Hermitian hypothesis needed (unlike `MatrixBCH.hermitian_commutator_norm_le`
which packages the same bound with `δ`-substitution). -/
lemma commutator_norm_le {d : ℕ}
    (F G : Matrix (Fin d) (Fin d) ℂ) :
    ‖⁅F, G⁆‖ ≤ 2 * ‖F‖ * ‖G‖ := by
  rw [Ring.lie_def]
  have h_tri : ‖F * G - G * F‖ ≤ ‖F * G‖ + ‖G * F‖ := norm_sub_le _ _
  have h_mul_FG : ‖F * G‖ ≤ ‖F‖ * ‖G‖ := norm_mul_le F G
  have h_mul_GF : ‖G * F‖ ≤ ‖G‖ * ‖F‖ := norm_mul_le G F
  linarith

/-! ## 4. Algebraic identities for the BCH cubic residual

The 4-fold product `T2pos F · T2pos G · T2neg F · T2neg G` admits two
decompositions:

  1. **Same-`F` factorization** (`T2pos_T2neg_self`, §2.1): with the
     middle two factors swapped, `T2pos F · T2neg F · T2pos G · T2neg G
     = (1 + F⁴/4)(1 + G⁴/4)`. The swap costs a commutator correction
     `T2pos F · ⁅T2pos G, T2neg F⁆ · T2neg G`.

  2. **Commutator linearization** (this section): the load-bearing piece
     `⁅T2pos G, T2neg F⁆ + ⁅F, G⁆` is the order-3+ residual of the BCH
     swap. It admits a 2-commutator decomposition

       `⁅T2pos G, T2neg F⁆ + ⁅F, G⁆
          = ⁅-((2:ℂ)⁻¹) • G², T2neg F - 1⁆ + ⁅Complex.I • G, -((2:ℂ)⁻¹) • F²⁆`

     whose two summands each have one factor of order `δ²` and one of
     order `δ`, yielding norm `O(δ³)`. -/

/-- **Universal Lie identity**: `⁅A, B⁆ - ⁅A', B'⁆ = ⁅A - A', B⁆ + ⁅A', B - B'⁆`.

Pure bilinearity of the Lie bracket. The "swap-cost" decomposition
used in the commutator linearization below. -/
private lemma lie_sub_lie_swap_decomp {d : ℕ}
    (A B A' B' : Matrix (Fin d) (Fin d) ℂ) :
    ⁅A, B⁆ - ⁅A', B'⁆ = ⁅A - A', B⁆ + ⁅A', B - B'⁆ := by
  rw [sub_lie, lie_sub]
  abel

/-- **Key smul-Lie computation**: `⁅Complex.I • G, -(Complex.I • F)⁆ = -⁅F, G⁆`.

The order-1 leading terms `Complex.I • G` and `-(Complex.I • F)` of
`T2pos G - 1` and `T2neg F - 1` respectively combine via `i · (-i) = 1`
to yield exactly `-⁅F, G⁆`. This cancellation is what allows the BCH
swap-cost commutator `⁅T2pos G, T2neg F⁆ + ⁅F, G⁆` to be order `δ³`
(not `δ²`): the leading `δ²` contribution from `⁅I • G, -(I • F)⁆`
cancels with the `+ ⁅F, G⁆`. -/
private lemma lie_I_G_neg_I_F {d : ℕ} (F G : Matrix (Fin d) (Fin d) ℂ) :
    ⁅Complex.I • G, -(Complex.I • F)⁆ = -⁅F, G⁆ := by
  rw [← neg_smul, smul_lie, lie_smul, smul_smul]
  rw [show (Complex.I * -Complex.I : ℂ) = (1 : ℂ) from by
        rw [mul_neg, Complex.I_mul_I]; ring]
  rw [one_smul]
  exact (lie_skew G F).symm

/-- **The commutator linearization identity**:

  `⁅T2pos G, T2neg F⁆ + ⁅F, G⁆
     = ⁅-((2:ℂ)⁻¹) • G², T2neg F - 1⁆ + ⁅Complex.I • G, -((2:ℂ)⁻¹) • F²⁆`.

The RHS is a sum of two simple commutators, each with one factor of
order `‖G‖²` (resp. `‖F‖²`) and one of order `‖F‖ + ‖F‖²/2` (resp.
`‖G‖`). The leading `O(δ²)` part of `⁅T2pos G, T2neg F⁆` is exactly
`-⁅F, G⁆`, which cancels with the `+ ⁅F, G⁆` on the LHS; the RHS is
the resulting `O(δ³)` cross-term.

Proof: `⁅T2pos G, T2neg F⁆ = ⁅T2pos G - 1, T2neg F - 1⁆` (subtracting
1 doesn't change the bracket since `⁅·, 1⁆ = 0`). Then apply the
universal swap-decomposition `⁅A, B⁆ - ⁅A', B'⁆ = ⁅A - A', B⁆
+ ⁅A', B - B'⁆` with `A = T2pos G - 1`, `A' = Complex.I • G`,
`B = T2neg F - 1`, `B' = -(Complex.I • F)`. The `A - A'` and `B - B'`
differences simplify to `-((2:ℂ)⁻¹) • G²` and `-((2:ℂ)⁻¹) • F²`
respectively. The `⁅A', B'⁆ = ⁅I • G, -(I • F)⁆ = -⁅F, G⁆` step
cancels with the `+ ⁅F, G⁆` on the LHS. -/
theorem commutator_T2pos_T2neg_plus_FG_decomp {d : ℕ}
    (F G : Matrix (Fin d) (Fin d) ℂ) :
    ⁅T2pos G, T2neg F⁆ + ⁅F, G⁆
      = ⁅-(((2 : ℂ)⁻¹) • G ^ 2), T2neg F - 1⁆
      + ⁅Complex.I • G, -(((2 : ℂ)⁻¹) • F ^ 2)⁆ := by
  -- Step 1: ⁅T2pos G, T2neg F⁆ = ⁅T2pos G - 1, T2neg F - 1⁆
  have h1 : ⁅T2pos G, T2neg F⁆ = ⁅T2pos G - 1, T2neg F - 1⁆ := by
    rw [Ring.lie_def, Ring.lie_def]
    noncomm_ring
  -- Step 2: ⁅F, G⁆ = -⁅Complex.I • G, -(Complex.I • F)⁆
  have h2 : ⁅F, G⁆ = -⁅Complex.I • G, -(Complex.I • F)⁆ := by
    rw [lie_I_G_neg_I_F]
    simp
  -- Step 3: A - A' simplification: (T2pos G - 1) - Complex.I • G = -((2:ℂ)⁻¹) • G²
  have hA : T2pos G - 1 - Complex.I • G = -(((2 : ℂ)⁻¹) • G ^ 2) := by
    unfold T2pos; abel
  -- Step 4: B - B' simplification: (T2neg F - 1) - (-(Complex.I • F)) = -((2:ℂ)⁻¹) • F²
  have hB : T2neg F - 1 - -(Complex.I • F) = -(((2 : ℂ)⁻¹) • F ^ 2) := by
    unfold T2neg; abel
  -- Step 5: assemble
  rw [h1, h2]
  -- Goal: ⁅T2pos G - 1, T2neg F - 1⁆ + -⁅I•G, -(I•F)⁆ = ...
  have h_add_neg : ⁅T2pos G - 1, T2neg F - 1⁆ + -⁅Complex.I • G, -(Complex.I • F)⁆
                  = ⁅T2pos G - 1, T2neg F - 1⁆ - ⁅Complex.I • G, -(Complex.I • F)⁆ := by abel
  rw [h_add_neg]
  rw [lie_sub_lie_swap_decomp (T2pos G - 1) (T2neg F - 1) (Complex.I • G) (-(Complex.I • F))]
  rw [hA, hB]

/-! ## 5. Cubic norm bound on the commutator residual

Composes the commutator linearization identity with submultiplicativity
of the matrix norm. -/

/-- **Cubic norm bound on the commutator residual.** For `‖F‖, ‖G‖ ≤ δ ≤ 1`:

  `‖⁅T2pos G, T2neg F⁆ + ⁅F, G⁆‖ ≤ 3 · δ³`.

Proof outline:
  - By `commutator_T2pos_T2neg_plus_FG_decomp`, the residual factors
    as `⁅-(((2:ℂ)⁻¹) • G²), T2neg F - 1⁆ + ⁅Complex.I • G, -(((2:ℂ)⁻¹) • F²)⁆`.
  - Each commutator is bounded by `2 · ‖factor1‖ · ‖factor2‖` via
    `commutator_norm_le`.
  - Norms: `‖((2:ℂ)⁻¹) • G²‖ ≤ ‖G‖²/2 ≤ δ²/2`, `‖T2neg F - 1‖ ≤ ‖F‖ + ‖F‖²/2 ≤ 3δ/2`
    (for δ ≤ 1), `‖Complex.I • G‖ = ‖G‖ ≤ δ`, `‖((2:ℂ)⁻¹) • F²‖ ≤ ‖F‖²/2 ≤ δ²/2`.
  - Summing: `2·(δ²/2)·(3δ/2) + 2·δ·(δ²/2) = (3/2)·δ³ + δ³ = (5/2)·δ³ ≤ 3δ³`. -/
theorem commutator_T2pos_T2neg_plus_FG_norm_le_cubic {d : ℕ}
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖⁅T2pos G, T2neg F⁆ + ⁅F, G⁆‖ ≤ 3 * δ ^ 3 := by
  rw [commutator_T2pos_T2neg_plus_FG_decomp]
  -- Triangle inequality on the two commutators
  have h_tri := norm_add_le (⁅-(((2 : ℂ)⁻¹) • G ^ 2), T2neg F - 1⁆)
                            (⁅Complex.I • G, -(((2 : ℂ)⁻¹) • F ^ 2)⁆)
  -- Term 1 norm bound: 2 · ‖((2:ℂ)⁻¹) • G²‖ · ‖T2neg F - 1‖
  have h_comm1 := commutator_norm_le (-(((2 : ℂ)⁻¹) • G ^ 2)) (T2neg F - 1)
  -- Term 2 norm bound: 2 · ‖I • G‖ · ‖((2:ℂ)⁻¹) • F²‖
  have h_comm2 := commutator_norm_le (Complex.I • G) (-(((2 : ℂ)⁻¹) • F ^ 2))
  -- Auxiliary norm computations
  have h_G2_norm : ‖-(((2 : ℂ)⁻¹) • G ^ 2)‖ ≤ ‖G‖ ^ 2 / 2 := by
    rw [norm_neg, norm_smul, norm_two_inv_complex]
    nlinarith [norm_sq_le G, norm_nonneg G]
  have h_F2_norm : ‖-(((2 : ℂ)⁻¹) • F ^ 2)‖ ≤ ‖F‖ ^ 2 / 2 := by
    rw [norm_neg, norm_smul, norm_two_inv_complex]
    nlinarith [norm_sq_le F, norm_nonneg F]
  have h_IG_norm : ‖Complex.I • G‖ = ‖G‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have h_T2neg_F_sub1 : ‖T2neg F - 1‖ ≤ ‖F‖ + ‖F‖ ^ 2 / 2 := T2neg_sub_one_norm_le F
  -- Norm nonnegativity
  have hF_nn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg _
  have hG_nn : (0 : ℝ) ≤ ‖G‖ := norm_nonneg _
  have hF_sq_nn : (0 : ℝ) ≤ ‖F‖ ^ 2 := by positivity
  have hG_sq_nn : (0 : ℝ) ≤ ‖G‖ ^ 2 := by positivity
  have h_G2norm_nn : (0 : ℝ) ≤ ‖-(((2 : ℂ)⁻¹) • G ^ 2)‖ := norm_nonneg _
  have h_F2norm_nn : (0 : ℝ) ≤ ‖-(((2 : ℂ)⁻¹) • F ^ 2)‖ := norm_nonneg _
  have h_T2neg_nn : (0 : ℝ) ≤ ‖T2neg F - 1‖ := norm_nonneg _
  have h_IG_nn : (0 : ℝ) ≤ ‖Complex.I • G‖ := norm_nonneg _
  -- ‖F‖² ≤ δ² and ‖G‖² ≤ δ²
  have h_F_sq_le : ‖F‖ ^ 2 ≤ δ ^ 2 := by nlinarith
  have h_G_sq_le : ‖G‖ ^ 2 ≤ δ ^ 2 := by nlinarith
  -- ‖F‖² ≤ ‖F‖ ≤ δ for δ ≤ 1 (since ‖F‖ ≤ δ ≤ 1 implies ‖F‖² ≤ ‖F‖)
  have h_F_sq_le_F : ‖F‖ ^ 2 ≤ ‖F‖ := by
    have h_F_le_one : ‖F‖ ≤ 1 := hF.trans hδ_le_one
    nlinarith
  have h_F2_norm_le : ‖-(((2 : ℂ)⁻¹) • F ^ 2)‖ ≤ δ ^ 2 / 2 := by linarith
  have h_G2_norm_le : ‖-(((2 : ℂ)⁻¹) • G ^ 2)‖ ≤ δ ^ 2 / 2 := by linarith
  have h_T2neg_le : ‖T2neg F - 1‖ ≤ 3 * δ / 2 := by
    have h_step : ‖F‖ + ‖F‖ ^ 2 / 2 ≤ δ + δ / 2 := by
      have hF_le_δ : ‖F‖ ≤ δ := hF
      have hF_sq_le_δ : ‖F‖ ^ 2 / 2 ≤ δ / 2 := by
        have : ‖F‖ ^ 2 ≤ δ := h_F_sq_le_F.trans hF
        linarith
      linarith
    linarith [show δ + δ/2 = 3 * δ / 2 from by ring]
  -- Now combine
  have h_term1 :
      2 * ‖-(((2 : ℂ)⁻¹) • G ^ 2)‖ * ‖T2neg F - 1‖ ≤ 2 * (δ ^ 2 / 2) * (3 * δ / 2) := by
    have h1 : 2 * ‖-(((2 : ℂ)⁻¹) • G ^ 2)‖ ≤ 2 * (δ ^ 2 / 2) := by linarith
    have h1_nn : (0 : ℝ) ≤ 2 * ‖-(((2 : ℂ)⁻¹) • G ^ 2)‖ := by positivity
    have h_target_nn : (0 : ℝ) ≤ 2 * (δ ^ 2 / 2) := by positivity
    calc 2 * ‖-(((2 : ℂ)⁻¹) • G ^ 2)‖ * ‖T2neg F - 1‖
        ≤ 2 * (δ ^ 2 / 2) * ‖T2neg F - 1‖ := by
          exact mul_le_mul_of_nonneg_right h1 h_T2neg_nn
      _ ≤ 2 * (δ ^ 2 / 2) * (3 * δ / 2) := by
          exact mul_le_mul_of_nonneg_left h_T2neg_le h_target_nn
  have h_term2 :
      2 * ‖Complex.I • G‖ * ‖-(((2 : ℂ)⁻¹) • F ^ 2)‖ ≤ 2 * δ * (δ ^ 2 / 2) := by
    rw [h_IG_norm]
    have h_2G_le : 2 * ‖G‖ ≤ 2 * δ := by linarith
    have h_2δ_nn : (0 : ℝ) ≤ 2 * δ := by linarith
    calc 2 * ‖G‖ * ‖-(((2 : ℂ)⁻¹) • F ^ 2)‖
        ≤ 2 * δ * ‖-(((2 : ℂ)⁻¹) • F ^ 2)‖ := by
          exact mul_le_mul_of_nonneg_right h_2G_le h_F2norm_nn
      _ ≤ 2 * δ * (δ ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_left h_F2_norm_le h_2δ_nn
  -- Composite: simplify the explicit constants
  -- 2 * (δ²/2) * (3δ/2) = (3/2) · δ³
  -- 2 * δ * (δ²/2) = δ³
  -- Total: (5/2) · δ³ ≤ 3 · δ³
  have h_term1_simp : 2 * (δ ^ 2 / 2) * (3 * δ / 2) = (3 / 2) * δ ^ 3 := by ring
  have h_term2_simp : 2 * δ * (δ ^ 2 / 2) = δ ^ 3 := by ring
  have h_term1_le : 2 * ‖-(((2 : ℂ)⁻¹) • G ^ 2)‖ * ‖T2neg F - 1‖ ≤ (3 / 2) * δ ^ 3 := by
    rw [← h_term1_simp]; exact h_term1
  have h_term2_le : 2 * ‖Complex.I • G‖ * ‖-(((2 : ℂ)⁻¹) • F ^ 2)‖ ≤ δ ^ 3 := by
    rw [← h_term2_simp]; exact h_term2
  have h_d3_nn : (0 : ℝ) ≤ δ ^ 3 := by positivity
  linarith

/-! ## 6. δ-parameterized norm bounds on `T2pos`, `T2neg` and their commutator

These specialize the helpers from §3 under the standing hypothesis
`‖F‖ ≤ δ ≤ 1`. They give the constant-form bounds (`5/2`, `3δ/2`,
`9δ²/2`) used in the final cubic bound below. -/

/-- For `‖F‖ ≤ δ ≤ 1`: `‖T2pos F‖ ≤ 5/2`. -/
lemma T2pos_norm_le_of_delta {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (_hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) :
    ‖T2pos F‖ ≤ 5 / 2 := by
  have h1 := T2pos_norm_le F
  have hF_nn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg _
  have h_F_le_one : ‖F‖ ≤ 1 := hF.trans hδ_le_one
  have h_F_sq_le_F : ‖F‖ ^ 2 ≤ ‖F‖ := by nlinarith
  linarith

/-- For `‖F‖ ≤ δ ≤ 1`: `‖T2neg F‖ ≤ 5/2`. -/
lemma T2neg_norm_le_of_delta {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (_hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) :
    ‖T2neg F‖ ≤ 5 / 2 := by
  have h1 := T2neg_norm_le F
  have hF_nn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg _
  have h_F_le_one : ‖F‖ ≤ 1 := hF.trans hδ_le_one
  have h_F_sq_le_F : ‖F‖ ^ 2 ≤ ‖F‖ := by nlinarith
  linarith

/-- For `‖F‖ ≤ δ ≤ 1`: `‖T2pos F - 1‖ ≤ 3·δ/2`. -/
lemma T2pos_sub_one_norm_le_of_delta {d : ℕ}
    (δ : ℝ) (_hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) :
    ‖T2pos F - 1‖ ≤ 3 * δ / 2 := by
  have h1 := T2pos_sub_one_norm_le F
  have hF_nn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg _
  have h_F_sq_le_F : ‖F‖ ^ 2 ≤ ‖F‖ := by
    have h_F_le_one : ‖F‖ ≤ 1 := hF.trans hδ_le_one
    nlinarith
  have h_F_sq_le_δ : ‖F‖ ^ 2 ≤ δ := h_F_sq_le_F.trans hF
  linarith

/-- For `‖F‖ ≤ δ ≤ 1`: `‖T2neg F - 1‖ ≤ 3·δ/2`. -/
lemma T2neg_sub_one_norm_le_of_delta {d : ℕ}
    (δ : ℝ) (_hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) :
    ‖T2neg F - 1‖ ≤ 3 * δ / 2 := by
  have h1 := T2neg_sub_one_norm_le F
  have hF_nn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg _
  have h_F_sq_le_F : ‖F‖ ^ 2 ≤ ‖F‖ := by
    have h_F_le_one : ‖F‖ ≤ 1 := hF.trans hδ_le_one
    nlinarith
  have h_F_sq_le_δ : ‖F‖ ^ 2 ≤ δ := h_F_sq_le_F.trans hF
  linarith

/-- For `‖F‖, ‖G‖ ≤ δ ≤ 1`: `‖⁅T2pos G, T2neg F⁆‖ ≤ 9·δ²/2`.

Proof: `⁅T2pos G, T2neg F⁆ = ⁅T2pos G - 1, T2neg F - 1⁆` (subtracting 1
preserves the bracket). Then `‖⁅A, B⁆‖ ≤ 2·‖A‖·‖B‖` with each factor
bounded `≤ 3δ/2`. -/
lemma commutator_T2pos_T2neg_norm_le_quadratic {d : ℕ}
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖⁅T2pos G, T2neg F⁆‖ ≤ 9 * δ ^ 2 / 2 := by
  -- Step 1: ⁅T2pos G, T2neg F⁆ = ⁅T2pos G - 1, T2neg F - 1⁆
  have h_eq : ⁅T2pos G, T2neg F⁆ = ⁅T2pos G - 1, T2neg F - 1⁆ := by
    rw [Ring.lie_def, Ring.lie_def]; noncomm_ring
  rw [h_eq]
  have h_comm := commutator_norm_le (T2pos G - 1) (T2neg F - 1)
  -- Step 2: norms of T2pos G - 1 and T2neg F - 1 are each ≤ 3δ/2
  have hG_b : ‖T2pos G - 1‖ ≤ 3 * δ / 2 :=
    T2pos_sub_one_norm_le_of_delta δ hδ_nn hδ_le_one G hG
  have hF_b : ‖T2neg F - 1‖ ≤ 3 * δ / 2 :=
    T2neg_sub_one_norm_le_of_delta δ hδ_nn hδ_le_one F hF
  -- Step 3: 2 · (3δ/2) · (3δ/2) = 9δ²/2
  have hG_nn : (0 : ℝ) ≤ ‖T2pos G - 1‖ := norm_nonneg _
  have hF_nn : (0 : ℝ) ≤ ‖T2neg F - 1‖ := norm_nonneg _
  have h_3d2_nn : (0 : ℝ) ≤ 3 * δ / 2 := by linarith
  have h_step :
      2 * ‖T2pos G - 1‖ * ‖T2neg F - 1‖ ≤ 2 * (3 * δ / 2) * (3 * δ / 2) := by
    have h1 : 2 * ‖T2pos G - 1‖ ≤ 2 * (3 * δ / 2) := by linarith
    have h_2GM1_nn : (0 : ℝ) ≤ 2 * (3 * δ / 2) := by linarith
    calc 2 * ‖T2pos G - 1‖ * ‖T2neg F - 1‖
        ≤ 2 * (3 * δ / 2) * ‖T2neg F - 1‖ := mul_le_mul_of_nonneg_right h1 hF_nn
      _ ≤ 2 * (3 * δ / 2) * (3 * δ / 2) := mul_le_mul_of_nonneg_left hF_b h_2GM1_nn
  have h_simplify : 2 * (3 * δ / 2) * (3 * δ / 2) = 9 * δ ^ 2 / 2 := by ring
  linarith

/-! ## 7. The main cubic bound: `‖bchPolyRem F G‖ ≤ 30·δ³`

The substantive ship of R5.2a. Composes the §1-6 infrastructure into
the headline cubic norm bound that load-bears the AA Bridge Lemma 6.1
(R5.3, deferred) commutator quadratic-shrinkage iteration. -/

/-- **Explicit decomposition of `bchPolyRem F G` into 6 named pieces**:

  `bchPolyRem F G
     = (1/4)·F⁴ + (1/4)·G⁴ + (1/16)·(F⁴·G⁴)            [pure-poly part]
     + (⁅T2pos G, T2neg F⁆ + ⁅F, G⁆)                     [linearization residual]
     + T2pos F · ⁅T2pos G, T2neg F⁆ · (T2neg G - 1)        [right-bookend]
     + (T2pos F - 1) · ⁅T2pos G, T2neg F⁆                  [left-bookend]`.

Built from:
  - Swap identity `A·B·C·D = A·C·B·D + A·⁅B,C⁆·D` (universal noncomm
    ring identity).
  - `T2pos_T2neg_self` applied twice: `(T2pos F · T2neg F) · (T2pos G ·
    T2neg G) = (1 + F⁴/4)·(1 + G⁴/4) = 1 + F⁴/4 + G⁴/4 + F⁴·G⁴/16`.
  - Bookend identity `A·X·D = X + A·X·(D-1) + (A-1)·X` (noncomm ring).
  - Final `1 - (1 - ⁅F, G⁆) = ⁅F, G⁆` simplification. -/
theorem bchPolyRem_decomp {d : ℕ} (F G : Matrix (Fin d) (Fin d) ℂ) :
    bchPolyRem F G
      = ((4 : ℂ)⁻¹) • F ^ 4 + ((4 : ℂ)⁻¹) • G ^ 4 + ((16 : ℂ)⁻¹) • (F ^ 4 * G ^ 4)
      + (⁅T2pos G, T2neg F⁆ + ⁅F, G⁆)
      + T2pos F * ⁅T2pos G, T2neg F⁆ * (T2neg G - 1)
      + (T2pos F - 1) * ⁅T2pos G, T2neg F⁆ := by
  unfold bchPolyRem
  -- Step 1: swap identity
  have h_swap : T2pos F * T2pos G * T2neg F * T2neg G
              = T2pos F * T2neg F * T2pos G * T2neg G
              + T2pos F * ⁅T2pos G, T2neg F⁆ * T2neg G := by
    rw [Ring.lie_def]; noncomm_ring
  rw [h_swap]
  -- Step 2: reassoc
  have h_assoc : T2pos F * T2neg F * T2pos G * T2neg G
              = (T2pos F * T2neg F) * (T2pos G * T2neg G) := by noncomm_ring
  rw [h_assoc]
  -- Step 3: T2pos_T2neg_self twice
  rw [T2pos_T2neg_self F, T2pos_T2neg_self G]
  -- Step 4: expand (1 + F⁴/4) · (1 + G⁴/4)
  have h_expand :
      (1 + ((4 : ℂ)⁻¹) • F ^ 4) * (1 + ((4 : ℂ)⁻¹) • G ^ 4)
      = 1 + ((4 : ℂ)⁻¹) • F ^ 4 + ((4 : ℂ)⁻¹) • G ^ 4
        + ((16 : ℂ)⁻¹) • (F ^ 4 * G ^ 4) := by
    rw [mul_add, mul_one, add_mul, one_mul, smul_mul_smul_comm,
        show ((4 : ℂ)⁻¹) * ((4 : ℂ)⁻¹) = ((16 : ℂ)⁻¹) from by norm_num]
    abel
  rw [h_expand]
  -- Step 5: bookend identity for T2pos F * X * T2neg G
  have h_bookend :
      T2pos F * ⁅T2pos G, T2neg F⁆ * T2neg G
      = ⁅T2pos G, T2neg F⁆
        + T2pos F * ⁅T2pos G, T2neg F⁆ * (T2neg G - 1)
        + (T2pos F - 1) * ⁅T2pos G, T2neg F⁆ := by noncomm_ring
  rw [h_bookend]
  -- Step 6: final regrouping (1 - (1 - ⁅F, G⁆) = ⁅F, G⁆)
  abel

/-- **R5.2a SHIP — Cubic norm bound on `bchPolyRem F G`**.

For Hermitian-or-arbitrary `F, G : Matrix (Fin d) (Fin d) ℂ` with
`‖F‖, ‖G‖ ≤ δ ≤ 1`:

  `‖bchPolyRem F G‖ ≤ 30 · δ³`.

This is the load-bearing cubic bound that upgrades the BCH order-2
estimate from linear `200·δ` (current `MatrixBCH.bch_order_2_thm`) to
cubic `K·δ³`, making the AA Bridge Lemma 6.1 commutator quadratic-
shrinkage iteration provable (R5.3, deferred).

**Proof.** Decompose `bchPolyRem F G` into 6 named pieces via
`bchPolyRem_decomp`. Each piece admits a cubic bound:
  - Pure-poly pieces (3 of them) total ≤ `δ³ · (1/4 + 1/4 + 1/16) ≤ δ³`.
  - Linearization residual: ≤ `3·δ³`
    (`commutator_T2pos_T2neg_plus_FG_norm_le_cubic`).
  - Right-bookend: ≤ `(5/2) · (9δ²/2) · (3δ/2) = 135·δ³/8 < 17·δ³`.
  - Left-bookend: ≤ `(3δ/2) · (9δ²/2) = 27·δ³/4 < 7·δ³`.

Total: `1 + 3 + 17 + 7 = 28 ≤ 30`. -/
theorem bchPolyRem_norm_le_cubic {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖bchPolyRem F G‖ ≤ 30 * δ ^ 3 := by
  -- Decomposition
  rw [bchPolyRem_decomp]
  -- Triangle inequality on the 6-piece sum
  -- Bundle as ((((A + B) + C) + D) + E) + F where:
  --   A = (1/4) • F^4
  --   B = (1/4) • G^4
  --   C = (1/16) • (F^4 * G^4)
  --   D = ⁅T2pos G, T2neg F⁆ + ⁅F, G⁆
  --   E = T2pos F * ⁅T2pos G, T2neg F⁆ * (T2neg G - 1)
  --   F' = (T2pos F - 1) * ⁅T2pos G, T2neg F⁆
  -- We bound each piece.

  -- Useful: ‖F‖ ≤ 1, ‖G‖ ≤ 1
  have hF_nn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg _
  have hG_nn : (0 : ℝ) ≤ ‖G‖ := norm_nonneg _
  have hF_le_one : ‖F‖ ≤ 1 := hF.trans hδ_le_one
  have hG_le_one : ‖G‖ ≤ 1 := hG.trans hδ_le_one
  have h_δ_nn : (0 : ℝ) ≤ δ := hδ_nn
  have h_δ2_nn : (0 : ℝ) ≤ δ ^ 2 := by positivity
  have h_δ3_nn : (0 : ℝ) ≤ δ ^ 3 := by positivity

  -- Norm bound: ‖F^n‖ ≤ ‖F‖^n
  have h_F4_norm : ‖F ^ 4‖ ≤ ‖F‖ ^ 4 := norm_pow_le F 4
  have h_G4_norm : ‖G ^ 4‖ ≤ ‖G‖ ^ 4 := norm_pow_le G 4
  -- ‖F‖^4 ≤ δ^4 ≤ δ^3 (for δ ≤ 1)
  have h_F4_le_δ4 : ‖F‖ ^ 4 ≤ δ ^ 4 := pow_le_pow_left₀ hF_nn hF 4
  have h_G4_le_δ4 : ‖G‖ ^ 4 ≤ δ ^ 4 := pow_le_pow_left₀ hG_nn hG 4
  have h_δ4_le_δ3 : δ ^ 4 ≤ δ ^ 3 := by
    have h_eq : δ ^ 4 = δ ^ 3 * δ := by ring
    rw [h_eq]
    calc δ ^ 3 * δ ≤ δ ^ 3 * 1 := mul_le_mul_of_nonneg_left hδ_le_one h_δ3_nn
      _ = δ ^ 3 := by ring

  -- Bound A: ‖(1/4) • F^4‖ ≤ δ^3 / 4
  have h_A : ‖((4 : ℂ)⁻¹) • F ^ 4‖ ≤ δ ^ 3 / 4 := by
    rw [norm_smul, norm_four_inv_complex]
    have h_F4_le_δ3 : ‖F ^ 4‖ ≤ δ ^ 3 := by linarith
    nlinarith
  -- Bound B: ‖(1/4) • G^4‖ ≤ δ^3 / 4
  have h_B : ‖((4 : ℂ)⁻¹) • G ^ 4‖ ≤ δ ^ 3 / 4 := by
    rw [norm_smul, norm_four_inv_complex]
    have h_G4_le_δ3 : ‖G ^ 4‖ ≤ δ ^ 3 := by linarith
    nlinarith
  -- Bound C: ‖(1/16) • (F^4 * G^4)‖ ≤ δ^3 / 16
  have h_C : ‖((16 : ℂ)⁻¹) • (F ^ 4 * G ^ 4)‖ ≤ δ ^ 3 / 16 := by
    rw [norm_smul]
    have h_inv16 : ‖((16 : ℂ)⁻¹)‖ = (1 : ℝ) / 16 := by
      rw [norm_inv]; simp
    rw [h_inv16]
    have h_mul : ‖F ^ 4 * G ^ 4‖ ≤ ‖F ^ 4‖ * ‖G ^ 4‖ := norm_mul_le _ _
    have h_FG4 : ‖F ^ 4‖ * ‖G ^ 4‖ ≤ δ ^ 4 * δ ^ 4 := by
      have h_G4_nn : (0 : ℝ) ≤ ‖G ^ 4‖ := norm_nonneg _
      have h_δ4_nn : (0 : ℝ) ≤ δ ^ 4 := by positivity
      have h_F4_le : ‖F ^ 4‖ ≤ δ ^ 4 := h_F4_norm.trans h_F4_le_δ4
      have h_G4_le : ‖G ^ 4‖ ≤ δ ^ 4 := h_G4_norm.trans h_G4_le_δ4
      calc ‖F ^ 4‖ * ‖G ^ 4‖ ≤ δ ^ 4 * ‖G ^ 4‖ :=
            mul_le_mul_of_nonneg_right h_F4_le h_G4_nn
        _ ≤ δ ^ 4 * δ ^ 4 := mul_le_mul_of_nonneg_left h_G4_le h_δ4_nn
    have h_δ8_le_δ3 : δ ^ 4 * δ ^ 4 ≤ δ ^ 3 := by
      have h_δ7_le_δ3 : δ ^ 4 * δ ^ 4 ≤ δ ^ 3 * 1 := by
        have h_δ4_le_1 : δ ^ 4 ≤ 1 := by
          calc δ ^ 4 ≤ 1 ^ 4 := pow_le_pow_left₀ h_δ_nn hδ_le_one 4
            _ = 1 := by ring
        have : δ ^ 4 * δ ^ 4 ≤ δ ^ 4 * 1 := by
          have h_δ4_nn : (0 : ℝ) ≤ δ ^ 4 := by positivity
          exact mul_le_mul_of_nonneg_left h_δ4_le_1 h_δ4_nn
        have h_δ4_le_δ3' : δ ^ 4 ≤ δ ^ 3 := h_δ4_le_δ3
        linarith
      linarith
    have h_FG4_nn : (0 : ℝ) ≤ ‖F ^ 4 * G ^ 4‖ := norm_nonneg _
    have h_mul_le : ‖F ^ 4 * G ^ 4‖ ≤ δ ^ 3 := by linarith
    nlinarith [h_mul_le, h_δ3_nn]

  -- Bound D: ‖⁅T2pos G, T2neg F⁆ + ⁅F, G⁆‖ ≤ 3 · δ^3
  have h_D : ‖⁅T2pos G, T2neg F⁆ + ⁅F, G⁆‖ ≤ 3 * δ ^ 3 :=
    commutator_T2pos_T2neg_plus_FG_norm_le_cubic δ hδ_nn hδ_le_one F G hF hG

  -- Quadratic bound on ⁅T2pos G, T2neg F⁆
  have h_comm_quad : ‖⁅T2pos G, T2neg F⁆‖ ≤ 9 * δ ^ 2 / 2 :=
    commutator_T2pos_T2neg_norm_le_quadratic δ hδ_nn hδ_le_one F G hF hG
  have h_comm_nn : (0 : ℝ) ≤ ‖⁅T2pos G, T2neg F⁆‖ := norm_nonneg _

  -- ‖T2pos F‖ ≤ 5/2
  have h_T2pos_F : ‖T2pos F‖ ≤ 5 / 2 :=
    T2pos_norm_le_of_delta δ hδ_nn hδ_le_one F hF
  -- ‖T2neg G - 1‖ ≤ 3δ/2
  have h_T2neg_G_sub1 : ‖T2neg G - 1‖ ≤ 3 * δ / 2 :=
    T2neg_sub_one_norm_le_of_delta δ hδ_nn hδ_le_one G hG
  -- ‖T2pos F - 1‖ ≤ 3δ/2
  have h_T2pos_F_sub1 : ‖T2pos F - 1‖ ≤ 3 * δ / 2 :=
    T2pos_sub_one_norm_le_of_delta δ hδ_nn hδ_le_one F hF
  -- Non-negativity helpers
  have h_T2pos_F_nn : (0 : ℝ) ≤ ‖T2pos F‖ := norm_nonneg _
  have h_T2neg_G_sub1_nn : (0 : ℝ) ≤ ‖T2neg G - 1‖ := norm_nonneg _
  have h_T2pos_F_sub1_nn : (0 : ℝ) ≤ ‖T2pos F - 1‖ := norm_nonneg _
  have h_9d2_2_nn : (0 : ℝ) ≤ 9 * δ ^ 2 / 2 := by positivity
  have h_3d_2_nn : (0 : ℝ) ≤ 3 * δ / 2 := by linarith
  have h_5_2_nn : (0 : ℝ) ≤ (5 / 2 : ℝ) := by norm_num

  -- Bound E: ‖T2pos F · ⁅T2pos G, T2neg F⁆ · (T2neg G - 1)‖ ≤ 135 δ^3 / 8
  -- Use submultiplicativity twice
  have h_E_prod_le : ‖T2pos F * ⁅T2pos G, T2neg F⁆ * (T2neg G - 1)‖
                  ≤ ‖T2pos F‖ * ‖⁅T2pos G, T2neg F⁆‖ * ‖T2neg G - 1‖ := by
    have h1 : ‖T2pos F * ⁅T2pos G, T2neg F⁆ * (T2neg G - 1)‖
            ≤ ‖T2pos F * ⁅T2pos G, T2neg F⁆‖ * ‖T2neg G - 1‖ := norm_mul_le _ _
    have h2 : ‖T2pos F * ⁅T2pos G, T2neg F⁆‖ ≤ ‖T2pos F‖ * ‖⁅T2pos G, T2neg F⁆‖ :=
      norm_mul_le _ _
    have h2_mul : ‖T2pos F * ⁅T2pos G, T2neg F⁆‖ * ‖T2neg G - 1‖
                ≤ ‖T2pos F‖ * ‖⁅T2pos G, T2neg F⁆‖ * ‖T2neg G - 1‖ :=
      mul_le_mul_of_nonneg_right h2 h_T2neg_G_sub1_nn
    linarith
  -- Chain the bounds: 5/2 · 9δ²/2 · 3δ/2 = 135 δ³/8
  have h_E_le_const : ‖T2pos F‖ * ‖⁅T2pos G, T2neg F⁆‖ * ‖T2neg G - 1‖
                    ≤ (5 / 2) * (9 * δ ^ 2 / 2) * (3 * δ / 2) := by
    have hT2pos_comm_le : ‖T2pos F‖ * ‖⁅T2pos G, T2neg F⁆‖
                        ≤ (5 / 2) * (9 * δ ^ 2 / 2) := by
      have h_F_le : ‖T2pos F‖ ≤ 5 / 2 := h_T2pos_F
      have h_5_2_pos : (0 : ℝ) ≤ 5 / 2 := h_5_2_nn
      calc ‖T2pos F‖ * ‖⁅T2pos G, T2neg F⁆‖
          ≤ (5 / 2) * ‖⁅T2pos G, T2neg F⁆‖ :=
            mul_le_mul_of_nonneg_right h_F_le h_comm_nn
        _ ≤ (5 / 2) * (9 * δ ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left h_comm_quad h_5_2_pos
    have h_outer_nn : (0 : ℝ) ≤ (5 / 2) * (9 * δ ^ 2 / 2) := by positivity
    calc ‖T2pos F‖ * ‖⁅T2pos G, T2neg F⁆‖ * ‖T2neg G - 1‖
        ≤ (5 / 2) * (9 * δ ^ 2 / 2) * ‖T2neg G - 1‖ :=
          mul_le_mul_of_nonneg_right hT2pos_comm_le h_T2neg_G_sub1_nn
      _ ≤ (5 / 2) * (9 * δ ^ 2 / 2) * (3 * δ / 2) :=
          mul_le_mul_of_nonneg_left h_T2neg_G_sub1 h_outer_nn
  have h_E_simp : (5 / 2 : ℝ) * (9 * δ ^ 2 / 2) * (3 * δ / 2) = 135 * δ ^ 3 / 8 := by ring
  have h_E : ‖T2pos F * ⁅T2pos G, T2neg F⁆ * (T2neg G - 1)‖ ≤ 135 * δ ^ 3 / 8 := by
    rw [← h_E_simp]; linarith

  -- Bound F': ‖(T2pos F - 1) · ⁅T2pos G, T2neg F⁆‖ ≤ 27 δ^3 / 4
  have h_F'_prod_le : ‖(T2pos F - 1) * ⁅T2pos G, T2neg F⁆‖
                   ≤ ‖T2pos F - 1‖ * ‖⁅T2pos G, T2neg F⁆‖ := norm_mul_le _ _
  have h_F'_le_const : ‖T2pos F - 1‖ * ‖⁅T2pos G, T2neg F⁆‖
                    ≤ (3 * δ / 2) * (9 * δ ^ 2 / 2) := by
    calc ‖T2pos F - 1‖ * ‖⁅T2pos G, T2neg F⁆‖
        ≤ (3 * δ / 2) * ‖⁅T2pos G, T2neg F⁆‖ :=
          mul_le_mul_of_nonneg_right h_T2pos_F_sub1 h_comm_nn
      _ ≤ (3 * δ / 2) * (9 * δ ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h_comm_quad h_3d_2_nn
  have h_F'_simp : (3 * δ / 2 : ℝ) * (9 * δ ^ 2 / 2) = 27 * δ ^ 3 / 4 := by ring
  have h_F' : ‖(T2pos F - 1) * ⁅T2pos G, T2neg F⁆‖ ≤ 27 * δ ^ 3 / 4 := by
    rw [← h_F'_simp]; linarith

  -- Triangle inequality on the 6-piece sum
  -- ‖S1 + S2 + S3 + D + E + F'‖ ≤ ‖S1‖ + ‖S2‖ + ‖S3‖ + ‖D‖ + ‖E‖ + ‖F'‖
  have h_tri :
      ‖((4 : ℂ)⁻¹) • F ^ 4 + ((4 : ℂ)⁻¹) • G ^ 4 + ((16 : ℂ)⁻¹) • (F ^ 4 * G ^ 4)
       + (⁅T2pos G, T2neg F⁆ + ⁅F, G⁆)
       + T2pos F * ⁅T2pos G, T2neg F⁆ * (T2neg G - 1)
       + (T2pos F - 1) * ⁅T2pos G, T2neg F⁆‖
      ≤ ‖((4 : ℂ)⁻¹) • F ^ 4‖ + ‖((4 : ℂ)⁻¹) • G ^ 4‖ + ‖((16 : ℂ)⁻¹) • (F ^ 4 * G ^ 4)‖
        + ‖⁅T2pos G, T2neg F⁆ + ⁅F, G⁆‖
        + ‖T2pos F * ⁅T2pos G, T2neg F⁆ * (T2neg G - 1)‖
        + ‖(T2pos F - 1) * ⁅T2pos G, T2neg F⁆‖ := by
    -- Cascade norm_add_le 5 times
    have step1 := norm_add_le
      (((4 : ℂ)⁻¹) • F ^ 4 + ((4 : ℂ)⁻¹) • G ^ 4 + ((16 : ℂ)⁻¹) • (F ^ 4 * G ^ 4)
       + (⁅T2pos G, T2neg F⁆ + ⁅F, G⁆)
       + T2pos F * ⁅T2pos G, T2neg F⁆ * (T2neg G - 1))
      ((T2pos F - 1) * ⁅T2pos G, T2neg F⁆)
    have step2 := norm_add_le
      (((4 : ℂ)⁻¹) • F ^ 4 + ((4 : ℂ)⁻¹) • G ^ 4 + ((16 : ℂ)⁻¹) • (F ^ 4 * G ^ 4)
       + (⁅T2pos G, T2neg F⁆ + ⁅F, G⁆))
      (T2pos F * ⁅T2pos G, T2neg F⁆ * (T2neg G - 1))
    have step3 := norm_add_le
      (((4 : ℂ)⁻¹) • F ^ 4 + ((4 : ℂ)⁻¹) • G ^ 4 + ((16 : ℂ)⁻¹) • (F ^ 4 * G ^ 4))
      (⁅T2pos G, T2neg F⁆ + ⁅F, G⁆)
    have step4 := norm_add_le
      (((4 : ℂ)⁻¹) • F ^ 4 + ((4 : ℂ)⁻¹) • G ^ 4)
      (((16 : ℂ)⁻¹) • (F ^ 4 * G ^ 4))
    have step5 := norm_add_le
      (((4 : ℂ)⁻¹) • F ^ 4) (((4 : ℂ)⁻¹) • G ^ 4)
    linarith
  -- Sum the bounds: 1/4 + 1/4 + 1/16 + 3 + 135/8 + 27/4 = 27.1875 ≤ 30
  -- (in δ³ units): 4/16 + 4/16 + 1/16 + 48/16 + 270/16 + 108/16 = 435/16 = 27.1875
  have h_sum_bound :
      δ ^ 3 / 4 + δ ^ 3 / 4 + δ ^ 3 / 16 + 3 * δ ^ 3 + 135 * δ ^ 3 / 8 + 27 * δ ^ 3 / 4
      ≤ 30 * δ ^ 3 := by nlinarith
  linarith

/-! ## 8. Taylor remainder bounds for `exp(±iF)` vs T2pos/T2neg (R5.2b)

These bridge the matrix exponential `exp(±i•F)` to its order-2 Taylor polynomial
`T2pos`/`T2neg`, with quantitative cubic remainder bounds. Built on
`MatrixTaylor.norm_exp_sub_order3_le_loose`.

A companion order-2 Taylor bound on `exp(-[F,G]) - (1 - [F,G])` is also shipped
here — the order-1 remainder of `exp` at `-[F,G]`, which is `O(δ⁴)` under
`‖F‖, ‖G‖ ≤ δ` thanks to `‖[F,G]‖ ≤ 2·δ²` (from `commutator_norm_le`, no
Hermitian hypothesis). -/

/-- **T2pos in Mathlib Taylor form**: `T2pos F = 1 + (Complex.I • F) + ((2:ℂ)⁻¹) • (Complex.I • F)^2`.

The intrinsic order-2 Taylor polynomial of `exp` at `Complex.I • F`, after
applying `(i•F)² = -F²` simplification. Direct rewrite that lets us
plug into `MatrixTaylor.norm_exp_sub_order3_le_loose`. -/
private lemma T2pos_eq_taylor_form {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ) :
    T2pos F = 1 + Complex.I • F + ((2 : ℂ)⁻¹) • (Complex.I • F) ^ 2 := by
  unfold T2pos
  rw [smul_pow, Complex.I_sq]
  simp
  module

/-- **T2neg in Mathlib Taylor form**: `T2neg F = 1 + (-(Complex.I • F)) + ((2:ℂ)⁻¹) • (-(Complex.I • F))^2`. -/
private lemma T2neg_eq_taylor_form {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ) :
    T2neg F = 1 + (-(Complex.I • F)) + ((2 : ℂ)⁻¹) • (-(Complex.I • F)) ^ 2 := by
  unfold T2neg
  rw [neg_pow, smul_pow, Complex.I_sq]
  simp
  module

/-- **Cubic Taylor remainder bound for `exp(iF) - T2pos F`**:

  `‖NormedSpace.exp (Complex.I • F) - T2pos F‖ ≤ ‖F‖³ · exp(‖F‖)`.

Direct application of `MatrixTaylor.norm_exp_sub_order3_le_loose` at
`X = Complex.I • F`, using `T2pos_eq_taylor_form` to identify the Taylor
polynomial and `‖Complex.I • F‖ = ‖F‖`. -/
theorem norm_exp_iF_sub_T2pos_le {d : ℕ} [Nonempty (Fin d)]
    (F : Matrix (Fin d) (Fin d) ℂ) :
    ‖NormedSpace.exp (Complex.I • F) - T2pos F‖ ≤ ‖F‖ ^ 3 * Real.exp ‖F‖ := by
  have h_taylor := MatrixTaylor.norm_exp_sub_order3_le_loose (Complex.I • F)
  rw [← T2pos_eq_taylor_form] at h_taylor
  have h_iF_norm : ‖Complex.I • F‖ = ‖F‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [h_iF_norm] at h_taylor
  exact h_taylor

/-- **Cubic Taylor remainder bound for `exp(-iF) - T2neg F`**:

  `‖NormedSpace.exp (-(Complex.I • F)) - T2neg F‖ ≤ ‖F‖³ · exp(‖F‖)`. -/
theorem norm_exp_neg_iF_sub_T2neg_le {d : ℕ} [Nonempty (Fin d)]
    (F : Matrix (Fin d) (Fin d) ℂ) :
    ‖NormedSpace.exp (-(Complex.I • F)) - T2neg F‖ ≤ ‖F‖ ^ 3 * Real.exp ‖F‖ := by
  have h_taylor := MatrixTaylor.norm_exp_sub_order3_le_loose (-(Complex.I • F))
  rw [← T2neg_eq_taylor_form] at h_taylor
  have h_neg_iF_norm : ‖(-(Complex.I • F))‖ = ‖F‖ := by
    rw [norm_neg, norm_smul, Complex.norm_I, one_mul]
  rw [h_neg_iF_norm] at h_taylor
  exact h_taylor

/-- **Quadratic Taylor remainder bound for `exp(-[F,G]) - (1 - [F,G])`**:

  `‖NormedSpace.exp (-⁅F, G⁆) - (1 - ⁅F, G⁆)‖ ≤ ‖⁅F, G⁆‖² · exp(‖⁅F, G⁆‖)`.

The order-1 Taylor remainder of `exp` at `-⁅F, G⁆`. The polynomial `1 - [F,G]`
is the BCH leading correction; the residual absorbs the higher-order content
of `exp`. Bounded `O(‖[F,G]‖²) = O(δ⁴)` under `‖F‖, ‖G‖ ≤ δ`. -/
theorem norm_exp_neg_comm_sub_one_plus_comm_le {d : ℕ} [Nonempty (Fin d)]
    (F G : Matrix (Fin d) (Fin d) ℂ) :
    ‖NormedSpace.exp (-⁅F, G⁆) - (1 - ⁅F, G⁆)‖
      ≤ ‖⁅F, G⁆‖ ^ 2 * Real.exp ‖⁅F, G⁆‖ := by
  have h_taylor := MatrixTaylor.norm_exp_sub_order2_le_loose (-⁅F, G⁆)
  have h_eq : (1 : Matrix (Fin d) (Fin d) ℂ) + (-⁅F, G⁆) = 1 - ⁅F, G⁆ := by abel
  rw [h_eq] at h_taylor
  have h_norm : ‖(-⁅F, G⁆ : Matrix (Fin d) (Fin d) ℂ)‖ = ‖⁅F, G⁆‖ := norm_neg _
  rw [h_norm] at h_taylor
  exact h_taylor

/-! ## 9. δ-parameterized Taylor remainder bounds (R5.2b)

Specialize the §8 bounds under the standing hypothesis `‖F‖ ≤ δ ≤ 1`. -/

/-- For `‖F‖ ≤ δ`: `‖exp(iF) - T2pos F‖ ≤ δ³ · exp(δ)`. -/
lemma norm_exp_iF_sub_T2pos_le_of_delta {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (_hδ_nn : 0 ≤ δ) (F : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) :
    ‖NormedSpace.exp (Complex.I • F) - T2pos F‖ ≤ δ ^ 3 * Real.exp δ := by
  have h := norm_exp_iF_sub_T2pos_le F
  have hF_nn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg _
  have h_F3_le : ‖F‖ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ hF_nn hF 3
  have h_exp_F_nn : (0 : ℝ) ≤ Real.exp ‖F‖ := le_of_lt (Real.exp_pos _)
  have h_exp_le : Real.exp ‖F‖ ≤ Real.exp δ := Real.exp_le_exp.mpr hF
  have h_d3_nn : (0 : ℝ) ≤ δ ^ 3 := by positivity
  have h_step1 : ‖F‖ ^ 3 * Real.exp ‖F‖ ≤ δ ^ 3 * Real.exp ‖F‖ :=
    mul_le_mul_of_nonneg_right h_F3_le h_exp_F_nn
  have h_step2 : δ ^ 3 * Real.exp ‖F‖ ≤ δ ^ 3 * Real.exp δ :=
    mul_le_mul_of_nonneg_left h_exp_le h_d3_nn
  linarith

/-- For `‖F‖ ≤ δ`: `‖exp(-iF) - T2neg F‖ ≤ δ³ · exp(δ)`. -/
lemma norm_exp_neg_iF_sub_T2neg_le_of_delta {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (_hδ_nn : 0 ≤ δ) (F : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) :
    ‖NormedSpace.exp (-(Complex.I • F)) - T2neg F‖ ≤ δ ^ 3 * Real.exp δ := by
  have h := norm_exp_neg_iF_sub_T2neg_le F
  have hF_nn : (0 : ℝ) ≤ ‖F‖ := norm_nonneg _
  have h_F3_le : ‖F‖ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ hF_nn hF 3
  have h_exp_F_nn : (0 : ℝ) ≤ Real.exp ‖F‖ := le_of_lt (Real.exp_pos _)
  have h_exp_le : Real.exp ‖F‖ ≤ Real.exp δ := Real.exp_le_exp.mpr hF
  have h_d3_nn : (0 : ℝ) ≤ δ ^ 3 := by positivity
  have h_step1 : ‖F‖ ^ 3 * Real.exp ‖F‖ ≤ δ ^ 3 * Real.exp ‖F‖ :=
    mul_le_mul_of_nonneg_right h_F3_le h_exp_F_nn
  have h_step2 : δ ^ 3 * Real.exp ‖F‖ ≤ δ ^ 3 * Real.exp δ :=
    mul_le_mul_of_nonneg_left h_exp_le h_d3_nn
  linarith

/-- For `‖F‖, ‖G‖ ≤ δ`: `‖exp(-[F,G]) - (1 - [F,G])‖ ≤ 4·δ⁴ · exp(2·δ²)`. -/
lemma norm_exp_neg_comm_sub_one_plus_comm_le_of_delta {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖NormedSpace.exp (-⁅F, G⁆) - (1 - ⁅F, G⁆)‖
      ≤ 4 * δ ^ 4 * Real.exp (2 * δ ^ 2) := by
  have h := norm_exp_neg_comm_sub_one_plus_comm_le F G
  -- ‖[F, G]‖ ≤ 2·δ²
  have h_comm_le : ‖⁅F, G⁆‖ ≤ 2 * δ ^ 2 := by
    have h_comm := commutator_norm_le F G
    have h_2δ_nn : (0 : ℝ) ≤ 2 * δ := by linarith [norm_nonneg F]
    have hG_nn : (0 : ℝ) ≤ ‖G‖ := norm_nonneg _
    have h_FG_le : 2 * ‖F‖ * ‖G‖ ≤ 2 * δ * δ := by
      have h_2F_le : 2 * ‖F‖ ≤ 2 * δ := by linarith
      calc 2 * ‖F‖ * ‖G‖ ≤ 2 * δ * ‖G‖ := mul_le_mul_of_nonneg_right h_2F_le hG_nn
        _ ≤ 2 * δ * δ := mul_le_mul_of_nonneg_left hG h_2δ_nn
    have h_eq : 2 * δ * δ = 2 * δ ^ 2 := by ring
    linarith
  have h_comm_nn : (0 : ℝ) ≤ ‖⁅F, G⁆‖ := norm_nonneg _
  have h_comm_sq_le : ‖⁅F, G⁆‖ ^ 2 ≤ (2 * δ ^ 2) ^ 2 :=
    pow_le_pow_left₀ h_comm_nn h_comm_le 2
  have h_exp_le : Real.exp ‖⁅F, G⁆‖ ≤ Real.exp (2 * δ ^ 2) := Real.exp_le_exp.mpr h_comm_le
  have h_exp_F_nn : (0 : ℝ) ≤ Real.exp ‖⁅F, G⁆‖ := le_of_lt (Real.exp_pos _)
  have h_2d2_sq_nn : (0 : ℝ) ≤ (2 * δ ^ 2) ^ 2 := by positivity
  have h_step1 :
      ‖⁅F, G⁆‖ ^ 2 * Real.exp ‖⁅F, G⁆‖ ≤ (2 * δ ^ 2) ^ 2 * Real.exp ‖⁅F, G⁆‖ :=
    mul_le_mul_of_nonneg_right h_comm_sq_le h_exp_F_nn
  have h_step2 :
      (2 * δ ^ 2) ^ 2 * Real.exp ‖⁅F, G⁆‖ ≤ (2 * δ ^ 2) ^ 2 * Real.exp (2 * δ ^ 2) :=
    mul_le_mul_of_nonneg_left h_exp_le h_2d2_sq_nn
  have h_eq_4d4 : (2 * δ ^ 2) ^ 2 = 4 * δ ^ 4 := by ring
  have h_step3 : (2 * δ ^ 2) ^ 2 * Real.exp (2 * δ ^ 2) = 4 * δ ^ 4 * Real.exp (2 * δ ^ 2) := by
    rw [h_eq_4d4]
  linarith

/-! ## 10. The headline cubic bound on the BCH order-2 estimate (R5.2b SHIP)

This composes the §1-9 infrastructure:

  P - Q = (P - PolyP) + (PolyP - (1 - [F,G])) - (Q - (1 - [F,G]))
        = TaylorCross + bchPolyRem F G - ExpRemainder

where:
  - P = exp(iF)·exp(iG)·exp(-iF)·exp(-iG)
  - PolyP = T2pos F · T2pos G · T2neg F · T2neg G
  - Q = exp(-[F,G])
  - TaylorCross via 4-term telescope, each O(δ³ · exp(δ))
  - bchPolyRem F G ≤ 30·δ³ (R5.2a)
  - ExpRemainder = Q - (1 - [F,G]) ≤ 4·δ⁴·exp(2δ²) ≤ 36·δ³ for δ ≤ 1.

The constant K = 320 is loose; D-N original K ≤ 4 is deferred to R5.2c.

For Pipeline Invariant #10 (no `maxHeartbeats`), the proof is decomposed
into 4 telescope-term lemmas + 1 numeric-collapse lemma + 1 final compose
lemma. Each sub-lemma has small enough scope to fit the default heartbeat
budget. -/

/-- **Telescope term 1**: `‖(exp(iF) - T2pos F)·exp(iG)·exp(-iF)·exp(-iG)‖ ≤ 81·δ³`
for `‖F‖, ‖G‖ ≤ δ ≤ 1`.

Bound: `‖A - A'‖ ≤ δ³·exp(δ)`, `‖B·C·D‖ ≤ exp(δ)³`. For δ ≤ 1, exp(δ) ≤ 3,
giving `≤ 3·δ³ · 27 = 81·δ³`. -/
private lemma bch_cubic_telescope_term1 {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖(NormedSpace.exp (Complex.I • F) - T2pos F)
        * NormedSpace.exp (Complex.I • G)
        * NormedSpace.exp (-(Complex.I • F))
        * NormedSpace.exp (-(Complex.I • G))‖ ≤ 81 * δ ^ 3 := by
  have h_A_sub : ‖NormedSpace.exp (Complex.I • F) - T2pos F‖ ≤ δ ^ 3 * Real.exp δ :=
    norm_exp_iF_sub_T2pos_le_of_delta δ hδ_nn F hF
  have h_B_norm : ‖NormedSpace.exp (Complex.I • G)‖ ≤ Real.exp δ :=
    (MatrixBCH.norm_exp_I_smul_le G).trans (Real.exp_le_exp.mpr hG)
  have h_C_norm : ‖NormedSpace.exp (-(Complex.I • F))‖ ≤ Real.exp δ :=
    (MatrixBCH.norm_exp_neg_I_smul_le F).trans (Real.exp_le_exp.mpr hF)
  have h_D_norm : ‖NormedSpace.exp (-(Complex.I • G))‖ ≤ Real.exp δ :=
    (MatrixBCH.norm_exp_neg_I_smul_le G).trans (Real.exp_le_exp.mpr hG)
  have h_exp_pos : (0 : ℝ) < Real.exp δ := Real.exp_pos _
  have h_exp_nn : (0 : ℝ) ≤ Real.exp δ := le_of_lt h_exp_pos
  have h_exp_le_3 : Real.exp δ ≤ 3 := by
    have h_exp_1_lt : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    linarith [Real.exp_le_exp.mpr hδ_le_one]
  have h_δ3_nn : (0 : ℝ) ≤ δ ^ 3 := by positivity
  set A := NormedSpace.exp (Complex.I • F)
  set A' := T2pos F
  set B := NormedSpace.exp (Complex.I • G)
  set C := NormedSpace.exp (-(Complex.I • F))
  set D := NormedSpace.exp (-(Complex.I • G))
  have h_BCD_norm : ‖B * C * D‖ ≤ Real.exp δ ^ 3 := by
    have h1 : ‖B * C * D‖ ≤ ‖B * C‖ * ‖D‖ := norm_mul_le _ _
    have h2 : ‖B * C‖ ≤ ‖B‖ * ‖C‖ := norm_mul_le B C
    have h3 : ‖B‖ * ‖C‖ ≤ Real.exp δ * Real.exp δ :=
      mul_le_mul h_B_norm h_C_norm (norm_nonneg _) h_exp_nn
    have h_BC_le : ‖B * C‖ ≤ Real.exp δ * Real.exp δ := h2.trans h3
    have h_sq_nn : (0 : ℝ) ≤ Real.exp δ * Real.exp δ := by positivity
    calc ‖B * C * D‖ ≤ ‖B * C‖ * ‖D‖ := h1
      _ ≤ (Real.exp δ * Real.exp δ) * Real.exp δ :=
          mul_le_mul h_BC_le h_D_norm (norm_nonneg _) h_sq_nn
      _ = Real.exp δ ^ 3 := by ring
  have h_exp_cube_le : Real.exp δ ^ 3 ≤ 27 := by
    have h_sq_le : Real.exp δ ^ 2 ≤ 9 := by nlinarith [h_exp_le_3]
    have h_eq : Real.exp δ ^ 3 = Real.exp δ ^ 2 * Real.exp δ := by ring
    rw [h_eq]
    calc Real.exp δ ^ 2 * Real.exp δ
        ≤ 9 * Real.exp δ := mul_le_mul_of_nonneg_right h_sq_le h_exp_nn
      _ ≤ 9 * 3 := mul_le_mul_of_nonneg_left h_exp_le_3 (by norm_num)
      _ = 27 := by norm_num
  have h_assoc : (A - A') * B * C * D = (A - A') * (B * C * D) := by simp only [mul_assoc]
  rw [h_assoc]
  have h_prod1 : ‖(A - A') * (B * C * D)‖ ≤ ‖A - A'‖ * ‖B * C * D‖ := norm_mul_le _ _
  have h_BCD_nn : (0 : ℝ) ≤ ‖B * C * D‖ := norm_nonneg _
  have h_d3exp_nn : (0 : ℝ) ≤ δ ^ 3 * Real.exp δ := by positivity
  have h_prod2 : ‖A - A'‖ * ‖B * C * D‖ ≤ (δ ^ 3 * Real.exp δ) * ‖B * C * D‖ :=
    mul_le_mul_of_nonneg_right h_A_sub h_BCD_nn
  have h_prod3 : (δ ^ 3 * Real.exp δ) * ‖B * C * D‖
                ≤ (δ ^ 3 * Real.exp δ) * Real.exp δ ^ 3 :=
    mul_le_mul_of_nonneg_left h_BCD_norm h_d3exp_nn
  have h_d3exp_le : δ ^ 3 * Real.exp δ ≤ δ ^ 3 * 3 :=
    mul_le_mul_of_nonneg_left h_exp_le_3 h_δ3_nn
  have h_exp_cube_nn : (0 : ℝ) ≤ Real.exp δ ^ 3 := by positivity
  have h_final :
      (δ ^ 3 * Real.exp δ) * Real.exp δ ^ 3 ≤ 81 * δ ^ 3 := by
    calc (δ ^ 3 * Real.exp δ) * Real.exp δ ^ 3
        ≤ (δ ^ 3 * 3) * Real.exp δ ^ 3 := mul_le_mul_of_nonneg_right h_d3exp_le h_exp_cube_nn
      _ ≤ (δ ^ 3 * 3) * 27 := mul_le_mul_of_nonneg_left h_exp_cube_le (by positivity)
      _ = 81 * δ ^ 3 := by ring
  linarith

/-- **Telescope term 2**: `‖T2pos F · (exp(iG) - T2pos G) · exp(-iF) · exp(-iG)‖ ≤ 68·δ³`. -/
private lemma bch_cubic_telescope_term2 {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖T2pos F * (NormedSpace.exp (Complex.I • G) - T2pos G)
        * NormedSpace.exp (-(Complex.I • F))
        * NormedSpace.exp (-(Complex.I • G))‖ ≤ 68 * δ ^ 3 := by
  have h_A'_norm : ‖T2pos F‖ ≤ 5 / 2 := T2pos_norm_le_of_delta δ hδ_nn hδ_le_one F hF
  have h_B_sub : ‖NormedSpace.exp (Complex.I • G) - T2pos G‖ ≤ δ ^ 3 * Real.exp δ :=
    norm_exp_iF_sub_T2pos_le_of_delta δ hδ_nn G hG
  have h_C_norm : ‖NormedSpace.exp (-(Complex.I • F))‖ ≤ Real.exp δ :=
    (MatrixBCH.norm_exp_neg_I_smul_le F).trans (Real.exp_le_exp.mpr hF)
  have h_D_norm : ‖NormedSpace.exp (-(Complex.I • G))‖ ≤ Real.exp δ :=
    (MatrixBCH.norm_exp_neg_I_smul_le G).trans (Real.exp_le_exp.mpr hG)
  have h_exp_pos : (0 : ℝ) < Real.exp δ := Real.exp_pos _
  have h_exp_nn : (0 : ℝ) ≤ Real.exp δ := le_of_lt h_exp_pos
  have h_exp_le_3 : Real.exp δ ≤ 3 := by
    have h_exp_1_lt : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith [Real.exp_le_exp.mpr hδ_le_one]
  have h_δ3_nn : (0 : ℝ) ≤ δ ^ 3 := by positivity
  have h_5_2_nn : (0 : ℝ) ≤ (5 / 2 : ℝ) := by norm_num
  set A' := T2pos F
  set B := NormedSpace.exp (Complex.I • G)
  set B' := T2pos G
  set C := NormedSpace.exp (-(Complex.I • F))
  set D := NormedSpace.exp (-(Complex.I • G))
  have h_assoc : A' * (B - B') * C * D = A' * ((B - B') * (C * D)) := by noncomm_ring
  rw [h_assoc]
  have h_CD_norm : ‖C * D‖ ≤ Real.exp δ ^ 2 := by
    have h_sq_eq : Real.exp δ * Real.exp δ = Real.exp δ ^ 2 := by ring
    calc ‖C * D‖ ≤ ‖C‖ * ‖D‖ := norm_mul_le C D
      _ ≤ Real.exp δ * Real.exp δ :=
          mul_le_mul h_C_norm h_D_norm (norm_nonneg _) h_exp_nn
      _ = Real.exp δ ^ 2 := h_sq_eq
  have h_exp_sq_le : Real.exp δ ^ 2 ≤ 9 := by nlinarith [h_exp_le_3]
  have h_d3exp_nn : (0 : ℝ) ≤ δ ^ 3 * Real.exp δ := by positivity
  have h_d3exp_le : δ ^ 3 * Real.exp δ ≤ δ ^ 3 * 3 :=
    mul_le_mul_of_nonneg_left h_exp_le_3 h_δ3_nn
  have h_BB'_CD : ‖(B - B') * (C * D)‖ ≤ (δ ^ 3 * Real.exp δ) * Real.exp δ ^ 2 := by
    calc ‖(B - B') * (C * D)‖
        ≤ ‖B - B'‖ * ‖C * D‖ := norm_mul_le _ _
      _ ≤ (δ ^ 3 * Real.exp δ) * ‖C * D‖ :=
          mul_le_mul_of_nonneg_right h_B_sub (norm_nonneg _)
      _ ≤ (δ ^ 3 * Real.exp δ) * Real.exp δ ^ 2 :=
          mul_le_mul_of_nonneg_left h_CD_norm h_d3exp_nn
  have h_BB'_CD_le_num :
      (δ ^ 3 * Real.exp δ) * Real.exp δ ^ 2 ≤ 27 * δ ^ 3 := by
    have h_sq_nn : (0 : ℝ) ≤ Real.exp δ ^ 2 := by positivity
    calc (δ ^ 3 * Real.exp δ) * Real.exp δ ^ 2
        ≤ (δ ^ 3 * 3) * Real.exp δ ^ 2 := mul_le_mul_of_nonneg_right h_d3exp_le h_sq_nn
      _ ≤ (δ ^ 3 * 3) * 9 := mul_le_mul_of_nonneg_left h_exp_sq_le (by positivity)
      _ = 27 * δ ^ 3 := by ring
  have h_BB'_CD_le_num' : ‖(B - B') * (C * D)‖ ≤ 27 * δ ^ 3 := h_BB'_CD.trans h_BB'_CD_le_num
  have h_main : ‖A' * ((B - B') * (C * D))‖ ≤ (5 / 2) * (27 * δ ^ 3) := by
    have h1 : ‖A' * ((B - B') * (C * D))‖ ≤ ‖A'‖ * ‖(B - B') * (C * D)‖ := norm_mul_le _ _
    have h2 : ‖A'‖ * ‖(B - B') * (C * D)‖ ≤ (5 / 2) * ‖(B - B') * (C * D)‖ :=
      mul_le_mul_of_nonneg_right h_A'_norm (norm_nonneg _)
    have h3 : (5 / 2 : ℝ) * ‖(B - B') * (C * D)‖ ≤ (5 / 2) * (27 * δ ^ 3) :=
      mul_le_mul_of_nonneg_left h_BB'_CD_le_num' h_5_2_nn
    linarith
  have h_num_eq : (5 / 2 : ℝ) * (27 * δ ^ 3) = (135 / 2) * δ ^ 3 := by ring
  have h_num_le : (135 / 2 : ℝ) * δ ^ 3 ≤ 68 * δ ^ 3 := by nlinarith [h_δ3_nn]
  linarith

/-- **Telescope term 3**: `‖T2pos F · T2pos G · (exp(-iF) - T2neg F) · exp(-iG)‖ ≤ 57·δ³`. -/
private lemma bch_cubic_telescope_term3 {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖T2pos F * T2pos G * (NormedSpace.exp (-(Complex.I • F)) - T2neg F)
        * NormedSpace.exp (-(Complex.I • G))‖ ≤ 57 * δ ^ 3 := by
  have h_A'_norm : ‖T2pos F‖ ≤ 5 / 2 := T2pos_norm_le_of_delta δ hδ_nn hδ_le_one F hF
  have h_B'_norm : ‖T2pos G‖ ≤ 5 / 2 := T2pos_norm_le_of_delta δ hδ_nn hδ_le_one G hG
  have h_C_sub : ‖NormedSpace.exp (-(Complex.I • F)) - T2neg F‖ ≤ δ ^ 3 * Real.exp δ :=
    norm_exp_neg_iF_sub_T2neg_le_of_delta δ hδ_nn F hF
  have h_D_norm : ‖NormedSpace.exp (-(Complex.I • G))‖ ≤ Real.exp δ :=
    (MatrixBCH.norm_exp_neg_I_smul_le G).trans (Real.exp_le_exp.mpr hG)
  have h_exp_pos : (0 : ℝ) < Real.exp δ := Real.exp_pos _
  have h_exp_nn : (0 : ℝ) ≤ Real.exp δ := le_of_lt h_exp_pos
  have h_exp_le_3 : Real.exp δ ≤ 3 := by
    have h_exp_1_lt : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith [Real.exp_le_exp.mpr hδ_le_one]
  have h_δ3_nn : (0 : ℝ) ≤ δ ^ 3 := by positivity
  have h_5_2_nn : (0 : ℝ) ≤ (5 / 2 : ℝ) := by norm_num
  set A' := T2pos F
  set B' := T2pos G
  set C := NormedSpace.exp (-(Complex.I • F))
  set C' := T2neg F
  set D := NormedSpace.exp (-(Complex.I • G))
  have h_d3exp_nn : (0 : ℝ) ≤ δ ^ 3 * Real.exp δ := by positivity
  have h_d3exp_le : δ ^ 3 * Real.exp δ ≤ δ ^ 3 * 3 :=
    mul_le_mul_of_nonneg_left h_exp_le_3 h_δ3_nn
  -- ‖(C - C') * D‖ ≤ (δ³ exp δ) * exp δ ≤ 9·δ³
  have h_CC'D : ‖(C - C') * D‖ ≤ 9 * δ ^ 3 := by
    have h1 : ‖(C - C') * D‖ ≤ ‖C - C'‖ * ‖D‖ := norm_mul_le _ _
    have h2 : ‖C - C'‖ * ‖D‖ ≤ (δ ^ 3 * Real.exp δ) * Real.exp δ :=
      mul_le_mul h_C_sub h_D_norm (norm_nonneg _) h_d3exp_nn
    have h3 : (δ ^ 3 * Real.exp δ) * Real.exp δ ≤ 9 * δ ^ 3 := by
      calc (δ ^ 3 * Real.exp δ) * Real.exp δ
          ≤ (δ ^ 3 * 3) * Real.exp δ := mul_le_mul_of_nonneg_right h_d3exp_le h_exp_nn
        _ ≤ (δ ^ 3 * 3) * 3 := mul_le_mul_of_nonneg_left h_exp_le_3 (by positivity)
        _ = 9 * δ ^ 3 := by ring
    linarith
  -- ‖A' * B'‖ ≤ 25/4
  have h_A'B' : ‖A' * B'‖ ≤ (5 / 2) ^ 2 := by
    have h1 : ‖A' * B'‖ ≤ ‖A'‖ * ‖B'‖ := norm_mul_le A' B'
    have h2 : ‖A'‖ * ‖B'‖ ≤ (5 / 2) * (5 / 2) :=
      mul_le_mul h_A'_norm h_B'_norm (norm_nonneg _) h_5_2_nn
    calc ‖A' * B'‖ ≤ ‖A'‖ * ‖B'‖ := h1
      _ ≤ (5 / 2) * (5 / 2) := h2
      _ = (5 / 2) ^ 2 := by ring
  have h_5_2_sq_nn : (0 : ℝ) ≤ (5 / 2 : ℝ) ^ 2 := by positivity
  -- Assoc
  have h_assoc : A' * B' * (C - C') * D = (A' * B') * ((C - C') * D) := by noncomm_ring
  rw [h_assoc]
  -- Final
  have h1 : ‖(A' * B') * ((C - C') * D)‖ ≤ ‖A' * B'‖ * ‖(C - C') * D‖ := norm_mul_le _ _
  have h_CC'D_nn : (0 : ℝ) ≤ ‖(C - C') * D‖ := norm_nonneg _
  have h2 : ‖A' * B'‖ * ‖(C - C') * D‖ ≤ (5 / 2) ^ 2 * ‖(C - C') * D‖ :=
    mul_le_mul_of_nonneg_right h_A'B' h_CC'D_nn
  have h3 : (5 / 2 : ℝ) ^ 2 * ‖(C - C') * D‖ ≤ (5 / 2) ^ 2 * (9 * δ ^ 3) :=
    mul_le_mul_of_nonneg_left h_CC'D h_5_2_sq_nn
  have h_simp : (5 / 2 : ℝ) ^ 2 * (9 * δ ^ 3) = (225 / 4) * δ ^ 3 := by ring
  have h_num_le : (225 / 4 : ℝ) * δ ^ 3 ≤ 57 * δ ^ 3 := by nlinarith [h_δ3_nn]
  linarith

/-- **Telescope term 4**: `‖T2pos F · T2pos G · T2neg F · (exp(-iG) - T2neg G)‖ ≤ 47·δ³`. -/
private lemma bch_cubic_telescope_term4 {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖T2pos F * T2pos G * T2neg F * (NormedSpace.exp (-(Complex.I • G)) - T2neg G)‖
      ≤ 47 * δ ^ 3 := by
  have h_A'_norm : ‖T2pos F‖ ≤ 5 / 2 := T2pos_norm_le_of_delta δ hδ_nn hδ_le_one F hF
  have h_B'_norm : ‖T2pos G‖ ≤ 5 / 2 := T2pos_norm_le_of_delta δ hδ_nn hδ_le_one G hG
  have h_C'_norm : ‖T2neg F‖ ≤ 5 / 2 := T2neg_norm_le_of_delta δ hδ_nn hδ_le_one F hF
  have h_D_sub : ‖NormedSpace.exp (-(Complex.I • G)) - T2neg G‖ ≤ δ ^ 3 * Real.exp δ :=
    norm_exp_neg_iF_sub_T2neg_le_of_delta δ hδ_nn G hG
  have h_exp_pos : (0 : ℝ) < Real.exp δ := Real.exp_pos _
  have h_exp_nn : (0 : ℝ) ≤ Real.exp δ := le_of_lt h_exp_pos
  have h_exp_le_3 : Real.exp δ ≤ 3 := by
    have h_exp_1_lt : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith [Real.exp_le_exp.mpr hδ_le_one]
  have h_δ3_nn : (0 : ℝ) ≤ δ ^ 3 := by positivity
  have h_5_2_nn : (0 : ℝ) ≤ (5 / 2 : ℝ) := by norm_num
  have h_5_2_sq_nn : (0 : ℝ) ≤ (5 / 2 : ℝ) ^ 2 := by positivity
  have h_5_2_cube_nn : (0 : ℝ) ≤ (5 / 2 : ℝ) ^ 3 := by positivity
  set A' := T2pos F
  set B' := T2pos G
  set C' := T2neg F
  set D := NormedSpace.exp (-(Complex.I • G))
  set D' := T2neg G
  -- ‖A' * B' * C'‖ ≤ (5/2)³
  have h_A'B' : ‖A' * B'‖ ≤ (5 / 2) ^ 2 := by
    have h_eq : (5 / 2 : ℝ) * (5 / 2) = (5 / 2) ^ 2 := by ring
    calc ‖A' * B'‖ ≤ ‖A'‖ * ‖B'‖ := norm_mul_le A' B'
      _ ≤ (5 / 2) * (5 / 2) := mul_le_mul h_A'_norm h_B'_norm (norm_nonneg _) h_5_2_nn
      _ = (5 / 2) ^ 2 := h_eq
  have h_A'B'_nn : (0 : ℝ) ≤ ‖A' * B'‖ := norm_nonneg _
  have h_C'_nn : (0 : ℝ) ≤ ‖C'‖ := norm_nonneg _
  have h_A'B'C' : ‖A' * B' * C'‖ ≤ (5 / 2) ^ 3 := by
    calc ‖A' * B' * C'‖
        ≤ ‖A' * B'‖ * ‖C'‖ := norm_mul_le _ _
      _ ≤ (5 / 2) ^ 2 * ‖C'‖ := mul_le_mul_of_nonneg_right h_A'B' h_C'_nn
      _ ≤ (5 / 2) ^ 2 * (5 / 2) := mul_le_mul_of_nonneg_left h_C'_norm h_5_2_sq_nn
      _ = (5 / 2) ^ 3 := by ring
  have h_d3exp_nn : (0 : ℝ) ≤ δ ^ 3 * Real.exp δ := by positivity
  have h_d3exp_le : δ ^ 3 * Real.exp δ ≤ δ ^ 3 * 3 :=
    mul_le_mul_of_nonneg_left h_exp_le_3 h_δ3_nn
  -- Final
  have h1 : ‖A' * B' * C' * (D - D')‖ ≤ ‖A' * B' * C'‖ * ‖D - D'‖ := norm_mul_le _ _
  have h_DD'_nn : (0 : ℝ) ≤ ‖D - D'‖ := norm_nonneg _
  have h2 : ‖A' * B' * C'‖ * ‖D - D'‖ ≤ (5 / 2) ^ 3 * ‖D - D'‖ :=
    mul_le_mul_of_nonneg_right h_A'B'C' h_DD'_nn
  have h3 : (5 / 2 : ℝ) ^ 3 * ‖D - D'‖ ≤ (5 / 2) ^ 3 * (δ ^ 3 * Real.exp δ) :=
    mul_le_mul_of_nonneg_left h_D_sub h_5_2_cube_nn
  have h4 : (5 / 2 : ℝ) ^ 3 * (δ ^ 3 * Real.exp δ) ≤ (5 / 2) ^ 3 * (δ ^ 3 * 3) :=
    mul_le_mul_of_nonneg_left h_d3exp_le h_5_2_cube_nn
  have h_simp : (5 / 2 : ℝ) ^ 3 * (δ ^ 3 * 3) = (375 / 8) * δ ^ 3 := by ring
  have h_num_le : (375 / 8 : ℝ) * δ ^ 3 ≤ 47 * δ ^ 3 := by nlinarith [h_δ3_nn]
  linarith

/-- **Telescope norm bound on `‖P - PolyP‖`**: the sum of the four
`bch_cubic_telescope_term[1-4]` bounds. -/
private lemma bch_cubic_PolyP_diff_norm_le {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖NormedSpace.exp (Complex.I • F) * NormedSpace.exp (Complex.I • G) *
       NormedSpace.exp (-(Complex.I • F)) * NormedSpace.exp (-(Complex.I • G))
       - T2pos F * T2pos G * T2neg F * T2neg G‖ ≤ 253 * δ ^ 3 := by
  set A := NormedSpace.exp (Complex.I • F)
  set A' := T2pos F
  set B := NormedSpace.exp (Complex.I • G)
  set B' := T2pos G
  set C := NormedSpace.exp (-(Complex.I • F))
  set C' := T2neg F
  set D := NormedSpace.exp (-(Complex.I • G))
  set D' := T2neg G
  -- Telescope identity
  have h_telescope :
      A * B * C * D - A' * B' * C' * D'
        = (A - A') * B * C * D + A' * (B - B') * C * D
        + A' * B' * (C - C') * D + A' * B' * C' * (D - D') := by noncomm_ring
  -- Per-term bounds
  have h_t1 := bch_cubic_telescope_term1 δ hδ_nn hδ_le_one F G hF hG
  have h_t2 := bch_cubic_telescope_term2 δ hδ_nn hδ_le_one F G hF hG
  have h_t3 := bch_cubic_telescope_term3 δ hδ_nn hδ_le_one F G hF hG
  have h_t4 := bch_cubic_telescope_term4 δ hδ_nn hδ_le_one F G hF hG
  -- Triangle inequality on the 4-piece sum
  rw [h_telescope]
  have hs1 := norm_add_le
    ((A - A') * B * C * D + A' * (B - B') * C * D + A' * B' * (C - C') * D)
    (A' * B' * C' * (D - D'))
  have hs2 := norm_add_le
    ((A - A') * B * C * D + A' * (B - B') * C * D)
    (A' * B' * (C - C') * D)
  have hs3 := norm_add_le ((A - A') * B * C * D) (A' * (B - B') * C * D)
  linarith

/-- **R5.2b SHIP — Cubic BCH order-2 estimate**.

For any dimension `d`, any norm-bound `0 ≤ δ ≤ 1`, and any
(not-necessarily-Hermitian) matrices `F, G : Matrix (Fin d) (Fin d) ℂ` with
`‖F‖, ‖G‖ ≤ δ`:

  `‖exp(iF) · exp(iG) · exp(-iF) · exp(-iG) - exp(-⁅F, G⁆)‖ ≤ 320 · δ³`.

This is the **cubic** version of `MatrixBCH.bch_order_2_thm` (linear `200·δ`),
matching the Dawson-Nielsen Lemma 3 cubic shape (constant K ≤ 4 deferred to
R5.2c). Crucially, this version drops the Hermitian hypothesis required by
`bch_order_2_thm`: the `‖[F,G]‖ ≤ 2·δ²` bound holds for arbitrary `F, G` via
`commutator_norm_le`.

**Architecture (decomposition into 3 cubic-bounded pieces):**

  `P - Q = (P - PolyP) + bchPolyRem F G - (Q - (1 - [F,G]))`

where `PolyP := T2pos F · T2pos G · T2neg F · T2neg G`, and the identity
`PolyP - (1 - [F,G]) = bchPolyRem F G` is from `bchPoly_decomp` (definitionally).

  - `‖P - PolyP‖ ≤ 253·δ³` via 4-term telescope (`bch_cubic_PolyP_diff_norm_le`).
  - `‖bchPolyRem F G‖ ≤ 30·δ³` (R5.2a, `bchPolyRem_norm_le_cubic`).
  - `‖Q - (1 - [F,G])‖ ≤ 36·δ³` via order-2 Taylor remainder of `exp` at `-[F,G]`
    plus `‖[F,G]‖ ≤ 2·δ²`.

Total: 253 + 30 + 36 = 319 ≤ 320. -/
theorem bch_order_2_cubic_thm {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖NormedSpace.exp (Complex.I • F) * NormedSpace.exp (Complex.I • G) *
       NormedSpace.exp (-(Complex.I • F)) * NormedSpace.exp (-(Complex.I • G)) -
       NormedSpace.exp (-⁅F, G⁆)‖ ≤ 320 * δ ^ 3 := by
  set A := NormedSpace.exp (Complex.I • F)
  set B := NormedSpace.exp (Complex.I • G)
  set C := NormedSpace.exp (-(Complex.I • F))
  set D := NormedSpace.exp (-(Complex.I • G))
  set A' := T2pos F
  set B' := T2pos G
  set C' := T2neg F
  set D' := T2neg G
  set Q := NormedSpace.exp (-⁅F, G⁆)
  have h_δ3_nn : (0 : ℝ) ≤ δ ^ 3 := by positivity
  -- Algebraic identity: P - Q = (P - PolyP) + bchPolyRem F G - (Q - (1 - [F,G]))
  -- PolyP = A'·B'·C'·D' and bchPoly_decomp says
  --   A'·B'·C'·D' = (1 - [F,G]) + bchPolyRem F G
  -- so (P - PolyP) + (PolyP - (1 - [F,G])) - (Q - (1 - [F,G])) = P - Q.
  have h_poly_eq : A' * B' * C' * D' = (1 - ⁅F, G⁆) + bchPolyRem F G :=
    bchPoly_decomp F G
  have h_split :
      A * B * C * D - Q
        = (A * B * C * D - A' * B' * C' * D')
        + bchPolyRem F G
        - (Q - (1 - ⁅F, G⁆)) := by
    rw [h_poly_eq]; abel
  -- Triangle inequality
  have h_tri :
      ‖A * B * C * D - Q‖
        ≤ ‖A * B * C * D - A' * B' * C' * D'‖
        + ‖bchPolyRem F G‖
        + ‖Q - (1 - ⁅F, G⁆)‖ := by
    rw [h_split]
    have h_eq : (A * B * C * D - A' * B' * C' * D') + bchPolyRem F G - (Q - (1 - ⁅F, G⁆))
              = ((A * B * C * D - A' * B' * C' * D') + bchPolyRem F G)
                + (-(Q - (1 - ⁅F, G⁆))) := by abel
    rw [h_eq]
    have h1 := norm_add_le
      ((A * B * C * D - A' * B' * C' * D') + bchPolyRem F G)
      (-(Q - (1 - ⁅F, G⁆)))
    have h2 := norm_add_le (A * B * C * D - A' * B' * C' * D') (bchPolyRem F G)
    have h_neg : ‖-(Q - (1 - ⁅F, G⁆))‖ = ‖Q - (1 - ⁅F, G⁆)‖ := norm_neg _
    linarith
  -- 3 cubic bounds:
  have h_PolyP_diff : ‖A * B * C * D - A' * B' * C' * D'‖ ≤ 253 * δ ^ 3 :=
    bch_cubic_PolyP_diff_norm_le δ hδ_nn hδ_le_one F G hF hG
  have h_bchPolyRem : ‖bchPolyRem F G‖ ≤ 30 * δ ^ 3 :=
    bchPolyRem_norm_le_cubic δ hδ_nn hδ_le_one F G hF hG
  -- ‖Q - (1 - [F,G])‖ ≤ 4·δ⁴·exp(2δ²) ≤ 36·δ³
  have h_exp_rem_taylor : ‖Q - (1 - ⁅F, G⁆)‖ ≤ 4 * δ ^ 4 * Real.exp (2 * δ ^ 2) :=
    norm_exp_neg_comm_sub_one_plus_comm_le_of_delta δ hδ_nn F G hF hG
  -- numeric: 4·δ⁴·exp(2δ²) ≤ 36·δ³
  have h_exp_rem_num :
      4 * δ ^ 4 * Real.exp (2 * δ ^ 2) ≤ 36 * δ ^ 3 := by
    have hδ_sq_nn : (0 : ℝ) ≤ δ ^ 2 := by positivity
    have hδ_sq_le_one : δ ^ 2 ≤ 1 := by nlinarith
    have h_2δ2_le_2 : 2 * δ ^ 2 ≤ 2 := by linarith
    have h_exp_2_le_9 : Real.exp 2 ≤ 9 := by
      have h_eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [show (2 : ℝ) = 1 + 1 from by norm_num, Real.exp_add]
      have h_exp_1_lt : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
      have h_exp1_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
      rw [h_eq]; nlinarith
    have h_exp_2δ2_le : Real.exp (2 * δ ^ 2) ≤ 9 :=
      (Real.exp_le_exp.mpr h_2δ2_le_2).trans h_exp_2_le_9
    have h_4δ4_nn : (0 : ℝ) ≤ 4 * δ ^ 4 := by positivity
    have h_step1 : 4 * δ ^ 4 * Real.exp (2 * δ ^ 2) ≤ 4 * δ ^ 4 * 9 :=
      mul_le_mul_of_nonneg_left h_exp_2δ2_le h_4δ4_nn
    have h_δ4_le_δ3 : δ ^ 4 ≤ δ ^ 3 := by
      have h_eq : δ ^ 4 = δ ^ 3 * δ := by ring
      rw [h_eq]
      calc δ ^ 3 * δ ≤ δ ^ 3 * 1 := mul_le_mul_of_nonneg_left hδ_le_one h_δ3_nn
        _ = δ ^ 3 := by ring
    have h_step2 : 4 * δ ^ 4 * 9 = 36 * δ ^ 4 := by ring
    have h_step3 : 36 * δ ^ 4 ≤ 36 * δ ^ 3 :=
      mul_le_mul_of_nonneg_left h_δ4_le_δ3 (by norm_num)
    linarith
  have h_exp_rem : ‖Q - (1 - ⁅F, G⁆)‖ ≤ 36 * δ ^ 3 := h_exp_rem_taylor.trans h_exp_rem_num
  -- Compose: 253 + 30 + 36 = 319 ≤ 320
  linarith

/-! ## 11. AA Bridge Lemma 6.1 — group commutator quadratic shrinkage (R5.3 SHIP)

The Aharonov-Arad Bridge Lemma 6.1 statement (group commutator quadratic
shrinkage from BCH order-2 estimate). Given `F, G : Matrix _ _ ℂ` with
`‖F‖, ‖G‖ ≤ δ ≤ 1`, the GROUP commutator
`[exp(iF), exp(iG)] := exp(iF)·exp(iG)·exp(-iF)·exp(-iG)`
satisfies `‖[exp(iF), exp(iG)] - 1‖ ≤ C · δ²`.

This is the **quadratic-shrinkage** content of AA Lemma 6.1: starting
from elements of "scale δ" in BCH coordinates, the group commutator is
of scale δ², not δ. Iterating, ε → ε² → ε⁴ → ... → 0 quadratically.

The **cubic-linearization** companion (R5.3.2):
  `‖[exp(iF), exp(iG)] - (1 - [F, G])‖ ≤ C · δ³`
identifies the LEADING-ORDER Lie-algebra DIRECTION of the group
commutator. This is consumed by Lemma 6.2 (basis-rotation / LieSpan
argument) since LieSpanProp is about Lie commutators `[F, G]`.

Both theorems are direct compositions of `bch_order_2_cubic_thm` (R5.2b)
with Taylor remainder bounds on `exp(-[F, G])`. -/

/-- **AA Bridge Lemma 6.1 — quadratic shrinkage** (R5.3 SHIP).

For `F, G : Matrix (Fin d) (Fin d) ℂ` with `‖F‖, ‖G‖ ≤ δ ≤ 1`:

  `‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - 1‖ ≤ 338 · δ²`.

This is the group commutator quadratic shrinkage: starting from
"scale δ" Lie-algebra elements, the group commutator is "scale δ²".
Iterating this lemma drives the commutator hierarchy `δ → δ² → δ⁴ → ...`
to zero quadratically.

**Proof.** Triangle inequality:
  `‖P - 1‖ ≤ ‖P - exp(-[F, G])‖ + ‖exp(-[F, G]) - 1‖`
where `P := exp(iF)·exp(iG)·exp(-iF)·exp(-iG)`.

- First term ≤ `320·δ³` (R5.2b, `bch_order_2_cubic_thm`).
- Second term: `‖exp(-[F, G]) - 1‖ ≤ ‖[F, G]‖ · exp(‖[F, G]‖)`
  (order-1 Taylor remainder of `exp`); with `‖[F, G]‖ ≤ 2δ²`
  (from `commutator_norm_le ≤ 2·‖F‖·‖G‖`) and `exp(2δ²) ≤ exp(2) ≤ 9`
  (for δ ≤ 1), we get `≤ 18·δ²`.

For δ ≤ 1: `320·δ³ ≤ 320·δ²`, so total `≤ 338·δ²`.

**No Hermitian hypothesis required** — the bound uses generic
`commutator_norm_le ≤ 2·‖F‖·‖G‖`, not the Hermitian-specific
`MatrixBCH.hermitian_commutator_norm_le`. -/
theorem bch_group_commutator_quadratic_shrinkage {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖NormedSpace.exp (Complex.I • F) * NormedSpace.exp (Complex.I • G) *
       NormedSpace.exp (-(Complex.I • F)) * NormedSpace.exp (-(Complex.I • G))
       - 1‖ ≤ 338 * δ ^ 2 := by
  set P := NormedSpace.exp (Complex.I • F) * NormedSpace.exp (Complex.I • G) *
           NormedSpace.exp (-(Complex.I • F)) * NormedSpace.exp (-(Complex.I • G))
  set Q := NormedSpace.exp (-⁅F, G⁆)
  -- Triangle: ‖P - 1‖ ≤ ‖P - Q‖ + ‖Q - 1‖
  have h_split : P - 1 = (P - Q) + (Q - 1) := by abel
  have h_tri : ‖P - 1‖ ≤ ‖P - Q‖ + ‖Q - 1‖ := by
    rw [h_split]; exact norm_add_le _ _
  -- ‖P - Q‖ ≤ 320·δ³ (R5.2b)
  have h_PQ : ‖P - Q‖ ≤ 320 * δ ^ 3 :=
    bch_order_2_cubic_thm δ hδ_nn hδ_le_one F G hF hG
  -- ‖Q - 1‖ via order-1 Taylor of exp at -[F, G]
  have h_Q_sub_1_taylor : ‖Q - 1‖ ≤ ‖⁅F, G⁆‖ * Real.exp ‖⁅F, G⁆‖ := by
    have := MatrixBCH.norm_exp_smul_sub_one_le (-⁅F, G⁆) 1 (by rw [norm_one])
    simp only [one_smul] at this
    rwa [show ‖(-⁅F, G⁆ : Matrix (Fin d) (Fin d) ℂ)‖ = ‖⁅F, G⁆‖ from norm_neg _] at this
  -- ‖[F, G]‖ ≤ 2·δ²  (generic commutator bound, no Hermitian)
  have h_comm_le : ‖⁅F, G⁆‖ ≤ 2 * δ ^ 2 := by
    have h_comm := commutator_norm_le F G
    have h_2F_le : 2 * ‖F‖ ≤ 2 * δ := by linarith [norm_nonneg F]
    have hG_nn : (0 : ℝ) ≤ ‖G‖ := norm_nonneg _
    have h_2δ_nn : (0 : ℝ) ≤ 2 * δ := by linarith [norm_nonneg F]
    have h_FG_le : 2 * ‖F‖ * ‖G‖ ≤ 2 * δ * δ := by
      calc 2 * ‖F‖ * ‖G‖ ≤ 2 * δ * ‖G‖ := mul_le_mul_of_nonneg_right h_2F_le hG_nn
        _ ≤ 2 * δ * δ := mul_le_mul_of_nonneg_left hG h_2δ_nn
    have h_eq : 2 * δ * δ = 2 * δ ^ 2 := by ring
    linarith
  have h_comm_nn : (0 : ℝ) ≤ ‖⁅F, G⁆‖ := norm_nonneg _
  have h_2δ2_nn : (0 : ℝ) ≤ 2 * δ ^ 2 := by positivity
  -- ‖Q - 1‖ ≤ 2·δ²·exp(2·δ²)
  have h_Q_sub_1 : ‖Q - 1‖ ≤ (2 * δ ^ 2) * Real.exp (2 * δ ^ 2) := by
    have h_exp_F_nn : (0 : ℝ) ≤ Real.exp ‖⁅F, G⁆‖ := le_of_lt (Real.exp_pos _)
    have h_exp_le : Real.exp ‖⁅F, G⁆‖ ≤ Real.exp (2 * δ ^ 2) := Real.exp_le_exp.mpr h_comm_le
    have h_step1 : ‖⁅F, G⁆‖ * Real.exp ‖⁅F, G⁆‖ ≤ (2 * δ ^ 2) * Real.exp ‖⁅F, G⁆‖ :=
      mul_le_mul_of_nonneg_right h_comm_le h_exp_F_nn
    have h_step2 : (2 * δ ^ 2) * Real.exp ‖⁅F, G⁆‖ ≤ (2 * δ ^ 2) * Real.exp (2 * δ ^ 2) :=
      mul_le_mul_of_nonneg_left h_exp_le h_2δ2_nn
    linarith
  -- Numeric collapse: bound exp(2δ²) ≤ 9 for δ ≤ 1
  have h_δ2_nn : (0 : ℝ) ≤ δ ^ 2 := by positivity
  have h_δ3_nn : (0 : ℝ) ≤ δ ^ 3 := by positivity
  have hδ_sq_le_one : δ ^ 2 ≤ 1 := by nlinarith
  have h_2δ2_le_2 : 2 * δ ^ 2 ≤ 2 := by linarith
  have h_exp_2_le_9 : Real.exp 2 ≤ 9 := by
    have h_eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 from by norm_num, Real.exp_add]
    have h_exp_1_lt : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    have h_exp1_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    rw [h_eq]; nlinarith
  have h_exp_2δ2_le : Real.exp (2 * δ ^ 2) ≤ 9 :=
    (Real.exp_le_exp.mpr h_2δ2_le_2).trans h_exp_2_le_9
  have h_Q_sub_1_num : ‖Q - 1‖ ≤ 18 * δ ^ 2 := by
    have h_step : (2 * δ ^ 2) * Real.exp (2 * δ ^ 2) ≤ (2 * δ ^ 2) * 9 :=
      mul_le_mul_of_nonneg_left h_exp_2δ2_le h_2δ2_nn
    have h_eq : (2 * δ ^ 2) * 9 = 18 * δ ^ 2 := by ring
    linarith
  -- 320·δ³ ≤ 320·δ² for δ ≤ 1
  have h_δ3_le_δ2 : δ ^ 3 ≤ δ ^ 2 := by
    have h_eq : δ ^ 3 = δ ^ 2 * δ := by ring
    rw [h_eq]
    calc δ ^ 2 * δ ≤ δ ^ 2 * 1 := mul_le_mul_of_nonneg_left hδ_le_one h_δ2_nn
      _ = δ ^ 2 := by ring
  have h_PQ_num : ‖P - Q‖ ≤ 320 * δ ^ 2 := by
    have : 320 * δ ^ 3 ≤ 320 * δ ^ 2 :=
      mul_le_mul_of_nonneg_left h_δ3_le_δ2 (by norm_num)
    linarith
  -- 320 + 18 = 338
  linarith

/-- **AA Bridge Lemma 6.1 cubic linearization** (R5.3.2 SHIP).

For `F, G : Matrix (Fin d) (Fin d) ℂ` with `‖F‖, ‖G‖ ≤ δ ≤ 1`:

  `‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - (1 - ⁅F, G⁆)‖ ≤ 356 · δ³`.

The **leading-order linearization** of the group commutator in Lie
coordinates: `[exp(iF), exp(iG)] = (1 - [F, G]) + O(δ³)`. Consumed by
AA Lemma 6.2 (basis-rotation): since `LieSpanProp` is about Lie
commutators `[F, G]`, the cubic-linearization identifies how a group
commutator points in the direction of a Lie commutator (with cubic
error).

**Proof.** Triangle inequality:
  `‖P - (1 - [F, G])‖ ≤ ‖P - exp(-[F, G])‖ + ‖exp(-[F, G]) - (1 - [F, G])‖`
- First term ≤ `320·δ³` (R5.2b).
- Second term ≤ `36·δ³` (R5.2b §9, `norm_exp_neg_comm_sub_one_plus_comm_le_of_delta`).

Total: `320 + 36 = 356`. -/
theorem bch_group_commutator_linearization {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖NormedSpace.exp (Complex.I • F) * NormedSpace.exp (Complex.I • G) *
       NormedSpace.exp (-(Complex.I • F)) * NormedSpace.exp (-(Complex.I • G))
       - (1 - ⁅F, G⁆)‖ ≤ 356 * δ ^ 3 := by
  set P := NormedSpace.exp (Complex.I • F) * NormedSpace.exp (Complex.I • G) *
           NormedSpace.exp (-(Complex.I • F)) * NormedSpace.exp (-(Complex.I • G))
  set Q := NormedSpace.exp (-⁅F, G⁆)
  -- P - (1 - [F,G]) = (P - Q) + (Q - (1 - [F,G]))
  have h_split : P - (1 - ⁅F, G⁆) = (P - Q) + (Q - (1 - ⁅F, G⁆)) := by abel
  have h_tri : ‖P - (1 - ⁅F, G⁆)‖ ≤ ‖P - Q‖ + ‖Q - (1 - ⁅F, G⁆)‖ := by
    rw [h_split]; exact norm_add_le _ _
  have h_PQ : ‖P - Q‖ ≤ 320 * δ ^ 3 :=
    bch_order_2_cubic_thm δ hδ_nn hδ_le_one F G hF hG
  have h_Q_taylor : ‖Q - (1 - ⁅F, G⁆)‖ ≤ 4 * δ ^ 4 * Real.exp (2 * δ ^ 2) :=
    norm_exp_neg_comm_sub_one_plus_comm_le_of_delta δ hδ_nn F G hF hG
  -- Numeric: 4·δ⁴·exp(2δ²) ≤ 36·δ³ for δ ≤ 1
  have h_δ3_nn : (0 : ℝ) ≤ δ ^ 3 := by positivity
  have h_δ4_nn : (0 : ℝ) ≤ δ ^ 4 := by positivity
  have hδ_sq_nn : (0 : ℝ) ≤ δ ^ 2 := by positivity
  have hδ_sq_le_one : δ ^ 2 ≤ 1 := by nlinarith
  have h_2δ2_le_2 : 2 * δ ^ 2 ≤ 2 := by linarith
  have h_exp_2_le_9 : Real.exp 2 ≤ 9 := by
    have h_eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 from by norm_num, Real.exp_add]
    have h_exp_1_lt : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    have h_exp1_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    rw [h_eq]; nlinarith
  have h_exp_2δ2_le : Real.exp (2 * δ ^ 2) ≤ 9 :=
    (Real.exp_le_exp.mpr h_2δ2_le_2).trans h_exp_2_le_9
  have h_4δ4_nn : (0 : ℝ) ≤ 4 * δ ^ 4 := by positivity
  have h_Q_taylor_num : ‖Q - (1 - ⁅F, G⁆)‖ ≤ 36 * δ ^ 3 := by
    have h_step1 : 4 * δ ^ 4 * Real.exp (2 * δ ^ 2) ≤ 4 * δ ^ 4 * 9 :=
      mul_le_mul_of_nonneg_left h_exp_2δ2_le h_4δ4_nn
    have h_δ4_le_δ3 : δ ^ 4 ≤ δ ^ 3 := by
      have h_eq : δ ^ 4 = δ ^ 3 * δ := by ring
      rw [h_eq]
      calc δ ^ 3 * δ ≤ δ ^ 3 * 1 := mul_le_mul_of_nonneg_left hδ_le_one h_δ3_nn
        _ = δ ^ 3 := by ring
    have h_step2 : 4 * δ ^ 4 * 9 = 36 * δ ^ 4 := by ring
    have h_step3 : 36 * δ ^ 4 ≤ 36 * δ ^ 3 :=
      mul_le_mul_of_nonneg_left h_δ4_le_δ3 (by norm_num)
    linarith
  linarith

/-! ## 12. Module summary

MatrixBCHCubic.lean (Wave 2d.2-followup-R5.2a+R5.2b+R5.3 ship, 2026-05-13 PM):
**BCH cubic norm bound on the polynomial residual + headline cubic
BCH order-2 estimate + AA Bridge Lemma 6.1 quadratic shrinkage**.

  *AA Bridge Lemma 6.1 (§11, R5.3 SHIP):*
  - **`bch_group_commutator_quadratic_shrinkage`** —
    `‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - 1‖ ≤ 338·δ²` for `‖F‖, ‖G‖ ≤ δ ≤ 1`.
    The quadratic-shrinkage content of AA Lemma 6.1: starting from
    "scale δ" Lie-algebra elements, the group commutator is "scale δ²".
  - **`bch_group_commutator_linearization`** —
    `‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - (1 - ⁅F, G⁆)‖ ≤ 356·δ³`.
    The cubic-linearization: the leading-order DIRECTION of the group
    commutator is the Lie commutator `-⁅F, G⁆` (consumed by Lemma 6.2).

  No Hermitian hypothesis required — uses `commutator_norm_le ≤ 2·‖F‖·‖G‖`.

**R5.2a + R5.2b SHIP — Substantive content**:

  *Algebraic infrastructure (§§1-2, shipped R5.2.1):*
  - `T2pos`, `T2neg` — order-2 Taylor polynomials of `exp(±iX)`.
  - `T2pos_neg_eq_T2neg` — symmetry identity.
  - `T2pos_T2neg_self` — same-F factorization
    `T2pos F · T2neg F = 1 + F⁴/4` (the substantive product collapse).
  - `bchPolyRem` — explicit cubic-or-higher polynomial residual.
  - `bchPoly_decomp` — trivial decomposition (names the residual).

  *Norm bounds (§3):*
  - `T2pos_norm_le`, `T2neg_norm_le` — `≤ 1 + ‖F‖ + ‖F‖²/2`.
  - `T2pos_sub_one_norm_le`, `T2neg_sub_one_norm_le` — `≤ ‖F‖ + ‖F‖²/2`.
  - `commutator_norm_le` — generic `‖⁅F, G⁆‖ ≤ 2·‖F‖·‖G‖`.

  *Commutator linearization (§4, R5.2a):*
  - `lie_sub_lie_swap_decomp` — universal Lie identity.
  - `lie_I_G_neg_I_F` — key smul-Lie cancellation `⁅I•G, -(I•F)⁆ = -⁅F, G⁆`.
  - **`commutator_T2pos_T2neg_plus_FG_decomp`** — explicit 2-commutator
    decomposition of `⁅T2pos G, T2neg F⁆ + ⁅F, G⁆`.

  *Cubic norm bound on commutator residual (§5, R5.2a):*
  - **`commutator_T2pos_T2neg_plus_FG_norm_le_cubic`** —
    `‖⁅T2pos G, T2neg F⁆ + ⁅F, G⁆‖ ≤ 3·δ³`.

  *δ-parameterized helpers (§6, R5.2a):*
  - `T2pos_norm_le_of_delta`, `T2neg_norm_le_of_delta` — `≤ 5/2`.
  - `T2pos_sub_one_norm_le_of_delta`, `T2neg_sub_one_norm_le_of_delta`
    — `≤ 3δ/2`.
  - `commutator_T2pos_T2neg_norm_le_quadratic` — `≤ 9δ²/2`.

  *Polynomial-residual cubic bound (§7, R5.2a SHIP):*
  - `bchPolyRem_decomp` — explicit 6-piece algebraic decomposition.
  - **`bchPolyRem_norm_le_cubic`** — `‖bchPolyRem F G‖ ≤ 30·δ³`
    for `‖F‖, ‖G‖ ≤ δ ≤ 1`.

  *Taylor-remainder bridges (§8, R5.2b):*
  - `T2pos_eq_taylor_form`, `T2neg_eq_taylor_form` — express T2pos/T2neg
    in Mathlib Taylor form for `MatrixTaylor` consumption.
  - **`norm_exp_iF_sub_T2pos_le`** — `‖exp(iF) - T2pos F‖ ≤ ‖F‖³·exp(‖F‖)`.
  - **`norm_exp_neg_iF_sub_T2neg_le`** — `‖exp(-iF) - T2neg F‖ ≤ ‖F‖³·exp(‖F‖)`.
  - **`norm_exp_neg_comm_sub_one_plus_comm_le`** —
    `‖exp(-⁅F,G⁆) - (1 - ⁅F,G⁆)‖ ≤ ‖⁅F,G⁆‖²·exp(‖⁅F,G⁆‖)`.

  *δ-parameterized Taylor bounds (§9, R5.2b):*
  - `norm_exp_iF_sub_T2pos_le_of_delta` — `≤ δ³·exp(δ)`.
  - `norm_exp_neg_iF_sub_T2neg_le_of_delta` — `≤ δ³·exp(δ)`.
  - `norm_exp_neg_comm_sub_one_plus_comm_le_of_delta` — `≤ 4·δ⁴·exp(2·δ²)`.

  *Headline cubic BCH estimate (§10, R5.2b SHIP):*
  - **`bch_order_2_cubic_thm`** —
    `‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - exp(-⁅F,G⁆)‖ ≤ 320·δ³`
    for `‖F‖, ‖G‖ ≤ δ ≤ 1`. No Hermitian hypothesis required (strictly
    stronger than `MatrixBCH.bch_order_2_thm` which needs Hermitian +
    gives only linear `200·δ`).

**Deferred (R5.2c sub-wave)**:
  - R5.2c: Optimize constant K (current K = 320 in `bch_order_2_cubic_thm`,
    K = 30 in `bchPolyRem_norm_le_cubic`; D-N original K ≤ 4).

**Downstream impact (R5.2a + R5.2b ship enables)**:
  - AA Bridge Lemma 6.1 (R5.3, deferred) becomes provable:
    `‖[g,h] - 1‖ ≤ C·ε²` for group commutator of ε-close elements.
    The cubic bound is what makes the iteration converge (the prior
    linear `200·δ` dominated the quadratic shrinkage; cubic `320·δ³`
    is dominated by `O(δ²)` for δ ≤ 1).
  - AA axiom `aa_residual_interior_at_one_for_hom` becomes
    constructively dischargeable via the chain R5.1 + R5.2 + R5.3 +
    R5.4 + R5.5 (full multi-session pipeline).

Zero sorry. Zero new project-local axioms.
-/

end SKEFTHawking.MatrixBCHCubic
