/-
SK_EFT_Hawking Phase 6p Wave 2d.2-followup-R5.2 (sub-wave 1): Order-2
Taylor polynomial product algebraic decomposition (BCH cubic-bound prep).

This module ships the **algebraic infrastructure** for tightening the
existing `bch_order_2_thm` (linear bound `200·δ`) to the cubic form
`K·δ³` mandated by Dawson-Nielsen Lemma 3 and required as an upstream
dependency for AA Bridge Lemma 6.1 (commutator quadratic-shrinkage
iteration; see `FKLW/AharonovAradLemma6.lean`).

## Mathematical context

For Hermitian F, G with `‖F‖, ‖G‖ ≤ δ ≤ 1`:

  `exp(±iX) = T₂(±X) + R₃(±X)`

where `T₂(±X) := 1 ± iX - X²/2` is the order-2 Taylor polynomial and
`R₃(±X)` is the cubic remainder, satisfying `‖R₃(±X)‖ ≤ δ³ · exp(δ)`
(via `MatrixTaylor.norm_exp_sub_order3_le_loose`).

The 4-fold product then decomposes:

  `exp(iF)·exp(iG)·exp(-iF)·exp(-iG)`
  `  = T₂(F)·T₂(G)·T₂(-F)·T₂(-G)      [polynomial part]`
  `    + (cross terms with at least one R₃ factor)  [cubic remainder]`

The cross-term bound is straightforward: at least one factor of size
`O(δ³)`, others bounded ≤ `(1 + δ + δ²/2) ≤ 3` for `δ ≤ 1`. Bound
≤ `15·δ³·e·27 ≈ 1100·δ³` (loose).

The polynomial part `T₂(F)·T₂(G)·T₂(-F)·T₂(-G)` reduces at order ≤ 2
to `1 - [F,G]` exactly (the BCH leading correction). At order ≥ 3,
some 66 explicit monomial terms remain, each bounded ≤ `(coefficient) · δ^k`
for `k ≥ 3`. Total polynomial-remainder bound: `O(δ³)`.

## What this ship contains

  - `T2pos X := 1 + iX - X²/2` — order-2 Taylor polynomial of `exp(iX)`.
  - `T2neg X := 1 - iX - X²/2` — order-2 Taylor polynomial of `exp(-iX)`.
  - `bchPolyRem F G := T2pos F · T2pos G · T2neg F · T2neg G - (1 - [F,G])`
    — the explicit cubic-or-higher polynomial residual.
  - `bchPoly_decomp` — trivial decomposition identity (the polynomial
    product equals `1 - [F,G] + bchPolyRem`).

## What is deferred (R5.2 sub-waves)

  - **R5.2a**: Prove `‖bchPolyRem F G‖ ≤ C·δ³` for some explicit C.
    Strategy: enumerate the order ≥ 3 monomials (66 terms total) and
    apply submultiplicativity. Lift each term to a closed-form bound.
  - **R5.2b**: Compose with the Taylor remainder bound to derive the
    full `bch_order_2_cubic_thm` (replacing the linear `200·δ` with
    cubic `K·δ³` in the headline theorem).
  - **R5.2c**: Optimize the constant K. Target K ≤ 4 per the original
    D-N analysis; the loose-bound version (K ≤ 1000 or so) is
    sufficient for downstream AA Bridge Lemma 6.1.

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
    definitions + a trivial algebraic decomposition.
  - Preemptive-strengthening:
    * P3/P4/P5 (trivial discharge): `bchPoly_decomp` is genuinely
      `a = b + (a - b)` (algebraically trivial), but its purpose
      is to NAME the residual so future bound work can target it.
      The substantive content is in the planned `R5.2a` cubic bound.
    * P6 (cross-module bridge): all cross-references docstring-cited
      (MatrixTaylor.norm_exp_sub_order3_le_loose, MatrixBCH).

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

/-! ## 3. Module summary

MatrixBCHCubic.lean (Wave 2d.2-followup-R5.2.1 ship, 2026-05-13):
algebraic infrastructure for the BCH cubic-bound discharge.

**Substantive content shipped**:
  - `T2pos`, `T2neg` — order-2 Taylor polynomials of `exp(±iX)`.
  - `T2pos_neg_eq_T2neg` — symmetry identity.
  - `bchPolyRem` — explicit cubic-or-higher polynomial residual.
  - `bchPoly_decomp` — trivial decomposition (names the residual).

**Deferred (R5.2 sub-waves, multi-session)**:
  - R5.2a: `‖bchPolyRem F G‖ ≤ C·δ³` bound (enumerate ~66 monomials).
  - R5.2b: Compose with Taylor cross-term bounds for the full
    `bch_order_2_cubic_thm`.
  - R5.2c: Optimize constant K ≤ 4 (per D-N original).

**Downstream impact when R5.2 fully ships**:
  - `bch_order_2_cubic_thm` replaces `bch_order_2_thm` (linear bound
    `200·δ` → cubic `K·δ³`).
  - AA Bridge Lemma 6.1 (R5.3, deferred) becomes provable:
    `‖[g,h] - 1‖ ≤ C·ε²` for group commutator of ε-close elements.
  - AA axiom `aa_residual_interior_at_one_for_hom` becomes
    constructively dischargeable via the chain R5.1 + R5.2 + R5.3 +
    R5.4 + R5.5 (full multi-session pipeline).

Zero sorry. Zero new project-local axioms.
-/

end SKEFTHawking.MatrixBCHCubic
