/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Generic order-2 BCH cubic estimate (Mathlib-upstream-PR-ready presentation)

Phase 6x Track M.1 ships a Mathlib-upstream-PR-ready presentation of the
project's `bch_order_2_cubic_thm` (in `SKEFTHawking.MatrixBCHCubic`).

The lemma is already generic over the matrix dimension parameter
`d : ℕ` in the project version. This file presents it with:
  * Mathlib-namespace placement (`Matrix.BCH`).
  * Mathlib-style docstring with full mathematical context.
  * Worked example demonstrating use at `Fin 2` (SU(2) case).
  * Citation to Dawson–Nielsen 2006.
  * Pointer to proposed Mathlib filename.

The `m : Type*` (arbitrary index type with `Fintype`) generalization
is a *standard Matrix.reindex transfer* (the L∞-op norm is reindex-
invariant; matrix multiplication, `exp`, and the Lie bracket all
commute with `Matrix.reindex` via `Matrix.reindexAlgEquiv`). The
in-project ship uses the `Fin d` form (matching the existing chain),
with the `m : Type*` reindex transfer left as the standard Mathlib-PR
boilerplate at submission time.

## Headline

`Matrix.BCH.bchOrder2Cubic`: for any matrix dimension `d : ℕ` with
`[Nonempty (Fin d)]`, norm-bound `0 ≤ δ ≤ 1`, and matrices
`F, G : Matrix (Fin d) (Fin d) ℂ` with `‖F‖, ‖G‖ ≤ δ`,

```
‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - exp(-⁅F,G⁆)‖ ≤ 320 · δ³.
```

## Mathlib-upstream target

Proposed file: `Mathlib/Analysis/Calculus/BCH/OrderTwo.lean`.
Accompanying lemma chain (`bchPolyRem_norm_le_cubic`,
`bch_cubic_PolyP_diff_norm_le`,
`norm_exp_neg_comm_sub_one_plus_comm_le_of_delta`) is already in the
project version and would be lifted alongside.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.MatrixBCHCubic

set_option autoImplicit false

namespace Matrix.BCH

open NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Order-2 Baker–Campbell–Hausdorff cubic estimate** (group-commutator form).

For any matrix dimension `d : ℕ` with `[Nonempty (Fin d)]`, any precision
threshold `δ ∈ [0, 1]`, and any two complex matrices
`F, G : Matrix (Fin d) (Fin d) ℂ` with `‖F‖, ‖G‖ ≤ δ` (in the L∞-op norm),
the four-fold group-commutator product
`exp(iF)·exp(iG)·exp(-iF)·exp(-iG)` approximates `exp(-⁅F,G⁆)` (where
`⁅F,G⁆ = F·G - G·F` is the matrix Lie bracket) to within a *cubic*
error `320·δ³`:

```
‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - exp(-⁅F,G⁆)‖ ≤ 320·δ³.
```

This is the **cubic** version of the linear order-2 BCH estimate; it
drops the Hermitian hypothesis required by the linear version (the
`‖⁅F,G⁆‖ ≤ 2·δ²` bound holds for arbitrary `F, G` via the matrix-
commutator norm inequality).

The constant `320 = 253 + 30 + 36 + 1` decomposes as:
  - `253 · δ³` — 4-term telescope `‖P - PolyP‖` (Taylor-2 of each `exp` factor).
  - `30 · δ³` — `‖bchPolyRem F G‖` (polynomial remainder after BCH).
  - `36 · δ³` — order-2 Taylor remainder of `exp(-⁅F,G⁆)`.
  - `1 · δ³` — rounding slack.

## Generalization to arbitrary index type

The lemma extends to `M : Matrix m m ℂ` for any `m : Type*` with
`[Fintype m] [DecidableEq m] [Nonempty m]` via the canonical equivalence
`Fintype.equivFin m : m ≃ Fin (Fintype.card m)` and `Matrix.reindexAlgEquiv`:
both sides of the inequality transfer through `Matrix.reindex e e` (which
is a normed-algebra automorphism), so the bound transfers unchanged. This
standard transfer is left as Mathlib-submission boilerplate.

## Citations

  - Dawson, C. M., and Nielsen, M. A. (2006). *The Solovay–Kitaev
    algorithm.* Quantum Information & Computation 6, 81–95.
    arXiv:quant-ph/0505030, Lemma 3.
-/
theorem bchOrder2Cubic {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖exp (Complex.I • F) * exp (Complex.I • G) *
       exp (-(Complex.I • F)) * exp (-(Complex.I • G)) -
       exp (-⁅F, G⁆)‖ ≤ 320 * δ ^ 3 :=
  SKEFTHawking.MatrixBCHCubic.bch_order_2_cubic_thm δ hδ_nn hδ_le_one F G hF hG

/-- Compact illustrative example: the BCH cubic estimate applied at `Fin 2`
(the canonical SU(2) setting for quantum-compiler applications). -/
example (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin 2) (Fin 2) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖exp (Complex.I • F) * exp (Complex.I • G) *
       exp (-(Complex.I • F)) * exp (-(Complex.I • G)) -
       exp (-⁅F, G⁆)‖ ≤ 320 * δ ^ 3 :=
  bchOrder2Cubic δ hδ_nn hδ_le_one F G hF hG

end Matrix.BCH
