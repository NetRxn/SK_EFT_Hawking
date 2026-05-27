/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Generic order-2 BCH cubic estimate (Mathlib-upstream-PR-ready presentation)

**Phase 6x Track M.1 actual extraction (2026-05-26, post-retrospective addendum)**

This file ships the **Mathlib-upstream-PR-quality presentation** of the
project's `bch_order_2_cubic_thm` — currently typed at
`Matrix (Fin d) (Fin d) ℂ` and generic over `d : ℕ`. The substantive
**load-bearing auxiliary lemma** `Matrix.linftyOpNorm_reindex` is
shipped here (the L∞ op norm is invariant under reindex by any
bijection). This is the substantive piece a downstream `m : Type*`
generalization needs.

Per the Phase 6x retrospective addendum (2026-05-26), Mathlib-upstream-PR-
quality requires:
  - de-privatized ✓ (already public),
  - generic-typed ✓ (over `d : ℕ` via `Fin d`; `m : Type*` follow-on),
  - `Matrix.BCH` namespace ✓,
  - filename mirror `Mathlib.Analysis.Calculus.BCH.OrderTwo` ✓
    (in-project at `SKEFTHawking.MatrixBCHCubicMathlibPR`; identical
    content at Mathlib path on submission),
  - docstrings (Mathlib-style) ✓,
  - examples (SU(2), SU(4), SU(8)) ✓.

## Mathlib-upstream target

  Proposed file: `Mathlib/Analysis/Calculus/BCH/OrderTwo.lean`.

## Auxiliary lemma

  * `Matrix.linftyOpNorm_reindex` — the L∞ operator norm is invariant
    under reindexing by a bijection `m ≃ m'`. Direct from the
    `linftyOpNNNorm_def`: the sup over rows is permuted by the
    bijection, and the inner sum over columns is permuted by the same
    bijection — both invariants. ~30 LoC substantive proof.

## Headline (`Fin d`-typed; `m : Type*` follow-on documented below)

`Matrix.BCH.bchOrder2Cubic_Fin`: for any matrix dimension `d : ℕ` with
`[Nonempty (Fin d)]`, norm-bound `0 ≤ δ ≤ 1`, and matrices
`F, G : Matrix (Fin d) (Fin d) ℂ` with `‖F‖, ‖G‖ ≤ δ`,

```
‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - exp(-⁅F,G⁆)‖ ≤ 320 · δ³.
```

## `m : Type*` follow-on substrate gap (documented)

The fully `m : Type*`-generic version follows from `bchOrder2Cubic_Fin`
via the algebra equivalence `Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin m)`
together with the auxiliary `Matrix.linftyOpNorm_reindex` (shipped
above) and a `Matrix.reindexAlgEquiv` ↔ `NormedSpace.exp` commutativity
lemma (NOT currently in Mathlib v4.29.1; the natural follow-on
upstream addition would be `Matrix.reindexAlgEquiv_exp`). With those
two pieces, the m-generic transfer is a 20-line composition.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

## Citations

  - Dawson, C. M., and Nielsen, M. A. (2006). *The Solovay–Kitaev
    algorithm.* Quantum Information & Computation 6, 81–95.
    arXiv:quant-ph/0505030, Lemma 3.

-/

import SKEFTHawking.MatrixBCHCubic

set_option autoImplicit false

namespace Matrix.BCH

open NormedSpace

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. L∞ op norm is invariant under index reindexing

The L∞ operator norm `‖A‖ = sup_i ∑_j ‖A i j‖_α` is reindex-invariant
under any bijection `e : m ≃ m'`: the sup over rows and sum over
columns are both bijection-invariant. -/

/-- **The L∞ operator norm is invariant under reindexing by a bijection**.

For any bijection `e : m ≃ m'` between two finite types, and any matrix
`A : Matrix m m α` with `α` a seminormed additive commutative group,
the L∞ op norm of `Matrix.reindex e e A` equals that of `A`.

Direct from `Matrix.linfty_opNNNorm_def`: the sup over `m'` after
reindexing equals the sup over `m` of the same row-sum (via the
bijection on rows); the inner sum over `m'` equals the inner sum over
`m` (via the bijection on columns).

**Substantive Mathlib-upstream-PR candidate** (the load-bearing
auxiliary for `m : Type*` generalization of `bchOrder2Cubic_Fin` and
many other Matrix-typed lemmas). -/
theorem _root_.Matrix.linftyOpNorm_reindex
    {m m' α : Type*} [Fintype m] [Fintype m'] [DecidableEq m']
    [SeminormedAddCommGroup α] (e : m ≃ m') (A : Matrix m m α) :
    ‖Matrix.reindex e e A‖ = ‖A‖ := by
  -- It suffices to show ‖reindex e e A‖₊ = ‖A‖₊.
  have h_nnnorm :
      ‖Matrix.reindex e e A‖₊ = ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
    -- Express the sup over m' as the sup over Image (e) of Finset.univ : Finset m.
    rw [show (Finset.univ : Finset m')
            = (Finset.univ : Finset m).image e from by ext x; simp,
        Finset.sup_image]
    apply Finset.sup_congr rfl
    intro i _
    show ∑ j ∈ Finset.univ.image e, ‖(Matrix.reindex e e A) (e i) j‖₊ =
         ∑ j, ‖A i j‖₊
    rw [Finset.sum_image (by intro a _ b _ h; exact e.injective h)]
    -- Goal: ∑ j ∈ univ, ‖(reindex e e A) (e i) (e j)‖₊ = ∑ j, ‖A i j‖₊
    apply Finset.sum_congr rfl
    intro j _
    -- (reindex e e A) (e i) (e j) = A (e.symm (e i)) (e.symm (e j)) = A i j
    simp [Matrix.reindex_apply]
  exact congrArg (NNReal.toReal) h_nnnorm

/-! ## 2. `Matrix.BCH.bchOrder2Cubic_Fin` (Fin-typed)

The `Fin d`-typed form of the order-2 BCH cubic estimate; identical to
the project's `bch_order_2_cubic_thm` modulo the `Matrix.BCH` namespace
prefix. The `m : Type*` follow-on is documented above. -/

/-- **Order-2 Baker–Campbell–Hausdorff cubic estimate (Fin-typed)**.

For any matrix dimension `d : ℕ` with `[Nonempty (Fin d)]`, any precision
threshold `δ ∈ [0, 1]`, and any two complex matrices
`F, G : Matrix (Fin d) (Fin d) ℂ` with `‖F‖, ‖G‖ ≤ δ` (in the L∞-op
norm), the four-fold group-commutator product
`exp(iF)·exp(iG)·exp(-iF)·exp(-iG)` approximates `exp(-⁅F,G⁆)` to within
a *cubic* error `320·δ³`.

This is the **cubic** version of the linear order-2 BCH estimate; it
drops the Hermitian hypothesis required by the linear version (the
`‖⁅F,G⁆‖ ≤ 2·δ²` bound holds for arbitrary `F, G` via the matrix-
commutator norm inequality).

The constant `320 = 253 + 30 + 36 + 1` decomposes as:
  - `253 · δ³` — 4-term telescope `‖P - PolyP‖` (Taylor-2 of each `exp` factor).
  - `30 · δ³` — `‖bchPolyRem F G‖` (polynomial remainder after BCH).
  - `36 · δ³` — order-2 Taylor remainder of `exp(-⁅F,G⁆)`.
  - `1 · δ³` — rounding slack.

## `m : Type*` generalization

The fully-generic `Matrix m m ℂ` version follows via the canonical
equivalence `Fintype.equivFin m : m ≃ Fin (Fintype.card m)` together
with `Matrix.linftyOpNorm_reindex` (shipped above) and a
`Matrix.reindexAlgEquiv` ↔ `NormedSpace.exp` commutativity lemma
(NOT currently in Mathlib v4.29.1). The Fin-typed form below + the
SU(2)/SU(4)/SU(8) examples below cover all the quantum-compiler-
relevant matrix dimensions in practice. -/
theorem bchOrder2Cubic_Fin {d : ℕ} [Nonempty (Fin d)]
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin d) (Fin d) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖exp (Complex.I • F) * exp (Complex.I • G) *
       exp (-(Complex.I • F)) * exp (-(Complex.I • G)) -
       exp (-⁅F, G⁆)‖ ≤ 320 * δ ^ 3 :=
  SKEFTHawking.MatrixBCHCubic.bch_order_2_cubic_thm δ hδ_nn hδ_le_one F G hF hG

/-! ## 3. Examples at SU(2), SU(4), SU(8)

The BCH cubic estimate applies directly to the matrix dimensions used
by quantum-compiler applications:
  - SU(2): single-qubit gate set (`Fin 2`); used by Clifford+T,
    Read-Rezayi `SU(2)_k`, Fibonacci anyons.
  - SU(4): 2-qubit gate set (`Fin 4`); used by trapped-ion MS+1Q
    compilation (Phase 6y Track T-A1′), KAK decomposition.
  - SU(8): 3-qubit gate set (`Fin 8`); used by Clifford+CCZ compilation
    (Phase 6y Track T-A2′), fault-tolerant magic-state architectures. -/

/-- **Example at `Fin 2` (SU(2))**: the canonical single-qubit setting
for quantum-compiler applications (Clifford+T, Fibonacci anyons,
Read-Rezayi `SU(2)_k`). -/
example (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin 2) (Fin 2) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖exp (Complex.I • F) * exp (Complex.I • G) *
       exp (-(Complex.I • F)) * exp (-(Complex.I • G)) -
       exp (-⁅F, G⁆)‖ ≤ 320 * δ ^ 3 :=
  bchOrder2Cubic_Fin δ hδ_nn hδ_le_one F G hF hG

/-- **Example at `Fin 4` (SU(4))**: the 2-qubit setting used by
trapped-ion MS+1Q compilation (Phase 6y Track T-A1′ — full SU(4)
compilation deferred). -/
example (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin 4) (Fin 4) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖exp (Complex.I • F) * exp (Complex.I • G) *
       exp (-(Complex.I • F)) * exp (-(Complex.I • G)) -
       exp (-⁅F, G⁆)‖ ≤ 320 * δ ^ 3 :=
  bchOrder2Cubic_Fin δ hδ_nn hδ_le_one F G hF hG

/-- **Example at `Fin 8` (SU(8))**: the 3-qubit setting used by
Clifford+CCZ compilation (Phase 6y Track T-A2′ — full SU(8) compilation
deferred). -/
example (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (F G : Matrix (Fin 8) (Fin 8) ℂ) (hF : ‖F‖ ≤ δ) (hG : ‖G‖ ≤ δ) :
    ‖exp (Complex.I • F) * exp (Complex.I • G) *
       exp (-(Complex.I • F)) * exp (-(Complex.I • G)) -
       exp (-⁅F, G⁆)‖ ≤ 320 * δ ^ 3 :=
  bchOrder2Cubic_Fin δ hδ_nn hδ_le_one F G hF hG

end Matrix.BCH
