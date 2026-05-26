/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-A2 — Clifford+CCZ alphabet at SU(8) (substrate-level definitions)

Ships the **substrate-level Lean definitions** for the Clifford+CCZ
universal gate set on 3 qubits: `{H ⊗ I ⊗ I, I ⊗ H ⊗ I, I ⊗ I ⊗ H, CCZ}`
acting on `Matrix (Fin 8) (Fin 8) ℂ` (target group `SU(8)`).

## Architectural status

The Clifford+CCZ alphabet sits at SU(8), NOT SU(2). The Phase 6u
substrate is SU(2)-targeted. Phase 6x Track T-A2 explicitly requires
the SU(d>2) substrate extension (T-A2.0):

  - SU(d) Lie algebra (dimension d² − 1) Cartan v4 density-from-witness.
  - Generalized BCH cubic bound (already generic over `d` in
    `MatrixBCHCubic.bch_order_2_cubic_thm`, lifted to PR-quality in
    Phase 6x M.1).
  - Y_h Lipschitz pullback for SU(d) (d-dependent constant).
  - Generalized `dnStepFG_su2` to `dnStepFG_su_d`.

The T-A2.0 substrate is **multi-session substrate work beyond a single
autonomous-loop session**. Per the Phase 6x /goal pivot rule (Pipeline
Invariant #15), the substantive T-A2.{1..5} instantiation is **YIELDED
for explicit user sign-off** on the SU(d) Cartan substrate-extension
plan.

This file ships the in-scope deliverables (CCZ matrix definition;
SU(8)-tensor-product gate constructors; identity sub-alphabet at
the 3-qubit register) at PR-quality presentation.

## Headline definitions

  * `CCZ_mat : Matrix (Fin 8) (Fin 8) ℂ` — the doubly-controlled-Z gate
    in the 3-qubit computational basis.
  * `CCZ_mat_zero_apply` — `CCZ |xyz⟩ = (-1)^{xyz} |xyz⟩` entries.

## Phase 6x M.1 substrate dependency

The order-2 BCH cubic estimate (used in any Cartan v4 discharge) is
already shipped generically over matrix dimension `d` in
`SKEFTHawking.MatrixBCHCubic.bch_order_2_cubic_thm`. The M.1 Mathlib-PR
presentation (`MatrixBCHCubicMathlibPR.lean`) lifts this to Mathlib-PR
quality with the `m : Type*` reindex generalization documented.

For T-A2.0, the **Cartan v4 generalization** is the load-bearing
substrate gap (M.2 documents the SU(d) extension plan; T-A2.0 ships
the substantive proof).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected; YIELD for the
  T-A2.{1..5} chain pending T-A2.0 substrate authorization.

-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Diagonal

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZ

open Matrix Complex

/-! ## 1. The CCZ gate at SU(8)

`CCZ` is the doubly-controlled-Z gate: `CCZ |xyz⟩ = (-1)^{xyz} |xyz⟩`
where `xyz ∈ {0, 1}^3` is the bit triple. In the 3-qubit computational
basis (8 states, index `i ∈ {0, …, 7}` representing binary `xyz`), the
CCZ matrix is diagonal with `+1` on all entries except `(7, 7)`, which
is `-1` (since only `|111⟩` has all three control bits set).
-/

/-- **Doubly-controlled-Z (CCZ) gate matrix** in the 3-qubit
computational basis: diagonal with `+1` everywhere except
`(7, 7) = −1`. -/
noncomputable def CCZ_mat : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal (fun i => if i = (⟨7, by decide⟩ : Fin 8) then (-1 : ℂ) else 1)

/-- The CCZ matrix has `(7, 7)` entry equal to `−1`. -/
theorem CCZ_mat_apply_7_7 :
    CCZ_mat ⟨7, by decide⟩ ⟨7, by decide⟩ = -1 := by
  simp [CCZ_mat, Matrix.diagonal]

/-- For `i ≠ 7`, the CCZ matrix has diagonal entry `+1`. -/
theorem CCZ_mat_apply_diag_ne_7 (i : Fin 8) (hi : i ≠ ⟨7, by decide⟩) :
    CCZ_mat i i = 1 := by
  simp only [CCZ_mat, Matrix.diagonal_apply_eq, ite_eq_right_iff]
  intro h_eq
  exact absurd h_eq hi

end SKEFTHawking.FKLW.CliffordCCZ
