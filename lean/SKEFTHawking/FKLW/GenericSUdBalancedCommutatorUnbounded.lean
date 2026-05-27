/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 d≥3 PROPER — Predicate-form unbounded discharge

For any `d ≥ 2`, the unbounded form of `BalancedCommutator_SUd` (i.e., the
algebraic conjuncts WITHOUT the linftyOp norm bound on F, G) is UNCONDITIONALLY
discharged via Session 33's `symmetric_balanced_commutator_hermitian_unconditional`.

This is the **predicate-form lift** of S.3 d≥3 PROPER: takes Session 33's
direct ∃-discharge and packages it as a `∀ d ≥ 2, BalancedCommutator_SUd_unbounded d`
predicate-style theorem suitable for downstream SK recursion consumers.

## Norm-bound omission

The full `BalancedCommutator_SUd` predicate includes
`‖F‖_linftyOp ≤ √(θ/2) ∧ ‖G‖_linftyOp ≤ √(θ/2)`. Session 33's discharge
does NOT preserve linftyOp bounds under spectral-then-conjugate
(linftyOp is not unitary-conjugation-invariant; only spectral norm is).
The norm-bridge substrate (linftyOpNorm ≤ √d · spectralNorm) gives a
`√d`-loose bound; this module SHIPS the unbounded form so downstream
consumers can either:
  (a) consume the algebraic form directly (no norm bound)
  (b) compose with the future norm-bridge for √d-loose bound

## Substantive content shipped

  * `BalancedCommutator_SUd_unbounded (d : ℕ) : Prop` — the predicate
    omitting norm bounds.
  * `BalancedCommutator_SUd_unbounded_holds (d : ℕ) (hd : 2 ≤ d) :
       BalancedCommutator_SUd_unbounded d` — UNCONDITIONAL discharge.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" — predicate-form lift of S.3 d≥3 PROPER
(cascade enabler for downstream SK recursion + headline composition).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeFull

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

/-! ## 1. Unbounded predicate -/

/-- **Unbounded balanced commutator predicate at SU(d)**: same as
`BalancedCommutator_SUd` but WITHOUT the linftyOp norm bound conjuncts.

For any Hermitian-traceless H ∈ Matrix (Fin d) (Fin d) ℂ and θ ∈ [0, 1],
there exist Hermitian-traceless F, G satisfying
`F · G − G · F = −((θ : ℂ) · Complex.I) • H`. -/
def BalancedCommutator_SUd_unbounded (d : ℕ) : Prop :=
  ∀ (H : Matrix (Fin d) (Fin d) ℂ)
    (_hH : H.IsHermitian) (_htr : H.trace = 0)
    (θ : ℝ) (_hθ_nn : 0 ≤ θ) (_hθ_le_one : θ ≤ 1),
    ∃ (F G : Matrix (Fin d) (Fin d) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧
      F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H

/-! ## 2. UNCONDITIONAL discharge for any d ≥ 2 -/

/-- **UNCONDITIONAL discharge of `BalancedCommutator_SUd_unbounded d` for any d ≥ 2**.

Composes Session 33's `symmetric_balanced_commutator_hermitian_unconditional`
(parameterized at `Fin (n + 2)`) via the rewriting `d = (d - 2) + 2`. -/
theorem BalancedCommutator_SUd_unbounded_holds (d : ℕ) (hd : 2 ≤ d) :
    BalancedCommutator_SUd_unbounded d := by
  -- Rewrite d = (d - 2) + 2 to apply S33's Fin (n + 2) form.
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  intro H h_herm h_tr θ hθ_nn hθ_le_one
  exact symmetric_balanced_commutator_hermitian_unconditional H h_herm h_tr θ hθ_nn hθ_le_one

/-! ### Worked examples at d = 2, d = 3, d = 4, d = 8 -/

/-- **Example**: `BalancedCommutator_SUd_unbounded 2` (Phase 6t/6u baseline). -/
example : BalancedCommutator_SUd_unbounded 2 := BalancedCommutator_SUd_unbounded_holds 2 (by norm_num)

/-- **Example**: `BalancedCommutator_SUd_unbounded 3` (smallest d≥3 case). -/
example : BalancedCommutator_SUd_unbounded 3 := BalancedCommutator_SUd_unbounded_holds 3 (by norm_num)

/-- **Example**: `BalancedCommutator_SUd_unbounded 4` (Phase 6y T-A1′ target). -/
example : BalancedCommutator_SUd_unbounded 4 := BalancedCommutator_SUd_unbounded_holds 4 (by norm_num)

/-- **Example**: `BalancedCommutator_SUd_unbounded 8` (Phase 6y T-A2′ target). -/
example : BalancedCommutator_SUd_unbounded 8 := BalancedCommutator_SUd_unbounded_holds 8 (by norm_num)

end SKEFTHawking.FKLW.GenericSUd
