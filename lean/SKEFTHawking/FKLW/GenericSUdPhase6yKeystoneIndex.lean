/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y S.3 d≥3 PROPER — Keystone theorem index + aliases

Index module re-exporting the load-bearing Phase 6y S.3 d≥3 PROPER theorems
under simplified, semantically-named aliases. Provides a single import point
for downstream consumers (SK recursion + per-alphabet headlines).

## Keystone theorems

  * `phase6y_S3_balancedCommutator_dischargeAlgebraic` — direct algebraic
    discharge for any Hermitian-traceless H (no norm bound).
  * `phase6y_S3_balancedCommutator_dischargePredicate` — predicate-form
    discharge for all d : ℕ.
  * `phase6y_S3_balancedCommutator_dischargeBounded` — bounded-form discharge
    with explicit linftyOp norm bound `(n+2)² · ‖F_inner‖`.

## Composition chain summary (Sessions 14-37)

  1. **S14-S22** (algebraic substrate): σ-block primitives + Hermiticity +
     trace + linftyOp norm bounds + commutator [σ_y, σ_x] = -2i σ_z +
     2-block classification + pair-swap cancellation + γ-weighted lift +
     antisymmetric off-diag sum vanishing.
  2. **S23** (`SymmetricFGEqIdentity`): MAIN identity F·G − G·F = -iθ·diag(a).
  3. **S24-S25** (`SymmetricDischarge` + `DecreasingSortPartialSums`):
     ∃-discharge for non-neg partial sums + eigenvalue sort substrate.
  4. **S26-S28** (`UnitaryConjugationInvariance` + `PermutationConjugation`
     + `PermutationDiagonal`): U(d) conjugation invariance + permMatrix
     unitary + diagonal conjugation identity.
  5. **S29-S30** (`PartialSumBridge` + `RangeFilterBridge`): bridges between
     ℂ-valued partialSumCoeff and real partial sums.
  6. **S31** (`SymmetricDiagonalDischargeFull`): FULL DIAGONAL CASE.
  7. **S32** (`SpectralLift`): spectral-lift form for any Hermitian H with
     supplied (U, a).
  8. **S33** (`HermitianDischargeFull`): UNCONDITIONAL via Mathlib's
     `Matrix.IsHermitian.spectral_theorem`.
  9. **S34-S35** (`BalancedCommutatorUnbounded` + `UnboundedAllD`):
     predicate-form lifts (d ≥ 2 → all d).
  10. **S36** (`NormBridgeUnitaryConjugation`): norm bridge
      `‖U · A · star U‖ ≤ n² · ‖A‖`.
  11. **S37** (`HermitianDischargeBounded`): bounded-form discharge composing
      S32 + S36.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected throughout.
  * **#15** (no new project-local axioms): respected throughout.
  * All theorems kernel-only: `{propext, Classical.choice, Quot.sound}`.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeFull
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorUnboundedAllD
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeBounded

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Phase 6y S.3 — algebraic discharge alias**: for any Hermitian-traceless H,
∃ Hermitian-traceless F, G satisfying `F · G − G · F = -iθ · H`.

Alias of `symmetric_balanced_commutator_hermitian_unconditional` (Session 33). -/
theorem phase6y_S3_balancedCommutator_dischargeAlgebraic {n : ℕ}
    (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (h_herm : H.IsHermitian) (h_tr : H.trace = 0)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H :=
  symmetric_balanced_commutator_hermitian_unconditional H h_herm h_tr θ hθ_nn hθ_le_one

/-- **Phase 6y S.3 — predicate discharge alias**: `BalancedCommutator_SUd_unbounded d`
holds for ANY d : ℕ.

Alias of `BalancedCommutator_SUd_unbounded_holds_all` (Session 35). -/
theorem phase6y_S3_balancedCommutator_dischargePredicate (d : ℕ) :
    BalancedCommutator_SUd_unbounded d :=
  BalancedCommutator_SUd_unbounded_holds_all d

/-- **Phase 6y S.3 — bounded-form discharge alias**: for Hermitian-traceless H
with spectral decomposition (U, a), there exist F, G satisfying the balanced
commutator equation with explicit linftyOp norm bounds.

Alias of `symmetric_balanced_commutator_hermitian_via_spectral_bounded`
(Session 37). -/
theorem phase6y_S3_balancedCommutator_dischargeBounded {n : ℕ}
    (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (h_tr : H.trace = 0)
    (U : ↥(Matrix.unitaryGroup (Fin (n + 2)) ℂ))
    (a : Fin (n + 2) → ℝ)
    (h_spec : H = U.val * Matrix.diagonal (fun k => (a k : ℂ)) * star U.val)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G F_inner G_inner : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H ∧
      ‖F‖ ≤ ((n + 2 : ℕ) : ℝ)^2 * ‖F_inner‖ ∧
      ‖G‖ ≤ ((n + 2 : ℕ) : ℝ)^2 * ‖G_inner‖ ∧
      F = U.val * F_inner * star U.val ∧
      G = U.val * G_inner * star U.val :=
  symmetric_balanced_commutator_hermitian_via_spectral_bounded H h_tr U a h_spec
    θ hθ_nn hθ_le_one

/-! ## Worked examples at Phase 6y target d values -/

/-- **Example**: `BalancedCommutator_SUd_unbounded 4` (SU(4), Phase 6y T-A1′). -/
example : BalancedCommutator_SUd_unbounded 4 :=
  phase6y_S3_balancedCommutator_dischargePredicate 4

/-- **Example**: `BalancedCommutator_SUd_unbounded 8` (SU(8), Phase 6y T-A2′). -/
example : BalancedCommutator_SUd_unbounded 8 :=
  phase6y_S3_balancedCommutator_dischargePredicate 8

end SKEFTHawking.FKLW.GenericSUd
