/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y S.3 d≥3 PROPER — Usage examples at Phase 6y target d values

Worked examples demonstrating how downstream consumers apply the
keystone S.3 d≥3 PROPER discharge (Sessions 14-38) at the Phase 6y
target dimensions d = 4 (T-A1′ trapped-ion SU(4)) and d = 8 (T-A2′
Clifford+CCZ SU(8)).

## Usage pattern

Given any Hermitian-traceless `H : Matrix (Fin d) (Fin d) ℂ`, the
keystone produces F, G satisfying the balanced commutator equation:

  ```lean
  obtain ⟨F, G, hF_herm, hG_herm, hF_tr, hG_tr, hcomm⟩ :=
    phase6y_S3_balancedCommutator_dischargePredicate d H h_herm h_tr θ hθ_nn hθ_le
  ```

This is the **direct consumer-facing entry point** for the SK recursion
machinery and per-alphabet headline discharges.

## Substantive content shipped

  * `usage_example_SU4` — verifying the keystone at SU(4)
  * `usage_example_SU8` — verifying the keystone at SU(8)
  * `usage_example_consumer_idiom` — demonstrating the obtain-pattern
    consumers would use in SK recursion contexts.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" — usage examples for the keystone
S.3 d≥3 PROPER discharge at Phase 6y target dimensions.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdPhase6yKeystoneIndex

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

/-! ## 1. Usage example at SU(4) (Phase 6y T-A1′ target dimension) -/

/-- **Usage example at SU(4)**: for any Hermitian-traceless H in
Matrix (Fin 4) (Fin 4) ℂ, the keystone produces F, G satisfying the
balanced commutator equation. -/
theorem usage_example_SU4
    (H : Matrix (Fin 4) (Fin 4) ℂ)
    (h_herm : H.IsHermitian) (h_tr : H.trace = 0)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin 4) (Fin 4) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧
      F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H :=
  phase6y_S3_balancedCommutator_dischargePredicate 4 H h_herm h_tr θ hθ_nn hθ_le_one

/-! ## 2. Usage example at SU(8) (Phase 6y T-A2′ target dimension) -/

/-- **Usage example at SU(8)**: for any Hermitian-traceless H in
Matrix (Fin 8) (Fin 8) ℂ, the keystone produces F, G satisfying the
balanced commutator equation. -/
theorem usage_example_SU8
    (H : Matrix (Fin 8) (Fin 8) ℂ)
    (h_herm : H.IsHermitian) (h_tr : H.trace = 0)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin 8) (Fin 8) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧
      F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H :=
  phase6y_S3_balancedCommutator_dischargePredicate 8 H h_herm h_tr θ hθ_nn hθ_le_one

/-! ## 3. Consumer idiom: obtain-pattern for SK recursion contexts -/

/-- **Consumer idiom**: demonstrates the obtain-pattern that downstream
SK recursion consumers would use to destructure the keystone's existential
witness.

In practice, the SK recursion's `dnStep` function consumes (F, G) pairs
satisfying the balanced commutator equation. This example shows how to
extract them. -/
theorem usage_example_consumer_idiom {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℂ)
    (h_herm : H.IsHermitian) (h_tr : H.trace = 0)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin d) (Fin d) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧
      F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H := by
  -- The keystone provides the discharge for any d : ℕ.
  obtain ⟨F, G, hF_herm, hG_herm, hF_tr, hG_tr, hcomm⟩ :=
    phase6y_S3_balancedCommutator_dischargePredicate d H h_herm h_tr θ hθ_nn hθ_le_one
  -- Downstream SK recursion would use F, G with the balanced-commutator hypothesis
  -- to construct the dnStep recursion step.
  exact ⟨F, G, hF_herm, hG_herm, hF_tr, hG_tr, hcomm⟩

end SKEFTHawking.FKLW.GenericSUd
