/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Loose bounded predicate (definition + properties)

The LOOSE bounded form of `BalancedCommutator_SUd` with explicit norm bound
constant `K_d`, intended for SU(d) discharges where the spectral-then-conjugate
construction produces F, G with linftyOp norm bounded by `K_d · √(θ/2)`.

For our composition (S37 + S36):
  `K_d ≤ d² · ‖F_inner‖ / √(θ/2)`
where `‖F_inner‖` is the inner diagonal-case witness norm.

The UNCONDITIONAL discharge of this loose predicate at `K_d = d²` (with the
tight inner-witness bound `‖F_inner‖ ≤ √(θ/2)`) is shipped in follow-on
sessions that refine Session 24's symmetric construction with explicit
inner-norm bounds.

## Substantive content shipped

  * `BalancedCommutator_SUd_loose (d : ℕ) (K_d : ℝ) : Prop` — the loose
    bounded predicate definition.
  * `BalancedCommutator_SUd_loose_extends_unbounded` — relation to
    Session 34's unbounded form (any loose bounded predicate implies
    the unbounded form by dropping norm conjuncts).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" — loose bounded predicate (S37 + S36
composition target framework).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorUnboundedAllD

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Loose bounded predicate definition -/

/-- **Loose bounded balanced commutator predicate at SU(d)** with explicit
norm bound constant `K_d`:

  `∀ Hermitian-traceless H, ∃ F G Hermitian-traceless,
     ‖F‖_linftyOp ≤ K_d · √(θ/2) ∧
     ‖G‖_linftyOp ≤ K_d · √(θ/2) ∧
     F · G − G · F = -iθ · H`

For the symmetric F=αG construction (S33 + S36 composition), `K_d = d²`
captures the spectral-then-conjugate looseness via the norm bridge. -/
def BalancedCommutator_SUd_loose (d : ℕ) (K_d : ℝ) : Prop :=
  ∀ (H : Matrix (Fin d) (Fin d) ℂ)
    (_hH : H.IsHermitian) (_htr : H.trace = 0)
    (θ : ℝ) (_hθ_nn : 0 ≤ θ) (_hθ_le_one : θ ≤ 1),
    ∃ (F G : Matrix (Fin d) (Fin d) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧
      F.trace = 0 ∧ G.trace = 0 ∧
      ‖F‖ ≤ K_d * Real.sqrt (θ / 2) ∧
      ‖G‖ ≤ K_d * Real.sqrt (θ / 2) ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H

/-! ## 2. Relation to unbounded form -/

/-- **Loose bounded predicate implies unbounded form**: dropping the
norm-bound conjuncts gives `BalancedCommutator_SUd_unbounded d`. -/
theorem BalancedCommutator_SUd_loose_extends_unbounded {d : ℕ} {K_d : ℝ}
    (h : BalancedCommutator_SUd_loose d K_d) :
    BalancedCommutator_SUd_unbounded d := by
  intro H hH htr θ hθ_nn hθ_le_one
  obtain ⟨F, G, hF_herm, hG_herm, hF_tr, hG_tr, _, _, hcomm⟩ :=
    h H hH htr θ hθ_nn hθ_le_one
  exact ⟨F, G, hF_herm, hG_herm, hF_tr, hG_tr, hcomm⟩

end SKEFTHawking.FKLW.GenericSUd
