/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Super-quad bound SUBSTRATE for SU(d) recursion discharge

Lift of the SU(2) super-quad bound substrate lemmas from Phase 6t/6u
(`SolovayKitaevPathA.lean`, `GenericSolovayKitaevRecursionDischarge.lean`)
to SU(d). Provides the per-step substrate lemmas needed for the
super-quad bound discharge `SkApproxCSuperQuadraticBound_generic_sud`
(Session 44 predicate).

## Substantive content shipped

  * `residual_norm_le_d_mul` — SU(d) analog of SU(2)'s
    `residual_norm_le_sqrt_two_mul`: for `V, U ∈ ↥SU(d)`, the residual
    `Δ = V⁻¹ * U` satisfies `‖Δ - 1‖ ≤ d · ‖V - U‖`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — super-quad bound
substrate lift (1st of ~10 substrate lemmas per Explore-agent intel).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdNormBridgeUnitaryConjugation

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## Residual norm bound at SU(d) -/

/-- **Residual norm bound at SU(d)**.

For `V, U ∈ ↥SU(d)` (d ≥ 1), the residual `Δ := V⁻¹ * U` satisfies
`‖Δ.val - 1‖_linftyOp ≤ d · ‖V.val - U.val‖_linftyOp`.

SU(d) analog of SU(2)'s `residual_norm_le_sqrt_two_mul` (which used
the SU(2)-specific `‖V⁻¹‖ ≤ √2` bound). The SU(d) version uses
`linftyOpNorm_unitary_le` (Session 36 substrate) giving `‖V⁻¹‖ ≤ d`.

Proof: `V⁻¹·U - 1 = V⁻¹·(U - V)`, then sub-multiplicativity of linftyOp
norm + `‖V⁻¹‖ ≤ d` + norm symmetry. -/
lemma residual_norm_le_d_mul {d : ℕ} [Nonempty (Fin d)]
    (V U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    ‖((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) - (1 : Matrix (Fin d) (Fin d) ℂ)‖ ≤
      (d : ℝ) *
        ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := by
  -- Unfold subtype-level mul.
  have h_mul_val : ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
                    Matrix (Fin d) (Fin d) ℂ) =
                   (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val *
                   U.val := rfl
  rw [h_mul_val]
  -- V⁻¹.val ∈ unitaryGroup via special ⊆ unitary.
  have h_V_inv_unitary : (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val ∈
      Matrix.unitaryGroup (Fin d) ℂ := by
    exact Matrix.specialUnitaryGroup_le_unitaryGroup (V⁻¹).property
  -- ‖V⁻¹.val‖ ≤ d.
  have h_V_inv_norm : ‖(V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val‖ ≤
      (d : ℝ) :=
    linftyOpNorm_unitary_le ⟨_, h_V_inv_unitary⟩
  -- V⁻¹.val * V.val = 1.
  have h_inv_left : (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val * V.val
      = 1 := by
    have h := inv_mul_cancel V
    have h_eq : ((V⁻¹ * V : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
                Matrix (Fin d) (Fin d) ℂ) =
              (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val * V.val := rfl
    rw [← h_eq, h]; rfl
  -- Factor: V⁻¹·U - 1 = V⁻¹·(U - V).
  have h_factor : (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val * U.val -
                    (1 : Matrix (Fin d) (Fin d) ℂ) =
                  (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val *
                    (U.val - V.val) := by
    rw [Matrix.mul_sub, h_inv_left]
  rw [h_factor]
  -- Submultiplicativity + norm bound.
  have h_sub_mul := norm_mul_le
    ((V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val) (U.val - V.val)
  have h_norm_sub_sym : ‖U.val - V.val‖ = ‖V.val - U.val‖ := norm_sub_rev _ _
  calc ‖(V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val * (U.val - V.val)‖
      ≤ ‖(V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val‖ * ‖U.val - V.val‖ :=
        h_sub_mul
    _ ≤ (d : ℝ) * ‖U.val - V.val‖ := by
        gcongr
    _ = (d : ℝ) * ‖V.val - U.val‖ := by rw [h_norm_sub_sym]

end SKEFTHawking.FKLW.GenericSUd
