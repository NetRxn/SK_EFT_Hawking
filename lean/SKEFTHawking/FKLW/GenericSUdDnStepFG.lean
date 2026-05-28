/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) Dawson-Nielsen step (composes keystone Session 33)

The **SU(d) generalization of `dnStepFG_su2`** (Phase 6u Wave 4 alphabet-agnostic
Dawson-Nielsen step at SU(2)). Composes the keystone Session 33
`symmetric_balanced_commutator_hermitian_unconditional` with Mathlib's matrix
exponential / matrix log substrate at SU(d) to extract the per-step (F, G)
pair for one Solovay-Kitaev iteration at arbitrary d ≥ 2.

## Construction outline

For `V_n U : ↥SU(d)` (d = n + 2):
  1. Δ := V_n⁻¹ · U  (residual SU(d) element to compile away)
  2. H := -i · matrixLog (n+2) Δ.val  (Hermitian-traceless when Δ near 1,
     by project's `matrixLog_in_su_d_on_nhd_one` substrate)
  3. θ := ‖H‖_linftyOp  (norm of the residual generator)
  4. If 0 < θ ≤ 1 ∧ H is verified Hermitian + traceless, normalize
     H_unit := (1/θ) · H and call the keystone:
     `symmetric_balanced_commutator_hermitian_unconditional H_unit ... θ ... → (F, G)`
  5. Otherwise fall back to `(0, 0)` (outside the valid recursion regime).

The validity branch matches `dnStepFG_su2`'s `if h : 0 < θ ∧ θ ≤ 1 then ... else
{F = 0, G = 0, ...}` shape, with an additional Hermitian + traceless guard
(automatic at SU(2) via Bloch-sphere parametrization; explicit at SU(d) since
Mathlib's matrix log is partial).

## Substantive content shipped

  * `DNStepData_SUd (d : ℕ)` — bundle structure (F, G) with Hermitian +
    traceless proofs, parametric in d.
  * `IsHermitian_real_smul_sud` — d-generic real-scalar Hermitian preservation.
  * `smul_trace_zero_sud` — d-generic traceless preservation under smul.
  * `dnStepFG_sud` — the SU(d) Dawson-Nielsen step using the keystone.
  * `dnStepFG_sud_F_isHermitian`, `dnStepFG_sud_G_isHermitian`,
    `dnStepFG_sud_F_traceless`, `dnStepFG_sud_G_traceless` — projection
    field accessors as theorems.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 — dnStepFG_sud (cascade
substrate for S.6 polylog UNCONDITIONAL via lifted Generic SK recursion).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeFull
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeKeystoneBounded
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. SU(d)-parametric DNStepData structure -/

/-- **DNStepData at SU(d)**: bundle of (F, G) matrices with Hermitian +
traceless properties, parametric in d. SU(d) analog of `DNStepData`
(Phase 6t Path A SolovayKitaevPathA.lean, Fin 2-specific). -/
structure DNStepData_SUd (d : ℕ) where
  F : Matrix (Fin d) (Fin d) ℂ
  G : Matrix (Fin d) (Fin d) ℂ
  hF_herm : F.IsHermitian
  hG_herm : G.IsHermitian
  hF_tr : F.trace = 0
  hG_tr : G.trace = 0

/-! ## 2. d-generic helper lemmas -/

/-- Real-scalar multiplication preserves the Hermitian property at SU(d).
SU(d) generalization of `IsHermitian_real_smul` (Fin 2-specific). -/
lemma IsHermitian_real_smul_sud {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.IsHermitian) (c : ℝ) : ((c : ℂ) • M).IsHermitian := by
  show ((c : ℂ) • M).conjTranspose = (c : ℂ) • M
  rw [Matrix.conjTranspose_smul,
      show star (c : ℂ) = (c : ℂ) from by
        rw [Complex.star_def, Complex.conj_ofReal],
      show M.conjTranspose = M from hM]

/-- Scalar multiplication of a traceless matrix is traceless at SU(d).
SU(d) generalization of `smul_trace_zero`. -/
lemma smul_trace_zero_sud {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (htr : M.trace = 0) (c : ℂ) : (c • M).trace = 0 := by
  rw [Matrix.trace_smul, htr, smul_zero]

/-! ## 3. dnStepFG_sud — SU(d) Dawson-Nielsen step

For `V_n U : ↥SU(n+2)`, extract (F, G) by:
  1. Δ := V_n⁻¹ · U
  2. H := -i · matrixLog (n+2) Δ.val  (Hermitian-traceless when Δ near 1)
  3. θ := ‖H‖
  4. If 0 < θ ≤ 1 AND H.IsHermitian AND H.trace = 0: keystone Session 33
  5. Else: fall back to (0, 0)

The Hermitian+traceless guard is decidable (matrix equality) via Classical
decidability. -/

open Classical in
/-- **The SU(d) Dawson-Nielsen F, G extraction step**.

Given the current level-n SU(d) approximation `V_n` and target `U`, extract
the (F, G) pair satisfying the balanced commutator identity for the
normalized residual log. Composes Mathlib's matrix log (project's
`matrixLog d` wrapper) with the keystone Session 33
`symmetric_balanced_commutator_hermitian_unconditional`.

Falls back to `(0, 0)` when the residual is outside the valid recursion
regime (either ‖H‖ ∉ (0, 1] or H not verified Hermitian-traceless, which
happens when Δ is too far from 1 for the partial matrix log to be in
𝔰𝔲(d)). -/
noncomputable def dnStepFG_sud {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    DNStepData_SUd (n + 2) :=
  let Δ : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ) := V_n⁻¹ * U
  let H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
    ((-Complex.I) : ℂ) • matrixLog (n + 2) Δ.val
  let θ : ℝ := ‖H‖
  if h : 0 < θ ∧ θ ≤ 1 ∧ H.IsHermitian ∧ H.trace = 0 then
    let H_unit : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ := ((1 / θ : ℝ) : ℂ) • H
    have hH_unit_herm : H_unit.IsHermitian :=
      IsHermitian_real_smul_sud h.2.2.1 (1 / θ)
    have hH_unit_tr : H_unit.trace = 0 :=
      smul_trace_zero_sud h.2.2.2 _
    have hθ_pos : 0 < θ := h.1
    have hH_unit_norm : ‖H_unit‖ ≤ 1 := by
      have h_eq : ‖H_unit‖ = 1 := by
        show ‖((1 / θ : ℝ) : ℂ) • H‖ = 1
        rw [norm_smul, Complex.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / θ), one_div]
        exact inv_mul_cancel₀ (ne_of_gt hθ_pos)
      rw [h_eq]
    let ex := symmetric_balanced_commutator_hermitian_unconditional_bounded
                H_unit hH_unit_herm hH_unit_tr hH_unit_norm θ h.1.le h.2.1
    { F := ex.choose
      G := ex.choose_spec.choose
      hF_herm := ex.choose_spec.choose_spec.1
      hG_herm := ex.choose_spec.choose_spec.2.1
      hF_tr := ex.choose_spec.choose_spec.2.2.1
      hG_tr := ex.choose_spec.choose_spec.2.2.2.1 }
  else
    { F := 0
      G := 0
      hF_herm := Matrix.isHermitian_zero
      hG_herm := Matrix.isHermitian_zero
      hF_tr := by simp
      hG_tr := by simp }

/-! ## 4. Projection accessors (already provided by DNStepData_SUd fields) -/

/-- **F is Hermitian** (extracted field). -/
theorem dnStepFG_sud_F_isHermitian {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    (dnStepFG_sud V_n U).F.IsHermitian :=
  (dnStepFG_sud V_n U).hF_herm

/-- **G is Hermitian** (extracted field). -/
theorem dnStepFG_sud_G_isHermitian {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    (dnStepFG_sud V_n U).G.IsHermitian :=
  (dnStepFG_sud V_n U).hG_herm

/-- **F is traceless** (extracted field). -/
theorem dnStepFG_sud_F_traceless {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    (dnStepFG_sud V_n U).F.trace = 0 :=
  (dnStepFG_sud V_n U).hF_tr

/-- **G is traceless** (extracted field). -/
theorem dnStepFG_sud_G_traceless {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    (dnStepFG_sud V_n U).G.trace = 0 :=
  (dnStepFG_sud V_n U).hG_tr

end SKEFTHawking.FKLW.GenericSUd
