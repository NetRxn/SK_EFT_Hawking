/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) matrix exponential coercion to specialUnitaryGroup

The **SU(d) generalization of `expIsu2`** (Phase 6t Path A) constructing the
SU(d)-valued matrix exponential of a Hermitian-traceless generator.

For `F : Matrix (Fin d) (Fin d) ℂ` Hermitian-traceless, `exp(I · F)` is
unitary (from skew-Hermiticity of `I·F`) and has determinant 1 — i.e., lies
in `SU(d)`.

This module ships:
  * `I_smul_isHermitian_mem_skewAdjoint` — for F Hermitian, I•F ∈ skewAdjoint
  * `expAmbient_I_smul_mem_unitaryGroup` — exp(I•F) ∈ unitaryGroup
  * `expIsud_conditional` — the SU(d)-coerced matrix exp, taking the
    det-equals-1 conjunct as a HYPOTHESIS (decouples the unitary-membership
    substrate from the substantive det = 1 discharge)
  * `expIsud_conditional_val` — `↑(expIsud_conditional F hF htr h_det) = exp(I•F)`

The substantive det = 1 discharge (analog of SU(2)'s `DetExpZeroOnSu2_SU2_discharged`,
~2300 LoC) ships in follow-on sessions via the matrix-trace ↔ matrix-det
exponential identity `det(exp X) = exp(trace X)`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" — `expIsud` (SU(d) exponentiator substrate
for the cascade SK recursion lift `skApproxC_generic_sud`).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. `Complex.I • F` is skew-adjoint when `F` is Hermitian -/

/-- For Hermitian `F`, `Complex.I • F` lies in the skew-adjoint subspace. -/
lemma I_smul_isHermitian_mem_skewAdjoint {d : ℕ}
    {F : Matrix (Fin d) (Fin d) ℂ} (hF : F.IsHermitian) :
    Complex.I • F ∈ skewAdjoint (Matrix (Fin d) (Fin d) ℂ) := by
  rw [skewAdjoint.mem_iff]
  -- star (I • F) = star I • star F = -I • F = -(I • F)
  show star (Complex.I • F) = -(Complex.I • F)
  rw [star_smul, Complex.star_def, Complex.conj_I,
      show star F = F from hF, neg_smul]

/-! ## 2. `exp(I • F)` lies in the unitary group when `F` is Hermitian -/

/-- For Hermitian `F`, `NormedSpace.exp (Complex.I • F)` lies in the
unitary submonoid of `Matrix (Fin d) (Fin d) ℂ`. -/
lemma expAmbient_I_smul_mem_unitary {d : ℕ}
    {F : Matrix (Fin d) (Fin d) ℂ} (hF : F.IsHermitian) :
    NormedSpace.exp (Complex.I • F) ∈ unitary (Matrix (Fin d) (Fin d) ℂ) :=
  NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (I_smul_isHermitian_mem_skewAdjoint hF)

/-- For Hermitian `F`, `NormedSpace.exp (Complex.I • F)` lies in
`Matrix.unitaryGroup (Fin d) ℂ`.

The `Matrix.unitaryGroup` is a renaming of the `unitary` submonoid for
matrix algebras (specialized via `star := conjTranspose`). -/
lemma expAmbient_I_smul_mem_unitaryGroup {d : ℕ}
    {F : Matrix (Fin d) (Fin d) ℂ} (hF : F.IsHermitian) :
    NormedSpace.exp (Complex.I • F) ∈ Matrix.unitaryGroup (Fin d) ℂ :=
  expAmbient_I_smul_mem_unitary hF

/-! ## 3. The SU(d) exponentiator (conditional on det = 1) -/

/-- **The SU(d) matrix exponential of a Hermitian generator** —
**conditional on a det = 1 hypothesis**.

For Hermitian-traceless `F : Matrix (Fin d) (Fin d) ℂ` AND a hypothesis
`Matrix.det (NormedSpace.exp (Complex.I • F)) = 1`, returns the SU(d)
element `exp(I · F)`.

The det = 1 hypothesis is the SU(d) analog of the SU(2) substrate
`DetExpZeroOnSu2_SU2_discharged` (Phase 6q OneParameterSubgroupSU2, ~2300
LoC). For SU(d), the substantive discharge of det(exp X) = exp(trace X)
requires the Mathlib-PR-quality matrix-trace ↔ matrix-det exponential
identity (Mathlib does not currently ship this as a single named lemma).

Downstream consumers (SU(d) SK recursion) can either:
  (a) supply the det = 1 proof via a Mathlib-style derivation
      `det_exp_eq_exp_trace _ _ _` once that lemma ships, OR
  (b) carry the conditional hypothesis through compositions and discharge
      at the headline integration point. -/
noncomputable def expIsud_conditional {d : ℕ}
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : F.IsHermitian) (_hF_tr : F.trace = 0)
    (h_det : Matrix.det (NormedSpace.exp (Complex.I • F)) = 1) :
    ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) :=
  ⟨NormedSpace.exp (Complex.I • F),
   Matrix.mem_specialUnitaryGroup_iff.mpr
     ⟨expAmbient_I_smul_mem_unitaryGroup hF, h_det⟩⟩

/-- **Value-extraction** for `expIsud_conditional`. -/
@[simp]
theorem expIsud_conditional_val {d : ℕ}
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : F.IsHermitian) (hF_tr : F.trace = 0)
    (h_det : Matrix.det (NormedSpace.exp (Complex.I • F)) = 1) :
    (expIsud_conditional F hF hF_tr h_det :
      Matrix (Fin d) (Fin d) ℂ) =
      NormedSpace.exp (Complex.I • F) := rfl

/-- **The expIsud det = 1 predicate** — captures the substantive content
to discharge for an unconditional `expIsud`. -/
def ExpIsud_det_eq_one_predicate (d : ℕ) : Prop :=
  ∀ (F : Matrix (Fin d) (Fin d) ℂ),
    F.IsHermitian → F.trace = 0 →
    Matrix.det (NormedSpace.exp (Complex.I • F)) = 1

/-- **Unconditional expIsud, factored through the det-predicate**.

Given a discharge of `ExpIsud_det_eq_one_predicate d`, produces the
unconditional `expIsud` (returning SU(d) directly without the per-call
det-hypothesis). -/
noncomputable def expIsud_of_det_predicate {d : ℕ}
    (h_det_pred : ExpIsud_det_eq_one_predicate d)
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : F.IsHermitian) (hF_tr : F.trace = 0) :
    ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) :=
  expIsud_conditional F hF hF_tr (h_det_pred F hF hF_tr)

/-- **Value-extraction** for `expIsud_of_det_predicate`. -/
@[simp]
theorem expIsud_of_det_predicate_val {d : ℕ}
    (h_det_pred : ExpIsud_det_eq_one_predicate d)
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : F.IsHermitian) (hF_tr : F.trace = 0) :
    (expIsud_of_det_predicate h_det_pred F hF hF_tr :
      Matrix (Fin d) (Fin d) ℂ) =
      NormedSpace.exp (Complex.I • F) := rfl

end SKEFTHawking.FKLW.GenericSUd
