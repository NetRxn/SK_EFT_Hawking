/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — UNCONDITIONAL `expIsud` at SU(d≥2)

The **UNCONDITIONAL SU(d) matrix exponential coercion** to
`specialUnitaryGroup (Fin (n+2)) ℂ` for Hermitian-traceless generators.

Composes Session 42's conditional `expIsud_conditional` with Session 49's
substantive `expIsud_det_eq_one_predicate_holds` discharge to remove the
det-hypothesis from downstream consumers. The result is the SU(d) analog
of Phase 6t SU(2)'s `expIsu2` — unconditional and ready-to-use.

## Substantive content shipped

  * `expIsud (n : ℕ) (F : Matrix (Fin (n+2)) (Fin (n+2)) ℂ) (hF : F.IsHermitian)
    (hF_tr : F.trace = 0) : ↥(specialUnitaryGroup (Fin (n+2)) ℂ)` — UNCONDITIONAL.
  * `expIsud_val` — value extraction theorem.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — unconditional SU(d) exp
coercion (composing Sessions 42 + 49 substantive discharges).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdExpIsuD
import SKEFTHawking.FKLW.GenericSUdExpIsuDDetDischarge

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## UNCONDITIONAL expIsud at SU(d≥2) -/

/-- **UNCONDITIONAL SU(d) matrix exponential coercion**.

For any Hermitian-traceless `F : Matrix (Fin (n+2)) (Fin (n+2)) ℂ`,
returns the SU(d) element `exp(I · F) ∈ specialUnitaryGroup (Fin (n+2)) ℂ`.

Composes Session 42's `expIsud_of_det_predicate` with Session 49's
substantive `expIsud_det_eq_one_predicate_holds` — the det-hypothesis is
now discharged unconditionally. -/
noncomputable def expIsud (n : ℕ)
    (F : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hF : F.IsHermitian) (hF_tr : F.trace = 0) :
    ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ) :=
  expIsud_of_det_predicate (expIsud_det_eq_one_predicate_holds n) F hF hF_tr

/-- **Value extraction**: `↑(expIsud n F hF hF_tr) = exp(I • F)`. -/
@[simp]
theorem expIsud_val (n : ℕ)
    (F : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (hF : F.IsHermitian) (hF_tr : F.trace = 0) :
    (expIsud n F hF hF_tr : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) =
      NormedSpace.exp (Complex.I • F) := rfl

/-! ## Worked examples at SU(2), SU(4), SU(8) -/

/-- **Example at SU(2)** (smoke-test; matches Phase 6t `expIsu2` shape). -/
noncomputable example (F : Matrix (Fin 2) (Fin 2) ℂ) (hF : F.IsHermitian) (hF_tr : F.trace = 0) :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  expIsud 0 F hF hF_tr

/-- **Example at SU(4)** (Phase 6y T-A1′ target). -/
noncomputable example (F : Matrix (Fin 4) (Fin 4) ℂ) (hF : F.IsHermitian) (hF_tr : F.trace = 0) :
    ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ) :=
  expIsud 2 F hF hF_tr

/-- **Example at SU(8)** (Phase 6y T-A2′ target). -/
noncomputable example (F : Matrix (Fin 8) (Fin 8) ℂ) (hF : F.IsHermitian) (hF_tr : F.trace = 0) :
    ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  expIsud 6 F hF hF_tr

end SKEFTHawking.FKLW.GenericSUd
