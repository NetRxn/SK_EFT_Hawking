/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.1-substrate — Trapped-ion SU(4) gate helpers

For Track T-A1′ (full SU(4) trapped-ion compilation), we need the
single-qubit-on-ion-i gates lifted to SU(4) via Kronecker products
with the identity on the other ion. This module ships the substrate
helpers:

  * `kronSU4 (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ`
    — the Kronecker product `A ⊗ B` reindexed from `Fin 2 × Fin 2 ≃ Fin 4`
    via `finProdFinEquiv`.

  * `H_SU_on_ion1 : Matrix (Fin 4) (Fin 4) ℂ` — Hadamard on ion 1.
  * `H_SU_on_ion2 : Matrix (Fin 4) (Fin 4) ℂ` — Hadamard on ion 2.
  * `T_SU_on_ion1 : Matrix (Fin 4) (Fin 4) ℂ` — T-gate on ion 1.
  * `T_SU_on_ion2 : Matrix (Fin 4) (Fin 4) ℂ` — T-gate on ion 2.

Phase 6x M.1 + Phase 6u substrate provide `H_SU` and `T_SU` as the
SU(2)-corrected Hadamard and T-gate (det = 1 confirmed). Kronecker
product with the 2x2 identity preserves det = 1 (since
det(A ⊗ B) = det(A)^n * det(B)^m for `n × n` and `m × m` matrices, and
det(I) = 1).

The full `trappedIonGeneratingSetSU4 : GeneratingSet 4` instance
(T-A1′.1 proper) consumes these substrate gates + the existing
`MSGateMat` (Phase 6x trapped-ion lift/shift ship) to form the discrete
alphabet for the full SU(4) compilation.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.1 substrate.

-/

import Mathlib
import SKEFTHawking.FKLW.CliffordTGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Kronecker product reindexed to `Fin 4`

The standard Kronecker product `Matrix.kronecker` returns
`Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`; we reindex to
`Matrix (Fin 4) (Fin 4) ℂ` via `finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4`. -/

/-- **Kronecker product of two SU(2) matrices reindexed to SU(4).**

`kronSU4 A B = A ⊗ B` viewed as a `Matrix (Fin 4) (Fin 4) ℂ` via the
canonical equivalence `finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4`
(index convention: `(b1, b2) ↦ b2 + 2 · b1`, so `|00⟩, |01⟩, |10⟩, |11⟩`
map to `0, 1, 2, 3`). -/
noncomputable def kronSU4 (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.kronecker A B)

/-! ## 2. Single-qubit-on-ion-i SU(4) gates

Hadamard and T-gate (SU(2)-corrected, from Phase 6u `CliffordTGeneratingSet`)
lifted to SU(4) via Kronecker product with the 2x2 identity. -/

/-- **Hadamard on ion 1 (SU(4))**: `H_SU ⊗ I` reindexed to `Fin 4`. -/
noncomputable def H_SU_on_ion1 : Matrix (Fin 4) (Fin 4) ℂ :=
  kronSU4 SKEFTHawking.FKLW.GenericSU2.H_SU_mat (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- **Hadamard on ion 2 (SU(4))**: `I ⊗ H_SU` reindexed to `Fin 4`. -/
noncomputable def H_SU_on_ion2 : Matrix (Fin 4) (Fin 4) ℂ :=
  kronSU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) SKEFTHawking.FKLW.GenericSU2.H_SU_mat

/-- **T-gate on ion 1 (SU(4))**: `T_SU ⊗ I` reindexed to `Fin 4`. -/
noncomputable def T_SU_on_ion1 : Matrix (Fin 4) (Fin 4) ℂ :=
  kronSU4 SKEFTHawking.FKLW.GenericSU2.T_SU_mat (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- **T-gate on ion 2 (SU(4))**: `I ⊗ T_SU` reindexed to `Fin 4`. -/
noncomputable def T_SU_on_ion2 : Matrix (Fin 4) (Fin 4) ℂ :=
  kronSU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) SKEFTHawking.FKLW.GenericSU2.T_SU_mat

/-! ## 3. Determinant lemmas for kronSU4

Substrate toward the SU(4) membership proofs (`kronSU4 A B ∈ specialUnitaryGroup`):
the determinant of the reindexed Kronecker product. -/

/-- **det(kronSU4 A B) = det(A)^2 * det(B)^2**. -/
theorem det_kronSU4 (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (kronSU4 A B).det = A.det ^ 2 * B.det ^ 2 := by
  unfold kronSU4
  rw [Matrix.det_reindex_self]
  show (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) A B).det = A.det ^ 2 * B.det ^ 2
  rw [Matrix.det_kronecker]
  simp [Fintype.card_fin]

/-- **kronSU4 of SU(2)-det-1 matrices has det 1**.

Given `A.det = 1` and `B.det = 1`, `(kronSU4 A B).det = 1`. -/
theorem det_kronSU4_eq_one {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.det = 1) (hB : B.det = 1) :
    (kronSU4 A B).det = 1 := by
  rw [det_kronSU4, hA, hB]
  ring

/-! ## 4. Unitary preservation for kronSU4

Composes Mathlib's `Matrix.kronecker_mem_unitary` (kronecker product of
unitaries is unitary) with the reindex preservation. -/

/-- **Reindex (same equiv on rows and cols) preserves unitarity**.

For `e : m ≃ n` and `M ∈ unitaryGroup (Matrix m m)`, we have
`Matrix.reindex e e M ∈ unitaryGroup (Matrix n n)`. Uses
`Matrix.submatrix_mul_equiv` + `Matrix.conjTranspose_reindex` +
`Matrix.submatrix_one_equiv`. -/
theorem reindex_mem_unitaryGroup {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    {M : Matrix m m ℂ} (hM : M ∈ Matrix.unitaryGroup m ℂ) :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup n ℂ := by
  -- Unfold mem_unitaryGroup: ↔ M * star M = 1.
  rw [Matrix.mem_unitaryGroup_iff]
  -- star (reindex e e M) = reindex e e (star M).
  have h_star_reindex : star (Matrix.reindex e e M) = Matrix.reindex e e (star M) := by
    show (Matrix.reindex e e M).conjTranspose = Matrix.reindex e e (Matrix.conjTranspose M)
    rw [Matrix.conjTranspose_reindex]
  rw [h_star_reindex]
  -- reindex e e M * reindex e e (star M) = reindex e e (M * star M).
  -- Use Matrix.submatrix_mul_equiv.
  show Matrix.submatrix M e.symm e.symm * Matrix.submatrix (star M) e.symm e.symm = 1
  rw [show (1 : Matrix n n ℂ) = Matrix.submatrix (1 : Matrix m m ℂ) e.symm e.symm from
      (Matrix.submatrix_one_equiv e.symm).symm]
  rw [show Matrix.submatrix M e.symm e.symm * Matrix.submatrix (star M) e.symm e.symm
       = Matrix.submatrix (M * star M) e.symm e.symm from
      Matrix.submatrix_mul_equiv M (star M) (⇑e.symm) e.symm (⇑e.symm)]
  congr 1
  exact Matrix.mem_unitaryGroup_iff.mp hM

/-- **`kronSU4` of two unitary 2x2 matrices is a 4x4 unitary**. -/
theorem kronSU4_mem_unitaryGroup {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    kronSU4 A B ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  unfold kronSU4
  apply reindex_mem_unitaryGroup
  -- Matrix.kronecker A B = Matrix.kroneckerMap (· * ·) A B
  show Matrix.kroneckerMap (fun x1 x2 => x1 * x2) A B ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ
  -- Map to Matrix.unitaryGroup via Mathlib.kronecker_mem_unitary.
  exact Matrix.kronecker_mem_unitary hA hB

/-- **`kronSU4` of two SU(2) matrices is in SU(4)** (substantive).

Combines `kronSU4_mem_unitaryGroup` (unitarity) + `det_kronSU4_eq_one`
(det = 1). -/
theorem kronSU4_mem_specialUnitaryGroup {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hB : B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    kronSU4 A B ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  obtain ⟨hA_unit, hA_det⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
  obtain ⟨hB_unit, hB_det⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hB
  exact ⟨kronSU4_mem_unitaryGroup hA_unit hB_unit, det_kronSU4_eq_one hA_det hB_det⟩

end SKEFTHawking.FKLW.TrappedIonSU4
