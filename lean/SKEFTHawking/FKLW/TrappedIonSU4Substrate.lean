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

end SKEFTHawking.FKLW.TrappedIonSU4
