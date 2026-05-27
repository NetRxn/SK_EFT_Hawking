/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.1-substrate — Clifford+CCZ SU(8) gate helpers

For Track T-A2′ (full SU(8) Clifford+CCZ compilation), we need the
Hadamard-on-qubit-i gates lifted to SU(8) via Kronecker products with
identities on the other qubits. This module ships the substrate
helpers:

  * `kronSU4SU2 (A : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ)
      : Matrix (Fin 8) (Fin 8) ℂ` — Kronecker `A ⊗ B` reindexed via
    `Fin 4 × Fin 2 ≃ Fin 8`.
  * `kronSU2SU4 (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 4) (Fin 4) ℂ)
      : Matrix (Fin 8) (Fin 8) ℂ` — Kronecker `A ⊗ B` reindexed via
    `Fin 2 × Fin 4 ≃ Fin 8`.
  * `H_SU_on_qubit1 : Matrix (Fin 8) (Fin 8) ℂ` — Hadamard on qubit 1.
  * `H_SU_on_qubit2 : Matrix (Fin 8) (Fin 8) ℂ` — Hadamard on qubit 2.
  * `H_SU_on_qubit3 : Matrix (Fin 8) (Fin 8) ℂ` — Hadamard on qubit 3.

Combined with Phase 6x's `CCZ_mat` (in
`SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat`), these form the discrete
alphabet for T-A2′.1's `cliffordCCZGeneratingSetSU8 : GeneratingSet 8`
(full SU(8) compilation; CCZ in alphabet, not primitive).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.1 substrate.

-/

import Mathlib
import SKEFTHawking.FKLW.CliffordTGeneratingSet
import SKEFTHawking.FKLW.TrappedIonSU4Substrate

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Kronecker products reindexed to `Fin 8` -/

/-- **Kronecker product of 4x4 and 2x2 matrices reindexed to SU(8).**

`kronSU4SU2 A B = A ⊗ B` viewed as `Matrix (Fin 8) (Fin 8) ℂ` via
`finProdFinEquiv : Fin 4 × Fin 2 ≃ Fin 8`. -/
noncomputable def kronSU4SU2 (A : Matrix (Fin 4) (Fin 4) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.kronecker A B)

/-- **Kronecker product of 2x2 and 4x4 matrices reindexed to SU(8).**

`kronSU2SU4 A B = A ⊗ B` viewed as `Matrix (Fin 8) (Fin 8) ℂ` via
`finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin 8`. -/
noncomputable def kronSU2SU4 (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.kronecker A B)

/-! ## 2. Hadamard-on-qubit-i SU(8) gates

Three Hadamards on the 3-qubit Hilbert space (8-dim):
  * Qubit 1 (leftmost): `H ⊗ I ⊗ I` = `H ⊗ I_4` via kronSU2SU4.
  * Qubit 2 (middle):   `I ⊗ H ⊗ I` = `kronSU2SU4 I (kronSU4 H I)` ...
    actually simpler: `(I ⊗ H) ⊗ I` via kronSU4SU2 with inner = (kronSU4 I H).
  * Qubit 3 (rightmost): `I ⊗ I ⊗ H` = `I_4 ⊗ H` via kronSU4SU2.

To avoid associativity issues, we use SU2SU4 for qubit 1 and SU4SU2 for
qubit 3, and a 2-stage Kronecker for qubit 2. -/

/-- **Hadamard on qubit 1 (SU(8))**: `H_SU ⊗ I_4` reindexed. -/
noncomputable def H_SU_on_qubit1 : Matrix (Fin 8) (Fin 8) ℂ :=
  kronSU2SU4 SKEFTHawking.FKLW.GenericSU2.H_SU_mat
    (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- **Hadamard on qubit 2 (SU(8))**: `I ⊗ H_SU ⊗ I` reindexed.

Computed as `kronSU2SU4 I (kronSU4 H_SU I)` — uses kronSU4 helper from
`TrappedIonSU4Substrate` for the inner 2-fold Kronecker. -/
noncomputable def H_SU_on_qubit2 : Matrix (Fin 8) (Fin 8) ℂ :=
  kronSU2SU4 (1 : Matrix (Fin 2) (Fin 2) ℂ)
    (SKEFTHawking.FKLW.TrappedIonSU4.kronSU4 SKEFTHawking.FKLW.GenericSU2.H_SU_mat
      (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- **Hadamard on qubit 3 (SU(8))**: `I_4 ⊗ H_SU` reindexed. -/
noncomputable def H_SU_on_qubit3 : Matrix (Fin 8) (Fin 8) ℂ :=
  kronSU4SU2 (1 : Matrix (Fin 4) (Fin 4) ℂ) SKEFTHawking.FKLW.GenericSU2.H_SU_mat

end SKEFTHawking.FKLW.CliffordCCZSU8
