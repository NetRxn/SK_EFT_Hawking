/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the Bloch image is orthogonal (`R(M) ∈ O(3)`)

For a unitary `M`, the SO(3) Bloch image `R(M)` is orthogonal: `R(M)ᵀ · R(M) = I`.
This is the **achievability** foundation for the `ma_step` existence proof: it forces
the cleared Bloch numerators `b = √2^kSO3 · R(M)` to satisfy `bᵀ·b = 2^kSO3 · I`,
hence `bᵀ·b ≡ 0 (mod 2)` (for `kSO3 ≥ 1`) — the constraint that cuts the Bloch parity
residue down to the 15 classes over which `∃` reducing syllable is `decide`-able.

## Headline results

  * `blochMat M` — the SO(3) image as a `Matrix (Fin 3) (Fin 3) ZOmegaSqrt2`.
  * `blochMat_mul` — matrix-form homomorphism (`bloch_hom` lifted): `R(A·B) = R(A)·R(B)`.
  * `blochMat_transpose` — `R(M)ᵀ = R(M†)` (trace cyclicity).
  * `blochMat_transpose_mul` — `R(M)ᵀ · R(M) = I` for unitary `M` (orthogonality).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only, finite `decide`).
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.BlochHomomorphism

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2
open scoped Matrix

/-- **The SO(3) Bloch image** as a matrix (entry `i j` = `blochEntry M i j`). -/
def blochMat (M : Mat2) : Matrix (Fin 3) (Fin 3) ZOmegaSqrt2 :=
  Matrix.of (fun i j => blochEntry M i j)

/-- **Matrix-form Bloch homomorphism**: `R(A·B) = R(A)·R(B)` for unitary `B`
(`bloch_hom` lifted to matrices). -/
theorem blochMat_mul {A B : Mat2} (hB : ZOmegaSqrt2.IsUnitaryT B) :
    blochMat (A * B) = blochMat A * blochMat B := by
  ext i j
  simp only [blochMat, Matrix.of_apply, Matrix.mul_apply]
  exact bloch_hom hB i j

set_option maxRecDepth 8000 in
/-- **`R(I) = I`**. -/
theorem blochMat_one : blochMat (1 : Mat2) = 1 := by decide

/-- **The matrix adjoint is an involution**: `(M†)† = M`. -/
theorem adjoint_adjoint (M : Mat2) : ZOmegaSqrt2.adjoint (ZOmegaSqrt2.adjoint M) = M := by
  ext i j; simp only [ZOmegaSqrt2.adjoint_apply, ZOmegaSqrt2.conj_conj]

/-- **`R(M)ᵀ = R(M†)`** — the Bloch image of the adjoint is the transpose
(trace cyclicity: `Tr(σⱼ M σᵢ M†) = Tr(σᵢ M† σⱼ M)`). -/
theorem blochMat_transpose (M : Mat2) :
    (blochMat M)ᵀ = blochMat (ZOmegaSqrt2.adjoint M) := by
  ext i j
  simp only [blochMat, Matrix.of_apply, Matrix.transpose_apply, blochEntry]
  rw [adjoint_adjoint]
  congr 1
  calc (pauliMat j * M * pauliMat i * ZOmegaSqrt2.adjoint M).trace
      = ((pauliMat j * M) * (pauliMat i * ZOmegaSqrt2.adjoint M)).trace :=
        congrArg Matrix.trace (Matrix.mul_assoc _ _ _)
    _ = ((pauliMat i * ZOmegaSqrt2.adjoint M) * (pauliMat j * M)).trace :=
        Matrix.trace_mul_comm _ _
    _ = (pauliMat i * ZOmegaSqrt2.adjoint M * pauliMat j * M).trace :=
        congrArg Matrix.trace (Matrix.mul_assoc _ _ _).symm

/-- **The Bloch image is orthogonal**: `R(M)ᵀ · R(M) = I` for unitary `M`.
(`R(M)ᵀ = R(M†)`, then `R(M†)·R(M) = R(M†·M) = R(1) = I`.) The `bᵀb = 2^kSO3·I`
achievability constraint follows by clearing. -/
theorem blochMat_transpose_mul {M : Mat2} (hM : ZOmegaSqrt2.IsUnitaryT M) :
    (blochMat M)ᵀ * blochMat M = 1 := by
  rw [blochMat_transpose, ← blochMat_mul hM, show ZOmegaSqrt2.adjoint M * M = 1 from hM,
      blochMat_one]

end KMM

end SKEFTHawking.RossSelinger
