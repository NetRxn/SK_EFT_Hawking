/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — the `reduceStep` column-0 transformation

`KMMCompute.lean` defines the KMM reduction step `reduceStep M k = H·Tᵏ·M`. The
KMM `sde(|z₀₀|²)` analysis needs the explicit effect of this step on column `0`.
Since `H = (1/√2)·!![1,1;1,-1]` and `Tᵏ = diag(1, ωᵏ)`, the new column-`0` entries
are the Hadamard combination of the old column-`0` entries (with the lower one
phased by `ωᵏ`), scaled by `1/√2`:

  `(reduceStep M k) 0 0 = (1/√2)·(M₀₀ + ωᵏ·M₁₀)`,
  `(reduceStep M k) 1 0 = (1/√2)·(M₀₀ − ωᵏ·M₁₀)`.

So the new top-left entry is `z' = (z + ωᵏ·w)/√2` with `z = M₀₀`, `w = M₁₀` —
exactly KMM's `s = −1` update, whose `|z'|² = |z+ωᵏw|²/2` is the quantity KMM
Lemma 3 (lifted to `kmm_lemma3_column`) controls. This is the algebraic bridge
between the residue-level reduction existence and the matrix-`sde` decrease.

## Headline results

  * `T_pow_diag` — `gateMatrix .T ^ k = diagonal ![1, ωᵏ]` (the `T`-power is the
    diagonal phase).
  * `reduceStep_zero_zero` — `(reduceStep M k) 0 0 = invSqrt2·(M₀₀ + ωᵏ·M₁₀)`.
  * `reduceStep_one_zero` — `(reduceStep M k) 1 0 = invSqrt2·(M₀₀ − ωᵏ·M₁₀)`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected (kernel-pure matrix algebra).

-/

import SKEFTHawking.FKLW.RossSelinger.KMMCompute

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2

/-- **The `T`-power is the diagonal phase**: `gateMatrix .T ^ k = diagonal ![1, ωᵏ]`.
`T = diag(1, ω)`, and `diagonal` powers act coordinatewise (`Matrix.diagonal_pow`). -/
theorem T_pow_diag (k : ℕ) : gateMatrix .T ^ k = Matrix.diagonal ![1, ωS ^ k] := by
  have hT : gateMatrix .T = Matrix.diagonal ![1, ωS] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [gateMatrix, Matrix.diagonal]
  rw [hT, Matrix.diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> first | exact one_pow k | rfl

/-- **`reduceStep` top-left entry**: `(H·Tᵏ·M) 0 0 = (1/√2)·(M₀₀ + ωᵏ·M₁₀)`. The
new `z' = (z + ωᵏw)/√2` of KMM's `s = −1` synthesis step. -/
theorem reduceStep_zero_zero (M : Mat2) (k : Fin 4) :
    (reduceStep M k) 0 0 = invSqrt2 * (M 0 0 + ωS ^ (k : ℕ) * M 1 0) := by
  have hd10 : (Matrix.diagonal ![1, ωS ^ (k : ℕ)]) 1 0 = 0 :=
    Matrix.diagonal_apply_ne _ (by decide)
  have hd01 : (Matrix.diagonal ![1, ωS ^ (k : ℕ)]) 0 1 = 0 :=
    Matrix.diagonal_apply_ne _ (by decide)
  have hd00 : (Matrix.diagonal ![1, ωS ^ (k : ℕ)]) 0 0 = 1 := by
    rw [Matrix.diagonal_apply_eq]; rfl
  have hd11 : (Matrix.diagonal ![1, ωS ^ (k : ℕ)]) 1 1 = ωS ^ (k : ℕ) := by
    rw [Matrix.diagonal_apply_eq]; rfl
  rw [reduceStep, T_pow_diag]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, gateMatrix, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, hd10, hd01, hd00, hd11]
  ring

/-- **`reduceStep` lower-left entry**: `(H·Tᵏ·M) 1 0 = (1/√2)·(M₀₀ − ωᵏ·M₁₀)`. The
orthogonal Hadamard combination (`H` row `1` is `[1/√2, −1/√2]`). -/
theorem reduceStep_one_zero (M : Mat2) (k : Fin 4) :
    (reduceStep M k) 1 0 = invSqrt2 * (M 0 0 - ωS ^ (k : ℕ) * M 1 0) := by
  have hd10 : (Matrix.diagonal ![1, ωS ^ (k : ℕ)]) 1 0 = 0 :=
    Matrix.diagonal_apply_ne _ (by decide)
  have hd01 : (Matrix.diagonal ![1, ωS ^ (k : ℕ)]) 0 1 = 0 :=
    Matrix.diagonal_apply_ne _ (by decide)
  have hd00 : (Matrix.diagonal ![1, ωS ^ (k : ℕ)]) 0 0 = 1 := by
    rw [Matrix.diagonal_apply_eq]; rfl
  have hd11 : (Matrix.diagonal ![1, ωS ^ (k : ℕ)]) 1 1 = ωS ^ (k : ℕ) := by
    rw [Matrix.diagonal_apply_eq]; rfl
  rw [reduceStep, T_pow_diag]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, gateMatrix, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, hd10, hd01, hd00, hd11]
  ring

end KMM

end SKEFTHawking.RossSelinger
