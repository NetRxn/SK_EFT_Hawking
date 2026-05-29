/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — unitarity over ZOmegaSqrt2 (KMM Lemma 4 substrate)

KMM Lemma 4 uses that a unitary `2×2` matrix `M` over `ZOmegaSqrt2` has
orthonormal columns — in particular the column squared-norm identity
`|M₀₀|² + |M₁₀|² = 1`, which forces the two column entries to share a
common `sde`. This file ships the conjugate-transpose `adjoint`, the
`IsUnitaryT` predicate (`adjoint M * M = 1`), and the column-norm
extraction `unitary_col_normSq`.

## Headline results

  * `ZOmegaSqrt2.adjoint M = fun i j => conj (M j i)` — conjugate transpose.
  * `ZOmegaSqrt2.IsUnitaryT M := adjoint M * M = 1`.
  * `ZOmegaSqrt2.unitary_col0_normSq` — `IsUnitaryT M ⟹ normSq (M 0 0) +
    normSq (M 1 0) = 1`.
  * `ZOmegaSqrt2.unitary_col1_normSq` — the second-column analogue.

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §3, Lemma 4.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.Conj
import SKEFTHawking.FKLW.RossSelinger.KMM

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmegaSqrt2

open scoped Matrix

/-- **Conjugate transpose** of a `2×2` matrix over `ZOmegaSqrt2`. -/
def adjoint (M : Mat2) : Mat2 := fun i j => conj (M j i)

@[simp] theorem adjoint_apply (M : Mat2) (i j : Fin 2) :
    adjoint M i j = conj (M j i) := rfl

/-- **`M` is unitary** (over the `*`-ring `ZOmegaSqrt2`): `M† · M = 1`. -/
def IsUnitaryT (M : Mat2) : Prop := adjoint M * M = 1

/-- **Column-0 squared-norm identity for a unitary**:
`|M₀₀|² + |M₁₀|² = 1`. Extracted from the `(0,0)` entry of `M† · M = 1`. -/
theorem unitary_col0_normSq {M : Mat2} (h : IsUnitaryT M) :
    normSq (M 0 0) + normSq (M 1 0) = 1 := by
  have hentry := congrFun (congrFun h 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, adjoint_apply, adjoint_apply,
      Matrix.one_apply_eq] at hentry
  rw [normSq, normSq, mul_comm (M 0 0), mul_comm (M 1 0)]
  exact hentry

/-- **Column-1 squared-norm identity for a unitary**:
`|M₀₁|² + |M₁₁|² = 1`. -/
theorem unitary_col1_normSq {M : Mat2} (h : IsUnitaryT M) :
    normSq (M 0 1) + normSq (M 1 1) = 1 := by
  have hentry := congrFun (congrFun h 1) 1
  rw [Matrix.mul_apply, Fin.sum_univ_two, adjoint_apply, adjoint_apply,
      Matrix.one_apply_eq] at hentry
  rw [normSq, normSq, mul_comm (M 0 1), mul_comm (M 1 1)]
  exact hentry

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
