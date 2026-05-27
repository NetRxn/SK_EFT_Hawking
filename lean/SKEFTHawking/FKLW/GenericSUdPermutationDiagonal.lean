/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Diagonal conjugation by permutation matrix

For `σ : Equiv.Perm (Fin n)` and `a : Fin n → ℂ`, the diagonal matrix
`diagonal a` conjugated by `permMatrix σ` is `diagonal (a ∘ σ)`:

  `permMatrix σ · diagonal a · permMatrix σ⁻¹ = diagonal (a ∘ σ)`

Equivalently (using `Matrix.conjTranspose_permMatrix`):

  `permMatrix σ · diagonal a · (permMatrix σ).conjTranspose = diagonal (a ∘ σ)`

Combined with Session 26's U(d) conjugation invariance and Session 27's
permutation-matrix unitary membership, this enables the eigenvalue-sort
lift: given a discharge for `diag(a ∘ σ)` (where σ sorts `a` decreasingly
per Session 25), conjugate by `permMatrix σ⁻¹` to recover a discharge for
`diag(a)`.

## Substantive content shipped

  * `permMatrix_mul_diagonal_mul_permMatrix_inv` — the diagonal conjugation identity.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (diagonal
conjugation identity for eigenvalue-sort lift).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdPermutationConjugation

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

/-! ## 1. Diagonal conjugation identity

`permMatrix σ · diag(a) · permMatrix σ⁻¹ = diag(a ∘ σ)`.

In Mathlib's convention, `permMatrix σ` has `(P)_{i, j} = if σ i = j then 1 else 0`,
so `(P · v)_i = v_{σ i}`. The conjugation identity follows by entry-wise
computation. -/

/-- **Diagonal conjugation by permutation matrix**: for `σ : Equiv.Perm (Fin n)`
and `a : Fin n → ℂ`,

  `permMatrix σ * diagonal a * permMatrix σ⁻¹ = diagonal (a ∘ σ)`. -/
theorem permMatrix_mul_diagonal_mul_permMatrix_inv {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (a : Fin n → ℂ) :
    Equiv.Perm.permMatrix ℂ σ * Matrix.diagonal a *
      Equiv.Perm.permMatrix ℂ σ⁻¹ =
        Matrix.diagonal (a ∘ σ) := by
  ext i l
  -- LHS entry: ∑_{j, k} (P_σ)_{i,j} · diag(a)_{j,k} · (P_{σ⁻¹})_{k,l}
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix,
             Equiv.toPEquiv_apply, Option.mem_def, Matrix.of_apply,
             Matrix.diagonal_apply]
  -- Goal: ∑ k, (∑ j, (if some (σ i) = some j then 1 else 0) ·
  --              (if j = k then a j else 0)) ·
  --          (if some (σ⁻¹ k) = some l then 1 else 0) = ...
  -- Simplify: inner sum collapses to a_{σ i} when k = σ i, 0 otherwise.
  by_cases h_il : i = l
  · subst h_il
    rw [if_pos rfl]
    rw [Finset.sum_eq_single (σ i)]
    · rw [Finset.sum_eq_single (σ i)]
      · -- j = k = σ i: contribution = 1 · a (σ i) · [σ⁻¹ (σ i) = i] = a (σ i)
        have h_inv : σ⁻¹ (σ i) = i := by simp
        simp [h_inv]
      · intro j _ h_j_ne
        -- j ≠ σ i: (some (σ i) = some j) is false (σ i ≠ j)
        have h_some : ¬ (some (σ i) = some j) := fun h => h_j_ne (Option.some_inj.mp h).symm
        simp [h_some]
      · intro h; exact absurd (Finset.mem_univ (σ i)) h
    · intro k _ h_k_ne
      -- For k ≠ σ i: outer factor (P_{σ⁻¹})_{k,i} = 0 since σ⁻¹ k ≠ i
      have : ¬ (some (σ⁻¹ k) = some i) := by
        rw [Option.some_inj]
        intro h
        apply h_k_ne
        have h_app : σ (σ⁻¹ k) = k := by simp
        rw [← h, h_app]
      rw [if_neg this]
      ring
    · intro h; exact absurd (Finset.mem_univ (σ i)) h
  · rw [if_neg h_il]
    -- For i ≠ l: every k either has σ⁻¹ k ≠ l (then outer factor 0) or σ⁻¹ k = l
    -- (i.e., k = σ l), then inner sum picks j = σ l, but then need σ i = σ l,
    -- which implies i = l, contradiction.
    apply Finset.sum_eq_zero
    intro k _
    by_cases h_k_σl : σ⁻¹ k = l
    · -- σ⁻¹ k = l ⟹ k = σ l (so the outer factor is 1)
      have h_k_eq : k = σ l := by
        have h_app : σ (σ⁻¹ k) = k := by simp
        rw [← h_k_σl, h_app]
      subst h_k_eq
      -- Inner sum: ∑ j, [σ i = j] · [j = σ l] · a_j
      -- Only j = σ l contributes if σ i = σ l, but σ i = σ l ⟺ i = l, false.
      rw [Finset.sum_eq_zero]
      · ring
      · intro j _
        by_cases h_j_σl : j = σ l
        · subst h_j_σl
          have h_si_ne : ¬ (some (σ i) = some (σ l)) := by
            rw [Option.some_inj]
            intro h
            apply h_il
            exact σ.injective h
          rw [if_neg h_si_ne]; ring
        · rw [if_neg h_j_σl]; ring
    · -- σ⁻¹ k ≠ l: outer factor is 0
      have h_outer : ¬ (some (σ⁻¹ k) = some l) := by
        rw [Option.some_inj]; exact h_k_σl
      rw [if_neg h_outer]; ring

end SKEFTHawking.FKLW.GenericSUd
