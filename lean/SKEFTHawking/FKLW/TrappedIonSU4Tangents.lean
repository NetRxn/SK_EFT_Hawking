/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness — the 15 tensor-Pauli tangents of 𝔰𝔲(4)

The `ClosureDenseWitness` for the trapped-ion SU(4) alphabet needs a finite family of
traceless skew-Hermitian matrices that ℝ-span `𝔰𝔲(4)` (the `hX_in_sud` + `hX_spans` fields).
This module ships the canonical **tensor-Pauli basis**:

  `X_{ab} := (i/2) · (σ_a ⊗ σ_b)`,  `(a, b) ∈ {0,1,2,3}² ∖ {(0,0)}`  (15 matrices),

with `σ_0 = I`, `σ_1 = σ_x`, `σ_2 = σ_y`, `σ_3 = σ_z`, lifted to `Matrix (Fin 4) (Fin 4) ℂ`
via `kronSU4` (the `finProdFinEquiv`-reindexed Kronecker product). This module proves the
`hX_in_sud` half of the witness:

  * **skew-Hermitian** — generic in `(a, b)`: `(σ_a ⊗ σ_b)` is Hermitian (tensor of Hermitians),
    so `((i/2)·σ_a⊗σ_b)ᴴ = (-i/2)·σ_a⊗σ_b = −X_{ab}`.
  * **traceless** — needs `(a, b) ≠ (0, 0)`: `tr(σ_a ⊗ σ_b) = tr σ_a · tr σ_b` and at least one
    factor is a traceless Pauli when `(a, b) ≠ (0, 0)`.

The 15-element enumeration `suFourTangent : Fin 15 → Matrix (Fin 4) (Fin 4) ℂ` maps `j ↦ X_{ab}`
where `(a, b)` is the `(j+1)`-th pair in lex order of `Fin 4 × Fin 4` (so `(0,0)` is skipped).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness tangent set
(`hX_in_sud`). DR blueprint `Lit-Search/Phase-6y/…ClosureDenseWitness…Blueprint.md` §1a + §2.
2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4Substrate
import SKEFTHawking.PauliMatrices
import SKEFTHawking.FKLW.SU2LieAlgebra

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix Complex

/-! ## 1. `kronSU4` conjugate-transpose and trace helpers -/

/-- **`kronSU4` commutes with conjugate-transpose**: `(A ⊗ B)ᴴ = Aᴴ ⊗ Bᴴ` (reindexed). -/
theorem kronSU4_conjTranspose (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (kronSU4 A B)ᴴ = kronSU4 Aᴴ Bᴴ := by
  unfold kronSU4
  rw [Matrix.conjTranspose_reindex]
  congr 1
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply]

/-- **Trace of `kronSU4`**: `tr (A ⊗ B) = tr A · tr B` (reindex preserves trace). -/
theorem kronSU4_trace (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (kronSU4 A B).trace = A.trace * B.trace := by
  unfold kronSU4
  rw [show (Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kronecker A B)).trace
        = (Matrix.kronecker A B).trace from ?_]
  · show (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) A B).trace = A.trace * B.trace
    exact Matrix.trace_kronecker A B
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp finProdFinEquiv.symm (fun j => (Matrix.kronecker A B) j j)

/-! ## 2. The Pauli-index family `pauli4` -/

/-- The four single-qubit Pauli matrices indexed by `Fin 4`: `0 ↦ I`, `1 ↦ σ_x`, `2 ↦ σ_y`,
`3 ↦ σ_z`. -/
noncomputable def pauli4 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | 1 => SKEFTHawking.σ_x
  | 2 => SKEFTHawking.σ_y
  | 3 => SKEFTHawking.σ_z

/-- Each `pauli4 a` is Hermitian. -/
theorem pauli4_hermitian (a : Fin 4) : (pauli4 a)ᴴ = pauli4 a := by
  fin_cases a <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z,
        Matrix.conjTranspose_apply])

/-- Trace of `pauli4 a`: `2` for the identity (`a = 0`), `0` for the genuine Paulis. -/
theorem pauli4_trace (a : Fin 4) : (pauli4 a).trace = if a = 0 then 2 else 0 := by
  fin_cases a <;>
    simp [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.trace,
      Matrix.diag_apply, Fin.sum_univ_two]

/-! ## 3. The 15 tensor-Pauli tangents -/

/-- The tensor-Pauli matrix `X_{ab} := (i/2) · (σ_a ⊗ σ_b)` in `Matrix (Fin 4) (Fin 4) ℂ`. -/
noncomputable def suFourTangentAux (a b : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (Complex.I / 2) • kronSU4 (pauli4 a) (pauli4 b)

/-- `X_{ab}` is skew-Hermitian (for all `a, b`). -/
theorem suFourTangentAux_skew (a b : Fin 4) :
    (suFourTangentAux a b)ᴴ = - suFourTangentAux a b := by
  unfold suFourTangentAux
  rw [Matrix.conjTranspose_smul, kronSU4_conjTranspose, pauli4_hermitian, pauli4_hermitian,
    show star (Complex.I / 2) = -(Complex.I / 2) by simp [Complex.ext_iff]; norm_num, neg_smul]

/-- `X_{ab}` is traceless whenever `(a, b) ≠ (0, 0)`. -/
theorem suFourTangentAux_trace (a b : Fin 4) (h : a ≠ 0 ∨ b ≠ 0) :
    (suFourTangentAux a b).trace = 0 := by
  unfold suFourTangentAux
  rw [Matrix.trace_smul, kronSU4_trace, pauli4_trace, pauli4_trace]
  rcases h with ha | hb
  · simp [ha]
  · simp [hb]

/-- Enumeration of the 15 non-`(0,0)` index pairs: `j ↦ ((j+1)/4, (j+1)%4)`. -/
def idx15 (j : Fin 15) : Fin 4 × Fin 4 :=
  (⟨(j.val + 1) / 4, by have := j.isLt; omega⟩, ⟨(j.val + 1) % 4, by omega⟩)

/-- Each enumerated index pair is non-`(0,0)`. -/
theorem idx15_ne_zero (j : Fin 15) : (idx15 j).1 ≠ 0 ∨ (idx15 j).2 ≠ 0 := by
  rcases Nat.lt_or_ge (j.val + 1) 4 with h | h
  · right
    intro hc
    have hv : ((idx15 j).2).val = 0 := by rw [hc]; rfl
    simp only [idx15] at hv
    omega
  · left
    intro hc
    have hv : ((idx15 j).1).val = 0 := by rw [hc]; rfl
    simp only [idx15] at hv
    omega

/-- **The 15-tangent family** `X : Fin 15 → Matrix (Fin 4) (Fin 4) ℂ` for the SU(4)
`ClosureDenseWitness`: `j ↦ X_{ab}` with `(a, b) = idx15 j`. -/
noncomputable def suFourTangent (j : Fin 15) : Matrix (Fin 4) (Fin 4) ℂ :=
  suFourTangentAux (idx15 j).1 (idx15 j).2

/-- Each tangent is skew-Hermitian. -/
theorem suFourTangent_isSkewHermitian (j : Fin 15) :
    (suFourTangent j).IsSkewHermitian := by
  show (suFourTangent j)ᴴ = - suFourTangent j
  exact suFourTangentAux_skew (idx15 j).1 (idx15 j).2

/-- Each tangent is traceless. -/
theorem suFourTangent_trace_zero (j : Fin 15) : (suFourTangent j).trace = 0 :=
  suFourTangentAux_trace (idx15 j).1 (idx15 j).2 (idx15_ne_zero j)

/-- **`hX_in_sud` for the SU(4) witness**: each tangent is traceless skew-Hermitian. -/
theorem suFourTangent_in_sud (j : Fin 15) :
    (suFourTangent j).IsSkewHermitian ∧ (suFourTangent j).trace = 0 :=
  ⟨suFourTangent_isSkewHermitian j, suFourTangent_trace_zero j⟩

end SKEFTHawking.FKLW.TrappedIonSU4
