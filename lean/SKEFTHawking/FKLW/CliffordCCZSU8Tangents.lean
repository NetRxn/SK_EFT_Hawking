/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2 (D) witness — the 63 tensor-Pauli tangents of 𝔰𝔲(8)

The `ClosureDenseWitness` for the SU(8) Clifford+CCZ alphabet needs a finite family of traceless
skew-Hermitian matrices that ℝ-span `𝔰𝔲(8)` (the `hX_in_sud` + `hX_spans` fields). This module
ships the canonical **3-qubit tensor-Pauli basis**:

  `X_{abc} := (i/2) · (σ_a ⊗ σ_b ⊗ σ_c)`,  `(a,b,c) ∈ {0,1,2,3}³ ∖ {(0,0,0)}`  (63 matrices),

with `σ_0 = I`, `σ_1 = σ_x`, `σ_2 = σ_y`, `σ_3 = σ_z`, lifted to `Matrix (Fin 8) (Fin 8) ℂ` via
`kronSU8 A B C := kronSU2SU4 A (kronSU4 B C)` (the `finProdFinEquiv`-reindexed 3-fold Kronecker
product). This module proves the `hX_in_sud` half of the witness:

  * **skew-Hermitian** — generic in `(a,b,c)`: `σ_a ⊗ σ_b ⊗ σ_c` is Hermitian (tensor of
    Hermitians), so `((i/2)·σ_a⊗σ_b⊗σ_c)ᴴ = (−i/2)·σ_a⊗σ_b⊗σ_c = −X_{abc}`.
  * **traceless** — needs `(a,b,c) ≠ (0,0,0)`: `tr(σ_a ⊗ σ_b ⊗ σ_c) = tr σ_a · tr σ_b · tr σ_c`
    and at least one factor is a traceless Pauli when `(a,b,c) ≠ (0,0,0)`.

The 63-element enumeration `suEightTangent : Fin 63 → Matrix (Fin 8) (Fin 8) ℂ` maps `j ↦ X_{abc}`
where `(a,b,c)` is the base-4 expansion of `j + 1` (so `(0,0,0)` is skipped).

This module is **alphabet-agnostic**: the tangent set + `hX_in_sud` (and the spanning ship in the
companion module) are identical for any genuinely-universal SU(8) gate set; only `hX_flow`
(the flow-line containment) depends on the specific generators.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 PROPER — (D) witness tangent set
(`hX_in_sud`). DR blueprint §5.3 (63-tangent tensor-Pauli family). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8Substrate
import SKEFTHawking.FKLW.TrappedIonSU4Tangents

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix Complex SKEFTHawking.FKLW.TrappedIonSU4

/-! ## 1. `kronSU2SU4` conjugate-transpose and trace helpers -/

/-- **`kronSU2SU4` commutes with conjugate-transpose**: `(A ⊗ B)ᴴ = Aᴴ ⊗ Bᴴ` (reindexed). -/
theorem kronSU2SU4_conjTranspose (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 4) (Fin 4) ℂ) :
    (kronSU2SU4 A B)ᴴ = kronSU2SU4 Aᴴ Bᴴ := by
  unfold kronSU2SU4
  rw [Matrix.conjTranspose_reindex]
  congr 1
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply]

/-- **Trace of `kronSU2SU4`**: `tr (A ⊗ B) = tr A · tr B` (reindex preserves trace). -/
theorem kronSU2SU4_trace (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 4) (Fin 4) ℂ) :
    (kronSU2SU4 A B).trace = A.trace * B.trace := by
  unfold kronSU2SU4
  rw [show (Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kronecker A B)).trace
        = (Matrix.kronecker A B).trace from ?_]
  · show (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) A B).trace = A.trace * B.trace
    exact Matrix.trace_kronecker A B
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp finProdFinEquiv.symm (fun j => (Matrix.kronecker A B) j j)

/-! ## 2. The 3-fold Kronecker `kronSU8` and its conjTranspose / trace -/

/-- The 3-fold Kronecker lift `σ_a ⊗ σ_b ⊗ σ_c : Matrix (Fin 8) (Fin 8) ℂ`, as
`kronSU2SU4 A (kronSU4 B C)` (first qubit `A`, last two qubits `B ⊗ C`). -/
noncomputable def kronSU8 (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  kronSU2SU4 A (kronSU4 B C)

/-- **`kronSU8` commutes with conjugate-transpose**: `(A⊗B⊗C)ᴴ = Aᴴ⊗Bᴴ⊗Cᴴ`. -/
theorem kronSU8_conjTranspose (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    (kronSU8 A B C)ᴴ = kronSU8 Aᴴ Bᴴ Cᴴ := by
  unfold kronSU8
  rw [kronSU2SU4_conjTranspose, kronSU4_conjTranspose]

/-- **Trace of `kronSU8`**: `tr (A⊗B⊗C) = tr A · tr B · tr C`. -/
theorem kronSU8_trace (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    (kronSU8 A B C).trace = A.trace * B.trace * C.trace := by
  unfold kronSU8
  rw [kronSU2SU4_trace, kronSU4_trace, mul_assoc]

/-! ## 3. The 63 tensor-Pauli tangents -/

/-- The tensor-Pauli matrix `X_{abc} := (i/2) · (σ_a ⊗ σ_b ⊗ σ_c)` in `Matrix (Fin 8) (Fin 8) ℂ`. -/
noncomputable def suEightTangentAux (a b c : Fin 4) : Matrix (Fin 8) (Fin 8) ℂ :=
  (Complex.I / 2) • kronSU8 (pauli4 a) (pauli4 b) (pauli4 c)

/-- `X_{abc}` is skew-Hermitian (for all `a, b, c`). -/
theorem suEightTangentAux_skew (a b c : Fin 4) :
    (suEightTangentAux a b c)ᴴ = - suEightTangentAux a b c := by
  unfold suEightTangentAux
  rw [Matrix.conjTranspose_smul, kronSU8_conjTranspose, pauli4_hermitian, pauli4_hermitian,
    pauli4_hermitian,
    show star (Complex.I / 2) = -(Complex.I / 2) by simp [Complex.ext_iff]; norm_num, neg_smul]

/-- `X_{abc}` is traceless whenever `(a, b, c) ≠ (0, 0, 0)`. -/
theorem suEightTangentAux_trace (a b c : Fin 4) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (suEightTangentAux a b c).trace = 0 := by
  unfold suEightTangentAux
  rw [Matrix.trace_smul, kronSU8_trace, pauli4_trace, pauli4_trace, pauli4_trace]
  rcases h with ha | hb | hc
  · simp [ha]
  · simp [hb]
  · simp [hc]

/-- Enumeration of the 63 non-`(0,0,0)` index triples via the base-4 expansion of `j + 1`. -/
def idx63 (j : Fin 63) : Fin 4 × Fin 4 × Fin 4 :=
  (⟨(j.val + 1) / 16, by have := j.isLt; omega⟩,
   ⟨((j.val + 1) / 4) % 4, by omega⟩,
   ⟨(j.val + 1) % 4, by omega⟩)

/-- Each enumerated index triple is non-`(0,0,0)`. -/
theorem idx63_ne_zero (j : Fin 63) :
    (idx63 j).1 ≠ 0 ∨ (idx63 j).2.1 ≠ 0 ∨ (idx63 j).2.2 ≠ 0 := by
  have hj := j.isLt
  by_contra h
  simp only [not_or, ne_eq, not_not] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : ((idx63 j).1).val = 0 := by rw [h1]; rfl
  have e2 : ((idx63 j).2.1).val = 0 := by rw [h2]; rfl
  have e3 : ((idx63 j).2.2).val = 0 := by rw [h3]; rfl
  simp only [idx63] at e1 e2 e3
  omega

/-- **The 63-tangent family** `X : Fin 63 → Matrix (Fin 8) (Fin 8) ℂ` for the SU(8)
`ClosureDenseWitness`: `j ↦ X_{abc}` with `(a, b, c) = idx63 j`. -/
noncomputable def suEightTangent (j : Fin 63) : Matrix (Fin 8) (Fin 8) ℂ :=
  suEightTangentAux (idx63 j).1 (idx63 j).2.1 (idx63 j).2.2

/-- Each tangent is skew-Hermitian. -/
theorem suEightTangent_isSkewHermitian (j : Fin 63) :
    (suEightTangent j).IsSkewHermitian :=
  suEightTangentAux_skew (idx63 j).1 (idx63 j).2.1 (idx63 j).2.2

/-- Each tangent is traceless. -/
theorem suEightTangent_trace_zero (j : Fin 63) : (suEightTangent j).trace = 0 :=
  suEightTangentAux_trace (idx63 j).1 (idx63 j).2.1 (idx63 j).2.2 (idx63_ne_zero j)

/-- **`hX_in_sud` for the SU(8) witness**: each tangent is traceless skew-Hermitian. -/
theorem suEightTangent_in_sud (j : Fin 63) :
    (suEightTangent j).IsSkewHermitian ∧ (suEightTangent j).trace = 0 :=
  ⟨suEightTangent_isSkewHermitian j, suEightTangent_trace_zero j⟩

end SKEFTHawking.FKLW.CliffordCCZSU8
