/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4f.2a — single-qubit Clifford generator conjugation values

The single-qubit conjugation action of the Clifford generators on the Paulis, in the form needed for the
tensor tableau lifts (`gen · σ_a · gen⁻¹ = sign • σ_{φ(a)}`). This module ships the **Hadamard** value:

  `litHadamard · σ_a · litHadamard = hSign a · σ_{hLabel a}`

(`litHadamard` is Hermitian and an involution, so `litHadamard⁻¹ = litHadamard`). The label map `hLabel`
(`X ↔ Z`, `I, Y` fixed) matches `CliffordCCZSU8LabelTransitivity.hLabel`; the sign `hSign` is `−1` only on
`Y` (`H σ_y H = −σ_y`). The companion S-gate and CNOT conjugation values follow in subsequent increments,
and tensor up (via `kronSU8_mul`) to the 3-qubit generator tableau lifts driving the W-transport.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4f.2a (single-qubit generator conjugation — Hadamard). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8LiteralSeed
import SKEFTHawking.FKLW.CliffordCCZSU8LabelTransitivity

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4 SKEFTHawking.FKLW.CliffordCCZ

/-- The Hadamard-conjugation sign on the Paulis: `+1` on `I, X, Z`; `−1` on `Y` (`H σ_y H = −σ_y`). -/
noncomputable def hSign : Fin 4 → ℂ := ![1, 1, -1, 1]

/-- **Single-qubit Hadamard conjugation value**: `H · σ_a · H = (±1) · σ_{hLabel a}` with `hLabel`
swapping `X ↔ Z` (and `H σ_y H = −σ_y`). Proof: factor the two `1/√2` scalars (`(1/√2)² = 1/2`) out of
`litHadamard = (1/√2)·!![1,1;1,-1]`, then the residual `(1/2)·(M σ_a M)` is a rational-entry 2×2
computation closed entrywise by `ring`. -/
theorem litHadamard_conj_pauli4 (a : Fin 4) :
    litHadamard * pauli4 a * litHadamard = hSign a • pauli4 (hLabel a) := by
  have hhalf : (1 / Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2 : ℂ) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  unfold litHadamard
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hhalf]
  fin_cases a <;>
    · simp only [hSign, hLabel]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.smul_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

end SKEFTHawking.FKLW.CliffordCCZSU8
