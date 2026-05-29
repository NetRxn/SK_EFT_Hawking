/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4e — the partial Pauli twirl

The projection at the heart of the Clifford-adjoint irreducibility: weighting the Pauli-conjugation
action `Y ↦ kronK8 w · Y · kronK8 w` by the character `χ_{v₀}(w) = (−1)^⟨w,v₀⟩` and summing over all 64
Pauli labels `w` **projects `Y` onto the single Pauli line** `ℝ·kronK8 v₀`:

  `∑_w (−1)^⟨w,v₀⟩ · (kronK8 w · Y · kronK8 w) = (64 · ⟨P_{v₀}, Y⟩) · kronK8 v₀`,

where `⟨P_{v₀}, Y⟩ = kronK8Basis.repr Y v₀` is the `v₀`-coordinate of `Y` in the tensor-Pauli basis.

The consequence (consumed by the irreducibility proof): if `Y` lies in a subspace `W` closed under Pauli
conjugation and the `v₀`-coordinate of `Y` is nonzero, then `kronK8 v₀ ∈ W` (the LHS is a linear
combination of `kronK8 w · Y · kronK8 w ∈ W`, and the scalar `64·repr` is invertible).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6z provenance

Phase 6z Wave 4 increment 4e (partial Pauli twirl). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8CharOrth

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix

/-- **Partial Pauli twirl**: the `χ_{v₀}`-weighted Pauli-conjugation sum projects `Y` onto the single
tensor-Pauli line `ℝ·kronK8 v₀`, with weight `64 · (v₀-coordinate of Y)`. -/
theorem pauli_twirl (Y : Matrix (Fin 8) (Fin 8) ℂ) (v0 : Fin 4 × Fin 4 × Fin 4) :
    ∑ w : Fin 4 × Fin 4 × Fin 4, sigmaSign8 w v0 • (kronK8 w * Y * kronK8 w)
      = (64 * kronK8Basis.repr Y v0) • kronK8 v0 := by
  -- Inner conjugation: `kronK8 w · Y · kronK8 w = ∑ p, (repr_p · (−1)^⟨w,p⟩) • kronK8 p`.
  have hconj : ∀ w : Fin 4 × Fin 4 × Fin 4,
      kronK8 w * Y * kronK8 w
        = ∑ p, (kronK8Basis.repr Y p * sigmaSign8 w p) • kronK8 p := by
    intro w
    conv_lhs => rw [← kronK8Basis_sum_repr Y]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [mul_smul_comm, smul_mul_assoc, kronK8_conj, smul_smul]
  simp_rw [hconj, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine (Finset.sum_eq_single v0 ?_ ?_).trans ?_
  · -- Off-diagonal `p ≠ v₀` terms vanish by character orthogonality.
    intro p _ hp
    have hfac : (∑ w : Fin 4 × Fin 4 × Fin 4,
          sigmaSign8 w v0 * (kronK8Basis.repr Y p * sigmaSign8 w p))
        = kronK8Basis.repr Y p * ∑ w, sigmaSign8 w v0 * sigmaSign8 w p := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => by ring)
    rw [← Finset.sum_smul, hfac, sigmaSign8_orth, if_neg (fun h => hp h.symm)]
    simp
  · intro h; exact absurd (Finset.mem_univ v0) h
  · -- The `p = v₀` diagonal term: orthogonality gives the factor `64`.
    have hfac : (∑ w : Fin 4 × Fin 4 × Fin 4,
          sigmaSign8 w v0 * (kronK8Basis.repr Y v0 * sigmaSign8 w v0))
        = kronK8Basis.repr Y v0 * ∑ w, sigmaSign8 w v0 * sigmaSign8 w v0 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => by ring)
    rw [← Finset.sum_smul, hfac, sigmaSign8_orth, if_pos rfl]
    rw [show kronK8Basis.repr Y v0 * (64 : ℂ) = 64 * kronK8Basis.repr Y v0 from by ring]

end SKEFTHawking.FKLW.CliffordCCZSU8
