/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item I — compile approximation helpers (entrywise → operator norm)

`compile_correct` (the SOUNDNESS of the Ross-Selinger compiler: when the grid finder returns a
word, the synthesized unitary approximates the target in operator norm) decomposes into:
the grid finder gives a COLUMN approximation (`u/√2^k ≈ U₀₀`, `t/√2^k ≈ U₁₀`); the SU(2) structure
`U = [[a, −b̄],[b, ā]]` propagates this to ALL FOUR entries; and an **entrywise → ℓ∞-operator-norm**
bound converts the entrywise approximation to the `Matrix.linftyOpNorm` the Solovay-Kitaev headlines
use. This file ships that last, self-contained bound.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Adjugate

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

open scoped Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- **Entrywise → ℓ∞ operator-norm bound for `2×2` matrices.** If every entry of
`A : Matrix (Fin 2) (Fin 2) ℂ` has norm `≤ δ`, then `‖A‖ ≤ 2·δ` in the `linftyOpNorm`
(max-row-sum, the norm the SK headlines use). The factor `2` is the number of columns. -/
theorem linftyOpNorm_fin_two_le {A : Matrix (Fin 2) (Fin 2) ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i j, ‖A i j‖ ≤ δ) : ‖A‖ ≤ 2 * δ := by
  rw [Matrix.linfty_opNorm_def, ← Real.coe_toNNReal (2 * δ) (by positivity), NNReal.coe_le_coe]
  refine Finset.sup_le (fun i _ => ?_)
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal (2 * δ) (by positivity)]
  rw [Fin.sum_univ_two]
  push_cast
  linarith [h i 0, h i 1]

/-- **SU(2) entry structure.** Every `U ∈ SU(2)` has the form `[[a, −b̄],[b, ā]]`:
`U 0 1 = −conj(U 1 0)` and `U 1 1 = conj(U 0 0)`. Derived from `star U = U⁻¹ = adjugate U`
(unitary + `det U = 1`) + `adjugate_fin_two`. This propagates a first-column approximation
(`u/√2^k ≈ U₀₀`, `t/√2^k ≈ U₁₀`) to all four entries (the second column is determined). -/
theorem su2_entry_structure (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -(starRingEnd ℂ) ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∧
      (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (starRingEnd ℂ) ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  set M := (U : Matrix (Fin 2) (Fin 2) ℂ) with hM
  obtain ⟨hunit, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp U.2
  have hstar : star M * M = 1 := (Matrix.mem_unitaryGroup_iff'.mp hunit)
  have hinv : star M = M⁻¹ := Matrix.inv_eq_left_inv hstar |>.symm
  have hadj : M⁻¹ = M.adjugate := by
    rw [Matrix.inv_def, hdet]; simp
  have hsa : star M = M.adjugate := hinv.trans hadj
  rw [Matrix.adjugate_fin_two] at hsa
  have h01 := congrFun (congrFun hsa 0) 1
  have h11 := congrFun (congrFun hsa 1) 1
  simp only [Matrix.star_apply, RCLike.star_def, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val_fin_one] at h01 h11
  refine ⟨?_, ?_⟩
  · rw [h01]; ring
  · rw [← h11, Complex.conj_conj]

end SKEFTHawking.RossSelinger
