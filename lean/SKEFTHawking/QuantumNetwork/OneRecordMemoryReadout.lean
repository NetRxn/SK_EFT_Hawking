import SKEFTHawking.QuantumNetwork.OneRecordCoherentPrior
import SKEFTHawking.QuantumNetwork.DiamondNorm

/-!
# Memory-only discrimination in the one-record timing circuit

The fixed memory-X instrument and an arbitrary memory-only binary effect
can have different success probabilities after timing selection.
-/

open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule

/-- The system-major entry formula agrees with the library partial trace,
with memory as the retained factor. -/
theorem memoryMarginal_eq_partialTrace (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    memoryMarginal ρ =
      partialTrace (Matrix.of fun (i j : Fin 2 × Fin 2) =>
        ρ (finProdFinEquiv (i.2, i.1)) (finProdFinEquiv (j.2, j.1))) := by
  ext i j
  rfl

private theorem memoryMarginal_smul (z : ℂ) (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    memoryMarginal (z • ρ) = z • memoryMarginal ρ := by
  ext i j
  simp [memoryMarginal, Matrix.smul_apply, mul_add]

/-- The projection onto the unit vector (3,-4)/5 supplies the explicit
memory-only score for equal priors after selection. -/
private theorem selected_memory_effect_score (c d : ℝ)
    (hc : c^2 = 1 / 2) (hd : d^2 = 1 / 2) :
    let P := memoryMarginal (coherentPriorState 1 0 c d)
    let Q := memoryMarginal (dephasedSelected 1 0 c d)
    ∃ E : Matrix (Fin 2) (Fin 2) ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
      (P * E).trace.re + (Q * (1 - E)).trace.re = 31 / 40 := by
  intro P Q
  let v : Fin 2 → ℂ := ![3, -4]
  let w : Fin 2 → ℂ := ![4, 3]
  let E := ((1 / 25 : ℝ) : ℂ) • vecMulVec v (star v)
  let F := ((1 / 25 : ℝ) : ℂ) • vecMulVec w (star w)
  have hE : E.PosSemidef :=
    (posSemidef_vecMulVec_self_star v).smul (Complex.zero_le_real.mpr (by norm_num))
  have hF : F.PosSemidef :=
    (posSemidef_vecMulVec_self_star w).smul (Complex.zero_le_real.mpr (by norm_num))
  have complement : (1 : Matrix (Fin 2) (Fin 2) ℂ) - E = F := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [E, F, v, w, Matrix.vecMulVec_apply, Matrix.smul_apply,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.div_ofNat_re, Complex.div_ofNat_im]
  obtain ⟨hC, hD⟩ := selected_memory_marginals 1 0 c d (by norm_num) (by rw [hc, hd]; norm_num)
  have hP : P = (1 / 4 : ℂ) • (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
    dsimp only [P, coherentPriorState]
    rw [memoryMarginal_smul, hC, hd, smul_smul, ← Complex.ofReal_mul]
    norm_num
  have hQ : Q = Matrix.diagonal ![(3 / 8 : ℂ), (1 / 8 : ℂ)] := by
    dsimp only [Q]
    rw [hD]
    norm_num [hc, hd]
  refine ⟨E, hE, complement.symm ▸ hF, ?_⟩
  rw [hP, hQ, complement]
  norm_num [E, F, v, w, Matrix.trace, Matrix.mul_apply, Matrix.diag,
    Matrix.vecMulVec_apply, Matrix.smul_apply, Fin.sum_univ_two,
    Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im]

/-- For the half-offset circuit and equal priors after selection, a memory
effect scores 31/40 and beats every decision rule applied to memory X. -/
theorem selected_memory_effect_beats_X (c d : ℝ)
    (hc : c^2 = 1 / 2) (hd : d^2 = 1 / 2) :
    let P := coherentPriorState 1 0 c d
    let Q := dephasedSelected 1 0 c d
    let XP := fun r => memoryXReadout.branch r P
    let XQ := fun r => memoryXReadout.branch r Q
    ∃ E : Matrix (Fin 2) (Fin 2) ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
      ((memoryMarginal P * E).trace.re + (memoryMarginal Q * (1 - E)).trace.re = 31 / 40) ∧
      (∀ rule : Fin 2 → Bool, finite_binary_record_success XP XQ rule < 31 / 40) := by
  intro P Q XP XQ
  obtain ⟨E, hE, hEF, hScore⟩ := selected_memory_effect_score c d hc hd
  refine ⟨E, hE, hEF, hScore, ?_⟩
  have hdn : d ≠ 0 := by
    intro h
    norm_num [h] at hd
  obtain ⟨_, hMax, _⟩ :=
    one_record_memoryX_optimal_with_prior 1 0 c d (1/2)
      (by norm_num) (by rw [hc, hd]; norm_num) hdn (by norm_num) (by norm_num)
  intro rule
  have hr := hMax rule
  have hfactor : (1 / 2 : ℝ) / (d^2 / 2) = (d^2)⁻¹ := by rw [hd]; norm_num
  have hother : (2 * (1 - 1 / 2) : ℝ) = 1 := by norm_num
  simp only [hfactor, hother, Complex.ofReal_one, one_smul] at hr
  apply lt_of_le_of_lt hr
  norm_num

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
