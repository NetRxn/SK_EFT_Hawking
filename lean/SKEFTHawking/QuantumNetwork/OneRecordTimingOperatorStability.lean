import SKEFTHawking.QuantumNetwork.FiniteInstrument
import SKEFTHawking.QuantumNetwork.OneRecordSelectionStability
import SKEFTHawking.QuantumNetwork.UnitaryDiamond

/-!
# Operator errors in the one-record timing circuit

Errors are measured in the shared system-memory basis, including the
relative phase used by the antisymmetric selection. The contraction
telescope bounds both selected density errors. The existing fixed
input prior certificate propagates the budget through conditioning.
-/

set_option autoImplicit false

namespace SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

private theorem anti_contraction {E L : Matrix (Fin 4) (Fin 4) ℂ}
    (hE : ‖E‖ ≤ 1) (hL : ‖L‖ ≤ 1) : ‖antisymmetricTimingOperator E L‖ ≤ 1 := by
  rw [antisymmetricTimingOperator, norm_smul, norm_div, norm_one]
  norm_num
  have h := (norm_sub_le L E).trans (add_le_add hL hE)
  linarith only [h]

private theorem anti_difference_le (E L E' L' : Matrix (Fin 4) (Fin 4) ℂ) :
    ‖antisymmetricTimingOperator E L - antisymmetricTimingOperator E' L'‖ ≤
      (‖E - E'‖ + ‖L - L'‖) / 2 := by
  have h : antisymmetricTimingOperator E L - antisymmetricTimingOperator E' L' =
      (1 / 2 : ℂ) • ((L - L') - (E - E')) := by
    simp only [antisymmetricTimingOperator,smul_sub]
    abel
  rw [h,norm_smul,norm_div,norm_one]
  norm_num
  have hSub := norm_sub_le (L - L') (E - E')
  linarith only [hSub]

private theorem timingInput_traceNorm : traceNorm timingInput = 1 := by
  rw [traceNorm_posSemidef timingInput_state.1, timingInput_state.2]

/-- Selected outputs from actual timing operators are positive. -/
theorem timingOutputs_positive (E L : Matrix (Fin 4) (Fin 4) ℂ) :
    (coherentTimingOutput E L).PosSemidef ∧ (dephasedTimingOutput E L).PosSemidef := by
  constructor
  · exact timingInput_state.1.mul_mul_conjTranspose_same _
  · unfold dephasedTimingOutput
    have h := (timingInput_state.1.mul_mul_conjTranspose_same E).add
      (timingInput_state.1.mul_mul_conjTranspose_same L)
    have hPos : (0 : ℂ) ≤ (1 / 4 : ℂ) := by
      convert Complex.zero_le_real.mpr (show (0 : ℝ) ≤ 1 / 4 by norm_num) using 1
      norm_num
    exact h.smul hPos

/-- Operator norm errors in the two contracted timing arms bound the raw
coherent density error and half as much in the dephased density. -/
theorem timing_operator_error_bound (a b c d : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1)
    (E' L' : Matrix (Fin 4) (Fin 4) ℂ) (hE' : ‖E'‖ ≤ 1) (hL' : ‖L'‖ ≤ 1) :
    let E := earlyTimingOperator a b c d
    let L := lateTimingOperator a b c d
    let e := ‖E - E'‖ + ‖L - L'‖
    traceNorm (coherentSelected a b c d - coherentTimingOutput E' L') ≤ e ∧
      traceNorm (dephasedSelected a b c d - dephasedTimingOutput E' L') ≤ e / 2 := by
  intro E L e
  obtain ⟨hEu,hLu⟩ := timingOperators_unitary a b c d train offset
  obtain ⟨hC,hD⟩ := timingOperators_reproduce_selected a b c d
  have hE := l2_opNorm_le_one_of_unitary hEu
  have hL := l2_opNorm_le_one_of_unitary hLu
  constructor
  · rw [← hC]
    unfold coherentTimingOutput
    dsimp only
    have h := traceNorm_conj_diff_le (anti_contraction hE hL)
      (anti_contraction hE' hL') timingInput
    rw [timingInput_traceNorm,mul_one] at h
    refine h.trans ?_
    have ha := anti_difference_le E L E' L'
    dsimp only [e]
    linarith only [ha]
  · rw [← hD]
    unfold dephasedTimingOutput
    rw [← smul_sub]
    have hsplit : (E * timingInput * Eᴴ + L * timingInput * Lᴴ) -
        (E' * timingInput * E'ᴴ + L' * timingInput * L'ᴴ) =
        (E * timingInput * Eᴴ - E' * timingInput * E'ᴴ) +
        (L * timingInput * Lᴴ - L' * timingInput * L'ᴴ) := by abel
    rw [hsplit,traceNorm_eq_physlib,Matrix.traceNorm_smul,← traceNorm_eq_physlib,
      norm_div,norm_one]
    norm_num
    have hE0 := traceNorm_conj_diff_le hE hE' timingInput
    have hL0 := traceNorm_conj_diff_le hL hL' timingInput
    rw [timingInput_traceNorm,mul_one] at hE0 hL0
    have h := (traceNorm_add_le _ _).trans (add_le_add hE0 hL0)
    dsimp only [e]
    linarith only [h]

/-- An operator error budget at the fixed input prior gives positive
observed selection mass and a joint effect beating every memory-only
binary effect after conditioning. -/
theorem selected_joint_beats_memory_under_timing_operator_error (a b c d r : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0)
    (hr : 1 / 3 < r) (hr1 : r < 1) (hd1 : d^2 < 1)
    (E' L' : Matrix (Fin 4) (Fin 4) ℂ) (hE' : ‖E'‖ ≤ 1) (hL' : ‖L'‖ ≤ 1) :
    let C' := coherentTimingOutput E' L'
    let D' := dephasedTimingOutput E' L'
    let e := ‖earlyTimingOperator a b c d - E'‖ + ‖lateTimingOperator a b c d - L'‖
    let m := r * (d^2 / 2) + (1 - r) / 2
    let m' := r * C'.trace.re + (1 - r) * D'.trace.re
    let p := r * (d^2 / 2) / m
    let q := 1 - p
    let P' := (((r / m' : ℝ) : ℂ)) • C'
    let Q' := ((((1 - r) / m' : ℝ) : ℂ)) • D'
    let margin := q * (1 - d^2) * (p - q * (d^2 / 2)) / (2 * (p + q * (1 - d^2)))
    2 / m * (((1 + r) / 2) * e) < margin →
    0 < m' ∧ ∃ E : Matrix (Fin 4) (Fin 4) ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
      ∀ F : Matrix (Fin 2) (Fin 2) ℂ, F.PosSemidef → (1 - F).PosSemidef →
        (memoryMarginal P' * F).trace.re + (memoryMarginal Q' * (1 - F)).trace.re <
          (P' * E).trace.re + (Q' * (1 - E)).trace.re := by
  intro C' D' e m m' p q P' Q' margin hbudget
  obtain ⟨hCpos,hDpos⟩ := timingOutputs_positive E' L'
  obtain ⟨hC,hD⟩ := timing_operator_error_bound a b c d train offset E' L' hE' hL'
  have hr0 : 0 < r := by linarith
  have hOther : 0 < 1 - r := sub_pos.mpr hr1
  have hm : 0 < m := add_pos (mul_pos hr0 (div_pos (sq_pos_of_ne_zero hd) (by norm_num)))
    (div_pos hOther (by norm_num))
  have hErr : r * traceNorm (coherentSelected a b c d - C') +
      (1 - r) * traceNorm (dephasedSelected a b c d - D') ≤ ((1 + r) / 2) * e := by
    calc
      _ ≤ r * e + (1 - r) * (e / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hC hr0.le) (mul_le_mul_of_nonneg_left hD hOther.le)
      _ = _ := by ring
  exact selected_joint_beats_memory_under_input_prior_error a b c d r train offset hd hr hr1 hd1
    C' D' hCpos hDpos ((mul_le_mul_of_nonneg_left hErr (by positivity)).trans_lt hbudget)

/-- A finite heralded instrument for the actual antisymmetric timing branch. -/
noncomputable def coherentTimingInstrument (E L : Matrix (Fin 4) (Fin 4) ℂ)
    (hE : ‖E‖ ≤ 1) (hL : ‖L‖ ≤ 1) :
    FiniteInstrument (Fin 4) 2 :=
  FiniteInstrument.ofContraction (antisymmetricTimingOperator E L) (anti_contraction hE hL)

/-- Its success branch is the existing unnormalized coherent timing output. -/
theorem coherentTimingInstrument_success (E L : Matrix (Fin 4) (Fin 4) ℂ)
    (hE : ‖E‖ ≤ 1) (hL : ‖L‖ ≤ 1) :
    (coherentTimingInstrument E L hE hL).branch 0 timingInput = coherentTimingOutput E L :=
  FiniteInstrument.ofContraction_success_branch _ _ _

/-- A normalized finite instrument for dephased timing with an explicit
failure outcome. The success branch keeps the two operator terms separate. -/
noncomputable def dephasedTimingInstrument (E L : Matrix (Fin 4) (Fin 4) ℂ)
    (hE : ‖E‖ ≤ 1) (hL : ‖L‖ ≤ 1) :
    FiniteInstrument (Fin 4) 2 := FiniteInstrument.halfArmInstrument E L hE hL

/-- The success branch equals the existing unnormalized dephased timing output. -/
theorem dephasedTimingInstrument_success (E L : Matrix (Fin 4) (Fin 4) ℂ)
    (hE : ‖E‖ ≤ 1) (hL : ‖L‖ ≤ 1) :
    (dephasedTimingInstrument E L hE hL).branch 0 timingInput = dephasedTimingOutput E L :=
  FiniteInstrument.halfArmInstrument_success_branch E L timingInput hE hL

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
