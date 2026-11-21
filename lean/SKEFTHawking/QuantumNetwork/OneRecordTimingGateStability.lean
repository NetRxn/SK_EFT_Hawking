import SKEFTHawking.QuantumNetwork.OneRecordTimingOperatorStability

/-!
# Gate errors in the one-record timing circuit

Each ordered arm product has an error bound from its copy, training and
offset gates. The calibrations can differ by arm. At the fixed input prior,
the weighted budget certifies the selected joint readout advantage.
-/

set_option autoImplicit false

namespace SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

private theorem contractive_mul_sub_mul_le {R : Type*} [NonUnitalSeminormedRing R]
    {A B A' B' : R} (hA : ‖A‖ ≤ 1) (hB' : ‖B'‖ ≤ 1) :
    ‖A * B - A' * B'‖ ≤ ‖A - A'‖ + ‖B - B'‖ := by
  rw [show A * B - A' * B' = (A - A') * B' + A * (B - B') by noncomm_ring]
  calc
    _ ≤ ‖(A - A') * B'‖ + ‖A * (B - B')‖ := norm_add_le _ _
    _ ≤ ‖A - A'‖ * ‖B'‖ + ‖A‖ * ‖B - B'‖ := add_le_add (norm_mul_le ..) (norm_mul_le ..)
    _ ≤ _ := add_le_add (mul_le_of_le_one_right (norm_nonneg _) hB')
      (mul_le_of_le_one_left (norm_nonneg _) hA)

private theorem contractive_mul {R : Type*} [NonUnitalSeminormedRing R]
    {A B : R} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A * B‖ ≤ 1 :=
  (norm_mul_le _ _).trans (mul_le_one₀ hA (norm_nonneg _) hB)

private theorem contractive_triple_sub_le {R : Type*} [NonUnitalSeminormedRing R]
    {A B C A' B' C' : R} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hB' : ‖B'‖ ≤ 1) (hC' : ‖C'‖ ≤ 1) :
    ‖(A * B) * C - (A' * B') * C'‖ ≤ ‖A - A'‖ + ‖B - B'‖ + ‖C - C'‖ :=
  (contractive_mul_sub_mul_le (contractive_mul hA hB) hC').trans
    (add_le_add (contractive_mul_sub_mul_le hA hB') le_rfl)

/-- Measured copy, training and offset contractions in the same phase convention
bound both arm errors. Each gate contributes once to each arm. -/
theorem timing_arm_error_of_gates (a b c d : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1)
    (C T O : Matrix (Fin 4) (Fin 4) ℂ) (hC : ‖C‖ ≤ 1) (hT : ‖T‖ ≤ 1) (hO : ‖O‖ ≤ 1) :
    let e := ‖timingMemoryCopy - C‖ + ‖timingSystemRotation a b - T‖ +
      ‖timingSystemRotation c d - O‖
    ‖earlyTimingOperator a b c d - C * T * O‖ ≤ e ∧
      ‖lateTimingOperator a b c d - O * C * T‖ ≤ e := by
  intro e
  have hCn := l2_opNorm_le_one_of_unitary timingMemoryCopy_unitary
  have hTn := l2_opNorm_le_one_of_unitary (timingSystemRotation_unitary a b train)
  have hOn := l2_opNorm_le_one_of_unitary (timingSystemRotation_unitary c d offset)
  constructor
  · exact contractive_triple_sub_le hCn hTn hT hO
  · change ‖timingSystemRotation c d * timingMemoryCopy * timingSystemRotation a b - O * C * T‖ ≤ _
    exact (contractive_triple_sub_le hOn hCn hC hT).trans_eq (by dsimp only [e]; ring)

/-- Independent calibrations of the copy, training and offset gates in each
arm certify the actual selected readout below the fixed-prior margin.
All six measured contractions use the same basis and phase convention as
the nominal timing circuit. -/
theorem selected_joint_beats_memory_under_separate_arm_gate_error (a b c d r : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0)
    (hr : 1 / 3 < r) (hr1 : r < 1) (hd1 : d^2 < 1)
    (CE TE OE CL TL OL : Matrix (Fin 4) (Fin 4) ℂ)
    (hCE : ‖CE‖ ≤ 1) (hTE : ‖TE‖ ≤ 1) (hOE : ‖OE‖ ≤ 1)
    (hCL : ‖CL‖ ≤ 1) (hTL : ‖TL‖ ≤ 1) (hOL : ‖OL‖ ≤ 1) :
    let E' := CE * TE * OE
    let L' := OL * CL * TL
    let C' := coherentTimingOutput E' L'
    let D' := dephasedTimingOutput E' L'
    let eEarly := ‖timingMemoryCopy - CE‖ + ‖timingSystemRotation a b - TE‖ +
      ‖timingSystemRotation c d - OE‖
    let eLate := ‖timingSystemRotation c d - OL‖ + ‖timingMemoryCopy - CL‖ +
      ‖timingSystemRotation a b - TL‖
    let m := r * (d^2 / 2) + (1 - r) / 2
    let m' := r * C'.trace.re + (1 - r) * D'.trace.re
    let p := r * (d^2 / 2) / m
    let q := 1 - p
    let P' := (((r / m' : ℝ) : ℂ)) • C'
    let Q' := ((((1 - r) / m' : ℝ) : ℂ)) • D'
    let margin := q * (1 - d^2) * (p - q * (d^2 / 2)) / (2 * (p + q * (1 - d^2)))
    2 / m * (((1 + r) / 2) * (eEarly + eLate)) < margin →
    0 < m' ∧ ∃ E : Matrix (Fin 4) (Fin 4) ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
      ∀ F : Matrix (Fin 2) (Fin 2) ℂ, F.PosSemidef → (1 - F).PosSemidef →
        (memoryMarginal P' * F).trace.re + (memoryMarginal Q' * (1 - F)).trace.re <
          (P' * E).trace.re + (Q' * (1 - E)).trace.re := by
  intro E' L' C' D' eEarly eLate m m' p q P' Q' margin hbudget
  have hCn := l2_opNorm_le_one_of_unitary timingMemoryCopy_unitary
  have hTn := l2_opNorm_le_one_of_unitary (timingSystemRotation_unitary a b train)
  have hOn := l2_opNorm_le_one_of_unitary (timingSystemRotation_unitary c d offset)
  have hEarly : ‖earlyTimingOperator a b c d - E'‖ ≤ eEarly :=
    contractive_triple_sub_le hCn hTn hTE hOE
  have hLate : ‖lateTimingOperator a b c d - L'‖ ≤ eLate :=
    contractive_triple_sub_le hOn hCn hCL hTL
  have hm : 0 < m := add_pos (mul_pos (by linarith) (div_pos (sq_pos_of_ne_zero hd) (by norm_num)))
    (div_pos (sub_pos.mpr hr1) (by norm_num))
  apply selected_joint_beats_memory_under_timing_operator_error a b c d r train offset hd hr hr1 hd1
    E' L' (contractive_mul (contractive_mul hCE hTE) hOE)
    (contractive_mul (contractive_mul hOL hCL) hTL)
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (add_le_add hEarly hLate) (by linarith)) (by positivity)).trans_lt hbudget


/-- When the amplified calibration budget is strictly below the nominal
margin, observed selection is positive and one joint effect beats every
binary memory-only effect. -/
theorem selected_joint_beats_memory_under_timing_gate_error (a b c d r : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0)
    (hr : 1 / 3 < r) (hr1 : r < 1) (hd1 : d^2 < 1)
    (C T O : Matrix (Fin 4) (Fin 4) ℂ) (hC : ‖C‖ ≤ 1) (hT : ‖T‖ ≤ 1) (hO : ‖O‖ ≤ 1) :
    let E' := C * T * O
    let L' := O * C * T
    let C' := coherentTimingOutput E' L'
    let D' := dephasedTimingOutput E' L'
    let e := ‖timingMemoryCopy - C‖ + ‖timingSystemRotation a b - T‖ +
      ‖timingSystemRotation c d - O‖
    let m := r * (d^2 / 2) + (1 - r) / 2
    let m' := r * C'.trace.re + (1 - r) * D'.trace.re
    let p := r * (d^2 / 2) / m
    let q := 1 - p
    let P' := (((r / m' : ℝ) : ℂ)) • C'
    let Q' := ((((1 - r) / m' : ℝ) : ℂ)) • D'
    let margin := q * (1 - d^2) * (p - q * (d^2 / 2)) / (2 * (p + q * (1 - d^2)))
    2 / m * ((1 + r) * e) < margin →
    0 < m' ∧ ∃ E : Matrix (Fin 4) (Fin 4) ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
      ∀ F : Matrix (Fin 2) (Fin 2) ℂ, F.PosSemidef → (1 - F).PosSemidef →
        (memoryMarginal P' * F).trace.re + (memoryMarginal Q' * (1 - F)).trace.re <
          (P' * E).trace.re + (Q' * (1 - E)).trace.re := by
  intro E' L' C' D' e m m' p q P' Q' margin hbudget
  apply selected_joint_beats_memory_under_separate_arm_gate_error a b c d r
    train offset hd hr hr1 hd1 C T O C T O hC hT hO hC hT hO
  convert hbudget using 1
  dsimp only [e, m]
  ring

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
