import SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedStrategyMemory
import SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyTransferExamples

/-!
# Actual binary compression and sampled memory

The family is the existing masked binary tree. Signed coefficients of actual
uninterrupted inserted histories are distinct from probability distributions.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedStrategyMemoryExamples
open Matrix FiniteInterventionProcess FiniteThreeLevelStationaryStrategyReflection
open FiniteThreeLevelStationaryStrategyTransfer FiniteThreeLevelStationaryStrategyTransferExamples
open FiniteThreeLevelCompressedStrategyMemory
open FiniteThreeLevelPositiveHistory (Q MatQ form Psi)
open FiniteThreeLevelHistoryTransfer (mean rotate)
open scoped BigOperators ComplexOrder InnerProductSpace

def centeredD : MatQ := Matrix.diagonal ![1/60, 1/60, -1/12]
def centeredH : MatQ := (1/10 : ℂ) • FiniteThreeLevelPositiveHistory.X 0 1
def centeredY : MatQ := (1/10 : ℂ) • FiniteThreeLevelPositiveHistory.Y 0 1
def centeredF : MatQ := binaryEffect - (1/12 : ℂ) • 1
def d : ℝ := 1/720
def h : ℝ := Real.sqrt 6 / 300
def N : ℝ := d + h
def alpha : ℝ := d / N

theorem centered_decomposition : centeredF = centeredD + centeredH := by
  rw [centeredF, binaryEffect_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.ext_iff, Matrix.cons_val, Matrix.cons_val_two, centeredD, centeredH, FiniteThreeLevelPositiveHistory.D,
      FiniteThreeLevelPositiveHistory.X, FiniteThreeLevelPositiveHistory.E, Matrix.single]

theorem centeredD_mode : centeredD = (1/60 : ℂ) • FiniteThreeLevelPositiveHistory.modeMatrix 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [centeredD, FiniteThreeLevelPositiveHistory.modeMatrix, FiniteThreeLevelPositiveHistory.Z2]

theorem centeredH_mode : centeredH = (1/10 : ℂ) • FiniteThreeLevelPositiveHistory.modeMatrix 2 := rfl
theorem centeredY_mode : centeredY = (1/10 : ℂ) • FiniteThreeLevelPositiveHistory.modeMatrix 3 := rfl

theorem form_DD : form centeredD centeredD = (d : ℂ) := by
  rw [centeredD_mode, FiniteThreeLevelPositiveHistory.form_smul,
    FiniteThreeLevelPositiveHistory.modeMatrix_form]
  norm_num [Matrix.cons_val, Fin.reduceFinMk, Fin.ext_iff, FiniteThreeLevelPositiveHistory.modeNorm, d]

theorem form_HH : form centeredH centeredH = (h : ℂ) := by
  have he : form (FiniteThreeLevelPositiveHistory.X 0 1)
      (FiniteThreeLevelPositiveHistory.X 0 1) = (Real.sqrt 6 / 3 : ℂ) := by
    simpa [FiniteThreeLevelPositiveHistory.modeMatrix, FiniteThreeLevelPositiveHistory.modeNorm]
      using FiniteThreeLevelPositiveHistory.modeMatrix_form 2 2
  rw [centeredH, FiniteThreeLevelPositiveHistory.form_smul, he]
  norm_num [h]
  ring

theorem form_YY : form centeredY centeredY = (h : ℂ) := by
  have he : form (FiniteThreeLevelPositiveHistory.Y 0 1)
      (FiniteThreeLevelPositiveHistory.Y 0 1) = (Real.sqrt 6 / 3 : ℂ) := by
    simpa [FiniteThreeLevelPositiveHistory.modeMatrix, FiniteThreeLevelPositiveHistory.modeNorm]
      using FiniteThreeLevelPositiveHistory.modeMatrix_form 3 3
  rw [centeredY, FiniteThreeLevelPositiveHistory.form_smul, he]
  norm_num [h]
  ring

theorem form_DH : form centeredD centeredH = 0 := by
  rw [centeredD_mode, centeredH_mode, FiniteThreeLevelPositiveHistory.form_smul,
    FiniteThreeLevelPositiveHistory.modeMatrix_form]
  norm_num [Fin.ext_iff]

theorem form_DY : form centeredD centeredY = 0 := by
  rw [centeredD_mode, centeredY_mode, FiniteThreeLevelPositiveHistory.form_smul,
    FiniteThreeLevelPositiveHistory.modeMatrix_form]
  norm_num [Fin.ext_iff]

theorem form_HY : form centeredH centeredY = 0 := by
  rw [centeredH_mode, centeredY_mode, FiniteThreeLevelPositiveHistory.form_smul,
    FiniteThreeLevelPositiveHistory.modeMatrix_form]
  norm_num [Fin.ext_iff]

theorem mean_D : mean centeredD = 0 := by
  rw [centeredD_mode]
  change FiniteThreeLevelHistoryTransfer.meanLinear ((1/60 : ℂ) •
    FiniteThreeLevelPositiveHistory.modeMatrix 1) = 0
  rw [map_smul]
  change (1/60 : ℂ) * _ = 0
  change _ * (FiniteThreeLevelPositiveHistory.rhoN * FiniteThreeLevelPositiveHistory.modeMatrix _).trace = 0
  rw [FiniteThreeLevelPositiveHistory.mode_mean_zero, mul_zero]

theorem mean_H : mean centeredH = 0 := by
  rw [centeredH_mode]
  change FiniteThreeLevelHistoryTransfer.meanLinear ((1/10 : ℂ) •
    FiniteThreeLevelPositiveHistory.modeMatrix 2) = 0
  rw [map_smul]
  change (1/10 : ℂ) * _ = 0
  change _ * (FiniteThreeLevelPositiveHistory.rhoN * FiniteThreeLevelPositiveHistory.modeMatrix _).trace = 0
  rw [FiniteThreeLevelPositiveHistory.mode_mean_zero, mul_zero]

theorem mean_Y : mean centeredY = 0 := by
  rw [centeredY_mode]
  change FiniteThreeLevelHistoryTransfer.meanLinear ((1/10 : ℂ) •
    FiniteThreeLevelPositiveHistory.modeMatrix 3) = 0
  rw [map_smul]
  change (1/10 : ℂ) * _ = 0
  change _ * (FiniteThreeLevelPositiveHistory.rhoN * FiniteThreeLevelPositiveHistory.modeMatrix _).trace = 0
  rw [FiniteThreeLevelPositiveHistory.mode_mean_zero, mul_zero]

theorem mean_F : mean centeredF = 0 := by
  rw [centered_decomposition]
  change FiniteThreeLevelHistoryTransfer.meanLinear (centeredD + centeredH) = 0
  rw [map_add]
  change mean centeredD + mean centeredH = 0
  rw [mean_D, mean_H, add_zero]

theorem binary_mean : mean binaryEffect = 1/12 := by
  have h := mean_F
  change FiniteThreeLevelHistoryTransfer.meanLinear
    (binaryEffect - (1/12 : ℂ) • 1) = 0 at h
  rw [map_sub, map_smul] at h
  change mean binaryEffect - (1/12 : ℂ) * mean 1 = 0 at h
  rw [FiniteThreeLevelHistoryTransfer.mean_one, mul_one] at h
  exact sub_eq_zero.mp h

theorem form_IF : form 1 centeredF = 0 := by rw [form_one_left, mean_F]

theorem form_FF : form centeredF centeredF = (N : ℂ) := by
  have hd : form centeredH centeredD = 0 := by
    rw [← FiniteThreeLevelHistoryTransfer.form_conj, form_DH, star_zero]
  have ha (A B C : MatQ) : form (A+B) C = form A C + form B C := by
    simp [form, Matrix.conjTranspose_add, mul_add, add_mul, Matrix.trace_add]
  rw [centered_decomposition, ha,
    FiniteThreeLevelHistoryTransfer.form_add_right,
    FiniteThreeLevelHistoryTransfer.form_add_right, form_DD, form_DH, hd, form_HH]
  simp [N]

theorem d_pos : 0 < d := by norm_num [d]
theorem h_pos : 0 < h := by unfold h; positivity
theorem N_pos : 0 < N := add_pos d_pos h_pos
theorem d_lt_h : d < h := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have hp := Real.sqrt_nonneg (6 : ℝ)
  dsimp [d, h]
  nlinarith

theorem alpha_pos : 0 < alpha := div_pos d_pos N_pos
theorem alpha_lt_half : alpha < 1/2 := by
  rw [alpha, div_lt_iff₀ N_pos]
  dsimp [N]
  linarith [d_lt_h]

theorem alpha_formula : alpha = 5 / (5 + 12 * Real.sqrt 6) := by
  unfold alpha N d h
  have hs := Real.sqrt_nonneg (6 : ℝ)
  have hn : (5 + 12 * Real.sqrt 6) ≠ 0 := by positivity
  have hd : (1/720 + Real.sqrt 6 / 300 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem centeredF_ne_zero : centeredF ≠ 0 := by
  intro he
  have hf := form_FF
  rw [he] at hf
  have hz : (N : ℂ) = 0 := by simpa [form] using hf.symm
  exact (ne_of_gt N_pos) (Complex.ofReal_eq_zero.mp hz)

theorem form_FI : form centeredF 1 = 0 := by
  rw [← FiniteThreeLevelHistoryTransfer.form_conj, form_IF, star_zero]

theorem form_add_left (A B C : MatQ) : form (A+B) C = form A C + form B C := by
  simp [form, Matrix.conjTranspose_add, mul_add, add_mul, Matrix.trace_add]

theorem form_smul_left (a : ℂ) (A B : MatQ) : form (a • A) B = star a * form A B := by
  simpa using FiniteThreeLevelPositiveHistory.form_smul a 1 A B

theorem centeredF_mem (p : ℝ) (hp : 0 < p) : centeredF ∈ accessible binaryTree p := by
  rw [binary_accessible p hp]
  exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem binary_span_coordinates {A : MatQ} (hA : A ∈ binarySpan) :
    ∃ a b : ℂ, A = a • (1 : MatQ) + b • centeredF := by
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp hA
  refine ⟨a+b/12,b,?_⟩
  rw [← hab, centeredF]
  module

theorem projection_binary (p : ℝ) (hp : 0 < p) (A : MatQ) :
    projection binaryTree p A = mean A • 1 + (form centeredF A / (N : ℂ)) • centeredF := by
  have hP := projection_mem binaryTree p A
  rw [binary_accessible p hp] at hP
  obtain ⟨a,b,hab⟩ := binary_span_coordinates hP
  have hm := projection_mean binaryTree p A
  rw [hab] at hm
  change FiniteThreeLevelHistoryTransfer.meanLinear (a • 1 + b • centeredF) = mean A at hm
  simp only [map_add, map_smul] at hm
  change a * mean 1 + b * mean centeredF = mean A at hm
  rw [FiniteThreeLevelHistoryTransfer.mean_one, mean_F, mul_one, mul_zero, add_zero] at hm
  have hf := form_projection_right binaryTree p (centeredF_mem p hp) A
  rw [hab, FiniteThreeLevelHistoryTransfer.form_add_right,
    FiniteThreeLevelHistoryTransfer.form_smul_right,
    FiniteThreeLevelHistoryTransfer.form_smul_right, form_FI, form_FF,
    mul_zero, zero_add] at hf
  have hn : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt N_pos)
  have hb : b = form centeredF A / (N : ℂ) := (eq_div_iff hn).mpr hf
  rw [hab, hm, hb]

theorem rotate_D (t : ℝ) : rotate leakingFrequencies t centeredD = centeredD :=
  FiniteThreeLevelHistoryTransfer.rotate_diagonal _ _ _

theorem rotate_H (t : ℝ) :
    rotate leakingFrequencies t centeredH =
      (Real.cos (Real.pi*t/2) : ℂ) • centeredH +
      (Real.sin (Real.pi*t/2) : ℂ) • centeredY := by
  have he := FiniteThreeLevelHistoryTransfer.observable_X 1 leakingFrequencies t
    (by decide : (0 : Q) ≠ 1)
  simp only [FiniteThreeLevelPositiveHistory.Psi_one, Complex.ofReal_one, one_smul] at he
  have ha : FiniteThreeLevelHistoryTransfer.angle leakingFrequencies t 0 1 = Real.pi*t/2 := by
    simp [FiniteThreeLevelHistoryTransfer.angle, leakingFrequencies]
    ring
  rw [ha] at he
  rw [centeredH, map_smul, he, centeredY]
  module

theorem rotate_Y (t : ℝ) :
    rotate leakingFrequencies t centeredY =
      -(Real.sin (Real.pi*t/2) : ℂ) • centeredH +
      (Real.cos (Real.pi*t/2) : ℂ) • centeredY := by
  have he := FiniteThreeLevelHistoryTransfer.observable_Y 1 leakingFrequencies t
    (by decide : (0 : Q) ≠ 1)
  simp only [FiniteThreeLevelPositiveHistory.Psi_one, Complex.ofReal_one, one_smul] at he
  have ha : FiniteThreeLevelHistoryTransfer.angle leakingFrequencies t 0 1 = Real.pi*t/2 := by
    simp [FiniteThreeLevelHistoryTransfer.angle, leakingFrequencies]
    ring
  rw [ha] at he
  rw [centeredY, map_smul, he, centeredH]
  module

theorem rotate_F (t : ℝ) :
    rotate leakingFrequencies t centeredF =
      centeredD + (Real.cos (Real.pi*t/2) : ℂ) • centeredH +
        (Real.sin (Real.pi*t/2) : ℂ) • centeredY := by
  rw [centered_decomposition, map_add, rotate_D, rotate_H]
  module

theorem form_FD : form centeredF centeredD = (d : ℂ) := by
  rw [centered_decomposition, form_add_left, form_DD,
    ← FiniteThreeLevelHistoryTransfer.form_conj centeredH centeredD, form_DH, star_zero, add_zero]

theorem form_FH : form centeredF centeredH = (h : ℂ) := by
  rw [centered_decomposition, form_add_left, form_DH, form_HH, zero_add]

theorem form_FY : form centeredF centeredY = 0 := by
  rw [centered_decomposition, form_add_left, form_DY, form_HY, add_zero]

def multiplier (t : ℝ) : ℝ := alpha + (1-alpha)*Real.cos (Real.pi*t/2)

theorem form_F_rotate (t : ℝ) :
    form centeredF (rotate leakingFrequencies t centeredF) = (N * multiplier t : ℝ) := by
  rw [rotate_F, FiniteThreeLevelHistoryTransfer.form_add_right,
    FiniteThreeLevelHistoryTransfer.form_add_right,
    FiniteThreeLevelHistoryTransfer.form_smul_right,
    FiniteThreeLevelHistoryTransfer.form_smul_right, form_FD, form_FH, form_FY]
  have hn := ne_of_gt N_pos
  have he : N * multiplier t = d + h * Real.cos (Real.pi*t/2) := by
    unfold multiplier alpha
    field_simp
    dsimp [N]
    ring
  rw [he]
  push_cast
  ring

theorem projection_rotate_F (p : ℝ) (hp : 0 < p) (t : ℝ) :
    projection binaryTree p (rotate leakingFrequencies t centeredF) =
      (multiplier t : ℂ) • centeredF := by
  rw [projection_binary p hp, FiniteThreeLevelHistoryTransfer.rotate_mean, mean_F,
    zero_smul, zero_add, form_F_rotate]
  have hn : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt N_pos)
  congr 1
  push_cast
  field_simp

theorem multiplier_one : multiplier 1 = alpha := by simp [multiplier]
theorem multiplier_two : multiplier 2 = 2*alpha-1 := by
  have he : Real.pi * 2 / 2 = Real.pi := by ring
  rw [multiplier, he, Real.cos_pi]
  ring

theorem binary_positive_time_defect (p : ℝ) (hp : 0 < p) :
    projection binaryTree p (rotate leakingFrequencies 2 centeredF) -
      projection binaryTree p (rotate leakingFrequencies 1
        (projection binaryTree p (rotate leakingFrequencies 1 centeredF))) =
      (-(1-alpha)^2 : ℂ) • centeredF := by
  rw [projection_rotate_F p hp, projection_rotate_F p hp,
    map_smul, map_smul, projection_rotate_F p hp, multiplier_one, multiplier_two]
  push_cast
  module

def signedCoefficients (p : ℝ) (u : History 2 1) : ℂ :=
  if u.1 = 0 then 11 / (12 * (p : ℂ)) else -1 / (12 * (p : ℂ))

theorem binary_column_zero (p : ℝ) :
    Psi p binaryEffect = (1/12 : ℂ) • 1 + (p : ℂ) • centeredF := by
  change (p : ℂ) • binaryEffect + (1 - (p : ℂ)) • (mean binaryEffect • 1) = _
  rw [binary_mean, centeredF]
  module

theorem binary_column_one (p : ℝ) :
    Psi p (1-binaryEffect) = (11/12 : ℂ) • 1 - (p : ℂ) • centeredF := by
  change FiniteThreeLevelPositiveHistory.PsiLinear p (1-binaryEffect) = _
  rw [map_sub]
  change Psi p 1 - Psi p binaryEffect = _
  rw [FiniteThreeLevelPositiveHistory.Psi_unital, binary_column_zero]
  module

theorem synthesis_signed (p : ℝ) (hp : 0 < p) :
    synthesis binaryTree p (signedCoefficients p) = centeredF := by
  have hpC : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hp)
  change (∑ u : Fin 2 × Unit, signedCoefficients p u • Psi p (effect binaryTree u)) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_two]
  change signedCoefficients p (0,()) • Psi p (effect binaryTree (0,())) +
    signedCoefficients p (1,()) • Psi p (effect binaryTree (1,())) = centeredF
  rw [binary_effect_zero, binary_effect_one, binary_column_zero, binary_column_one]
  simp only [signedCoefficients, show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte]
  have hi : (11 / (12 * (p : ℂ))) * (1/12) + (-1 / (12 * (p : ℂ))) * (11/12) = 0 := by ring
  have hf : (11 / (12 * (p : ℂ))) * (p : ℂ) - (-1 / (12 * (p : ℂ))) * (p : ℂ) = 1 := by
    field_simp
    ring
  rw [smul_add, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
  calc
    _ = (11 / (12 * (p : ℂ)) * (1/12) + -1 / (12 * (p : ℂ)) * (11/12)) • (1 : MatQ) +
      (11 / (12 * (p : ℂ)) * (p : ℂ) - -1 / (12 * (p : ℂ)) * (p : ℂ)) • centeredF := by module
    _ = centeredF := by rw [hi, hf, zero_smul, one_smul, zero_add]

def actualKernel (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    Matrix (History 2 1) (History 2 1) ℂ :=
  insertedKernel binaryTree p (by norm_num) binary_stationary hp hp1
    (FiniteThreeLevelHistoryTransfer.pulseKraus leakingFrequencies t)
    (FiniteThreeLevelHistoryTransfer.pulse_normalized leakingFrequencies t)

/-- Every real pulse is the existing normalized insertion, with no intermediate projection. -/
theorem actual_pairing (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ)
    (f g : History 2 1 → ℂ) :
    FinitePositiveKernel.pairing (actualKernel p hp hp1 t) f g =
      form (synthesis binaryTree p f) (rotate leakingFrequencies t (synthesis binaryTree p g)) := by
  rw [actualKernel, inserted_pairing_form _ _ _ _ _ _ _ _ (by
    intro A
    simp only [FiniteThreeLevelHistoryTransfer.pulse_observable,
      FiniteThreeLevelHistoryTransfer.rotate_Psi]), FiniteThreeLevelHistoryTransfer.pulse_observable]

theorem actual_signed_pairing (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) (t : ℝ) :
    FinitePositiveKernel.pairing (actualKernel p hp hp1 t) (signedCoefficients p) (signedCoefficients p) =
      (N * multiplier t : ℝ) := by
  rw [actual_pairing, synthesis_signed p hpos, form_F_rotate]

theorem actual_signed_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    FinitePositiveKernel.pairing (actualKernel p hp hp1 1) (signedCoefficients p) (signedCoefficients p) =
      (d : ℂ) := by
  rw [actual_signed_pairing p hp hp1 hpos, multiplier_one]
  congr 1
  have hn := ne_of_gt N_pos
  unfold alpha
  field_simp

theorem actual_signed_two (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    FinitePositiveKernel.pairing (actualKernel p hp hp1 2) (signedCoefficients p) (signedCoefficients p) =
      (d-h : ℝ) := by
  rw [actual_signed_pairing p hp hp1 hpos, multiplier_two]
  congr 1
  have hn := ne_of_gt N_pos
  unfold alpha
  field_simp
  dsimp [N]
  ring

theorem actual_signed_two_negative (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    (FinitePositiveKernel.pairing (actualKernel p hp hp1 2)
      (signedCoefficients p) (signedCoefficients p)).re < 0 := by
  rw [actual_signed_two p hp hp1 hpos]
  exact sub_neg.mpr d_lt_h

theorem positive_time_defect_nonzero :
    (-(1-alpha)^2 : ℂ) • centeredF ≠ 0 := by
  apply smul_ne_zero
  · have ha : (1-alpha : ℝ) ≠ 0 := by linarith [alpha_lt_half]
    exact neg_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast ha))
  · exact centeredF_ne_zero

theorem defect_quadratic :
    form centeredF ((-(1-alpha)^2 : ℂ) • centeredF) = (-h^2/N : ℝ) := by
  rw [FiniteThreeLevelHistoryTransfer.form_smul_right, form_FF]
  have hn := ne_of_gt N_pos
  have he : -(1-alpha)^2 * N = -h^2/N := by
    unfold alpha
    field_simp
    dsimp [N]
    ring
  exact_mod_cast he

theorem defect_quadratic_negative :
    (form centeredF ((-(1-alpha)^2 : ℂ) • centeredF)).re < 0 := by
  rw [defect_quadratic]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos h_pos)) N_pos

theorem D2_decomposition :
    FiniteThreeLevelPositiveHistory.D 2 = (1/6 : ℂ) • 1 - (10 : ℂ) • centeredD := by
  change Matrix.single (2 : Fin 3) 2 1 = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.ext_iff, centeredD, Matrix.single]

theorem projection_D2 (p : ℝ) (hp : 0 < p) :
    projection binaryTree p (FiniteThreeLevelPositiveHistory.D 2) =
      (1/6 : ℂ) • 1 - (1/(72*(N : ℂ))) • centeredF := by
  have hm : mean (FiniteThreeLevelPositiveHistory.D 2) = 1/6 := by
    rw [D2_decomposition]
    change FiniteThreeLevelHistoryTransfer.meanLinear ((1/6 : ℂ) • 1 - (10 : ℂ) • centeredD) = _
    rw [map_sub, map_smul, map_smul]
    change (1/6 : ℂ) * mean 1 - 10 * mean centeredD = _
    rw [FiniteThreeLevelHistoryTransfer.mean_one, mean_D]
    ring
  have hf : form centeredF (FiniteThreeLevelPositiveHistory.D 2) = -1/72 := by
    rw [D2_decomposition]
    have hs (A B : MatQ) : form centeredF (A-B) = form centeredF A - form centeredF B := by
      simp [form, sub_mul, Matrix.trace_sub]
    rw [hs, FiniteThreeLevelHistoryTransfer.form_smul_right,
      FiniteThreeLevelHistoryTransfer.form_smul_right, form_FI, form_FD]
    norm_num [d]
  rw [projection_binary p hp, hm, hf]
  module

theorem N_upper : N < 7/720 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have hp := Real.sqrt_nonneg (6 : ℝ)
  dsimp [N, d, h]
  nlinarith

def plusVector : Q → ℂ := ![1,1,0]
def normalizedPlus : Q → ℂ := ((Real.sqrt 2 : ℂ)⁻¹) • plusVector

theorem plus_F : centeredF *ᵥ plusVector = (7/60 : ℂ) • plusVector := by
  rw [centered_decomposition]
  ext i
  fin_cases i <;>
    norm_num [Fin.ext_iff, Matrix.cons_val, Matrix.cons_val_two, centeredD, centeredH, plusVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      FiniteThreeLevelPositiveHistory.X, FiniteThreeLevelPositiveHistory.E, Matrix.single]

theorem plus_norm : star plusVector ⬝ᵥ plusVector = (2 : ℂ) := by
  norm_num [Matrix.cons_val_two, plusVector, dotProduct, Fin.sum_univ_three]

theorem projection_D2_plus (p : ℝ) (hp : 0 < p) :
    star plusVector ⬝ᵥ (projection binaryTree p (FiniteThreeLevelPositiveHistory.D 2) *ᵥ plusVector) =
      1/3 - 7/(2160*(N : ℂ)) := by
  rw [projection_D2 p hp, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, plus_F, smul_smul,
    dotProduct_sub, dotProduct_smul, dotProduct_smul, plus_norm]
  ring

theorem projection_not_positive (p : ℝ) (hp : 0 < p) :
    (FiniteThreeLevelPositiveHistory.D 2).PosSemidef ∧
      ¬ (projection binaryTree p (FiniteThreeLevelPositiveHistory.D 2)).PosSemidef := by
  constructor
  · convert FiniteThreeLevelPositiveHistory.projector_posSemidef 2 using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.ext_iff, Matrix.cons_val, Matrix.cons_val_two, FiniteThreeLevelPositiveHistory.projector, FiniteThreeLevelPositiveHistory.D,
        FiniteThreeLevelPositiveHistory.E, Matrix.single]
  · intro hP
    have hz := hP.dotProduct_mulVec_nonneg plusVector
    rw [projection_D2_plus p hp] at hz
    have hr : (0 : ℝ) ≤ 1/3 - 7/(2160*N) := by
      have he : (1/3 - 7/(2160*(N : ℂ)) : ℂ) = ((1/3 - 7/(2160*N) : ℝ) : ℂ) := by push_cast; rfl
      rw [he] at hz
      exact hz.1
    have hn := N_pos
    have hu := N_upper
    have ht : 1/3 - 7/(2160*N) < 0 := by
      have hden : 0 < 2160*N := by positivity
      have hdiv : 1/3 < 7/(2160*N) := (lt_div_iff₀ hden).mpr (by nlinarith)
      linarith
    linarith

def sampled : MatQ →ₗ[ℂ] MatQ := rotate leakingFrequencies 1
def closureBasis : Fin 4 → MatQ := ![1, centeredD, centeredH, centeredY]
def invariantClosure : Submodule ℂ MatQ := Submodule.span ℂ (Set.range closureBasis)
def hiddenG : MatQ := centeredD - (alpha : ℂ) • centeredF

theorem sampled_I : sampled 1 = 1 := FiniteThreeLevelHistoryTransfer.rotate_one _ _
theorem sampled_D : sampled centeredD = centeredD := rotate_D 1
theorem sampled_H : sampled centeredH = centeredY := by simpa [sampled] using rotate_H 1
theorem sampled_Y : sampled centeredY = -centeredH := by simpa [sampled] using rotate_Y 1

theorem sampled_F : sampled centeredF = centeredD + centeredY := by
  rw [centered_decomposition, map_add, sampled_D, sampled_H]

theorem sampled_twice_F : sampled (sampled centeredF) = centeredD - centeredH := by
  rw [sampled_F, map_add, sampled_D, sampled_Y, sub_eq_add_neg]

theorem closure_basis_mem (i : Fin 4) : closureBasis i ∈ invariantClosure :=
  Submodule.subset_span ⟨i,rfl⟩

theorem closure_I : (1 : MatQ) ∈ invariantClosure := closure_basis_mem 0
theorem closure_D : centeredD ∈ invariantClosure := closure_basis_mem 1
theorem closure_H : centeredH ∈ invariantClosure := closure_basis_mem 2
theorem closure_Y : centeredY ∈ invariantClosure := closure_basis_mem 3

theorem closure_F : centeredF ∈ invariantClosure := by
  rw [centered_decomposition]
  exact invariantClosure.add_mem closure_D closure_H

theorem accessible_le_closure (p : ℝ) (hp : 0 < p) : accessible binaryTree p ≤ invariantClosure := by
  intro A hA
  rw [binary_accessible p hp] at hA
  obtain ⟨a,b,rfl⟩ := binary_span_coordinates hA
  exact invariantClosure.add_mem (invariantClosure.smul_mem _ closure_I)
    (invariantClosure.smul_mem _ closure_F)

theorem closure_preserved_U {A : MatQ} (hA : A ∈ invariantClosure) :
    sampled A ∈ invariantClosure := by
  induction hA using Submodule.span_induction with
  | mem A h =>
    obtain ⟨i,rfl⟩ := h
    fin_cases i
    · exact sampled_I ▸ closure_I
    · exact sampled_D ▸ closure_D
    · exact sampled_H ▸ closure_Y
    · exact sampled_Y ▸ invariantClosure.neg_mem closure_H
  | zero => simp
  | add A B _ _ hA hB => simpa only [map_add] using invariantClosure.add_mem hA hB
  | smul c A _ hA => simpa only [map_smul] using invariantClosure.smul_mem c hA

theorem closure_preserved_P (p : ℝ) (hp : 0 < p) (A : MatQ) :
    projection binaryTree p A ∈ invariantClosure :=
  accessible_le_closure p hp (projection_mem binaryTree p A)

theorem closure_preserved_Q (p : ℝ) (hp : 0 < p) {A : MatQ} (hA : A ∈ invariantClosure) :
    hiddenProjection binaryTree p A ∈ invariantClosure :=
  invariantClosure.sub_mem hA (closure_preserved_P p hp A)

/-- Minimality concerns the invariant closure, not a claim about minimal recurrence order. -/
theorem closure_minimal (p : ℝ) (hp : 0 < p) (W : Submodule ℂ MatQ)
    (hV : accessible binaryTree p ≤ W) (hU : ∀ A ∈ W, sampled A ∈ W) :
    invariantClosure ≤ W := by
  have hI := hV (one_mem_accessible binaryTree p)
  have hF := hV (centeredF_mem p hp)
  have hUF := hU _ hF
  have hUUF := hU _ hUF
  have hD : centeredD ∈ W := by
    have he : (1/2 : ℂ) • (centeredF + sampled (sampled centeredF)) = centeredD := by
      rw [sampled_twice_F, centered_decomposition]
      module
    rw [← he]
    exact W.smul_mem _ (W.add_mem hF hUUF)
  have hH : centeredH ∈ W := by
    have he : centeredF - centeredD = centeredH := by rw [centered_decomposition]; module
    rw [← he]
    exact W.sub_mem hF hD
  have hY : centeredY ∈ W := by
    have he : sampled centeredF - centeredD = centeredY := by rw [sampled_F]; module
    rw [← he]
    exact W.sub_mem hUF hD
  apply Submodule.span_le.mpr
  rintro A ⟨i,rfl⟩
  fin_cases i <;> assumption

theorem closure_coordinates {A : MatQ} (hA : A ∈ invariantClosure) :
    ∃ a b c e : ℂ, A = a • (1 : MatQ) + b • centeredD + c • centeredH + e • centeredY := by
  induction hA using Submodule.span_induction with
  | mem A h =>
    obtain ⟨i,rfl⟩ := h
    fin_cases i
    · exact ⟨1,0,0,0,by simp [closureBasis]⟩
    · exact ⟨0,1,0,0,by simp [closureBasis]⟩
    · exact ⟨0,0,1,0,by simp [closureBasis]⟩
    · exact ⟨0,0,0,1,by simp [closureBasis]⟩
  | zero => exact ⟨0,0,0,0,by simp⟩
  | add A B _ _ hA hB =>
    obtain ⟨a,b,c,e,rfl⟩ := hA
    obtain ⟨a',b',c',e',rfl⟩ := hB
    exact ⟨a+a',b+b',c+c',e+e',by module⟩
  | smul z A _ hA =>
    obtain ⟨a,b,c,e,rfl⟩ := hA
    exact ⟨z*a,z*b,z*c,z*e,by module⟩

theorem closure_coefficients_zero (a b c e : ℂ)
    (he : a • (1 : MatQ) + b • centeredD + c • centeredH + e • centeredY = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  have h00 := congrArg (fun A : MatQ => A 0 0) he
  have h22 := congrArg (fun A : MatQ => A 2 2) he
  have h01 := congrArg (fun A : MatQ => A 0 1) he
  have h10 := congrArg (fun A : MatQ => A 1 0) he
  norm_num [centeredD, centeredH, centeredY, FiniteThreeLevelPositiveHistory.X,
    FiniteThreeLevelPositiveHistory.Y, FiniteThreeLevelPositiveHistory.E, Matrix.single,
    Fin.ext_iff, Matrix.cons_val_two] at h00 h22 h01 h10
  have ha : a = 0 := by linear_combination (5/6 : ℂ)*h00 + (1/6 : ℂ)*h22
  have hb : b = 0 := by linear_combination (10 : ℂ)*h00 - 10*h22
  have hc : c = 0 := by linear_combination (5 : ℂ)*h01 + 5*h10
  have hd : e = 0 := by
    have hei : e * Complex.I = 0 := by
      linear_combination (-5 : ℂ)*h01 + 5*h10
    exact (mul_eq_zero.mp hei).resolve_right Complex.I_ne_zero
  exact ⟨ha,hb,hc,hd⟩

theorem closure_independent : LinearIndependent ℂ closureBasis := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he : c 0 • (1 : MatQ) + c 1 • centeredD + c 2 • centeredH + c 3 • centeredY = 0 := by
    simpa [Fin.sum_univ_succ, closureBasis, add_assoc] using hc
  have hz := closure_coefficients_zero _ _ _ _ he
  fin_cases i <;> tauto

theorem closure_finrank : Module.finrank ℂ invariantClosure = 4 :=
  finrank_span_eq_card closure_independent

theorem sampled_annihilator {A : MatQ} (hA : A ∈ invariantClosure) :
    sampled (sampled (sampled A)) - sampled (sampled A) + sampled A - A = 0 := by
  obtain ⟨a,b,c,e,rfl⟩ := closure_coordinates hA
  simp only [map_add, map_smul, map_neg, sampled_I, sampled_D, sampled_H, sampled_Y]
  module

theorem sampled_four {A : MatQ} (hA : A ∈ invariantClosure) :
    sampled (sampled (sampled (sampled A))) = A := by
  obtain ⟨a,b,c,e,rfl⟩ := closure_coordinates hA
  simp only [map_add, map_smul, map_neg, sampled_I, sampled_D, sampled_H, sampled_Y]
  module

theorem sampled_power_mem {A : MatQ} (hA : A ∈ invariantClosure) (k : ℕ) :
    (sampled ^ k) A ∈ invariantClosure := by
  induction k with
  | zero => simpa using hA
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact closure_preserved_U ih

/-- Uninterrupted ambient powers; repeated compression is a different sequence. -/
theorem visible_order_three (p : ℝ) (hp : 0 < p) (A : MatQ)
    (hA : A ∈ accessible binaryTree p) (k : ℕ) :
    visibleOrbit binaryTree p sampled A (k+3) - visibleOrbit binaryTree p sampled A (k+2) +
      visibleOrbit binaryTree p sampled A (k+1) - visibleOrbit binaryTree p sampled A k = 0 := by
  apply Subtype.ext
  change projection binaryTree p ((sampled ^ (k+3)) A) -
    projection binaryTree p ((sampled ^ (k+2)) A) +
    projection binaryTree p ((sampled ^ (k+1)) A) - projection binaryTree p ((sampled ^ k) A) = 0
  have he := sampled_annihilator (sampled_power_mem (accessible_le_closure p hp hA) k)
  have hP := congrArg (projection binaryTree p) he
  simpa only [show k+3 = (k+2)+1 from rfl, show k+2 = (k+1)+1 from rfl,
    pow_succ', Module.End.mul_apply, map_sub, map_add, map_zero] using hP

theorem visible_four_return (p : ℝ) (hp : 0 < p) (A : MatQ)
    (hA : A ∈ accessible binaryTree p) (k : ℕ) :
    visibleOrbit binaryTree p sampled A (k+4) = visibleOrbit binaryTree p sampled A k := by
  apply Subtype.ext
  change projection binaryTree p ((sampled ^ (k+4)) A) = projection binaryTree p ((sampled ^ k) A)
  have he := sampled_four (sampled_power_mem (accessible_le_closure p hp hA) k)
  have hP := congrArg (projection binaryTree p) he
  simpa only [show k+4 = ((k+1)+1+1)+1 from rfl, pow_succ', Module.End.mul_apply] using hP

theorem projection_F (p : ℝ) (hp : 0 < p) : projection binaryTree p centeredF = centeredF :=
  projection_fixed binaryTree p (centeredF_mem p hp)

theorem projection_D (p : ℝ) (hp : 0 < p) :
    projection binaryTree p centeredD = (alpha : ℂ) • centeredF := by
  rw [projection_binary p hp, mean_D, form_FD, zero_smul, zero_add]
  simp only [alpha, Complex.ofReal_div]

theorem projection_H (p : ℝ) (hp : 0 < p) :
    projection binaryTree p centeredH = (1-alpha : ℂ) • centeredF := by
  have he : centeredH = centeredF - centeredD := by rw [centered_decomposition]; abel
  rw [he, map_sub, projection_F p hp, projection_D p hp]
  module

theorem projection_Y (p : ℝ) (hp : 0 < p) : projection binaryTree p centeredY = 0 := by
  rw [projection_binary p hp, mean_Y, form_FY]
  simp

theorem projection_G (p : ℝ) (hp : 0 < p) : projection binaryTree p hiddenG = 0 := by
  rw [hiddenG, map_sub, map_smul, projection_D p hp, projection_F p hp, sub_self]

theorem closure_G : hiddenG ∈ invariantClosure :=
  invariantClosure.sub_mem closure_D (invariantClosure.smul_mem _ closure_F)

theorem closure_split_coordinates {A : MatQ} (hA : A ∈ invariantClosure) :
    ∃ a b c e : ℂ, A = a • (1 : MatQ) + b • centeredF + c • hiddenG + e • centeredY := by
  obtain ⟨a,b,c,e,rfl⟩ := closure_coordinates hA
  refine ⟨a, (alpha : ℂ)*b+(1-alpha)*c, b-c, e, ?_⟩
  rw [hiddenG, centered_decomposition]
  module

theorem visible_coefficients_zero (a b : ℂ)
    (he : a • (1 : MatQ) + b • centeredF = 0) : a = 0 ∧ b = 0 := by
  have he' : a • (1 : MatQ) + b • centeredD + b • centeredH + (0 : ℂ) • centeredY = 0 := by
    rw [centered_decomposition, smul_add] at he
    simpa only [zero_smul, add_zero, add_assoc] using he
  have hz := closure_coefficients_zero a b b 0 he'
  exact ⟨hz.1,hz.2.1⟩

def restrictedHidden (p : ℝ) : Submodule ℂ MatQ := invariantClosure ⊓ (projection binaryTree p).ker

theorem restricted_hidden_span (p : ℝ) (hp : 0 < p) :
    restrictedHidden p = Submodule.span ℂ {hiddenG, centeredY} := by
  apply le_antisymm
  · intro A hA
    obtain ⟨a,b,c,e,he⟩ := closure_split_coordinates hA.1
    have hz : projection binaryTree p A = 0 := hA.2
    rw [he, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      projection_one, projection_F p hp, projection_G p hp, projection_Y p hp] at hz
    simp only [smul_zero, add_zero] at hz
    obtain ⟨ha,hb⟩ := visible_coefficients_zero a b hz
    simp only [he, ha, hb, zero_smul, zero_add]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact ⟨closure_G, projection_G p hp⟩
    · exact ⟨closure_Y, projection_Y p hp⟩

def hiddenBasis : Fin 2 → MatQ := ![hiddenG, centeredY]

theorem hidden_independent : LinearIndependent ℂ hiddenBasis := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he : (0 : ℂ) • (1 : MatQ) + (c 0 * (1-alpha)) • centeredD +
      (-c 0 * alpha) • centeredH + c 1 • centeredY = 0 := by
    have he' : c 0 • hiddenG + c 1 • centeredY = 0 := by
      simpa [hiddenBasis, Fin.sum_univ_two] using hc
    rw [hiddenG, centered_decomposition] at he'
    convert he' using 1
    module
  have hz := closure_coefficients_zero _ _ _ _ he
  have ha : (1-alpha : ℂ) ≠ 0 := by
    have hr : (1-alpha : ℝ) ≠ 0 := by linarith [alpha_lt_half]
    exact_mod_cast hr
  have h0 : c 0 = 0 := (mul_eq_zero.mp hz.2.1).resolve_right ha
  fin_cases i
  · exact h0
  · exact hz.2.2.2

theorem restricted_hidden_finrank (p : ℝ) (hp : 0 < p) :
    Module.finrank ℂ (restrictedHidden p) = 2 := by
  rw [restricted_hidden_span p hp]
  have hr : Set.range hiddenBasis = {hiddenG, centeredY} := by
    ext A
    simp [hiddenBasis, or_comm]
  rw [← hr]
  exact finrank_span_eq_card hidden_independent

/-- Ambient kernel dimension is separate from the restricted hidden dimension. -/
theorem ambient_hidden_finrank (p : ℝ) (hp : 0 < p) :
    Module.finrank ℂ (projection binaryTree p).ker = 7 := by
  have hr := (projection binaryTree p).finrank_range_add_finrank_ker
  rw [projection_range, binary_accessible p hp, binarySpan_rank] at hr
  have hm : Module.finrank ℂ MatQ = 9 := by
    change Module.finrank ℂ (Matrix (Fin 3) (Fin 3) ℂ) = 9
    simp [Module.finrank_matrix]
  omega

theorem sampled_G : sampled hiddenG =
    (alpha*(1-alpha) : ℂ) • centeredF + (1-alpha : ℂ) • hiddenG -
      (alpha : ℂ) • centeredY := by
  rw [hiddenG, map_sub, map_smul, sampled_D, sampled_F]
  module

theorem sampled_Y_split : sampled centeredY = -(1-alpha : ℂ) • centeredF + hiddenG := by
  rw [sampled_Y, hiddenG, centered_decomposition]
  module

theorem actual_A_I (p : ℝ) : projection binaryTree p (sampled 1) = 1 := by
  rw [sampled_I, projection_one]

theorem actual_A_F (p : ℝ) (hp : 0 < p) :
    projection binaryTree p (sampled centeredF) = (alpha : ℂ) • centeredF := by
  rw [sampled_F, map_add, projection_D p hp, projection_Y p hp, add_zero]

theorem actual_B_G (p : ℝ) (hp : 0 < p) :
    projection binaryTree p (sampled hiddenG) = (alpha*(1-alpha) : ℂ) • centeredF := by
  rw [sampled_G, map_sub, map_add, map_smul, map_smul, map_smul,
    projection_F p hp, projection_G p hp, projection_Y p hp]
  simp

theorem actual_B_Y (p : ℝ) (hp : 0 < p) :
    projection binaryTree p (sampled centeredY) = -(1-alpha : ℂ) • centeredF := by
  rw [sampled_Y, map_neg, projection_H p hp, neg_smul]

theorem actual_C_I (p : ℝ) : hiddenProjection binaryTree p (sampled 1) = 0 := by
  rw [sampled_I]
  exact hidden_fixed_zero binaryTree p (one_mem_accessible binaryTree p)

theorem actual_C_F (p : ℝ) (hp : 0 < p) :
    hiddenProjection binaryTree p (sampled centeredF) = hiddenG + centeredY := by
  change sampled centeredF - projection binaryTree p (sampled centeredF) = _
  rw [actual_A_F p hp, sampled_F, hiddenG]
  module

theorem actual_D_G (p : ℝ) (hp : 0 < p) :
    hiddenProjection binaryTree p (sampled hiddenG) =
      (1-alpha : ℂ) • hiddenG - (alpha : ℂ) • centeredY := by
  change sampled hiddenG - projection binaryTree p (sampled hiddenG) = _
  rw [actual_B_G p hp, sampled_G]
  module

theorem actual_D_Y (p : ℝ) (hp : 0 < p) :
    hiddenProjection binaryTree p (sampled centeredY) = hiddenG := by
  change sampled centeredY - projection binaryTree p (sampled centeredY) = _
  rw [actual_B_Y p hp, sampled_Y_split]
  module

theorem actual_K0_I (p : ℝ) :
    memoryKernel binaryTree p sampled 0 ⟨1,one_mem_accessible binaryTree p⟩ = 0 := by
  apply Subtype.ext
  change projection binaryTree p (sampled (hiddenProjection binaryTree p (sampled 1))) = 0
  rw [actual_C_I, map_zero, map_zero]

theorem actual_K0_F (p : ℝ) (hp : 0 < p) :
    (memoryKernel binaryTree p sampled 0 ⟨centeredF,centeredF_mem p hp⟩ : MatQ) =
      (-(1-alpha)^2 : ℂ) • centeredF := by
  change projection binaryTree p (sampled (hiddenProjection binaryTree p (sampled centeredF))) = _
  rw [actual_C_F p hp, map_add, map_add, actual_B_G p hp, actual_B_Y p hp]
  module

theorem normalizedPlus_dot : star normalizedPlus ⬝ᵥ normalizedPlus = (1 : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  have hc : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by simp
  rw [normalizedPlus, star_smul, dotProduct_smul, smul_dotProduct, plus_norm]
  change (Real.sqrt 2 : ℂ)⁻¹ * (star ((Real.sqrt 2 : ℂ)⁻¹) * 2) = 1
  rw [hc]
  field_simp
  linear_combination -hs

theorem normalizedPlus_F : centeredF *ᵥ normalizedPlus = (7/60 : ℂ) • normalizedPlus := by
  rw [normalizedPlus, Matrix.mulVec_smul, plus_F]
  module

theorem projection_D2_normalizedPlus (p : ℝ) (hp : 0 < p) :
    star normalizedPlus ⬝ᵥ (projection binaryTree p (FiniteThreeLevelPositiveHistory.D 2) *ᵥ normalizedPlus) =
      1/6 - 7/(4320*(N : ℂ)) := by
  rw [projection_D2 p hp, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, normalizedPlus_F, smul_smul,
    dotProduct_sub, dotProduct_smul, dotProduct_smul, normalizedPlus_dot]
  ring

theorem normalized_expectation_negative : (1/6 : ℝ) - 7/(4320*N) < 0 := by
  have hden : 0 < 4320*N := mul_pos (by norm_num) N_pos
  have hdiv : (1/6 : ℝ) < 7/(4320*N) := (lt_div_iff₀ hden).mpr (by nlinarith [N_upper])
  linarith

theorem signed_coefficient_negative (p : ℝ) (hp : 0 < p) :
    (signedCoefficients p (1,())).re < 0 := by
  have he : signedCoefficients p (1,()) = ((-1/(12*p) : ℝ) : ℂ) := by
    simp [signedCoefficients]
  rw [he]
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem signed_not_probability (p : ℝ) (hp : 0 < p) :
    ¬ (∀ u, 0 ≤ (signedCoefficients p u).re) := by
  intro h
  exact (not_le_of_gt (signed_coefficient_negative p hp)) (h (1,()))

/-- Natural samples of the same uninterrupted phase, on every complex observable. -/
theorem sampled_power_rotate (k : ℕ) : sampled ^ k = rotate leakingFrequencies (k : ℝ) := by
  induction k with
  | zero =>
    apply LinearMap.ext
    intro A
    simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, FiniteThreeLevelHistoryTransfer.rotate_zero]
  | succ k ih =>
    rw [pow_succ, ih]
    apply LinearMap.ext
    intro A
    change rotate leakingFrequencies (k : ℝ) (rotate leakingFrequencies 1 A) = _
    simpa only [Nat.cast_add, Nat.cast_one] using
      FiniteThreeLevelHistoryTransfer.rotate_group leakingFrequencies (k : ℝ) 1 A

theorem visible_initial_zero (p : ℝ) (A : accessible binaryTree p) :
    visibleOrbit binaryTree p sampled A 0 = A := by
  apply Subtype.ext
  exact projection_fixed binaryTree p A.property

theorem visible_coordinates (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (z : Reconstructed binaryTree (by norm_num) binary_stationary p hp hp1) (k : ℕ) :
    (visibleOrbit binaryTree p sampled (coordinates binaryTree (by norm_num) binary_stationary p hp hp1 z) k : MatQ) =
      coordinates binaryTree (by norm_num) binary_stationary p hp hp1
        (compressedPhase binaryTree p (by norm_num) binary_stationary hp hp1 leakingFrequencies (k : ℝ) z) := by
  change projection binaryTree p ((sampled ^ k) _) =
    coordinates binaryTree (by norm_num) binary_stationary p hp hp1
      (compression binaryTree p (by norm_num) binary_stationary hp hp1 (rotate leakingFrequencies (k : ℝ)) z)
  rw [coordinates_compression, sampled_power_rotate]

theorem quotient_initial_values (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (z : Reconstructed binaryTree (by norm_num) binary_stationary p hp hp1) :
    (visibleOrbit binaryTree p sampled (coordinates binaryTree (by norm_num) binary_stationary p hp hp1 z) 0 : MatQ) =
      coordinates binaryTree (by norm_num) binary_stationary p hp hp1 z ∧
    (visibleOrbit binaryTree p sampled (coordinates binaryTree (by norm_num) binary_stationary p hp hp1 z) 1 : MatQ) =
      coordinates binaryTree (by norm_num) binary_stationary p hp hp1
        (compressedPhase binaryTree p (by norm_num) binary_stationary hp hp1 leakingFrequencies 1 z) ∧
    (visibleOrbit binaryTree p sampled (coordinates binaryTree (by norm_num) binary_stationary p hp hp1 z) 2 : MatQ) =
      coordinates binaryTree (by norm_num) binary_stationary p hp hp1
        (compressedPhase binaryTree p (by norm_num) binary_stationary hp hp1 leakingFrequencies 2 z) := by
  constructor
  · change projection binaryTree p ((sampled ^ 0) _) = _
    rw [pow_zero, Module.End.one_apply]
    exact projection_fixed binaryTree p (coordinates_mem binaryTree p (by norm_num) binary_stationary hp hp1 z)
  constructor
  · simpa only [Nat.cast_one] using visible_coordinates p hp hp1 z 1
  · simpa only [Nat.cast_ofNat] using visible_coordinates p hp hp1 z 2

theorem actual_sampled_pairing (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f g : History 2 1 → ℂ) (k : ℕ) :
    FinitePositiveKernel.pairing (actualKernel p hp hp1 (k : ℝ)) f g =
      form (synthesis binaryTree p f)
        (visibleOrbit binaryTree p sampled (synthesis binaryTree p g) k) := by
  rw [actual_pairing]
  change form _ (rotate leakingFrequencies (k : ℝ) _) = form _ (projection binaryTree p ((sampled ^ k) _))
  rw [sampled_power_rotate, form_projection_right binaryTree p]
  rw [← synthesis_range]
  exact ⟨f,rfl⟩

theorem uninterrupted_centered_sequence (p : ℝ) (hp : 0 < p) (k : ℕ) :
    (visibleOrbit binaryTree p sampled centeredF k : MatQ) =
      (alpha+(1-alpha)*Real.cos ((k : ℝ)*Real.pi/2) : ℂ) • centeredF := by
  change projection binaryTree p ((sampled ^ k) centeredF) = _
  rw [sampled_power_rotate, projection_rotate_F p hp]
  simp only [multiplier, mul_comm Real.pi, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem repeated_compression_centered (p : ℝ) (hp : 0 < p) (k : ℕ) :
    (((projection binaryTree p).comp sampled)^k) centeredF = (alpha^k : ℂ) • centeredF := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul]
    change (alpha^k : ℂ) • projection binaryTree p (sampled centeredF) = _
    rw [actual_A_F p hp, smul_smul, pow_succ]

theorem repeated_compression_discrepancy (p : ℝ) (hp : 0 < p) :
    (visibleOrbit binaryTree p sampled centeredF 2 : MatQ) ≠
      (((projection binaryTree p).comp sampled)^2) centeredF := by
  intro he
  apply positive_time_defect_nonzero
  rw [← binary_positive_time_defect p hp]
  apply sub_eq_zero.mpr
  have hs : (sampled ^ 2) = rotate leakingFrequencies 2 := sampled_power_rotate 2
  change projection binaryTree p ((sampled ^ 2) centeredF) = _ at he
  rw [hs] at he
  exact he

open FiniteThreeLevelStationaryStrategyExamples

theorem computational_projection (p : ℝ) (hp : 0 < p) (A : MatQ) :
    projection computationalTree p A = Matrix.diagonal A.diag := by
  apply projection_eq_of_pairings
  · rw [computational_range p hp]
    exact ⟨A.diag,rfl⟩
  · intro C hC
    rw [computational_range p hp] at hC
    obtain ⟨c,rfl⟩ := hC
    change form (Matrix.diagonal c) (Matrix.diagonal A.diag) = form (Matrix.diagonal c) A
    simp [FiniteThreeLevelPositiveHistory.form_entries, Matrix.diagonal_apply, Matrix.diag, apply_ite]

theorem computational_compression_identity (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : Q → ℝ) (t : ℝ) :
    compression computationalTree p (Nat.zero_lt_succ 2) computational_stationary hp hp1 (rotate ω t) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply coordinates_injective computationalTree (by norm_num) computational_stationary p hp hp1
  rw [coordinates_compression, computational_phase_fixed_all p hp ω t _
    (coordinates_mem computationalTree p (by norm_num) computational_stationary hp hp1 z)]
  exact projection_fixed computationalTree p (coordinates_mem _ _ _ _ _ _ z)

theorem computational_compression_defect_zero (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : Q → ℝ) (t s : ℝ) :
    compression computationalTree p (Nat.zero_lt_succ 2) computational_stationary hp hp1 (rotate ω (t+s)) -
      (compression computationalTree p (Nat.zero_lt_succ 2) computational_stationary hp hp1 (rotate ω t)).comp
        (compression computationalTree p (Nat.zero_lt_succ 2) computational_stationary hp hp1 (rotate ω s)) = 0 := by
  rw [computational_compression_identity, computational_compression_identity, computational_compression_identity]
  simp

theorem done_compression_identity (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (O : MatQ →ₗ[ℂ] MatQ) (hO : O 1 = 1) :
    compression (Tree.done : Tree Q Unit 1 0) p (Nat.zero_lt_succ 0) done_stationary hp hp1 O = LinearMap.id :=
  compression_scalar _ p _ done_stationary hp hp1 (done_scalar_range p hp hp1) O hO

theorem done_compression_defect_zero (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (U V : MatQ →ₗ[ℂ] MatQ) (hU : U 1 = 1) (hV : V 1 = 1) :
    compression (Tree.done : Tree Q Unit 1 0) p (Nat.zero_lt_succ 0) done_stationary hp hp1 (U.comp V) -
      (compression (Tree.done : Tree Q Unit 1 0) p (Nat.zero_lt_succ 0) done_stationary hp hp1 U).comp
        (compression (Tree.done : Tree Q Unit 1 0) p (Nat.zero_lt_succ 0) done_stationary hp hp1 V) = 0 := by
  rw [compression_scalar_comp _ p _ done_stationary hp hp1 (done_scalar_range p hp hp1) U V hU hV, sub_self]

theorem normalizedPlus_norm_one :
    ‖(WithLp.toLp 2 normalizedPlus : EuclideanSpace ℂ Q)‖ = 1 := by
  have hh : inner ℂ (WithLp.toLp 2 normalizedPlus : EuclideanSpace ℂ Q)
      (WithLp.toLp 2 normalizedPlus : EuclideanSpace ℂ Q) = 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    exact normalizedPlus_dot
  have hn : ‖(WithLp.toLp 2 normalizedPlus : EuclideanSpace ℂ Q)‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hh]
    rfl
  nlinarith [norm_nonneg (WithLp.toLp 2 normalizedPlus : EuclideanSpace ℂ Q)]

theorem compressed_one_quadratic (p : ℝ) (hp : 0 < p) (a b : ℂ) :
    form (projection binaryTree p (sampled (a • 1 + b • centeredF))) (a • 1 + b • centeredF) =
      ((Complex.normSq a + alpha * N * Complex.normSq b : ℝ) : ℂ) := by
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, actual_A_I, actual_A_F p hp,
    smul_smul, form_add_left]
  simp only [form_smul_left, FiniteThreeLevelHistoryTransfer.form_add_right,
    FiniteThreeLevelHistoryTransfer.form_smul_right, FiniteThreeLevelPositiveHistory.form_one,
    form_IF, form_FI, form_FF, mul_one, mul_zero, zero_add, add_zero]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  ring

theorem compressed_one_positive (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    (compressedPhase binaryTree p (by norm_num) binary_stationary hp hp1 leakingFrequencies 1).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro z
  have hm := coordinates_mem binaryTree p (by norm_num) binary_stationary hp hp1 z
  rw [binary_accessible p hpos] at hm
  obtain ⟨a,b,he⟩ := binary_span_coordinates hm
  have hv : inner ℂ (compressedPhase binaryTree p (by norm_num) binary_stationary hp hp1 leakingFrequencies 1 z) z =
      ((Complex.normSq a + alpha*N*Complex.normSq b : ℝ) : ℂ) := by
    change inner ℂ (compression binaryTree p (by norm_num) binary_stationary hp hp1 (rotate leakingFrequencies 1) z) z = _
    rw [coordinates_inner, coordinates_compression, he]
    exact compressed_one_quadratic p hpos a b
  rw [hv]
  constructor
  · rfl
  · change 0 ≤ Complex.normSq a + alpha*N*Complex.normSq b
    exact add_nonneg (Complex.normSq_nonneg a)
      (mul_nonneg (mul_nonneg (le_of_lt alpha_pos) (le_of_lt N_pos)) (Complex.normSq_nonneg b))

theorem positive_compression_not_invariance (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    (compressedPhase binaryTree p (by norm_num) binary_stationary hp hp1 leakingFrequencies 1).IsPositive ∧
      ¬ Invariant binaryTree p sampled :=
  ⟨compressed_one_positive p hp hp1 hpos, binary_not_invariant p hpos⟩

def visibleVector (p : ℝ) (hp : 0 < p) (a b : ℂ) : accessible binaryTree p :=
  ⟨a • 1 + b • centeredF, (accessible binaryTree p).add_mem
    ((accessible binaryTree p).smul_mem a (one_mem_accessible binaryTree p))
    ((accessible binaryTree p).smul_mem b (centeredF_mem p hp))⟩

def hiddenVector (p : ℝ) (hp : 0 < p) (c e : ℂ) : (projection binaryTree p).ker :=
  ⟨c • hiddenG + e • centeredY, by
    change projection binaryTree p (c • hiddenG + e • centeredY) = 0
    rw [map_add, map_smul, map_smul, projection_G p hp, projection_Y p hp]
    simp⟩

theorem hiddenVector_in_closure (p : ℝ) (hp : 0 < p) (c e : ℂ) :
    (hiddenVector p hp c e : MatQ) ∈ invariantClosure :=
  invariantClosure.add_mem (invariantClosure.smul_mem c closure_G) (invariantClosure.smul_mem e closure_Y)

/-- Matrix columns in the actual visible basis (I,F). -/
theorem blockA_matrix (p : ℝ) (hp : 0 < p) (a b : ℂ) :
    blockA binaryTree p sampled (visibleVector p hp a b) = visibleVector p hp a (alpha*b) := by
  apply Subtype.ext
  change projection binaryTree p (sampled (a • 1 + b • centeredF)) = _
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, actual_A_I, actual_A_F p hp]
  change a • 1 + b • ((alpha : ℂ) • centeredF) = a • 1 + (alpha*b : ℂ) • centeredF
  module

/-- Matrix columns in the restricted hidden basis (G,Y), mapped into (I,F). -/
theorem blockB_matrix (p : ℝ) (hp : 0 < p) (c e : ℂ) :
    blockB binaryTree p sampled (hiddenVector p hp c e) =
      visibleVector p hp 0 (alpha*(1-alpha)*c-(1-alpha)*e) := by
  apply Subtype.ext
  change projection binaryTree p (sampled (c • hiddenG + e • centeredY)) = _
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, actual_B_G p hp, actual_B_Y p hp]
  dsimp [visibleVector]
  module

theorem blockC_matrix (p : ℝ) (hp : 0 < p) (a b : ℂ) :
    blockC binaryTree p sampled (visibleVector p hp a b) = hiddenVector p hp b b := by
  apply Subtype.ext
  change hiddenProjection binaryTree p (sampled (a • 1 + b • centeredF)) = _
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, actual_C_I, actual_C_F p hp]
  dsimp [hiddenVector]
  module

theorem blockD_matrix (p : ℝ) (hp : 0 < p) (c e : ℂ) :
    blockD binaryTree p sampled (hiddenVector p hp c e) = hiddenVector p hp ((1-alpha)*c+e) (-alpha*c) := by
  apply Subtype.ext
  change hiddenProjection binaryTree p (sampled (c • hiddenG + e • centeredY)) = _
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, actual_D_G p hp, actual_D_Y p hp]
  dsimp [hiddenVector]
  module

theorem K0_matrix (p : ℝ) (hp : 0 < p) (a b : ℂ) :
    memoryKernel binaryTree p sampled 0 (visibleVector p hp a b) =
      visibleVector p hp 0 (-(1-alpha)^2*b) := by
  simp only [memoryKernel, LinearMap.comp_apply, pow_zero, Module.End.one_apply,
    blockC_matrix, blockB_matrix]
  congr 1
  ring

theorem closure_hidden_initial (p : ℝ) (hp : 0 < p) (a b c e : ℂ) :
    hidden binaryTree p (a • 1 + b • centeredF + c • hiddenG + e • centeredY) = hiddenVector p hp c e := by
  apply Subtype.ext
  change (a • 1 + b • centeredF + c • hiddenG + e • centeredY) -
    projection binaryTree p (a • 1 + b • centeredF + c • hiddenG + e • centeredY) = _
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    projection_one, projection_F p hp, projection_G p hp, projection_Y p hp]
  dsimp [hiddenVector]
  module

/-- Arbitrary initial hidden coordinates remain in the exact memory term. -/
theorem closure_memory (p : ℝ) (hp : 0 < p) (a b c e : ℂ) (k : ℕ) :
    let x := a • (1 : MatQ) + b • centeredF + c • hiddenG + e • centeredY
    visibleOrbit binaryTree p sampled x (k+1) =
      blockA binaryTree p sampled (visibleOrbit binaryTree p sampled x k) +
      blockB binaryTree p sampled ((blockD binaryTree p sampled ^ k) (hiddenVector p hp c e)) +
      ∑ j ∈ Finset.range k, memoryKernel binaryTree p sampled (k-1-j)
        (visibleOrbit binaryTree p sampled x j) := by
  dsimp only
  rw [visible_memory, closure_hidden_initial p hp]

def formReadout (A : MatQ) : MatQ →ₗ[ℂ] ℂ where
  toFun := form A
  map_add' := FiniteThreeLevelHistoryTransfer.form_add_right A
  map_smul' c B := FiniteThreeLevelHistoryTransfer.form_smul_right A B c

theorem synthesis_mem (p : ℝ) (f : History 2 1 → ℂ) : synthesis binaryTree p f ∈ accessible binaryTree p := by
  rw [← synthesis_range]
  exact ⟨f,rfl⟩

/-- These probabilities use one central reset, one uninterrupted pulse, and endpoint readout. -/
theorem actual_history_order_three (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (f g : History 2 1 → ℂ) (k : ℕ) :
    FinitePositiveKernel.pairing (actualKernel p hp hp1 ((k+3 : ℕ) : ℝ)) f g -
      FinitePositiveKernel.pairing (actualKernel p hp hp1 ((k+2 : ℕ) : ℝ)) f g +
      FinitePositiveKernel.pairing (actualKernel p hp hp1 ((k+1 : ℕ) : ℝ)) f g -
      FinitePositiveKernel.pairing (actualKernel p hp hp1 (k : ℝ)) f g = 0 := by
  simp only [actual_sampled_pairing]
  have he := visible_order_three p hpos (synthesis binaryTree p g) (synthesis_mem p g) k
  have hf := congrArg ((formReadout (synthesis binaryTree p f)).comp (accessible binaryTree p).subtype) he
  simp only [map_sub, map_add, map_zero] at hf
  simpa only [LinearMap.comp_apply, formReadout, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.subtype_apply] using hf

theorem actual_history_four_return (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (f g : History 2 1 → ℂ) (k : ℕ) :
    FinitePositiveKernel.pairing (actualKernel p hp hp1 ((k+4 : ℕ) : ℝ)) f g =
      FinitePositiveKernel.pairing (actualKernel p hp hp1 (k : ℝ)) f g := by
  rw [actual_sampled_pairing, actual_sampled_pairing,
    visible_four_return p hpos _ (synthesis_mem p g)]

theorem actual_centered_sequence (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) (k : ℕ) :
    FinitePositiveKernel.pairing (actualKernel p hp hp1 (k : ℝ))
      (signedCoefficients p) (signedCoefficients p) =
      ((N*(alpha+(1-alpha)*Real.cos ((k : ℝ)*Real.pi/2)) : ℝ) : ℂ) := by
  rw [actual_signed_pairing p hp hp1 hpos]
  simp only [multiplier, mul_comm Real.pi]

def centeredQuotient (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Reconstructed binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1 :=
  FinitePositiveKernel.mk _ _ (signedCoefficients p)

theorem coordinates_centeredQuotient (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    coordinates binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1 (centeredQuotient p hp hp1) = centeredF := by
  rw [centeredQuotient, coordinates_mk, synthesis_signed p hpos]

theorem compressed_centeredQuotient (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) (t : ℝ) :
    compression binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 (rotate leakingFrequencies t)
      (centeredQuotient p hp hp1) = (multiplier t : ℂ) • centeredQuotient p hp hp1 := by
  apply coordinates_injective binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1
  rw [coordinates_compression, map_smul, coordinates_centeredQuotient p hp hp1 hpos,
    projection_rotate_F p hpos]

theorem repeated_quotient_centered (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) (k : ℕ) :
    ((compression binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 (rotate leakingFrequencies 1))^k)
      (centeredQuotient p hp hp1) = (alpha^k : ℂ) • centeredQuotient p hp hp1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul,
      compressed_centeredQuotient p hp hp1 hpos, multiplier_one, smul_smul, pow_succ]

theorem quotient_not_semigroup (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    compression binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 (rotate leakingFrequencies 2) ≠
      (compression binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 (rotate leakingFrequencies 1)).comp
        (compression binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 (rotate leakingFrequencies 1)) := by
  intro he
  have hz := congrArg (fun M => coordinates binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1
    (M (centeredQuotient p hp hp1))) he
  simp only [LinearMap.comp_apply, coordinates_compression, coordinates_centeredQuotient p hp hp1 hpos] at hz
  apply positive_time_defect_nonzero
  rw [← binary_positive_time_defect p hpos, hz, sub_self]

open FiniteAdaptiveKrausRealization
open FiniteThreeLevelPositiveHistory (rhoN Phi)
open FiniteThreeLevelHistoryTransfer (pulseKraus pulse_normalized)

/-- The existing normalized chronological tree, with every padded history retained. -/
def actualTree (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :=
  insertedTree binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1
    (pulseKraus leakingFrequencies t) (pulse_normalized leakingFrequencies t)

theorem actual_run (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ)
    (u v : History 2 1) (X : MatQ) :
    unJoint (run Q Unit _ (actualTree p hp hp1 t) (pairedHistory u v) (joint X)) =
      branch binaryTree v (rotate leakingFrequencies (-t) (Phi (p*p) (reverseBranch binaryTree u X))) := by
  rw [actualTree, inserted_run, FiniteThreeLevelHistoryTransfer.pulse_state]

theorem actual_invalid_zero (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ)
    (v : History (pairedArity 2 1) 3)
    (hv : v ∉ Set.range (fun uv : History 2 1 × History 2 1 => pairedHistory uv.1 uv.2))
    (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    run Q Unit _ (actualTree p hp hp1 t) v X = 0 :=
  inserted_invalid_zero _ _ _ _ _ _ _ _ v hv X

theorem actual_encoded_sum (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ)
    (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    (∑ uv : History 2 1 × History 2 1, run Q Unit _ (actualTree p hp hp1 t) (pairedHistory uv.1 uv.2) X) =
      ∑ v, run Q Unit _ (actualTree p hp hp1 t) v X :=
  inserted_encoded_sum _ _ _ _ _ _ _ _ X

theorem actual_probabilities (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    (∀ v, 0 ≤ weight Q Unit _ (actualTree p hp hp1 t) v (joint rhoN)) ∧
      (∑ v, weight Q Unit _ (actualTree p hp hp1 t) v (joint rhoN)) = 1 :=
  inserted_probabilities _ _ _ _ _ _ _ _

theorem actual_kernel_normalized (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    (∀ u v, 0 ≤ (actualKernel p hp hp1 t u v).re) ∧
      (∑ u, ∑ v, actualKernel p hp hp1 t u v) = 1 :=
  ⟨insertedKernel_nonnegative _ _ _ _ _ _ _ _, insertedKernel_normalized _ _ _ _ _ _ _ _⟩

theorem actual_row_marginal (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) (u : History 2 1) :
    (∑ v, actualKernel p hp hp1 t u v) = (mass binaryTree u : ℂ) :=
  insertedKernel_row_sum _ _ _ _ _ _ _ _ u

theorem pulse_stationary (t : ℝ) : krausMap (pulseKraus leakingFrequencies t) rhoN = rhoN := by
  rw [FiniteThreeLevelHistoryTransfer.pulse_state]
  exact FiniteThreeLevelHistoryTransfer.rotate_diagonal _ _ _

/-- This column marginal discharges stationarity, separately from normalization. -/
theorem actual_column_marginal (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) (v : History 2 1) :
    (∑ u, actualKernel p hp hp1 t u v) = (mass binaryTree v : ℂ) :=
  insertedKernel_column_sum _ _ _ _ _ _ _ _ (pulse_stationary t) v

theorem actual_quotient_pairing (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ)
    (f g : History 2 1 → ℂ) :
    FinitePositiveKernel.pairing (actualKernel p hp hp1 t) f g =
      inner ℂ (FinitePositiveKernel.mk (kernel binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1)
        (kernel_posSemidef binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1) f)
        (compression binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 (rotate leakingFrequencies t)
          (FinitePositiveKernel.mk (kernel binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1)
            (kernel_posSemidef binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1) g)) := by
  rw [actual_pairing, coordinates_inner, coordinates_compression, coordinates_mk, coordinates_mk,
    form_projection_right binaryTree p (synthesis_mem p f)]

theorem compressed_constant (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    compression binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 (rotate leakingFrequencies t)
      (FinitePositiveKernel.mk (kernel binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1)
        (kernel_posSemidef binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1) (fun _ => 1)) =
      FinitePositiveKernel.mk (kernel binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1)
        (kernel_posSemidef binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1) (fun _ => 1) := by
  apply coordinates_injective binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1
  rw [coordinates_compression, coordinates_mk, synthesis_constant,
    FiniteThreeLevelHistoryTransfer.rotate_one, projection_one]

theorem quotient_order_three (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (z : Reconstructed binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1) (k : ℕ) :
    compressedPhase binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 leakingFrequencies ((k+3 : ℕ) : ℝ) z -
      compressedPhase binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 leakingFrequencies ((k+2 : ℕ) : ℝ) z +
      compressedPhase binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 leakingFrequencies ((k+1 : ℕ) : ℝ) z -
      compressedPhase binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 leakingFrequencies (k : ℝ) z = 0 := by
  apply coordinates_injective binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1
  simp only [map_sub, map_add, map_zero, ← visible_coordinates]
  exact congrArg Subtype.val (visible_order_three p hpos _
    (coordinates_mem binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 z) k)

theorem quotient_four_return (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p)
    (z : Reconstructed binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1) (k : ℕ) :
    compressedPhase binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 leakingFrequencies ((k+4 : ℕ) : ℝ) z =
      compressedPhase binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 leakingFrequencies (k : ℝ) z := by
  apply coordinates_injective binaryTree (Nat.zero_lt_succ 1) binary_stationary p hp hp1
  rw [← visible_coordinates, ← visible_coordinates,
    visible_four_return p hpos _ (coordinates_mem binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 z)]

theorem adaptive_full_projection {k : ℕ} (U : Fin 15 → Tree Q Unit 15 k)
    (p : ℝ) (hp : 0 < p) : projection (adaptiveFamily U) p = LinearMap.id := by
  apply projection_full
  rw [range_positive_eq_effect_span _ _ hp, adaptiveFamily_full_span]

theorem positive_compression_not_semigroup (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpos : 0 < p) :
    (compressedPhase binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 leakingFrequencies 1).IsPositive ∧
    compression binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 (rotate leakingFrequencies 2) ≠
      (compression binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 (rotate leakingFrequencies 1)).comp
        (compression binaryTree p (Nat.zero_lt_succ 1) binary_stationary hp hp1 (rotate leakingFrequencies 1)) :=
  ⟨compressed_one_positive p hp hp1 hpos, quotient_not_semigroup p hp hp1 hpos⟩

/-- The actual hidden basis with its restricted, rather than ambient, carrier. -/
def restrictedHiddenVector (p : ℝ) (hp : 0 < p) (c e : ℂ) : restrictedHidden p :=
  ⟨hiddenVector p hp c e, hiddenVector_in_closure p hp c e, (hiddenVector p hp c e).property⟩

def restrictedBlockB (p : ℝ) : restrictedHidden p →ₗ[ℂ] accessible binaryTree p :=
  (retained binaryTree p).comp (sampled.comp (restrictedHidden p).subtype)

def restrictedBlockC (p : ℝ) (hp : 0 < p) : accessible binaryTree p →ₗ[ℂ] restrictedHidden p :=
  ((hiddenProjection binaryTree p).comp (sampled.comp (accessible binaryTree p).subtype)).codRestrict _
    (fun x => ⟨closure_preserved_Q p hp (closure_preserved_U (accessible_le_closure p hp x.property)),
      projection_hidden binaryTree p (sampled x)⟩)

def restrictedBlockD (p : ℝ) (hp : 0 < p) : restrictedHidden p →ₗ[ℂ] restrictedHidden p :=
  ((hiddenProjection binaryTree p).comp (sampled.comp (restrictedHidden p).subtype)).codRestrict _
    (fun x => ⟨closure_preserved_Q p hp (closure_preserved_U x.property.1),
      projection_hidden binaryTree p (sampled x)⟩)

theorem restricted_B_matrix (p : ℝ) (hp : 0 < p) (c e : ℂ) :
    restrictedBlockB p (restrictedHiddenVector p hp c e) =
      visibleVector p hp 0 (alpha*(1-alpha)*c-(1-alpha)*e) :=
  blockB_matrix p hp c e

theorem restricted_C_matrix (p : ℝ) (hp : 0 < p) (a b : ℂ) :
    restrictedBlockC p hp (visibleVector p hp a b) = restrictedHiddenVector p hp b b := by
  apply Subtype.ext
  exact congrArg (fun x : (projection binaryTree p).ker => (x : MatQ)) (blockC_matrix p hp a b)

theorem restricted_D_matrix (p : ℝ) (hp : 0 < p) (c e : ℂ) :
    restrictedBlockD p hp (restrictedHiddenVector p hp c e) =
      restrictedHiddenVector p hp ((1-alpha)*c+e) (-alpha*c) := by
  apply Subtype.ext
  exact congrArg (fun x : (projection binaryTree p).ker => (x : MatQ)) (blockD_matrix p hp c e)

theorem restricted_K0_matrix (p : ℝ) (hp : 0 < p) (a b : ℂ) :
    (restrictedBlockB p).comp (restrictedBlockC p hp) (visibleVector p hp a b) =
      visibleVector p hp 0 (-(1-alpha)^2*b) := by
  rw [LinearMap.comp_apply, restricted_C_matrix, restricted_B_matrix]
  congr 1
  ring

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedStrategyMemoryExamples
