import SKEFTHawking.FiniteGibbsResetSchedule
import SKEFTHawking.QuantumNetwork.FiniteInstrument

/-! An exact occupation readout separates two equal-dose sequences of
thermal resets on a two-level system. -/

noncomputable section

set_option autoImplicit false

namespace SKEFTHawking.FinitePositiveKernel.GibbsReset

open Matrix QuantumNetwork OpenSystems GibbsObservable DiagonalLindblad

def thermalGround (ground i : Fin 2) : ℝ :=
  if i = ground then 0 else Real.log 3

def halfAttenuationThermalSlice (ground : Fin 2) : ResetSlice (Fin 2) :=
  gibbsResetSlice (thermalGround ground) 1 1 (Real.log 2) (by norm_num)
    (Real.log_nonneg (by norm_num))

theorem halfAttenuationThermalSlice_attenuation (ground : Fin 2) :
    (halfAttenuationThermalSlice ground).attenuation = (1/2 : ℂ) := by
  change (Real.exp (-(1*Real.log 2)) : ℂ) = _
  rw [one_mul, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

private theorem boltzmannThermalGap : Real.exp (-(Real.log 3)) = 1/3 := by
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 3)]
  norm_num

private theorem thermalGround_zero_weights :
    gibbsWeights (thermalGround 0) 1 0 = 3/4 := by
  have h := gibbsWeights_normalized (thermalGround 0) 1
  rw [Fin.sum_univ_two] at h
  simp [gibbsWeights, thermalGround, boltzmannThermalGap] at h ⊢
  linarith

private theorem thermalGround_one_weights :
    gibbsWeights (thermalGround 1) 1 0 = 1/4 := by
  have h := gibbsWeights_normalized (thermalGround 1) 1
  rw [Fin.sum_univ_two] at h
  simp [gibbsWeights, thermalGround, boltzmannThermalGap] at h ⊢
  linarith

/-- Equal-dose Gibbs sequences give distinct first-level occupations on
every input of trace one. The difference is for first cooling level zero
and then level one, minus the reverse order. -/
theorem thermalOrder_firstOccupation (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : X.trace = 1) :
    let s := halfAttenuationThermalSlice 0
    let t := halfAttenuationThermalSlice 1
    resetScheduleDose [s,t] = resetScheduleDose [t,s] ∧
      ((evolveResetSchedule [s,t] X) 0 0).re -
      ((evolveResetSchedule [t,s] X) 0 0).re = -(1/8 : ℝ) := by
  dsimp only
  refine ⟨resetScheduleDose_reversal _ _, ?_⟩
  have h := congrArg (fun Y : Matrix (Fin 2) (Fin 2) ℂ => (Y 0 0).re)
    (evolveResetSchedule_two_slice_reversal (halfAttenuationThermalSlice 0)
      (halfAttenuationThermalSlice 1) X)
  have h0 : (halfAttenuationThermalSlice 0).target 0 0 = (3/4 : ℂ) := by
    change (density (gibbsWeights (thermalGround 0) 1)) 0 0 = _
    simp [density, thermalGround_zero_weights]
  have h1 : (halfAttenuationThermalSlice 1).target 0 0 = (1/4 : ℂ) := by
    change (density (gibbsWeights (thermalGround 1) 1)) 0 0 = _
    simp [density, thermalGround_one_weights]
  change ((evolveResetSchedule [halfAttenuationThermalSlice 0,
      halfAttenuationThermalSlice 1] X - evolveResetSchedule [halfAttenuationThermalSlice 1,
      halfAttenuationThermalSlice 0] X) 0 0).re = _ at h
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hX,
    halfAttenuationThermalSlice_attenuation, h0, h1] at h
  norm_num [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im] at h
  simpa only [Complex.sub_re] using h

/-- The timed slice has a single instrument outcome. The Kraus
alternatives remain internal to that outcome. -/
def ResetSlice.instrument {n : Type*} [Fintype n] [DecidableEq n]
    (s : ResetSlice n) : FiniteInstrument n 1 :=
  .singleton (timeKraus s.weights (Real.exp (-s.rate*s.duration))) s.normalized_kraus

theorem ResetSlice.instrument_branch {n : Type*} [Fintype n] [DecidableEq n]
    (s : ResetSlice n) (X : Matrix n n ℂ) : s.instrument.branch 0 X = s.evolve X := by
  exact (s.evolve_eq_kraus X).symm

/-- Read the first level after two consecutive timed reset instruments. -/
def thermalOrderWeight (s t : ResetSlice (Fin 2)) (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  FiniteInstrument.computational.weight 0 (t.instrument.branch 0 (s.instrument.branch 0 X))

private theorem computational_first_weight (X : Matrix (Fin 2) (Fin 2) ℂ) :
    FiniteInstrument.computational.weight 0 X = (X 0 0).re := by
  simp [FiniteInstrument.weight, FiniteInstrument.branch, FiniteInstrument.computational,
    krausMap, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    FiniteMemoryProcess.basisState]

/-- On density inputs the two chronological experiments give valid first
outcome probabilities, separated by exactly one eighth. -/
theorem thermalOrder_probability (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : IsDensityOperator X) :
    let s := halfAttenuationThermalSlice 0
    let t := halfAttenuationThermalSlice 1
    resetScheduleDose [s,t] = resetScheduleDose [t,s] ∧
      thermalOrderWeight s t X ∈ Set.Icc (0 : ℝ) 1 ∧
      thermalOrderWeight t s X ∈ Set.Icc (0 : ℝ) 1 ∧
      thermalOrderWeight s t X - thermalOrderWeight t s X = -(1/8 : ℝ) := by
  dsimp only
  have hRange (s t : ResetSlice (Fin 2)) : thermalOrderWeight s t X ∈ Set.Icc (0 : ℝ) 1 := by
    have hPos := t.instrument.branch_posSemidef 0 (s.instrument.branch_posSemidef 0 hX.1)
    have hTrace : (t.instrument.branch 0 (s.instrument.branch 0 X)).trace = 1 := by
      rw [s.instrument_branch, t.instrument_branch, t.trace_evolve, s.trace_evolve, hX.2]
    have hUpper := FiniteInstrument.computational.weight_le_trace 0 hPos
    rw [hTrace, Complex.one_re] at hUpper
    exact ⟨FiniteInstrument.computational.weight_nonneg 0 hPos, hUpper⟩
  obtain ⟨hDose,hGap⟩ := thermalOrder_firstOccupation X hX.2
  refine ⟨hDose, hRange _ _, hRange _ _, ?_⟩
  simpa only [thermalOrderWeight, computational_first_weight, ResetSlice.instrument_branch,
    evolveResetSchedule] using hGap

end SKEFTHawking.FinitePositiveKernel.GibbsReset
