import SKEFTHawking.FiniteGibbsResetScheduleReachability
import SKEFTHawking.FiniteGibbsResetScheduleReadout
/-! Sensitivity of a fixed real linear detector to the effective split
of a two-bath reset channel at fixed total doses. -/

namespace SKEFTHawking.FinitePositiveKernel.GibbsReset

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem negExp_sub_bounds_ordered (a r s : ℝ)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ a) :
    Real.exp (-a) * (s - r) ≤ Real.exp (-r) - Real.exp (-s) ∧
    Real.exp (-r) - Real.exp (-s) ≤ s - r := by
  have hLow : s - r ≤ Real.exp (s-r) - 1 := by
    linarith only [Real.add_one_le_exp (s-r)]
  have hHigh : 1 - Real.exp (r-s) ≤ s - r := by
    linarith only [Real.add_one_le_exp (r-s)]
  have hSr : 0 ≤ s-r := sub_nonneg.mpr hrs
  have hLater : Real.exp (-a) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (neg_le_neg hs)
  have hEarlier : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
  have hFrac : 0 ≤ 1 - Real.exp (r-s) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (sub_nonpos.mpr hrs))
  constructor
  · calc
      Real.exp (-a) * (s-r) ≤ Real.exp (-s) * (s-r) :=
        mul_le_mul_of_nonneg_right hLater hSr
      _ ≤ Real.exp (-s) * (Real.exp (s-r) - 1) :=
        mul_le_mul_of_nonneg_left hLow (Real.exp_pos _).le
      _ = _ := by
        rw [mul_sub, ← Real.exp_add, mul_one, show -s + (s-r) = -r by ring]
  · calc
      Real.exp (-r) - Real.exp (-s) = Real.exp (-r) * (1 - Real.exp (r-s)) := by
        rw [mul_sub, ← Real.exp_add, mul_one, show -r + (r-s) = -s by ring]
      _ ≤ 1 - Real.exp (r-s) := mul_le_of_le_one_left hFrac hEarlier
      _ ≤ s-r := hHigh

/-- On every admissible dose interval, attenuation determines the split
with a uniform positive inverse sensitivity. -/
theorem negExp_sub_bounds (a r s : ℝ) (hr : r ∈ Set.Icc 0 a) (hs : s ∈ Set.Icc 0 a) :
    Real.exp (-a) * |r-s| ≤ |Real.exp (-r) - Real.exp (-s)| ∧
    |Real.exp (-r) - Real.exp (-s)| ≤ |r-s| := by
  rcases le_total r s with h | h
  · have hExp : Real.exp (-s) ≤ Real.exp (-r) := Real.exp_le_exp.mpr (neg_le_neg h)
    rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub, abs_of_nonneg (sub_nonneg.mpr hExp)]
    exact negExp_sub_bounds_ordered a r s hr.1 h hs.2
  · have hExp : Real.exp (-r) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (neg_le_neg h)
    rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonpos (sub_nonpos.mpr hExp), neg_sub]
    exact negExp_sub_bounds_ordered a s r hs.1 h hr.2

/-- The effective split of the first bath around a full second-bath
block. The trailing duration may be zero. -/
def threeSliceReset (s t : ResetSlice n) (a b r : ℝ)
    (hb : 0 ≤ b) (hr : r ∈ Set.Icc 0 a) : List (ResetSlice n) :=
  [s.withUnitRateDose (a-r) (sub_nonneg.mpr hr.2),
    t.withUnitRateDose b hb, s.withUnitRateDose r hr.1]

/-- After fixing total doses and a trace-one input, the only
split-dependent readout term is an explicit multiple of exp(-r). -/
theorem threeSliceReset_readout
    (s t : ResetSlice n) (a b r : ℝ) (hb : 0 ≤ b) (hr : r ∈ Set.Icc 0 a)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ) (hTrace : X.trace = 1) :
    L (evolveResetSchedule (threeSliceReset s t a b r hb hr) X) =
      (Real.exp (-a) * Real.exp (-b)) * L X +
      (1 - Real.exp (-a) * Real.exp (-b)) * L s.target +
      (Real.exp (-r) * (1 - Real.exp (-b))) * (L t.target - L s.target) := by
  let tagged : List (Bool × ResetSlice n) :=
    [(false, s.withUnitRateDose (a-r) (sub_nonneg.mpr hr.2)),
     (true, t.withUnitRateDose b hb),
     (false, s.withUnitRateDose r hr.1)]
  have hTagged : ∀ p ∈ tagged, p.2.target = if p.1 then t.target else s.target := by
    intro p hp
    simp only [tagged, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  have hCoeff : twoBathCoefficients tagged =
      (Real.exp (-a), Real.exp (-b), Real.exp (-r) * (1 - Real.exp (-b))) := by
    simp only [tagged, twoBathCoefficients, ResetSlice.withUnitRateDose_dose,
      Bool.false_eq_true, if_false, if_true, mul_one, zero_add]
    rw [← Real.exp_add]
    congr 2
    ring
  have hAction := evolveResetSchedule_eq_twoBathCoefficients tagged _ _ hTagged X
  rw [hCoeff, hTrace] at hAction
  change L (evolveResetSchedule (tagged.map Prod.snd) X) = _
  rw [hAction]
  have hLin (w : ℝ) (Y : Matrix n n ℂ) : L ((w : ℂ) • Y) = w * L Y := by
    change L ((algebraMap ℝ ℂ w) • Y) = w * L Y
    rw [IsScalarTower.algebraMap_smul, map_smul, smul_eq_mul]
  simp only [one_smul, map_add, hLin, map_sub]

/-- A calibrated readout bounds the distance between two admissible
effective splits from both sides on one fixed trace-one input. -/
theorem threeSliceReset_readout_split_bounds
    (s t : ResetSlice n) (a b r r' : ℝ) (hb : 0 ≤ b)
    (hr : r ∈ Set.Icc 0 a) (hr' : r' ∈ Set.Icc 0 a)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ) (hTrace : X.trace = 1) :
    let c := (1 - Real.exp (-b)) * |L t.target - L s.target|
    let y := L (evolveResetSchedule (threeSliceReset s t a b r hb hr) X)
    let y' := L (evolveResetSchedule (threeSliceReset s t a b r' hb hr') X)
    c * (Real.exp (-a) * |r-r'|) ≤ |y-y'| ∧ |y-y'| ≤ c * |r-r'| := by
  let c := (1 - Real.exp (-b)) * |L t.target - L s.target|
  have hb' : 0 ≤ 1 - Real.exp (-b) := sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb))
  have hc : 0 ≤ c := mul_nonneg hb' (abs_nonneg _)
  have hDiff :
      L (evolveResetSchedule (threeSliceReset s t a b r hb hr) X) -
          L (evolveResetSchedule (threeSliceReset s t a b r' hb hr') X) =
        (1 - Real.exp (-b)) * (L t.target - L s.target) * (Real.exp (-r) - Real.exp (-r')) := by
    rw [threeSliceReset_readout s t a b r hb hr L X hTrace,
      threeSliceReset_readout s t a b r' hb hr' L X hTrace]
    ring
  have hAbs :
      |L (evolveResetSchedule (threeSliceReset s t a b r hb hr) X) -
        L (evolveResetSchedule (threeSliceReset s t a b r' hb hr') X)| =
      c * |Real.exp (-r) - Real.exp (-r')| := by
    rw [hDiff, abs_mul, abs_mul, abs_of_nonneg hb']
  obtain ⟨hLow, hHigh⟩ := negExp_sub_bounds a r r' hr hr'
  dsimp only
  rw [hAbs]
  exact ⟨mul_le_mul_of_nonneg_left hLow hc, mul_le_mul_of_nonneg_left hHigh hc⟩

/-- If two effective splits fit one reported datum, their distance is
bounded by the total measurement allowance divided by the calibrated
sensitivity. The initial trace-one input is the same for both fits. -/
theorem threeSliceReset_split_uncertainty
    (s t : ResetSlice n) (a b r r' : ℝ) (hb : 0 < b)
    (hr : r ∈ Set.Icc 0 a) (hr' : r' ∈ Set.Icc 0 a)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ) (hTrace : X.trace = 1)
    (hResolve : L t.target ≠ L s.target) (z ε ε' : ℝ)
    (hObs : |L (evolveResetSchedule (threeSliceReset s t a b r hb.le hr) X) - z| ≤ ε)
    (hObs' : |L (evolveResetSchedule (threeSliceReset s t a b r' hb.le hr') X) - z| ≤ ε') :
    |r-r'| ≤ (ε + ε') /
      ((1 - Real.exp (-b)) * |L t.target - L s.target| * Real.exp (-a)) := by
  let y := L (evolveResetSchedule (threeSliceReset s t a b r hb.le hr) X)
  let y' := L (evolveResetSchedule (threeSliceReset s t a b r' hb.le hr') X)
  have hPath : |y-y'| ≤ ε + ε' := (abs_sub_le y z y').trans
    (add_le_add hObs (by simpa only [abs_sub_comm z y'] using hObs'))
  have hb' : 0 < 1 - Real.exp (-b) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hb))
  have hPos : 0 < (1 - Real.exp (-b)) * |L t.target - L s.target| * Real.exp (-a) :=
    mul_pos (mul_pos hb' (abs_pos.mpr (sub_ne_zero.mpr hResolve))) (Real.exp_pos _)
  have hLow := (threeSliceReset_readout_split_bounds s t a b r r' hb.le hr hr' L X hTrace).1
  apply (le_div_iff₀ hPos).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hLow.trans hPath

private theorem exists_threeSliceReset_of_doses
    (steps : List (Bool × ResetSlice n)) (s t : ResetSlice n) (a b : ℝ) (hb : 0 ≤ b)
    (hA : resetBathDose false steps = a) (hB : resetBathDose true steps = b)
    (hTargets : ∀ p ∈ steps, p.2.target = if p.1 then t.target else s.target) :
    ∃ (r : ℝ) (hr : r ∈ Set.Icc 0 a),
      ∀ Y : Matrix n n ℂ, evolveResetSchedule (steps.map Prod.snd) Y =
        evolveResetSchedule (threeSliceReset s t a b r hb hr) Y := by
  subst a
  subst b
  obtain ⟨r, hr₀, hra, hEq⟩ := exists_equivalent_threeSlice_schedule steps s t hTargets
  exact ⟨r, ⟨hr₀, hra⟩, hEq⟩

/-- For two arbitrary schedules with the same physical bath doses,
observation compatibility bounds the distance between their effective
splits. The reductions describe the entire channel actions. -/
theorem resetSchedules_effective_split_uncertainty
    (steps steps' : List (Bool × ResetSlice n)) (s t : ResetSlice n)
    (a b : ℝ) (hb : 0 < b)
    (hA : resetBathDose false steps = a) (hB : resetBathDose true steps = b)
    (hA' : resetBathDose false steps' = a) (hB' : resetBathDose true steps' = b)
    (hTargets : ∀ p ∈ steps, p.2.target = if p.1 then t.target else s.target)
    (hTargets' : ∀ p ∈ steps', p.2.target = if p.1 then t.target else s.target)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ) (hTrace : X.trace = 1)
    (hResolve : L t.target ≠ L s.target) (z ε ε' : ℝ)
    (hObs : |L (evolveResetSchedule (steps.map Prod.snd) X) - z| ≤ ε)
    (hObs' : |L (evolveResetSchedule (steps'.map Prod.snd) X) - z| ≤ ε') :
    ∃ (r r' : ℝ) (hr : r ∈ Set.Icc 0 a) (hr' : r' ∈ Set.Icc 0 a),
      (∀ Y : Matrix n n ℂ, evolveResetSchedule (steps.map Prod.snd) Y =
        evolveResetSchedule (threeSliceReset s t a b r hb.le hr) Y) ∧
      (∀ Y : Matrix n n ℂ, evolveResetSchedule (steps'.map Prod.snd) Y =
        evolveResetSchedule (threeSliceReset s t a b r' hb.le hr') Y) ∧
      |r-r'| ≤ (ε + ε') / ((1 - Real.exp (-b)) * |L t.target - L s.target| * Real.exp (-a)) := by
  obtain ⟨r, hr, hEq⟩ := exists_threeSliceReset_of_doses steps s t a b hb.le hA hB hTargets
  obtain ⟨r', hr', hEq'⟩ := exists_threeSliceReset_of_doses steps' s t a b hb.le hA' hB' hTargets'
  refine ⟨r, r', hr, hr', hEq, hEq', ?_⟩
  exact threeSliceReset_split_uncertainty s t a b r r' hb hr hr' L X hTrace hResolve z ε ε'
    (by simpa only [← hEq X] using hObs)
    (by simpa only [← hEq' X] using hObs')

/-- Real occupation of the first level. -/
def firstLevelOccupation : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℝ where
  toFun X := (X 0 0).re
  map_add' X Y := by simp
  map_smul' r X := by simp [Matrix.smul_apply]

private theorem thermal_target_occupation_gap (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hTrace : X.trace = 1) :
    firstLevelOccupation (halfAttenuationThermalSlice 1).target -
      firstLevelOccupation (halfAttenuationThermalSlice 0).target = -1/2 := by
  let s := halfAttenuationThermalSlice 0
  let t := halfAttenuationThermalSlice 1
  have hAction := congrArg firstLevelOccupation
    (evolveResetSchedule_two_slice_reversal s t X)
  have hRead := (thermalOrder_firstOccupation X hTrace).2
  change firstLevelOccupation (evolveResetSchedule [s,t] X) -
    firstLevelOccupation (evolveResetSchedule [t,s] X) = _ at hRead
  rw [map_sub, hRead, hTrace] at hAction
  have hc : (1-s.attenuation)*(1-t.attenuation)*1 = ((1/4 : ℝ) : ℂ) := by
    simp [s, t, halfAttenuationThermalSlice_attenuation]
    norm_num
  rw [hc] at hAction
  change (-(1/8) : ℝ) = firstLevelOccupation
    ((algebraMap ℝ ℂ (1/4 : ℝ)) • (t.target - s.target)) at hAction
  rw [IsScalarTower.algebraMap_smul, map_smul, map_sub, smul_eq_mul] at hAction
  change firstLevelOccupation t.target - firstLevelOccupation s.target = _
  linarith only [hAction]

/-- In the existing two-level occupation experiment, admissible equal-dose
splits that fit one reported datum are within eight times the sum of
their measurement allowances. -/
theorem thermal_first_occupation_split_uncertainty
    (X : Matrix (Fin 2) (Fin 2) ℂ) (hTrace : X.trace = 1) (r r' z ε ε' : ℝ)
    (hr : r ∈ Set.Icc 0 (Real.log 2)) (hr' : r' ∈ Set.Icc 0 (Real.log 2))
    (hObs : |firstLevelOccupation (evolveResetSchedule (threeSliceReset
      (halfAttenuationThermalSlice 0) (halfAttenuationThermalSlice 1)
      (Real.log 2) (Real.log 2) r (Real.log_nonneg (by norm_num)) hr) X) - z| ≤ ε)
    (hObs' : |firstLevelOccupation (evolveResetSchedule (threeSliceReset
      (halfAttenuationThermalSlice 0) (halfAttenuationThermalSlice 1)
      (Real.log 2) (Real.log 2) r' (Real.log_nonneg (by norm_num)) hr') X) - z| ≤ ε') :
    |r-r'| ≤ 8 * (ε + ε') := by
  have hDiff := thermal_target_occupation_gap X hTrace
  have hPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := threeSliceReset_split_uncertainty (halfAttenuationThermalSlice 0)
    (halfAttenuationThermalSlice 1) (Real.log 2) (Real.log 2) r r' hPos hr hr'
    firstLevelOccupation X hTrace (sub_ne_zero.mp (by rw [hDiff]; norm_num)) z ε ε' hObs hObs'
  rw [hDiff, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)] at h
  norm_num at h
  linarith only [h]

end SKEFTHawking.FinitePositiveKernel.GibbsReset
