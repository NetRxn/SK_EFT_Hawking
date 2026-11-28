import SKEFTHawking.FiniteGibbsResetScheduleReadoutCalibration

/-! Transfer of one calibrated response difference across inputs and detectors.

The two tagged reset schedules have the same endpoint targets and total
dose for each bath. The whole-matrix model therefore leaves just one real
coefficient in their difference. A detector that resolves the endpoint
difference identifies this coefficient on a single trace-one input. The
comparison input can have arbitrary complex trace. -/

set_option autoImplicit false

namespace SKEFTHawking.FinitePositiveKernel.GibbsReset

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem equalDose_resetSchedule_difference
    (steps steps' : List (Bool × ResetSlice n)) (A B : Matrix n n ℂ)
    (hDoseA : resetBathDose false steps = resetBathDose false steps')
    (hDoseB : resetBathDose true steps = resetBathDose true steps')
    (hTargets : ∀ p ∈ steps, p.2.target = if p.1 then B else A)
    (hTargets' : ∀ p ∈ steps', p.2.target = if p.1 then B else A) :
    ∃ weight : ℝ, ∀ Y : Matrix n n ℂ,
      evolveResetSchedule (steps.map Prod.snd) Y -
        evolveResetSchedule (steps'.map Prod.snd) Y =
          weight • (Y.trace • (B - A)) := by
  rcases hCoeff : twoBathCoefficients steps with ⟨x, y, w⟩
  rcases hCoeff' : twoBathCoefficients steps' with ⟨x', y', w'⟩
  have hAttenuation := twoBathCoefficients_attenuation steps
  have hAttenuation' := twoBathCoefficients_attenuation steps'
  rw [hCoeff] at hAttenuation
  rw [hCoeff', ← hDoseA, ← hDoseB] at hAttenuation'
  obtain ⟨hx, hy⟩ := hAttenuation
  obtain ⟨hx', hy'⟩ := hAttenuation'
  have hX : x' = x := hx'.trans hx.symm
  have hY : y' = y := hy'.trans hy.symm
  refine ⟨w - w', fun Y => ?_⟩
  have hReal (r : ℝ) (Z : Matrix n n ℂ) : (r : ℂ) • Z = r • Z := by
    change (algebraMap ℝ ℂ r) • Z = r • Z
    rw [IsScalarTower.algebraMap_smul]
  have hFirst := evolveResetSchedule_eq_twoBathCoefficients steps A B hTargets Y
  have hSecond := evolveResetSchedule_eq_twoBathCoefficients steps' A B hTargets' Y
  simp only [hCoeff, hReal] at hFirst
  simp only [hCoeff', hX, hY, hReal] at hSecond
  rw [hFirst, hSecond, sub_smul w w' (Y.trace • (B - A))]
  abel

/-- The signed detector-response difference of two equal-dose schedules
on one shared trace-one input reconstructs their action difference on
every matrix. The detector need only be real linear. -/
theorem resetSchedules_channel_difference_of_readout
    (steps steps' : List (Bool × ResetSlice n)) (A B : Matrix n n ℂ)
    (hDoseA : resetBathDose false steps = resetBathDose false steps')
    (hDoseB : resetBathDose true steps = resetBathDose true steps')
    (hTargets : ∀ p ∈ steps, p.2.target = if p.1 then B else A)
    (hTargets' : ∀ p ∈ steps', p.2.target = if p.1 then B else A)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ) (hTrace : X.trace = 1)
    (hResolve : L (B - A) ≠ 0) (Y : Matrix n n ℂ) :
    evolveResetSchedule (steps.map Prod.snd) Y -
        evolveResetSchedule (steps'.map Prod.snd) Y =
      ((L (evolveResetSchedule (steps.map Prod.snd) X) -
        L (evolveResetSchedule (steps'.map Prod.snd) X)) / L (B - A)) •
          (Y.trace • (B - A)) := by
  obtain ⟨weight, hDifference⟩ :=
    equalDose_resetSchedule_difference steps steps' A B hDoseA hDoseB hTargets hTargets'
  have hReadout := congrArg L (hDifference X)
  rw [map_sub, hTrace, one_smul, map_smul, smul_eq_mul] at hReadout
  have hWeight :
      (L (evolveResetSchedule (steps.map Prod.snd) X) -
        L (evolveResetSchedule (steps'.map Prod.snd) X)) / L (B - A) = weight :=
    (div_eq_iff hResolve).2 hReadout
  rw [hWeight]
  exact hDifference Y

/-- Two fits to one datum bound any other real-linear detector's response
difference on an arbitrary matrix. Its complex trace acts inside the
second detector, and the calibration denominator is the absolute gap. -/
theorem resetSchedules_readout_transfer_bound
    (steps steps' : List (Bool × ResetSlice n)) (A B : Matrix n n ℂ)
    (hDoseA : resetBathDose false steps = resetBathDose false steps')
    (hDoseB : resetBathDose true steps = resetBathDose true steps')
    (hTargets : ∀ p ∈ steps, p.2.target = if p.1 then B else A)
    (hTargets' : ∀ p ∈ steps', p.2.target = if p.1 then B else A)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ) (hTrace : X.trace = 1)
    (hResolve : L (B - A) ≠ 0)
    (datum ε ε' : ℝ)
    (hObs : |L (evolveResetSchedule (steps.map Prod.snd) X) - datum| ≤ ε)
    (hObs' : |L (evolveResetSchedule (steps'.map Prod.snd) X) - datum| ≤ ε')
    (J : Matrix n n ℂ →ₗ[ℝ] ℝ) (Y : Matrix n n ℂ) :
    |J (evolveResetSchedule (steps.map Prod.snd) Y) -
      J (evolveResetSchedule (steps'.map Prod.snd) Y)| ≤
      (ε + ε') * |J (Y.trace • (B - A))| / |L (B - A)| := by
  let u := L (evolveResetSchedule (steps.map Prod.snd) X)
  let v := L (evolveResetSchedule (steps'.map Prod.snd) X)
  have hPath : |u - v| ≤ ε + ε' := (abs_sub_le u datum v).trans
    (add_le_add hObs (by simpa only [abs_sub_comm datum v] using hObs'))
  have hTransfer := congrArg J (resetSchedules_channel_difference_of_readout
    steps steps' A B hDoseA hDoseB hTargets hTargets' L X hTrace hResolve Y)
  rw [map_sub, map_smul, smul_eq_mul] at hTransfer
  rw [hTransfer, abs_mul, abs_div, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hPath (abs_nonneg _))
    (abs_nonneg _)

private noncomputable def resetActionAtWeight
    (A B : Matrix n n ℂ) (a b weight : ℝ) (Y : Matrix n n ℂ) : Matrix n n ℂ :=
  let attenuation := Real.exp (-a) * Real.exp (-b)
  attenuation • Y + (1 - attenuation) • (Y.trace • A) +
    weight • (Y.trace • (B - A))

private noncomputable def resetWeightFromReadout
    (A B : Matrix n n ℂ) (a b : ℝ) (L : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (X : Matrix n n ℂ) (datum : ℝ) : ℝ :=
  (datum - L (resetActionAtWeight A B a b 0 X)) / L (B - A)

/-- Compute the affine reset prediction from known doses and a scalar
readout at the common trace-one calibration input. -/
noncomputable def resetActionFromReadout
    (A B : Matrix n n ℂ) (a b : ℝ) (L : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (X : Matrix n n ℂ) (datum : ℝ) (Y : Matrix n n ℂ) : Matrix n n ℂ :=
  resetActionAtWeight A B a b (resetWeightFromReadout A B a b L X datum) Y

/-- One exact scalar readout determines the full action when the
bath doses and targets are known and the detector resolves the targets. -/
theorem resetSchedule_eq_resetActionFromReadout
    (steps : List (Bool × ResetSlice n)) (A B : Matrix n n ℂ) (a b : ℝ)
    (hDoseA : resetBathDose false steps = a)
    (hDoseB : resetBathDose true steps = b)
    (hTargets : ∀ p ∈ steps, p.2.target = if p.1 then B else A)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ)
    (hTrace : X.trace = 1) (hResolve : L (B - A) ≠ 0) (Y : Matrix n n ℂ) :
    evolveResetSchedule (steps.map Prod.snd) Y =
      resetActionFromReadout A B a b L X (L (evolveResetSchedule (steps.map Prod.snd) X)) Y := by
  rcases hCoeff : twoBathCoefficients steps with ⟨x, y, w⟩
  have hAttenuation := twoBathCoefficients_attenuation steps
  rw [hCoeff, hDoseA, hDoseB] at hAttenuation
  obtain ⟨hx, hy⟩ := hAttenuation
  let attenuation := Real.exp (-a) * Real.exp (-b)
  let base (Z : Matrix n n ℂ) := attenuation • Z + (1 - attenuation) • (Z.trace • A)
  have hForm (Z : Matrix n n ℂ) : evolveResetSchedule (steps.map Prod.snd) Z =
      base Z + w • (Z.trace • (B - A)) := by
    have hReal (r : ℝ) (W : Matrix n n ℂ) : (r : ℂ) • W = r • W := by
      change (algebraMap ℝ ℂ r) • W = r • W
      rw [IsScalarTower.algebraMap_smul]
    have h := evolveResetSchedule_eq_twoBathCoefficients steps A B hTargets Z
    simpa only [hCoeff, hx, hy, attenuation, base, hReal] using h
  have hRead := congrArg L (hForm X)
  rw [map_add, hTrace, one_smul, map_smul, smul_eq_mul] at hRead
  have hWeight :
      (L (evolveResetSchedule (steps.map Prod.snd) X) - L (base X)) / L (B - A) = w :=
    (div_eq_iff hResolve).2 (by linarith only [hRead])
  simp only [resetActionFromReadout, resetWeightFromReadout, resetActionAtWeight, zero_smul, add_zero]
  change _ = base Y + ((L (evolveResetSchedule (steps.map Prod.snd) X) - L (base X)) /
    L (B - A)) • (Y.trace • (B - A))
  rw [hWeight]
  exact hForm Y

/-- A scalar measurement allowance transfers to any other detector
and matrix with the exact absolute sensitivity ratio. -/
theorem resetSchedule_resetActionFromReadout_error
    (steps : List (Bool × ResetSlice n)) (A B : Matrix n n ℂ) (a b : ℝ)
    (hDoseA : resetBathDose false steps = a)
    (hDoseB : resetBathDose true steps = b)
    (hTargets : ∀ p ∈ steps, p.2.target = if p.1 then B else A)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ)
    (hTrace : X.trace = 1) (hResolve : L (B - A) ≠ 0)
    (datum ε : ℝ) (hObs : |L (evolveResetSchedule (steps.map Prod.snd) X) - datum| ≤ ε)
    (J : Matrix n n ℂ →ₗ[ℝ] ℝ) (Y : Matrix n n ℂ) :
    |J (evolveResetSchedule (steps.map Prod.snd) Y) -
        J (resetActionFromReadout A B a b L X datum Y)| ≤
      ε * |J (Y.trace • (B - A))| / |L (B - A)| := by
  rw [resetSchedule_eq_resetActionFromReadout steps A B a b hDoseA hDoseB hTargets
    L X hTrace hResolve Y]
  let exactDatum := L (evolveResetSchedule (steps.map Prod.snd) X)
  change |exactDatum - datum| ≤ ε at hObs
  let attenuation := Real.exp (-a) * Real.exp (-b)
  let base (Z : Matrix n n ℂ) := attenuation • Z + (1 - attenuation) • (Z.trace • A)
  simp only [resetActionFromReadout, resetWeightFromReadout, resetActionAtWeight, zero_smul, add_zero]
  change |J (base Y + ((exactDatum - L (base X)) / L (B - A)) • (Y.trace • (B - A))) -
    J (base Y + ((datum - L (base X)) / L (B - A)) • (Y.trace • (B - A)))| ≤ _
  simp only [map_add, map_smul, smul_eq_mul]
  have hDiff :
      J (base Y) + (exactDatum - L (base X)) / L (B - A) * J (Y.trace • (B - A)) -
          (J (base Y) + (datum - L (base X)) / L (B - A) * J (Y.trace • (B - A))) =
        (exactDatum - datum) * J (Y.trace • (B - A)) / L (B - A) := by
    ring
  rw [hDiff, abs_div, abs_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hObs (abs_nonneg _))
    (abs_nonneg _)

private noncomputable def projectResetWeight (a b weight : ℝ) : ℝ :=
  max (Real.exp (-a) * (1 - Real.exp (-b))) (min (1 - Real.exp (-b)) weight)

private theorem weightProjection_mem (a b weight : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    projectResetWeight a b weight ∈
      Set.Icc (Real.exp (-a) * (1 - Real.exp (-b))) (1 - Real.exp (-b)) := by
  have hOne : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have hB : 0 ≤ 1 - Real.exp (-b) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb))
  have hOrder : Real.exp (-a) * (1 - Real.exp (-b)) ≤ 1 - Real.exp (-b) :=
    mul_le_of_le_one_left hB hOne
  exact ⟨le_max_left _ _, max_le hOrder (min_le_left _ _)⟩

private theorem abs_sub_projectWeight_le {a b w : ℝ} (u : ℝ)
    (hw : w ∈ Set.Icc (Real.exp (-a) * (1 - Real.exp (-b))) (1 - Real.exp (-b))) :
    |w - projectResetWeight a b u| ≤ |w - u| := by
  let lo := Real.exp (-a) * (1 - Real.exp (-b))
  let hi := 1 - Real.exp (-b)
  change lo ≤ w ∧ w ≤ hi at hw
  change |w - max lo (min hi u)| ≤ |w - u|
  by_cases hLow : u ≤ lo
  · have hUHi := (hLow.trans hw.1).trans hw.2
    rw [min_eq_right hUHi, max_eq_left hLow,
      abs_of_nonneg (sub_nonneg.mpr hw.1),
      abs_of_nonneg (sub_nonneg.mpr (hLow.trans hw.1))]
    linarith only [hLow]
  by_cases hHigh : hi ≤ u
  · rw [min_eq_left hHigh, max_eq_right (hw.1.trans hw.2),
      abs_of_nonpos (sub_nonpos.mpr hw.2),
      abs_of_nonpos (sub_nonpos.mpr (hw.2.trans hHigh))]
    linarith only [hHigh]
  rw [min_eq_right (le_of_not_ge hHigh), max_eq_right (le_of_not_ge hLow)]

omit [DecidableEq n] in
private theorem resetActionAtWeight_readout_difference
    (A B : Matrix n n ℂ) (a b u v : ℝ)
    (J : Matrix n n ℂ →ₗ[ℝ] ℝ) (Y : Matrix n n ℂ) :
    |J (resetActionAtWeight A B a b u Y) - J (resetActionAtWeight A B a b v Y)| =
      |u - v| * |J (Y.trace • (B - A))| := by
  simp only [resetActionAtWeight, map_add, map_smul, smul_eq_mul]
  rw [← abs_mul]
  congr 1
  ring

/-- Clip the readout's inferred weight to the exact reachable two-bath
interval. The same clipped weight defines the action on every input. -/
noncomputable def clippedResetActionFromReadout
    (A B : Matrix n n ℂ) (a b : ℝ) (L : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (X : Matrix n n ℂ) (datum : ℝ) (Y : Matrix n n ℂ) : Matrix n n ℂ :=
  resetActionAtWeight A B a b
    (projectResetWeight a b (resetWeightFromReadout A B a b L X datum)) Y

omit [Fintype n] [DecidableEq n] in
private theorem complex_ofReal_smul_eq_real (r : ℝ) (M : Matrix n n ℂ) :
    (r : ℂ) • M = r • M := by
  change (algebraMap ℝ ℂ r) • M = r • M
  rw [IsScalarTower.algebraMap_smul]

/-- Every scalar datum, including one outside the unprojected range,
predicts a realizable same-dose reset action after clipping. -/
theorem clippedResetActionFromReadout_reachable
    (s t : ResetSlice n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ) (datum : ℝ) :
    ∃ steps : List (Bool × ResetSlice n),
      resetBathDose false steps = a ∧ resetBathDose true steps = b ∧
      (∀ p ∈ steps, p.2.target = if p.1 then t.target else s.target) ∧
      ∀ Y, clippedResetActionFromReadout s.target t.target a b L X datum Y =
        evolveResetSchedule (steps.map Prod.snd) Y := by
  apply (twoBath_channel_reachable_iff s t a b ha hb _).2
  let weight := projectResetWeight a b
    (resetWeightFromReadout s.target t.target a b L X datum)
  refine ⟨weight, weightProjection_mem a b _ ha hb, fun Y => ?_⟩
  simp only [clippedResetActionFromReadout, resetActionAtWeight, weight,
    complex_ofReal_smul_eq_real]

/-- The projected action can be implemented by a single split of the
first bath around the second-bath slice, at the known total doses. -/
theorem clippedResetActionFromReadout_three_slices
    (s t : ResetSlice n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ) (datum : ℝ) :
    ∃ (r : ℝ) (hr : r ∈ Set.Icc 0 a),
      ∀ Y, clippedResetActionFromReadout s.target t.target a b L X datum Y =
        evolveResetSchedule (threeSliceReset s t a b r hb hr) Y := by
  obtain ⟨steps, hA, hB, hTargets, hAction⟩ :=
    clippedResetActionFromReadout_reachable s t a b ha hb L X datum
  subst a
  subst b
  obtain ⟨r, hr, hra, hEq⟩ := exists_equivalent_threeSlice_schedule steps s t hTargets
  exact ⟨r, ⟨hr, hra⟩, fun Y => (hAction Y).trans (hEq Y)⟩

/-- Projection onto the reachable interval weakly improves every
detector's absolute prediction error on every comparison matrix. -/
theorem clippedResetActionFromReadout_error_le_raw
    (steps : List (Bool × ResetSlice n)) (s t : ResetSlice n) (a b : ℝ)
    (hA : resetBathDose false steps = a) (hB : resetBathDose true steps = b)
    (hTargets : ∀ p ∈ steps, p.2.target = if p.1 then t.target else s.target)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ) (datum : ℝ)
    (J : Matrix n n ℂ →ₗ[ℝ] ℝ) (Y : Matrix n n ℂ) :
    |J (evolveResetSchedule (steps.map Prod.snd) Y) -
        J (clippedResetActionFromReadout s.target t.target a b L X datum Y)| ≤
      |J (evolveResetSchedule (steps.map Prod.snd) Y) -
        J (resetActionFromReadout s.target t.target a b L X datum Y)| := by
  have ha : 0 ≤ a := hA ▸ resetBathDose_nonnegative false steps
  have hb : 0 ≤ b := hB ▸ resetBathDose_nonnegative true steps
  obtain ⟨w, hw, hAction⟩ :=
    (twoBath_channel_reachable_iff s t a b ha hb _).1 ⟨steps, hA, hB, hTargets, fun _ => rfl⟩
  have hActual : evolveResetSchedule (steps.map Prod.snd) Y =
      resetActionAtWeight s.target t.target a b w Y := by
    simpa only [resetActionAtWeight, complex_ofReal_smul_eq_real] using hAction Y
  rw [hActual, clippedResetActionFromReadout, resetActionFromReadout,
    resetActionAtWeight_readout_difference, resetActionAtWeight_readout_difference]
  exact mul_le_mul_of_nonneg_right (abs_sub_projectWeight_le _ hw) (abs_nonneg _)

/-- Clipping preserves the quantitative detector error allowance while
giving the action of a feasible bath schedule. -/
theorem clippedResetActionFromReadout_error
    (steps : List (Bool × ResetSlice n)) (s t : ResetSlice n) (a b : ℝ)
    (hA : resetBathDose false steps = a) (hB : resetBathDose true steps = b)
    (hTargets : ∀ p ∈ steps, p.2.target = if p.1 then t.target else s.target)
    (L : Matrix n n ℂ →ₗ[ℝ] ℝ) (X : Matrix n n ℂ)
    (hTrace : X.trace = 1) (hResolve : L (t.target - s.target) ≠ 0)
    (datum ε : ℝ) (hObs : |L (evolveResetSchedule (steps.map Prod.snd) X) - datum| ≤ ε)
    (J : Matrix n n ℂ →ₗ[ℝ] ℝ) (Y : Matrix n n ℂ) :
    |J (evolveResetSchedule (steps.map Prod.snd) Y) -
        J (clippedResetActionFromReadout s.target t.target a b L X datum Y)| ≤
      ε * |J (Y.trace • (t.target - s.target))| / |L (t.target - s.target)| :=
  (clippedResetActionFromReadout_error_le_raw steps s t a b hA hB hTargets L X datum J Y).trans
    (resetSchedule_resetActionFromReadout_error steps s.target t.target a b hA hB hTargets
      L X hTrace hResolve datum ε hObs J Y)


/-- A concrete out-of-range datum for two positive diagonal targets.
Clipping replaces the negative predicted second-level occupation by
the nearest reachable two-bath output. -/
theorem clippedResetActionFromReadout_two_level_control :
    let A : Matrix (Fin 2) (Fin 2) ℂ := !![3/4, 0; 0, 1/4]
    let B : Matrix (Fin 2) (Fin 2) ℂ := !![1/4, 0; 0, 3/4]
    let Y : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
    let raw := resetActionFromReadout A B (Real.log 2) (Real.log 2)
      firstLevelOccupation A 1 Y
    let clipped := clippedResetActionFromReadout A B (Real.log 2) (Real.log 2)
      firstLevelOccupation A 1 Y
    raw = !![17/16, 0; 0, -(1/16)] ∧ clipped = !![11/16, 0; 0, 5/16] := by
  have hExp : Real.exp (-(Real.log 2)) = (1/2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  dsimp only
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [resetActionFromReadout, clippedResetActionFromReadout, resetActionAtWeight,
      resetWeightFromReadout, projectResetWeight, hExp, firstLevelOccupation,
      Matrix.trace_fin_two, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Complex.real_smul, Complex.mul_re, Complex.div_re, max_def, min_def]

end SKEFTHawking.FinitePositiveKernel.GibbsReset
