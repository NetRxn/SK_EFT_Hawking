import SKEFTHawking.QuantumNetwork.FinitePersistentMeasuredHandErrors

/-! # Same-input persistent versus fresh measured-hand experiments -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FinitePersistentMeasuredHandExamples
open Matrix FiniteInterventionProcess FinitePersistentMeasuredHand
open FiniteClockControlledRetainedMemoryExamples
open scoped BigOperators ComplexOrder Kronecker

/-- The old parity-zero data input does not distinguish keep from reset-before-J. -/
theorem data_first (a : A) (i : Fin 11) :
    FiniteClockControlledRetainedMemory.dataBranch Unit a i
      (prepareData 0 FiniteQutritRetainedClock.rho0) =
      if i=FiniteQutritRetainedClock.noneLabel then
        prepareData 1 FiniteQutritRetainedClock.rho0 else 0 := by
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl
  · rw [FiniteClockControlledRetainedMemory.dataBranch_keep]
    rcases FiniteQutritRetainedClock.label_cases i with rfl | ⟨k,rfl⟩
    · rw [prepareData, FiniteQutritRetainedClock.none_zero_branch]
      simp [prepareData]
    · rw [prepareData, FiniteQutritRetainedClock.some_zero_branch]
      simp [Ne.symm (FiniteQutritRetainedClock.none_ne_some k)]
  · rw [FiniteClockControlledRetainedMemory.dataBranch_reset,
      FiniteQutritRetainedClock.reset_amplified_action, old_reduce_prepare]
    rcases FiniteQutritRetainedClock.label_cases i with rfl | ⟨k,rfl⟩
    · rw [FiniteQutritRetainedClock.none_zero_branch]
      simp [prepareData]
    · rw [FiniteQutritRetainedClock.some_zero_branch]
      simp [Ne.symm (FiniteQutritRetainedClock.none_ne_some k)]

def afterFirstLabel (a : A) : FullMat Unit :=
  FiniteClockControlledRetainedMemory.insert Unit
    (prepareData 1 FiniteQutritRetainedClock.rho0) (FiniteClockHandReadout.Q a)

theorem first_branch {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) (i : Fin 11) :
    (step Unit ω ℏ t hℏ).branch S Unit 22 (outcomeEquiv (a,i))
      (input FiniteClockHandReadout.rhoPlus) =
      if i=FiniteQutritRetainedClock.noneLabel then
        (FiniteClockHandReadout.mass ω t a : ℂ) • afterFirstLabel a else 0 := by
  rw [input, FiniteClockHandReadout.rhoPlus_eq, branch_posterior, data_first]
  have ht : transition ω t a 1 = FiniteClockHandReadout.mass ω t a := by
    fin_cases a <;> simp [transition, FiniteClockHandReadout.mass]
  rw [ht]
  split
  · rfl
  · rw [FiniteClockControlledRetainedMemoryExamples.insert_zero, smul_zero]

def dataSecond (b : A) (j : Fin 11) : ReducedMat Unit :=
  if b=0 then match FiniteQutritRetainedClock.labelEquiv.symm j with
    | none => 0
    | some k => prepareData 0 (micro k)
  else if j=FiniteQutritRetainedClock.noneLabel then
    prepareData 1 FiniteQutritRetainedClock.rho0 else 0

theorem data_second (b : A) (j : Fin 11) :
    FiniteClockControlledRetainedMemory.dataBranch Unit b j
      (prepareData 1 FiniteQutritRetainedClock.rho0) = dataSecond b j := by
  rcases (show b=0 ∨ b=1 by fin_cases b <;> decide) with rfl | rfl
  · rw [FiniteClockControlledRetainedMemory.dataBranch_keep]
    rcases FiniteQutritRetainedClock.label_cases j with rfl | ⟨k,rfl⟩
    · rw [prepareData, FiniteQutritRetainedClock.none_one_branch]
      simp [dataSecond, FiniteQutritRetainedClock.noneLabel]
    · rw [prepareData, FiniteQutritRetainedClock.some_one_branch, ten_branch]
      simp [dataSecond, prepareData, FiniteQutritRetainedClock.someLabel]
  · rw [FiniteClockControlledRetainedMemory.dataBranch_reset,
      FiniteQutritRetainedClock.reset_amplified_action, old_reduce_prepare]
    rcases FiniteQutritRetainedClock.label_cases j with rfl | ⟨k,rfl⟩
    · rw [FiniteQutritRetainedClock.none_zero_branch]
      simp [dataSecond, prepareData]
    · rw [FiniteQutritRetainedClock.some_zero_branch]
      simp [dataSecond, Ne.symm (FiniteQutritRetainedClock.none_ne_some k)]

def twoPolicy (t s : Duration) : Policy 2 :=
  .node t (fun _ => .node s (fun _ => .done))

def table (ω t s : ℝ) (a b : A) (i j : Fin 11) : FullMat Unit :=
  if i=FiniteQutritRetainedClock.noneLabel then
    ((FiniteClockHandReadout.mass ω t a * transition ω s b a : ℝ) : ℂ) •
      FiniteClockControlledRetainedMemory.insert Unit (dataSecond b j) (FiniteClockHandReadout.Q b)
  else 0

/-- The full 22×22 chronological table, with all zero micro-alternatives retained. -/
theorem two_round_table {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) (t s : Duration)
    (a b : A) (i j : Fin 11) :
    run S Unit 22 (policyTree Unit ω ℏ hℏ (twoPolicy t s))
      (outcomeEquiv (a,i),outcomeEquiv (b,j),()) (input FiniteClockHandReadout.rhoPlus) =
      table ω t s a b i j := by
  change (step Unit ω ℏ s hℏ).branch S Unit 22 (outcomeEquiv (b,j))
    ((step Unit ω ℏ t hℏ).branch S Unit 22 (outcomeEquiv (a,i))
      (input FiniteClockHandReadout.rhoPlus)) = _
  rw [first_branch]
  unfold table
  split
  · rw [Step.branch_smul, afterFirstLabel, branch_posterior, data_second, smul_smul,
      Complex.ofReal_mul]
  · exact Step.branch_zero S Unit 22 _ _

theorem dataSecond_keep_sum : (∑ j : Fin 11, dataSecond 0 j) =
    prepareData 0 (FiniteQutritAveragedTransfer.transfer FiniteQutritRetainedClock.rho0) := by
  simp_rw [← data_second]
  rw [dataBranch_keep_sum Unit, amplified_prepare_one]

theorem dataSecond_reset_sum : (∑ j : Fin 11, dataSecond 1 j) =
    prepareData 1 FiniteQutritRetainedClock.rho0 := by
  simp_rw [← data_second]
  rw [dataBranch_reset_sum Unit, FiniteQutritRetainedClock.reset_amplified_action,
    old_reduce_prepare]
  exact amplified_prepare_zero _

theorem eventValue_sum {I : Type*} [Fintype I] (Z : I → FullMat Unit) :
    eventValue (∑ i, Z i) = ∑ i, eventValue (Z i) := by
  simp [eventValue, Matrix.mul_sum, Matrix.trace_sum]

theorem second_event_sum (b : A) :
    (∑ j : Fin 11, eventValue (FiniteClockControlledRetainedMemory.insert Unit
      (dataSecond b j) (FiniteClockHandReadout.Q b))) = if b=0 then 4/5 else 1 := by
  rw [← eventValue_sum, ← FiniteClockControlledRetainedMemory.insert_sum]
  rcases (show b=0 ∨ b=1 by fin_cases b <;> decide) with rfl | rfl
  · rw [dataSecond_keep_sum, event_prepare 0 _ _ (FiniteClockHandReadout.Q_trace 0),
      event0_entry, FiniteQutritRetainedClock.transfer_rho0]
    norm_num
  · rw [dataSecond_reset_sum, event_prepare 1 _ _ (FiniteClockHandReadout.Q_trace 1), event0_entry]
    norm_num [FiniteQutritRetainedClock.rho0, FiniteQutritPhysicalMemory.projector]

def weightedTable (weights : A → A → ℝ) (a b : A) (i j : Fin 11) : FullMat Unit :=
  if i=FiniteQutritRetainedClock.noneLabel then (weights a b:ℂ) •
    FiniteClockControlledRetainedMemory.insert Unit (dataSecond b j) (FiniteClockHandReadout.Q b)
  else 0

theorem weighted_table_event (weights : A → A → ℝ) :
    (∑ a : A, ∑ i : Fin 11, ∑ b : A, ∑ j : Fin 11,
      eventValue (weightedTable weights a b i j)) =
      (weights 0 0+weights 1 0)*(4/5)+(weights 0 1+weights 1 1) := by
  have hz : eventValue (0 : FullMat Unit) = 0 := by simp [eventValue]
  have hi (a : A) (i : Fin 11) :
      (∑ b : A, ∑ j : Fin 11, eventValue (weightedTable weights a b i j)) =
      if i=FiniteQutritRetainedClock.noneLabel then weights a 0*(4/5)+weights a 1 else 0 := by
    by_cases h : i=FiniteQutritRetainedClock.noneLabel
    · simp only [weightedTable, h, ite_true, eventValue_real_smul,
        ← Finset.mul_sum, second_event_sum, Fin.sum_univ_two]
      norm_num
    · simp only [weightedTable, h, ite_false, hz, Finset.sum_const_zero]
  simp only [hi, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.sum_univ_two]
  ring

def keepProbability (ω t s : ℝ) : ℝ :=
  FiniteClockHandReadout.p ω t*(1-FiniteClockHandReadout.p ω s)+
    (1-FiniteClockHandReadout.p ω t)*FiniteClockHandReadout.p ω s

def terminalProbability (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) {n : ℕ} (P : Policy n)
    (X : FullMat Unit) : ℝ :=
  ∑ h, eventValue (run S Unit 22 (policyTree Unit ω ℏ hℏ P) h X)

def twoHistoryEquiv : ((A × Fin 11) × (A × Fin 11)) ≃ History 22 2 where
  toFun h := (outcomeEquiv h.1,outcomeEquiv h.2,())
  invFun h := (outcomeEquiv.symm h.1,outcomeEquiv.symm h.2.1)
  left_inv h := by simp
  right_inv h := by rcases h with ⟨o,p,⟨⟩⟩; simp

theorem sum_histories_two (f : History 22 2 → ℝ) :
    (∑ h, f h) = ∑ a : A, ∑ i : Fin 11, ∑ b : A, ∑ j : Fin 11,
      f (outcomeEquiv (a,i),outcomeEquiv (b,j),()) := by
  rw [← twoHistoryEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, twoHistoryEquiv]
  rfl

theorem persistent_event {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) (t s : Duration) :
    terminalProbability ω ℏ hℏ (twoPolicy t s) (input FiniteClockHandReadout.rhoPlus) =
      1-keepProbability ω t s/5 := by
  rw [terminalProbability, sum_histories_two]
  simp_rw [two_round_table]
  change (∑ a : A, ∑ i : Fin 11, ∑ b : A, ∑ j : Fin 11,
    eventValue (weightedTable (fun a b => FiniteClockHandReadout.mass ω t a*transition ω s b a)
      a b i j)) = _
  rw [weighted_table_event]
  simp [FiniteClockHandReadout.mass, transition, keepProbability]
  ring

theorem fresh_first_branch {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) (i : Fin 11) :
    (FiniteClockControlledRetainedMemory.step Unit ω ℏ t hℏ).branch S Unit 22
      (outcomeEquiv (a,i)) (input FiniteClockHandReadout.rhoPlus) =
      if i=FiniteQutritRetainedClock.noneLabel then
        (FiniteClockHandReadout.mass ω t a:ℂ) • afterFirstLabel a else 0 := by
  rw [FiniteClockControlledRetainedMemory.branch_action, input,
    FiniteClockControlledRetainedMemory.handTrace_insert,
    FiniteClockHandReadout.rhoPlus_density.2, one_smul, data_first]
  split
  · rfl
  · rw [FiniteClockControlledRetainedMemoryExamples.insert_zero, smul_zero]

theorem fresh_second_branch {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (b a : A) (j : Fin 11) :
    (FiniteClockControlledRetainedMemory.step Unit ω ℏ t hℏ).branch S Unit 22
      (outcomeEquiv (b,j)) (afterFirstLabel a) =
      (FiniteClockHandReadout.mass ω t b:ℂ) •
        FiniteClockControlledRetainedMemory.insert Unit (dataSecond b j) (FiniteClockHandReadout.Q b) := by
  rw [FiniteClockControlledRetainedMemory.branch_action, afterFirstLabel,
    FiniteClockControlledRetainedMemory.handTrace_insert, FiniteClockHandReadout.Q_trace,
    one_smul, data_second]

/-- Same input, duration policy, data maps and terminal effect; only hand replacement differs. -/
theorem fresh_two_round_table {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) (t s : Duration)
    (a b : A) (i j : Fin 11) :
    run S Unit 22 (FiniteClockControlledRetainedMemory.policyTree Unit ω ℏ hℏ (twoPolicy t s))
      (outcomeEquiv (a,i),outcomeEquiv (b,j),()) (input FiniteClockHandReadout.rhoPlus) =
      weightedTable (fun a b => FiniteClockHandReadout.mass ω t a*FiniteClockHandReadout.mass ω s b)
        a b i j := by
  change (FiniteClockControlledRetainedMemory.step Unit ω ℏ s hℏ).branch S Unit 22
    (outcomeEquiv (b,j))
    ((FiniteClockControlledRetainedMemory.step Unit ω ℏ t hℏ).branch S Unit 22
      (outcomeEquiv (a,i)) (input FiniteClockHandReadout.rhoPlus)) = _
  rw [fresh_first_branch]
  unfold weightedTable
  split
  · rw [Step.branch_smul, fresh_second_branch, smul_smul, Complex.ofReal_mul]
  · exact Step.branch_zero S Unit 22 _ _

def freshTerminalProbability (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) {n : ℕ} (P : Policy n)
    (X : FullMat Unit) : ℝ :=
  ∑ h, eventValue (run S Unit 22 (FiniteClockControlledRetainedMemory.policyTree Unit ω ℏ hℏ P) h X)

theorem fresh_event {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) (t s : Duration) :
    freshTerminalProbability ω ℏ hℏ (twoPolicy t s) (input FiniteClockHandReadout.rhoPlus) =
      1-FiniteClockHandReadout.p ω s/5 := by
  rw [freshTerminalProbability, sum_histories_two]
  simp_rw [fresh_two_round_table]
  rw [weighted_table_event]
  simp [FiniteClockHandReadout.mass]
  ring

theorem calibrated_events {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) :
    keepProbability ω (rightDuration hω) (leftDuration hω) = 5/8 ∧
    terminalProbability ω ℏ hℏ (twoPolicy (rightDuration hω) (leftDuration hω))
      (input FiniteClockHandReadout.rhoPlus) = 7/8 ∧
    freshTerminalProbability ω ℏ hℏ (twoPolicy (rightDuration hω) (leftDuration hω))
      (input FiniteClockHandReadout.rhoPlus) = 19/20 := by
  rw [persistent_event, fresh_event]
  simp only [keepProbability, rightDuration, leftDuration, Subtype.coe_mk,
    FiniteClockHandReadout.p_right hω.ne', FiniteClockHandReadout.p_left hω.ne']
  norm_num

theorem calibrated_physical_gap {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) :
    freshTerminalProbability ω ℏ hℏ (twoPolicy (rightDuration hω) (leftDuration hω))
      (input FiniteClockHandReadout.rhoPlus)-
    terminalProbability ω ℏ hℏ (twoPolicy (rightDuration hω) (leftDuration hω))
      (input FiniteClockHandReadout.rhoPlus) = 3/40 := by
  rw [(calibrated_events hω hℏ).2.1,(calibrated_events hω hℏ).2.2]
  norm_num

theorem dataSecond_positive (b : A) (j : Fin 11) : (dataSecond b j).PosSemidef := by
  rw [← data_second]
  exact FiniteClockControlledRetainedMemory.dataBranch_positive Unit b j
    (prepareData_density 1 FiniteQutritRetainedClock.rho0_density).1

theorem dataSecond_trace_sum (b : A) : (∑ j : Fin 11, (dataSecond b j).trace.re) = 1 := by
  simp_rw [← data_second]
  rw [← Complex.re_sum, FiniteClockControlledRetainedMemory.dataBranch_sum_trace,
    (prepareData_density 1 FiniteQutritRetainedClock.rho0_density).2]
  rfl

theorem weighted_norm (weights nominal : A → A → ℝ) (a b : A) (i j : Fin 11) :
    traceNorm (weightedTable weights a b i j-weightedTable nominal a b i j) =
      if i=FiniteQutritRetainedClock.noneLabel then
        |weights a b-nominal a b| *(dataSecond b j).trace.re else 0 := by
  unfold weightedTable
  split
  · rw [← sub_smul, ← Complex.ofReal_sub,
      FinitePersistentMeasuredHandErrors.traceNorm_real_smul,
      traceNorm_posSemidef (FiniteClockControlledRetainedMemory.insert_positive Unit
        (dataSecond_positive b j) (FiniteClockHandReadout.Q_density b).1),
      FiniteClockControlledRetainedMemory.insert_trace, FiniteClockHandReadout.Q_trace, mul_one]
  · simp [traceNorm_zero]

theorem weighted_table_norm_sum (weights nominal : A → A → ℝ) :
    (∑ a : A, ∑ i : Fin 11, ∑ b : A, ∑ j : Fin 11,
      traceNorm (weightedTable weights a b i j-weightedTable nominal a b i j)) =
      ∑ a : A, (|weights a 0-nominal a 0|+|weights a 1-nominal a 1|) := by
  have hi (a : A) (i : Fin 11) :
      (∑ b : A, ∑ j : Fin 11,
        traceNorm (weightedTable weights a b i j-weightedTable nominal a b i j)) =
      if i=FiniteQutritRetainedClock.noneLabel then
        |weights a 0-nominal a 0|+|weights a 1-nominal a 1| else 0 := by
    simp only [weighted_norm]
    by_cases h : i=FiniteQutritRetainedClock.noneLabel
    · simp only [h, ite_true, ← Finset.mul_sum, dataSecond_trace_sum, mul_one, Fin.sum_univ_two]
    · simp only [h, ite_false, Finset.sum_const_zero]
  simp only [hi, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem recorded_distance_formula {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) (t s : Duration) :
    FiniteAdaptiveMapPerturbation.outputDistance S Unit 22
      (policyTree Unit ω ℏ hℏ (twoPolicy t s))
      (FiniteClockControlledRetainedMemory.policyTree Unit ω ℏ hℏ (twoPolicy t s))
      (input FiniteClockHandReadout.rhoPlus) (input FiniteClockHandReadout.rhoPlus) =
      (∑ a : A, (|FiniteClockHandReadout.mass ω t a*transition ω s 0 a-
        FiniteClockHandReadout.mass ω t a*FiniteClockHandReadout.mass ω s 0|+
        |FiniteClockHandReadout.mass ω t a*transition ω s 1 a-
        FiniteClockHandReadout.mass ω t a*FiniteClockHandReadout.mass ω s 1|))/2 := by
  unfold FiniteAdaptiveMapPerturbation.outputDistance
  rw [sum_histories_two]
  simp_rw [two_round_table, fresh_two_round_table]
  change (∑ a : A, ∑ i : Fin 11, ∑ b : A, ∑ j : Fin 11,
    traceNorm (weightedTable (fun a b => FiniteClockHandReadout.mass ω t a*transition ω s b a) a b i j-
      weightedTable (fun a b => FiniteClockHandReadout.mass ω t a*FiniteClockHandReadout.mass ω s b) a b i j))/2 = _
  rw [weighted_table_norm_sum]

theorem calibrated_recorded_distance {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) :
    FiniteAdaptiveMapPerturbation.outputDistance S Unit 22
      (policyTree Unit ω ℏ hℏ (twoPolicy (rightDuration hω) (leftDuration hω)))
      (FiniteClockControlledRetainedMemory.policyTree Unit ω ℏ hℏ
        (twoPolicy (rightDuration hω) (leftDuration hω)))
      (input FiniteClockHandReadout.rhoPlus) (input FiniteClockHandReadout.rhoPlus) = 3/8 := by
  rw [recorded_distance_formula]
  have ht : FiniteClockHandReadout.p ω (rightDuration hω) = 3/4 := FiniteClockHandReadout.p_right hω.ne'
  have hs : FiniteClockHandReadout.p ω (leftDuration hω) = 1/4 := FiniteClockHandReadout.p_left hω.ne'
  simp only [FiniteClockHandReadout.mass, transition, ht, hs]
  norm_num [Fin.sum_univ_two]

theorem eta_duration_error {ω : ℝ} (hω : 0 < ω) (t s : Duration)
    (ht : |(t:ℝ)-(s:ℝ)| ≤ 1/(100*ω)) :
    FinitePersistentMeasuredHandErrors.eta (ω*t) (ω*s) ≤ 1/200 := by
  have hb := (FinitePersistentMeasuredHandErrors.eta_bound (ω*t) (ω*s)).trans (min_le_right _ _)
  rw [← mul_sub, abs_mul, abs_of_pos hω] at hb
  have he : ω*(1/(100*ω))/2 = (1/200:ℝ) := by field_simp <;> ring
  exact hb.trans (he ▸ (mul_le_mul_of_nonneg_left ht hω.le |> fun h =>
    div_le_div_of_nonneg_right h (by norm_num)))

theorem persistent_two_event_error {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (t s u v : Duration) (ht : |(t:ℝ)-(u:ℝ)| ≤ 1/(100*ω))
    (hs : |(s:ℝ)-(v:ℝ)| ≤ 1/(100*ω)) :
    |terminalProbability ω ℏ hℏ (twoPolicy t s) (input FiniteClockHandReadout.rhoPlus)-
      terminalProbability ω ℏ hℏ (twoPolicy u v) (input FiniteClockHandReadout.rhoPlus)| ≤ 1/100 := by
  have hp : FinitePersistentMeasuredHandErrors.PhasePolicyErrors ω
      (twoPolicy t s) (twoPolicy u v) [1/200,1/200] :=
    .node (eta_duration_error hω t u ht) rfl (fun _ =>
      .node (eta_duration_error hω s v hs) rfl (fun _ => .done))
  have hh := FinitePersistentMeasuredHandErrors.policy_event_error Unit hℏ hp
    (input_density FiniteClockHandReadout.rhoPlus_density)
    (input_density FiniteClockHandReadout.rhoPlus_density) (fun _ => event) (fun _ => event_effect)
  change |terminalProbability ω ℏ hℏ (twoPolicy t s) (input FiniteClockHandReadout.rhoPlus)-
      terminalProbability ω ℏ hℏ (twoPolicy u v) (input FiniteClockHandReadout.rhoPlus)| ≤ _ at hh
  norm_num [traceDist_self] at hh
  exact hh

theorem fresh_two_event_error {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (t s u v : Duration) (ht : |(t:ℝ)-(u:ℝ)| ≤ 1/(100*ω))
    (hs : |(s:ℝ)-(v:ℝ)| ≤ 1/(100*ω)) :
    |freshTerminalProbability ω ℏ hℏ (twoPolicy t s) (input FiniteClockHandReadout.rhoPlus)-
      freshTerminalProbability ω ℏ hℏ (twoPolicy u v) (input FiniteClockHandReadout.rhoPlus)| ≤ 1/100 := by
  have hp : FiniteClockControlledRetainedMemory.PolicyErrors ω
      (twoPolicy t s) (twoPolicy u v) [1/200,1/200] :=
    .node (duration_error hω t u ht) rfl (fun _ =>
      .node (duration_error hω s v hs) rfl (fun _ => .done))
  have hh := FiniteClockControlledRetainedMemory.policy_event_error Unit hℏ hp
    (input_density FiniteClockHandReadout.rhoPlus_density)
    (input_density FiniteClockHandReadout.rhoPlus_density) (fun _ => event) (fun _ => event_effect)
  change |freshTerminalProbability ω ℏ hℏ (twoPolicy t s) (input FiniteClockHandReadout.rhoPlus)-
      freshTerminalProbability ω ℏ hℏ (twoPolicy u v) (input FiniteClockHandReadout.rhoPlus)| ≤ _ at hh
  norm_num [traceDist_self] at hh
  exact hh

theorem noisy_physical_gap {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (u v : Duration)
    (hu : |(rightDuration hω:ℝ)-(u:ℝ)| ≤ 1/(100*ω))
    (hv : |(leftDuration hω:ℝ)-(v:ℝ)| ≤ 1/(100*ω)) :
    11/200 ≤ freshTerminalProbability ω ℏ hℏ (twoPolicy u v) (input FiniteClockHandReadout.rhoPlus)-
      terminalProbability ω ℏ hℏ (twoPolicy u v) (input FiniteClockHandReadout.rhoPlus) := by
  have hp := persistent_two_event_error hω hℏ (rightDuration hω) (leftDuration hω) u v hu hv
  have hf := fresh_two_event_error hω hℏ (rightDuration hω) (leftDuration hω) u v hu hv
  rw [(calibrated_events hω hℏ).2.1] at hp
  rw [(calibrated_events hω hℏ).2.2] at hf
  have hp' := (abs_le.mp hp).1
  have hf' := (abs_le.mp hf).2
  linarith

def quarterDuration {ω : ℝ} (hω : 0 < ω) : Duration := ⟨Real.pi/(2*ω),by positivity⟩
def zeroDuration : Duration := ⟨0,le_rfl⟩

theorem quarter_zero_events {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) :
    terminalProbability ω ℏ hℏ (twoPolicy (quarterDuration hω) zeroDuration)
      (input FiniteClockHandReadout.rhoPlus) = 9/10 ∧
    freshTerminalProbability ω ℏ hℏ (twoPolicy (quarterDuration hω) zeroDuration)
      (input FiniteClockHandReadout.rhoPlus) = 1 := by
  rw [persistent_event,fresh_event]
  simp only [keepProbability,quarterDuration,zeroDuration,Subtype.coe_mk,
    FiniteClockHandReadout.p_quarter hω.ne',FiniteClockHandReadout.p_zero]
  norm_num

theorem half_zero_events {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) :
    terminalProbability ω ℏ hℏ (twoPolicy (keepDuration hω) zeroDuration)
      (input FiniteClockHandReadout.rhoPlus) = 4/5 ∧
    freshTerminalProbability ω ℏ hℏ (twoPolicy (keepDuration hω) zeroDuration)
      (input FiniteClockHandReadout.rhoPlus) = 1 := by
  rw [persistent_event,fresh_event]
  simp only [keepProbability,keepDuration,zeroDuration,Subtype.coe_mk,
    FiniteClockHandReadout.p_keep hω.ne',FiniteClockHandReadout.p_zero]
  norm_num

/-- The +Y preparation is (1,i)/sqrt(2), with its complex coherence retained. -/
def rhoY : FiniteClockHandReadout.Mat := !![1/2,-Complex.I/2;Complex.I/2,1/2]

theorem rhoY_density : IsDensityOperator rhoY := by
  have he : rhoY = FiniteClockHandReadout.rho 1 1 (-Real.pi/2) := by
    have hr := FiniteClockHandReadout.rho_entries (by norm_num : (1:ℝ) ≠ 0) 1 (-Real.pi/2)
    simp only [one_mul,neg_div,Real.cos_neg,Real.sin_neg,
      Real.cos_pi_div_two,Real.sin_pi_div_two] at hr
    rw [show -Real.pi/2=-(Real.pi/2) by ring,hr]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [rhoY]
  rw [he]
  exact FiniteClockHandReadout.rho_density (by norm_num) 1 _

def yMass (θ : ℝ) (a : A) : ℝ := if a=0 then (1-Real.sin θ)/2 else (1+Real.sin θ)/2

theorem extract_y (θ : ℝ) (a : A) (Y : ReducedMat Unit) :
    extract Unit 1 1 θ a (FiniteClockControlledRetainedMemory.insert Unit Y rhoY) =
      (yMass θ a:ℂ) • Y := by
  ext bf dg
  rw [FinitePersistentMeasuredHandErrors.extract_trig Unit]
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl <;>
    norm_num [FiniteClockControlledRetainedMemory.insert,rhoY,sign,yMass] <;> push_cast <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem afterFirstLabel_density (a : A) : IsDensityOperator (afterFirstLabel a) := by
  have hd := prepareData_density 1 FiniteQutritRetainedClock.rho0_density
  exact ⟨FiniteClockControlledRetainedMemory.insert_positive Unit hd.1 (FiniteClockHandReadout.Q_density a).1,
    by rw [afterFirstLabel,FiniteClockControlledRetainedMemory.insert_trace,hd.2,
      FiniteClockHandReadout.Q_trace,mul_one]⟩

theorem y_branch {ℏ : ℝ} (hℏ : ℏ ≠ 0) (θ : ℝ) (a : A) (i : Fin 11) :
    (step Unit 1 ℏ θ hℏ).branch S Unit 22 (outcomeEquiv (a,i)) (input rhoY) =
      if i=FiniteQutritRetainedClock.noneLabel then (yMass θ a:ℂ) • afterFirstLabel a else 0 := by
  rw [branch_action,FinitePersistentMeasuredHandErrors.extract_frequency Unit hℏ]
  simp only [one_mul,input,extract_y,FiniteClockControlledRetainedMemory.dataBranch,
    krausMap_smul,FinitePersistentMeasuredHand.insert_smul]
  change (yMass θ a:ℂ) • FiniteClockControlledRetainedMemory.insert Unit
    (FiniteClockControlledRetainedMemory.dataBranch Unit a i (prepareData 0 FiniteQutritRetainedClock.rho0))
    (FiniteClockHandReadout.Q a) = _
  rw [data_first]
  split
  · rfl
  · rw [FiniteClockControlledRetainedMemoryExamples.insert_zero,smul_zero]

theorem y_stepDistance {ℏ : ℝ} (hℏ : ℏ ≠ 0) (θ φ : ℝ) :
    FiniteAdaptiveMapPerturbation.stepDistance S Unit 22 (step Unit 1 ℏ θ hℏ) (step Unit 1 ℏ φ hℏ)
      (input rhoY) = (∑ a : A, |yMass θ a-yMass φ a|)/2 := by
  unfold FiniteAdaptiveMapPerturbation.stepDistance
  rw [← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type,y_branch]
  have hi (a : A) (i : Fin 11) :
      traceNorm ((if i=FiniteQutritRetainedClock.noneLabel then (yMass θ a:ℂ) • afterFirstLabel a else 0)-
        (if i=FiniteQutritRetainedClock.noneLabel then (yMass φ a:ℂ) • afterFirstLabel a else 0)) =
      if i=FiniteQutritRetainedClock.noneLabel then |yMass θ a-yMass φ a| else 0 := by
    split
    · rw [← sub_smul,← Complex.ofReal_sub,FinitePersistentMeasuredHandErrors.traceNorm_real_smul,
        traceNorm_posSemidef (afterFirstLabel_density a).1,(afterFirstLabel_density a).2,Complex.one_re,mul_one]
    · simp [traceNorm_zero]
  simp only [hi,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- Equal fresh p does not control the actual persistent instrument on physical inputs. -/
theorem y_fresh_bound_falsifier {ℏ : ℝ} (hℏ : ℏ ≠ 0) :
    IsDensityOperator (input rhoY) ∧
    FiniteClockHandReadout.p 1 (Real.pi/2)=FiniteClockHandReadout.p 1 (3*Real.pi/2) ∧
    FiniteAdaptiveMapPerturbation.stepDistance S Unit 22
      (step Unit 1 ℏ (Real.pi/2) hℏ) (step Unit 1 ℏ (3*Real.pi/2) hℏ) (input rhoY)=1 := by
  refine ⟨input_density rhoY_density,?_,?_⟩
  · rw [show 3*Real.pi/2=Real.pi/2+Real.pi by ring]
    simp [FiniteClockHandReadout.p,Real.cos_add]
  · rw [y_stepDistance,show 3*Real.pi/2=Real.pi/2+Real.pi by ring]
    norm_num [Fin.sum_univ_two,yMass,Real.sin_add]

def measuredAdaptivePolicy {ω : ℝ} (hω : 0 < ω) (n : ℕ) : Policy (n+1) :=
  .node (quarterDuration hω) (fun o => feedbackPolicy hω n (outcomeEquiv.symm o).1)

theorem adaptive_two_table {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (a b : A) (i j : Fin 11) :
    run S Unit 22 (policyTree Unit ω ℏ hℏ (measuredAdaptivePolicy hω 1))
      (outcomeEquiv (a,i),outcomeEquiv (b,j),()) (input FiniteClockHandReadout.rhoPlus) =
      table ω (quarterDuration hω) (feedbackDuration hω a) a b i j := by
  simp only [measuredAdaptivePolicy,feedbackPolicy,policyTree,run,Equiv.symm_apply_apply]
  exact two_round_table hℏ ω (quarterDuration hω) (feedbackDuration hω a) a b i j

theorem table_trace (ω t s : ℝ) (a b : A) (i j : Fin 11) :
    (table ω t s a b i j).trace.re =
      if i=FiniteQutritRetainedClock.noneLabel then
        FiniteClockHandReadout.mass ω t a*transition ω s b a*(dataSecond b j).trace.re else 0 := by
  unfold table
  split
  · simp [Matrix.trace_smul,FiniteClockControlledRetainedMemory.insert_trace,
      FiniteClockHandReadout.Q_trace,Complex.mul_re]
  · simp

theorem dataSecond_micro_trace (k : Fin 10) :
    (dataSecond 0 (FiniteQutritRetainedClock.someLabel k)).trace.re = (micro k).trace.re := by
  simp only [dataSecond,FiniteQutritRetainedClock.someLabel,Equiv.symm_apply_apply,
    if_pos rfl,ite_true]
  rw [prepareData,FiniteQutritRetainedClock.preparation_trace,unitQutrit,Matrix.trace_kronecker]
  norm_num [Matrix.trace]

theorem dataSecond_none_trace :
    (dataSecond 1 FiniteQutritRetainedClock.noneLabel).trace.re=1 := by
  simpa only [dataSecond,show (1:A) ≠ 0 by decide,if_false,if_pos rfl,ite_true,
    (prepareData_density 1 FiniteQutritRetainedClock.rho0_density).2,Complex.one_re]

theorem adaptive_first_masses {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (a : A) :
    ((step Unit ω ℏ (quarterDuration hω) hℏ).branch S Unit 22
      (outcomeEquiv (a,FiniteQutritRetainedClock.noneLabel)) (input FiniteClockHandReadout.rhoPlus)).trace.re=1/2 := by
  have hp : FiniteClockHandReadout.p ω (quarterDuration hω)=1/2 := FiniteClockHandReadout.p_quarter hω.ne'
  have hm : FiniteClockHandReadout.mass ω (quarterDuration hω) a=1/2 := by
    unfold FiniteClockHandReadout.mass
    rw [hp]
    split <;> norm_num
  rw [first_branch,if_pos rfl,Matrix.trace_smul,(afterFirstLabel_density a).2,hm]
  norm_num

theorem adaptive_keep_both {ω : ℝ} (hω : 0 < ω) (a : A) :
    transition ω (feedbackDuration hω a) 0 a=3/4 := by
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl
  · simp only [feedbackDuration,if_pos rfl,transition,ite_true]
    rw [show FiniteClockHandReadout.p ω (leftDuration hω)=1/4 from FiniteClockHandReadout.p_left hω.ne']
    norm_num
  · simp only [feedbackDuration,show (1:A) ≠ 0 by decide,if_false,transition,
      show (0:A) ≠ 1 by decide]
    exact FiniteClockHandReadout.p_right hω.ne'

theorem adaptive_prefix_masses {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) :
    (run S Unit 22 (policyTree Unit ω ℏ hℏ (measuredAdaptivePolicy hω 1))
      (firstRecord,secondLeftRecord,()) (input FiniteClockHandReadout.rhoPlus)).trace.re=3/40 ∧
    (run S Unit 22 (policyTree Unit ω ℏ hℏ (measuredAdaptivePolicy hω 1))
      (firstRecord,secondRightRecord,()) (input FiniteClockHandReadout.rhoPlus)).trace.re=1/8 := by
  simp only [firstRecord,secondLeftRecord,secondRightRecord,adaptive_two_table,table_trace,
    if_pos rfl,dataSecond_micro_trace,dataSecond_none_trace]
  have hp : FiniteClockHandReadout.p ω (quarterDuration hω)=1/2 := FiniteClockHandReadout.p_quarter hω.ne'
  have hl : FiniteClockHandReadout.p ω (leftDuration hω)=1/4 := FiniteClockHandReadout.p_left hω.ne'
  rw [micro_weight]
  simp only [FiniteClockHandReadout.mass,feedbackDuration,transition,if_pos rfl,ite_true,
    show (1:A) ≠ 0 by decide,if_false]
  rw [hp,hl]
  norm_num [microWeight]

theorem adaptive_second_duration {ω : ℝ} (hω : 0 < ω) (n : ℕ) (a : A) :
    FiniteClockControlledRetainedMemory.durationAt (measuredAdaptivePolicy hω (n+1))
      ((0:Fin (n+1)).succ) (outcomeEquiv (a,FiniteQutritRetainedClock.noneLabel),()) =
      feedbackDuration hω a := by
  simp only [measuredAdaptivePolicy,FiniteClockControlledRetainedMemory.durationAt,
    Fin.cases_succ,feedbackPolicy,Fin.cases_zero,Equiv.symm_apply_apply]

theorem adaptive_third_durations {ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    FiniteClockControlledRetainedMemory.durationAt (measuredAdaptivePolicy hω (n+2))
      ((0:Fin (n+1)).succ.succ) (firstRecord,secondLeftRecord,())=leftDuration hω ∧
    FiniteClockControlledRetainedMemory.durationAt (measuredAdaptivePolicy hω (n+2))
      ((0:Fin (n+1)).succ.succ) (firstRecord,secondRightRecord,())=rightDuration hω := by
  simp only [measuredAdaptivePolicy,FiniteClockControlledRetainedMemory.durationAt,
    Fin.cases_succ,feedbackPolicy,Fin.cases_zero]
  simp [firstRecord,secondLeftRecord,secondRightRecord,feedbackDuration]

theorem adaptive_reachable_third {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) (n : ℕ) :
    0 < (run S Unit 22 (policyTree Unit ω ℏ hℏ
      (truncatePolicy (measuredAdaptivePolicy hω (n+2)) 2 (by omega)))
      (firstRecord,secondLeftRecord,()) (input FiniteClockHandReadout.rhoPlus)).trace.re ∧
    0 < (run S Unit 22 (policyTree Unit ω ℏ hℏ
      (truncatePolicy (measuredAdaptivePolicy hω (n+2)) 2 (by omega)))
      (firstRecord,secondRightRecord,()) (input FiniteClockHandReadout.rhoPlus)).trace.re ∧
    FiniteClockControlledRetainedMemory.durationAt (measuredAdaptivePolicy hω (n+2))
      ((0:Fin (n+1)).succ.succ) (firstRecord,secondLeftRecord,()) ≠
    FiniteClockControlledRetainedMemory.durationAt (measuredAdaptivePolicy hω (n+2))
      ((0:Fin (n+1)).succ.succ) (firstRecord,secondRightRecord,()) := by
  have ht : truncatePolicy (measuredAdaptivePolicy hω (n+2)) 2 (by omega)=measuredAdaptivePolicy hω 1 := rfl
  rw [ht]
  have hm := adaptive_prefix_masses hω hℏ
  refine ⟨by rw [hm.1]; norm_num,by rw [hm.2]; norm_num,?_⟩
  rw [(adaptive_third_durations hω n).1,(adaptive_third_durations hω n).2]
  intro he
  have hv := congrArg Subtype.val he
  change Real.pi/(3*ω)=2*Real.pi/(3*ω) at hv
  have hd := (div_lt_div_iff_of_pos_right (by positivity : 0<3*ω)).2
    (show Real.pi<2*Real.pi by linarith [Real.pi_pos])
  exact (ne_of_lt hd) hv

def fullTurnDuration {ω : ℝ} (hω : 0 < ω) (k : ℕ) : Duration :=
  ⟨(k:ℝ)*(2*Real.pi/ω),by positivity⟩

def oddHalfDuration {ω : ℝ} (hω : 0 < ω) (k : ℕ) : Duration :=
  ⟨Real.pi/ω+(k:ℝ)*(2*Real.pi/ω),by positivity⟩

theorem fullTurn_mass {ω : ℝ} (hω : 0 < ω) (k : ℕ) :
    FiniteClockHandReadout.p ω (fullTurnDuration hω k) = 0 := by
  induction k with
  | zero => simp only [fullTurnDuration,Subtype.coe_mk,Nat.cast_zero,zero_mul,FiniteClockHandReadout.p_zero]
  | succ k ih =>
    change FiniteClockHandReadout.p ω (((k+1:ℕ):ℝ)*(2*Real.pi/ω)) = 0
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,FiniteClockHandReadout.p_periodic hω.ne']
    exact ih

theorem oddHalf_mass {ω : ℝ} (hω : 0 < ω) (k : ℕ) :
    FiniteClockHandReadout.p ω (oddHalfDuration hω k) = 1 :=
  FiniteClockHandReadout.keep_alias hω.ne' k

def fullTurnPolicy {ω : ℝ} (hω : 0 < ω) : (ks : List ℕ) → Policy ks.length
  | [] => .done
  | k::ks => .node (fullTurnDuration hω k) (fun _ => fullTurnPolicy hω ks)

def recoveryPolicy {ω : ℝ} (hω : 0 < ω) (k : ℕ) (ks : List ℕ) : Policy (ks.length+1) :=
  .node (oddHalfDuration hω k) (fun _ => fullTurnPolicy hω ks)

variable (F : Type*) [Fintype F] [DecidableEq F]

theorem zero_phase_keep {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ)
    (hp : FiniteClockHandReadout.p ω t=0) (a : A) (i : Fin 11) (Y : ReducedMat F) :
    (step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 0)) =
      if a=0 then FiniteClockControlledRetainedMemory.insert F
        ((localStep B F 11 FiniteQutritRetainedClock.instrument).branch B F 11 i Y)
        (FiniteClockHandReadout.Q 0) else 0 := by
  rw [branch_posterior]
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl <;>
    simp [transition,hp,FiniteClockControlledRetainedMemory.dataBranch_keep]

theorem first_phase_keep {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ)
    (hp : FiniteClockHandReadout.p ω t=1) (a : A) (i : Fin 11) (Y : ReducedMat F) :
    (step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 1)) =
      if a=0 then FiniteClockControlledRetainedMemory.insert F
        ((localStep B F 11 FiniteQutritRetainedClock.instrument).branch B F 11 i Y)
        (FiniteClockHandReadout.Q 0) else 0 := by
  rw [branch_posterior]
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl <;>
    simp [transition,hp,FiniteClockControlledRetainedMemory.dataBranch_keep]

theorem fullTurn_injected {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (ks : List ℕ) (h : History 11 ks.length) (Y : ReducedMat F) :
    run S F 22 (policyTree F ω ℏ hℏ (fullTurnPolicy hω ks))
      (FiniteClockControlledRetainedMemory.injectRecord ks.length h)
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 0)) =
      FiniteClockControlledRetainedMemory.insert F
        (run B F 11 (FiniteQutritRetainedClock.recordTree F ks.length) h Y) (FiniteClockHandReadout.Q 0) := by
  induction ks generalizing Y with
  | nil => cases h; rfl
  | cons k ks ih =>
    rcases h with ⟨i,h⟩
    change run S F 22 (policyTree F ω ℏ hℏ (fullTurnPolicy hω ks))
      (FiniteClockControlledRetainedMemory.injectRecord ks.length h)
      ((step F ω ℏ (fullTurnDuration hω k) hℏ).branch S F 22 (outcomeEquiv (0,i))
        (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 0))) = _
    rw [zero_phase_keep F hℏ ω _ (fullTurn_mass hω k),if_pos rfl,ih]
    rfl

/-- An odd half-turn prepares Q0 once; all subsequent full turns preserve it. -/
theorem recovery_injected {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (k : ℕ) (ks : List ℕ) (h : History 11 (ks.length+1)) (Y : ReducedMat F) :
    run S F 22 (policyTree F ω ℏ hℏ (recoveryPolicy hω k ks))
      (FiniteClockControlledRetainedMemory.injectRecord (ks.length+1) h)
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 1)) =
      FiniteClockControlledRetainedMemory.insert F
        (run B F 11 (FiniteQutritRetainedClock.recordTree F (ks.length+1)) h Y) (FiniteClockHandReadout.Q 0) := by
  rcases h with ⟨i,h⟩
  change run S F 22 (policyTree F ω ℏ hℏ (fullTurnPolicy hω ks))
    (FiniteClockControlledRetainedMemory.injectRecord ks.length h)
    ((step F ω ℏ (oddHalfDuration hω k) hℏ).branch S F 22 (outcomeEquiv (0,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 1))) = _
  rw [first_phase_keep F hℏ ω _ (oddHalf_mass hω k),if_pos rfl,fullTurn_injected]
  rfl

theorem fullTurn_forbidden {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (ks : List ℕ) (h : History 22 ks.length)
    (hn : h ∉ Set.range (FiniteClockControlledRetainedMemory.injectRecord ks.length)) (Y : ReducedMat F) :
    run S F 22 (policyTree F ω ℏ hℏ (fullTurnPolicy hω ks)) h
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 0)) = 0 := by
  induction ks generalizing Y with
  | nil => exact False.elim (hn ⟨(),by cases h; rfl⟩)
  | cons k ks ih =>
    rcases h with ⟨o,h⟩
    obtain ⟨⟨a,i⟩,rfl⟩ := outcomeEquiv.surjective o
    change run S F 22 (policyTree F ω ℏ hℏ (fullTurnPolicy hω ks)) h
      ((step F ω ℏ (fullTurnDuration hω k) hℏ).branch S F 22 (outcomeEquiv (a,i))
        (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 0))) = 0
    rw [zero_phase_keep F hℏ ω _ (fullTurn_mass hω k)]
    rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl
    · rw [if_pos rfl]
      apply ih
      rintro ⟨w,hw⟩
      exact hn ⟨(i,w),by simp [FiniteClockControlledRetainedMemory.injectRecord,hw]⟩
    · rw [if_neg (by decide),run_zero]

theorem recovery_forbidden {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (k : ℕ) (ks : List ℕ) (h : History 22 (ks.length+1))
    (hn : h ∉ Set.range (FiniteClockControlledRetainedMemory.injectRecord (ks.length+1))) (Y : ReducedMat F) :
    run S F 22 (policyTree F ω ℏ hℏ (recoveryPolicy hω k ks)) h
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 1)) = 0 := by
  rcases h with ⟨o,h⟩
  obtain ⟨⟨a,i⟩,rfl⟩ := outcomeEquiv.surjective o
  change run S F 22 (policyTree F ω ℏ hℏ (fullTurnPolicy hω ks)) h
    ((step F ω ℏ (oddHalfDuration hω k) hℏ).branch S F 22 (outcomeEquiv (a,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 1))) = 0
  rw [first_phase_keep F hℏ ω _ (oddHalf_mass hω k)]
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl
  · rw [if_pos rfl]
    apply fullTurn_forbidden F hω hℏ
    rintro ⟨w,hw⟩
    exact hn ⟨(i,w),by simp [FiniteClockControlledRetainedMemory.injectRecord,hw]⟩
  · rw [if_neg (by decide),run_zero]

theorem recovery_all_records {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (k : ℕ) (ks : List ℕ) (Y : ReducedMat F) :
    (∑ h, run S F 22 (policyTree F ω ℏ hℏ (recoveryPolicy hω k ks)) h
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 1))) =
      FiniteClockControlledRetainedMemory.insert F
        (FiniteQutritRetainedClock.amplifiedJointIterate F (ks.length+1) Y) (FiniteClockHandReadout.Q 0) := by
  rw [← FiniteQutritRetainedClock.all_records_sum,FiniteClockControlledRetainedMemory.insert_sum]
  symm
  exact Fintype.sum_of_injective
    (FiniteClockControlledRetainedMemory.injectRecord (ks.length+1))
    (FiniteClockControlledRetainedMemory.injectRecord_injective (ks.length+1)) _ _
    (fun h hn => recovery_forbidden F hω hℏ k ks h hn Y)
    (fun h => (recovery_injected F hω hℏ k ks h Y).symm)

theorem recovery_reduced {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0)
    (k : ℕ) (ks : List ℕ) (Y : ReducedMat F) :
    FiniteClockControlledRetainedMemory.handTrace F
      (∑ h, run S F 22 (policyTree F ω ℏ hℏ (recoveryPolicy hω k ks)) h
        (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 1))) =
      FiniteQutritRetainedClock.amplifiedJointIterate F (ks.length+1) Y := by
  rw [recovery_all_records F hω hℏ,FiniteClockControlledRetainedMemory.handTrace_insert,
    FiniteClockHandReadout.Q_trace,one_smul]

open FinitePersistentMeasuredHandErrors

def handEffect (θ : ℝ) (a : A) : FiniteClockHandReadout.Mat :=
  (FiniteClockHandReadout.U 1 1 θ)ᴴ * FiniteClockHandReadout.Q a * FiniteClockHandReadout.U 1 1 θ

theorem U_mul_adjoint (θ : ℝ) :
    FiniteClockHandReadout.U 1 1 θ*(FiniteClockHandReadout.U 1 1 θ)ᴴ=1 := by
  simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp
    (FiniteClockHandReadout.U_unitary (by norm_num : (1:ℝ) ≠ 0) 1 θ)

theorem handEffect_density (θ : ℝ) (a : A) : IsDensityOperator (handEffect θ a) := by
  refine ⟨(FiniteClockHandReadout.Q_density a).1.conjTranspose_mul_mul_same _,?_⟩
  rw [handEffect,Matrix.trace_mul_cycle,U_mul_adjoint,Matrix.one_mul,FiniteClockHandReadout.Q_trace]

theorem handEffect_sandwich (θ : ℝ) (a b : A) :
    handOperator 1 1 θ a*handEffect θ b*(handOperator 1 1 θ a)ᴴ =
      if a=b then FiniteClockHandReadout.Q a else 0 := by
  simp only [handOperator,handEffect,Matrix.conjTranspose_mul,FiniteClockHandReadout.Q_adjoint,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (FiniteClockHandReadout.U 1 1 θ),U_mul_adjoint,Matrix.one_mul]
  rw [← Matrix.mul_assoc (FiniteClockHandReadout.U 1 1 θ),U_mul_adjoint,Matrix.one_mul]
  rw [← Matrix.mul_assoc,FiniteClockHandReadout.Q_mul]
  split
  · simp [FiniteClockHandReadout.Q_mul]
  · simp

theorem extract_product (ω ℏ t : ℝ) (a : A) (Y : ReducedMat F)
    (σ : FiniteClockHandReadout.Mat) :
    extract F ω ℏ t a (FiniteClockControlledRetainedMemory.insert F Y σ) =
      (2*(handOperator ω ℏ t a*σ*(handOperator ω ℏ t a)ᴴ) 1 1) • Y := by
  ext bf dg
  rw [extract_entry]
  simp [FiniteClockControlledRetainedMemory.insert,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fin.sum_univ_two]
  ring

theorem Q_last_diagonal (a : A) : FiniteClockHandReadout.Q a 1 1=(1/2:ℂ) := by
  fin_cases a <;> norm_num [FiniteClockHandReadout.Q]

theorem extract_effect (θ : ℝ) (a b : A) (Y : ReducedMat F) :
    extract F 1 1 θ a (FiniteClockControlledRetainedMemory.insert F Y (handEffect θ b)) =
      if a=b then Y else 0 := by
  rw [extract_product,handEffect_sandwich]
  split
  · rw [Q_last_diagonal]
    norm_num
  · simp

def plusLabel (θ φ : ℝ) : A := if 0 ≤ Real.sin ((θ-φ)/2) then 0 else 1

def productAttainer (θ φ : ℝ) (Y : ReducedMat F) : FullMat F :=
  FiniteClockControlledRetainedMemory.insert F Y (handEffect (midpointPhase θ φ) (plusLabel θ φ))

theorem productAttainer_density (θ φ : ℝ) {Y : ReducedMat F} (hY : IsDensityOperator Y) :
    IsDensityOperator (productAttainer F θ φ Y) := by
  have hh := handEffect_density (midpointPhase θ φ) (plusLabel θ φ)
  exact ⟨FiniteClockControlledRetainedMemory.insert_positive F hY.1 hh.1,
    by rw [productAttainer,FiniteClockControlledRetainedMemory.insert_trace,hY.2,hh.2,mul_one]⟩

theorem product_spectral (θ φ : ℝ) (Y : ReducedMat F) :
    Vplus F θ φ (productAttainer F θ φ Y)=Y ∧
    Vminus F θ φ (productAttainer F θ φ Y)=0 := by
  unfold Vplus Vminus productAttainer plusLabel
  split <;> simp [extract_effect]

theorem measured_data_smul (a : A) (i : Fin 11) (c : ℂ) (Y : ReducedMat F) :
    FiniteClockControlledRetainedMemory.dataBranch F a i (c • Y) =
      c • FiniteClockControlledRetainedMemory.dataBranch F a i Y := krausMap_smul _ _ _

theorem product_attains (θ φ : ℝ) {Y : ReducedMat F} (hY : Y.PosSemidef) :
    FiniteAdaptiveMapPerturbation.stepDistance S F 22
      (step F 1 1 θ (by norm_num)) (step F 1 1 φ (by norm_num))
      (productAttainer F θ φ Y) = eta θ φ*Y.trace.re := by
  have hv := product_spectral F θ φ Y
  have hi (a : A) (i : Fin 11) :
      traceNorm ((step F 1 1 θ (by norm_num)).branch S F 22 (outcomeEquiv (a,i))
        (productAttainer F θ φ Y)-
        (step F 1 1 φ (by norm_num)).branch S F 22 (outcomeEquiv (a,i))
          (productAttainer F θ φ Y)) =
      eta θ φ*(FiniteClockControlledRetainedMemory.dataBranch F a i Y).trace.re := by
    rw [branch_action,branch_action,← insert_sub,← dataBranch_sub,spectral_arm_difference,hv.1,hv.2]
    rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl
    · simp only [if_pos rfl,ite_true,sub_zero]
      rw [measured_data_smul F,FinitePersistentMeasuredHand.insert_smul,traceNorm_real_smul,
        abs_of_nonneg (show 0 ≤ eta θ φ from abs_nonneg _),insert_traceNorm,
        traceNorm_posSemidef (FiniteClockControlledRetainedMemory.dataBranch_positive F 0 i hY)]
    · simp only [show (1:A) ≠ 0 by decide,if_false,zero_sub]
      rw [show (eta θ φ:ℂ) • -Y = ((-eta θ φ:ℝ):ℂ) • Y by simp]
      rw [measured_data_smul F,
        FinitePersistentMeasuredHand.insert_smul,traceNorm_real_smul,abs_neg,
        abs_of_nonneg (show 0 ≤ eta θ φ from abs_nonneg _),insert_traceNorm,
        traceNorm_posSemidef (FiniteClockControlledRetainedMemory.dataBranch_positive F 1 i hY)]
  unfold FiniteAdaptiveMapPerturbation.stepDistance
  rw [← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type,hi,← Finset.mul_sum,← Complex.re_sum,
    FiniteClockControlledRetainedMemory.dataBranch_sum_trace,Fin.sum_univ_two]
  norm_num [Complex.mul_re]
  ring

theorem handEffect_row (θ : ℝ) (a u w : A) :
    handEffect θ a u w = 2*handOperator 1 1 θ a 1 w*star (handOperator 1 1 θ a 1 u) := by
  change ((FiniteClockHandReadout.U 1 1 θ)ᴴ*FiniteClockHandReadout.Q a*
    FiniteClockHandReadout.U 1 1 θ) u w = _
  rw [← hand_gram]
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl <;>
    simp [handOperator,FiniteClockHandReadout.Q,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_two,Matrix.vecMul,dotProduct] <;> ring_nf <;> simp only [starRingEnd_apply,star_ofNat] <;> ring

theorem extract_hand_single (θ : ℝ) (a u w : A) (Y : ReducedMat F) :
    extract F 1 1 θ a (FiniteClockControlledRetainedMemory.insert F Y (Matrix.single w u 1)) =
      handEffect θ a u w • Y := by
  rw [extract_product,handEffect_row]
  congr 1
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.single,Fin.sum_univ_two]
  fin_cases u <;> fin_cases w <;> norm_num <;> ring

/-- The actual effect difference has the same spectral compressions as the full instrument. -/
theorem handEffect_spectral (θ φ : ℝ) :
    handEffect θ 0-handEffect φ 0 = (Real.sin ((θ-φ)/2):ℂ) •
      (handEffect (midpointPhase θ φ) 0-handEffect (midpointPhase θ φ) 1) := by
  let r : B × Unit := (((0:FiniteQutritPhysicalMemory.Q),(0:A)),())
  let Y : ReducedMat Unit := Matrix.single r r 1
  ext u w
  have h := compression_signed_difference Unit θ φ
    (FiniteClockControlledRetainedMemory.insert Unit Y (Matrix.single w u 1))
  simp only [extract_hand_single] at h
  have he := congrFun (congrFun h r) r
  simpa [Y,Matrix.single] using he

theorem handEffect_mul (θ : ℝ) (a b : A) :
    handEffect θ a*handEffect θ b = if a=b then handEffect θ a else 0 := by
  simp only [handEffect,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (FiniteClockHandReadout.U 1 1 θ),U_mul_adjoint,Matrix.one_mul]
  rw [← Matrix.mul_assoc (FiniteClockHandReadout.Q a),FiniteClockHandReadout.Q_mul]
  split <;> simp [Matrix.mul_assoc]

theorem handEffect_sum (θ : ℝ) : handEffect θ 0+handEffect θ 1=1 := by
  have hq : FiniteClockHandReadout.Q 0+FiniteClockHandReadout.Q 1=1 := by
    simpa only [Fin.sum_univ_two] using FiniteClockHandReadout.Q_complete
  have hu : (FiniteClockHandReadout.U 1 1 θ)ᴴ*FiniteClockHandReadout.U 1 1 θ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp
      (FiniteClockHandReadout.U_unitary (by norm_num : (1:ℝ) ≠ 0) 1 θ)
  simp only [handEffect,← Matrix.mul_add,← Matrix.add_mul,hq,Matrix.mul_one,hu]

theorem handEffect_involution (θ : ℝ) :
    (handEffect θ 0-handEffect θ 1)*(handEffect θ 0-handEffect θ 1)=1 := by
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub]
  simp only [handEffect_mul,if_pos rfl,show (0:A) ≠ 1 by decide,
    show (1:A) ≠ 0 by decide,if_false,sub_zero,zero_sub,sub_neg_eq_add]
  exact handEffect_sum θ

/-- Squaring the actual effect difference gives exactly eta² I, including eta=0. -/
theorem handEffect_difference_square (θ φ : ℝ) :
    (handEffect θ 0-handEffect φ 0)*(handEffect θ 0-handEffect φ 0) =
      ((eta θ φ)^2:ℂ) • (1 : FiniteClockHandReadout.Mat) := by
  rw [handEffect_spectral,Matrix.smul_mul,Matrix.mul_smul,smul_smul,handEffect_involution]
  congr 1
  have h : Real.sin ((θ-φ)/2)^2=(eta θ φ)^2 := (sq_abs _).symm
  exact_mod_cast (show Real.sin ((θ-φ)/2)*Real.sin ((θ-φ)/2)=(eta θ φ)^2 by
    simpa only [pow_two] using h)

theorem single_density {D : Type*} [Fintype D] [DecidableEq D] (r : D) :
    IsDensityOperator (Matrix.single r r (1:ℂ)) := by
  have hs : (Matrix.single r r (1:ℂ))ᴴ*Matrix.single r r 1=Matrix.single r r 1 := by
    ext i j
    by_cases hi : r=i
    · subst i
      by_cases hj : r=j
      · subst j
        simp [Matrix.conjTranspose_apply,Matrix.mul_apply,Matrix.single,eq_comm]
      · simp [Matrix.conjTranspose_apply,Matrix.mul_apply,Matrix.single,hj]
    · simp [Matrix.conjTranspose_apply,Matrix.mul_apply,Matrix.single,hi]
  refine ⟨?_,?_⟩
  · have h := Matrix.posSemidef_conjTranspose_mul_self (Matrix.single r r (1:ℂ))
    rwa [hs] at h
  · simp [Matrix.trace,Matrix.single]

/-- Nonempty spectators admit normalized actual eigenstate/product-data sharpness witnesses. -/
theorem sharp_attainer_nonempty [Nonempty F] (θ φ : ℝ) :
    ∃ Z : FullMat F, IsDensityOperator Z ∧
      FiniteAdaptiveMapPerturbation.stepDistance S F 22
        (step F 1 1 θ (by norm_num)) (step F 1 1 φ (by norm_num)) Z=eta θ φ := by
  obtain ⟨f⟩ := ‹Nonempty F›
  let r : B × F := (((0:FiniteQutritPhysicalMemory.Q),(0:A)),f)
  have hY := single_density r
  refine ⟨productAttainer F θ φ (Matrix.single r r 1),productAttainer_density F θ φ hY,?_⟩
  rw [product_attains F θ φ hY.1,hY.2,Complex.one_re,mul_one]

def normalized {D : Type*} [Fintype D] (X : Matrix D D ℂ) : Matrix D D ℂ :=
  ((X.trace.re:ℂ)⁻¹) • X

theorem normalized_density {D : Type*} [Fintype D] [DecidableEq D]
    {X : Matrix D D ℂ} (hX : X.PosSemidef) (hm : 0<X.trace.re) : IsDensityOperator (normalized X) := by
  have ht : X.trace=(X.trace.re:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using trace_im_zero_of_posSemidef hX
  refine ⟨?_,?_⟩
  · unfold normalized
    rw [← Complex.ofReal_inv]
    exact hX.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hm.le))
  · rw [normalized,Matrix.trace_smul,ht]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hm.ne')

theorem normalized_insert (Y : ReducedMat F) (a : A) :
    normalized (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)) =
      FiniteClockControlledRetainedMemory.insert F (normalized Y) (FiniteClockHandReadout.Q a) := by
  rw [normalized,FiniteClockControlledRetainedMemory.insert_trace,
    FiniteClockHandReadout.Q_trace,mul_one,normalized,FinitePersistentMeasuredHand.insert_smul]

theorem conditioned_branch {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) (i : Fin 11)
    {Z : FullMat F} (hZ : Z.PosSemidef)
    (hm : 0<((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z).trace.re) :
    IsDensityOperator (normalized ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z)) ∧
    normalized ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z) =
      FiniteClockControlledRetainedMemory.insert F
        (normalized (FiniteClockControlledRetainedMemory.dataBranch F a i (extract F ω ℏ t a Z)))
        (FiniteClockHandReadout.Q a) := by
  refine ⟨normalized_density (branch_positive F hℏ ω t _ hZ) hm,?_⟩
  rw [branch_action,normalized_insert]

theorem conditional_transition {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (b a : A)
    {Y : ReducedMat F} (hY : Y.PosSemidef) (hm : 0<Y.trace.re) :
    (∑ i : Fin 11, ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (b,i))
      (normalized (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)))).trace.re) =
      transition ω t b a := by
  rw [normalized_insert,← Complex.re_sum,arm_trace,extract_insert,
    Matrix.trace_smul,(normalized_density hY hm).2]
  · simp
  · exact hℏ

def finalLabel : (n : ℕ) → History 22 (n+1) → A
  | 0, (o,_) => (outcomeEquiv.symm o).1
  | n+1, (_,h) => finalLabel n h

/-- Every actual positive-depth record is in its measured sector, even if its mass is zero. -/
theorem run_sector {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) (n : ℕ) (P : Policy (n+1))
    (h : History 22 (n+1)) {Z : FullMat F} (hZ : Z.PosSemidef) :
    ∃ Y : ReducedMat F, Y.PosSemidef ∧
      run S F 22 (policyTree F ω ℏ hℏ P) h Z =
        FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q (finalLabel n h)) := by
  induction n generalizing Z with
  | zero =>
    cases P with | node t next =>
      obtain ⟨rfl⟩ := show next = fun _ => FiniteClockControlledRetainedMemory.Policy.done from by funext o; cases next o; rfl
      rcases h with ⟨o,h⟩
      cases h
      obtain ⟨⟨a,i⟩,rfl⟩ := outcomeEquiv.surjective o
      refine ⟨FiniteClockControlledRetainedMemory.dataBranch F a i (extract F ω ℏ t a Z),
        FiniteClockControlledRetainedMemory.dataBranch_positive F a i (extract_positive F ω ℏ t a hZ),?_⟩
      simpa only [policyTree,run,finalLabel,Equiv.symm_apply_apply] using branch_action F hℏ ω t a i Z
  | succ n ih =>
    cases P with | node t next =>
      rcases h with ⟨o,h⟩
      exact ih (next o) h (branch_positive F hℏ ω t o hZ)

theorem reachable_conditional_transition {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) (n : ℕ) (P : Policy (n+1))
    (h : History 22 (n+1)) {Z : FullMat F} (hZ : Z.PosSemidef)
    (hm : 0<(run S F 22 (policyTree F ω ℏ hℏ P) h Z).trace.re) (t : ℝ) (b : A) :
    (∑ i : Fin 11, ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (b,i))
      (normalized (run S F 22 (policyTree F ω ℏ hℏ P) h Z))).trace.re) =
      transition ω t b (finalLabel n h) := by
  obtain ⟨Y,hY,he⟩ := run_sector F hℏ n P h hZ
  rw [he] at hm ⊢
  rw [FiniteClockControlledRetainedMemory.insert_trace,FiniteClockHandReadout.Q_trace,mul_one] at hm
  exact conditional_transition F hℏ ω t b _ hY hm

/-- Four amplitudes ±1/2 pair qutrit0/1 at old parity0 with the two X eigenvectors. -/
def bellRect : Matrix S Unit ℂ := fun z _ =>
  if z.1.2=0 then
    if z.1.1=0 then (if z.2=0 then -1/2 else 1/2)
    else if z.1.1=1 then 1/2 else 0
  else 0

def bell : JointMat := bellRect*bellRectᴴ

theorem bell_density : IsDensityOperator bell := by
  refine ⟨?_,?_⟩
  · simpa only [bell,Matrix.conjTranspose_conjTranspose] using
      Matrix.posSemidef_conjTranspose_mul_self bellRectᴴ
  · rw [bell,Matrix.trace_mul_comm]
    simp only [Matrix.trace,Fintype.sum_unique,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply]
    change (∑ z : S,star (bellRect z ())*bellRect z ())=1
    norm_num [bellRect,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three,
      Complex.star_def,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]
    simp only [starRingEnd_apply,star_ofNat]
    norm_num


def handRotation (θ : ℝ) : JointMat := (1:DataMat) ⊗ₖ (FiniteClockHandReadout.U 1 1 θ)ᴴ

theorem handRotation_normalized (θ : ℝ) : (handRotation θ)ᴴ*handRotation θ=1 := by
  simp only [handRotation,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    Matrix.conjTranspose_conjTranspose,← Matrix.mul_kronecker_mul,Matrix.one_mul,
    U_mul_adjoint,Matrix.one_kronecker_one]

def rotatedBell (θ : ℝ) : JointMat := handRotation θ*bell*(handRotation θ)ᴴ

theorem rotatedBell_density (θ : ℝ) : IsDensityOperator (rotatedBell θ) := by
  refine ⟨?_,?_⟩
  · simpa only [rotatedBell,Matrix.conjTranspose_conjTranspose] using
      bell_density.1.conjTranspose_mul_mul_same (handRotation θ)ᴴ
  · rw [rotatedBell,Matrix.trace_mul_cycle,handRotation_normalized,Matrix.one_mul,bell_density.2]

def baseCompression (a : A) (Z : JointMat) : DataMat := (2:ℂ) • ((J a)ᴴ*Z*J a)

theorem C_rotation (θ : ℝ) (a : A) : C 1 1 θ a=handRotation θ*J a := by
  ext ⟨b,u⟩ d
  change (1:DataMat) b d * ((FiniteClockHandReadout.Q a*FiniteClockHandReadout.U 1 1 θ)ᴴ) u 1 = _
  rw [Matrix.conjTranspose_mul,FiniteClockHandReadout.Q_adjoint]
  by_cases hb : b=d <;> simp [handRotation,FinitePersistentMeasuredHand.J,Matrix.mul_apply,
    Fintype.sum_prod_type,Matrix.one_apply,apply_ite,hb,eq_comm]


theorem extract_tensor (θ : ℝ) (a : A) (Z : JointMat) (σ : Matrix F F ℂ) :
    extract F 1 1 θ a (Z ⊗ₖ σ) = ((2:ℂ) • ((C 1 1 θ a)ᴴ*Z*C 1 1 θ a)) ⊗ₖ σ := by
  simp only [extract,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one,Matrix.smul_kronecker]

theorem extract_rotatedBell (θ : ℝ) (a : A) (σ : Matrix F F ℂ) :
    extract F 1 1 θ a (rotatedBell θ ⊗ₖ σ)=baseCompression a bell ⊗ₖ σ := by
  rw [extract_tensor,C_rotation,rotatedBell]
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (handRotation θ)ᴴ,handRotation_normalized,Matrix.one_mul]
  rw [← Matrix.mul_assoc (handRotation θ)ᴴ,handRotation_normalized,Matrix.one_mul]
  simp only [baseCompression,Matrix.mul_assoc]

def dataPoint (a : A) : B := (⟨a.val,lt_trans a.isLt (by decide : 2<3)⟩,0)
def basisRect (a : A) : Matrix B Unit ℂ := fun b _ => if b=dataPoint a then 1 else 0

theorem bell_compressed_vector (a : A) : (J a)ᴴ*bellRect=(1/2:ℂ) • basisRect a := by
  ext ⟨q,c⟩ f
  cases f
  have he : ((FinitePersistentMeasuredHand.J a)ᴴ*bellRect) (q,c) ()=
      ∑ u : A, star (FiniteClockHandReadout.Q a u 1)*bellRect ((q,c),u) () := by
    simp [FinitePersistentMeasuredHand.J,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_prod_type,Matrix.one_apply,apply_ite,eq_comm]
  rw [he]
  fin_cases a <;> fin_cases q <;> fin_cases c <;>
    norm_num [bellRect,basisRect,dataPoint,Fin.sum_univ_two,FiniteClockHandReadout.Q,
      Complex.star_def,star_ofNat,Matrix.smul_apply,smul_eq_mul,show (2:Fin 3) ≠ 0 by decide,
      show (2:Fin 3) ≠ 1 by decide]
  all_goals simp only [starRingEnd_apply,star_ofNat]
  all_goals norm_num


theorem basisRect_outer (a : A) : basisRect a*(basisRect a)ᴴ=Matrix.single (dataPoint a) (dataPoint a) 1 := by
  ext b d
  by_cases hb : b=dataPoint a <;> by_cases hd : d=dataPoint a <;>
    simp [basisRect,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.single,hb,hd,eq_comm]

theorem bell_compressions (a : A) :
    baseCompression a bell=(1/2:ℂ) • Matrix.single (dataPoint a) (dataPoint a) 1 := by
  have he : (J a)ᴴ*(bellRect*bellRectᴴ)*J a=((J a)ᴴ*bellRect)*((J a)ᴴ*bellRect)ᴴ := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [baseCompression,bell,he,bell_compressed_vector,Matrix.conjTranspose_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,basisRect_outer,smul_smul]
  norm_num

/-- Tensor the same pure spectator state onto the actual entangled eigenvector preparation. -/
def entangledAttainer (θ φ : ℝ) (f : F) : FullMat F :=
  rotatedBell (midpointPhase θ φ) ⊗ₖ Matrix.single f f 1

theorem entangledAttainer_density (θ φ : ℝ) (f : F) :
    IsDensityOperator (entangledAttainer F θ φ f) := by
  have hb := rotatedBell_density (midpointPhase θ φ)
  have hf := single_density f
  exact ⟨hb.1.kronecker hf.1,by rw [entangledAttainer,Matrix.trace_kronecker,hb.2,hf.2,mul_one]⟩

theorem entangled_compressions (θ φ : ℝ) (f : F) (a : A) :
    extract F 1 1 (midpointPhase θ φ) a (entangledAttainer F θ φ f) =
      ((1/2:ℂ) • Matrix.single (dataPoint a) (dataPoint a) 1) ⊗ₖ Matrix.single f f 1 := by
  rw [entangledAttainer,extract_rotatedBell,bell_compressions]


/-- A real diagonal norm, proved by the positive square root guard. -/
theorem real_diagonal_norm {D : Type*} [Fintype D] [DecidableEq D] (d : D → ℝ) :
    traceNorm (Matrix.diagonal (fun i => (d i:ℂ)))=∑ i,|d i| := by
  have ha : absOp (Matrix.diagonal (fun i => (d i:ℂ))) =
      Matrix.diagonal (fun i => ((|d i|:ℝ):ℂ)) := by
    refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _) ?_ ?_
    · exact Matrix.PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (abs_nonneg _))
    · rw [absOp_mul_self]
      simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      change star (d i:ℂ)*(d i:ℂ)=((|d i|:ℝ):ℂ)*((|d i|:ℝ):ℂ)
      simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul]
      congr 1
      nlinarith [sq_abs (d i)]
  rw [traceNorm_eq_trace_absOp,ha,Matrix.trace_diagonal,Complex.re_sum]
  rfl

def signedQ : FiniteQutritPhysicalMemory.Mat := Matrix.diagonal ![(1/2:ℂ),-1/2,0]
def signedData (c : A) : DataMat := FiniteQutritRetainedClock.embedClock c signedQ

theorem signedQ_norm : traceNorm signedQ=1 := by
  have he : signedQ=Matrix.diagonal (fun i : Fin 3 => ((![1/2,-1/2,0] i:ℝ):ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [signedQ,Matrix.diagonal,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  rw [he,real_diagonal_norm,Fin.sum_univ_three]
  change |(1/2:ℝ)|+|(-1/2:ℝ)|+|(0:ℝ)|=1
  norm_num


theorem parity_norm (c : A) : traceNorm (FiniteQutritRetainedClock.P c)=1 := by
  have he : FiniteQutritRetainedClock.P c=Matrix.single c c 1 := by
    ext a b
    simp [FiniteQutritRetainedClock.P,FiniteQutritRetainedClock.e,Matrix.single]
  rw [he,traceNorm_density_eq_one (single_density c)]


theorem signedData_norm (c : A) : traceNorm (signedData c)=1 := by
  change traceNorm (signedQ ⊗ₖ FiniteQutritRetainedClock.P c)=1
  rw [traceNorm_kronecker,signedQ_norm,parity_norm,mul_one]

theorem preparation_tensor (c : A) (X : FiniteQutritPhysicalMemory.Mat) (σ : Matrix F F ℂ) :
    FiniteQutritRetainedClock.amplifiedPreparation F c (X ⊗ₖ σ)=
      FiniteQutritRetainedClock.embedClock c X ⊗ₖ σ := by
  ext ⟨⟨q,a⟩,f⟩ ⟨⟨r,b⟩,g⟩
  rw [FiniteQutritRetainedClock.preparation_entry]
  change (X q r*σ f g)*FiniteQutritRetainedClock.P c a b =
    (X q r*FiniteQutritRetainedClock.P c a b)*σ f g
  ring

theorem old_reduction_preparation (c : A) (Y : Matrix (Fin 3 × F) (Fin 3 × F) ℂ) :
    FiniteQutritRetainedClock.amplifiedReduction F
      (FiniteQutritRetainedClock.amplifiedPreparation F c Y)=Y := by
  ext ⟨q,f⟩ ⟨r,g⟩
  simp only [FiniteQutritRetainedClock.reduction_entry,
    FiniteQutritRetainedClock.preparation_entry,Fin.sum_univ_two]
  fin_cases c <;> simp [FiniteQutritRetainedClock.P,FiniteQutritRetainedClock.e,Matrix.single]

/-- Actual parity-zero data maps preserve this signed two-block input, with only none surviving. -/
theorem parity_zero_data (a : A) (i : Fin 11) (Y : Matrix (Fin 3 × F) (Fin 3 × F) ℂ) :
    FiniteClockControlledRetainedMemory.dataBranch F a i
      (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y)=
      if i=FiniteQutritRetainedClock.noneLabel then
        FiniteQutritRetainedClock.amplifiedPreparation F 1 Y else 0 := by
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl
  · rw [FiniteClockControlledRetainedMemory.dataBranch_keep]
    rcases FiniteQutritRetainedClock.label_cases i with rfl | ⟨k,rfl⟩
    · rw [FiniteQutritRetainedClock.none_zero_branch,if_pos rfl]
    · rw [FiniteQutritRetainedClock.some_zero_branch,if_neg
        (Ne.symm (FiniteQutritRetainedClock.none_ne_some k))]
  · rw [FiniteClockControlledRetainedMemory.dataBranch_reset,
      FiniteQutritRetainedClock.reset_amplified_action,old_reduction_preparation]
    rcases FiniteQutritRetainedClock.label_cases i with rfl | ⟨k,rfl⟩
    · rw [FiniteQutritRetainedClock.none_zero_branch,if_pos rfl]
    · rw [FiniteQutritRetainedClock.some_zero_branch,if_neg
        (Ne.symm (FiniteQutritRetainedClock.none_ne_some k))]

theorem signed_data_action (a : A) (i : Fin 11) (σ : Matrix F F ℂ) :
    FiniteClockControlledRetainedMemory.dataBranch F a i (signedData 0 ⊗ₖ σ)=
      if i=FiniteQutritRetainedClock.noneLabel then signedData 1 ⊗ₖ σ else 0 := by
  rw [signedData,← preparation_tensor,parity_zero_data,preparation_tensor]
  rfl

theorem signed_data_norm_preserved (a : A) (σ : Matrix F F ℂ) :
    (∑ i : Fin 11,traceNorm (FiniteClockControlledRetainedMemory.dataBranch F a i
      (signedData 0 ⊗ₖ σ)))=traceNorm (signedData 0 ⊗ₖ σ) := by
  simp only [signed_data_action,apply_ite,traceNorm_zero,Finset.sum_ite_eq',Finset.mem_univ,
    ite_true,traceNorm_kronecker,signedData_norm,one_mul]

theorem entangled_signed_compression (θ φ : ℝ) (f : F) :
    extract F 1 1 (midpointPhase θ φ) 0 (entangledAttainer F θ φ f)-
      extract F 1 1 (midpointPhase θ φ) 1 (entangledAttainer F θ φ f)=
      signedData 0 ⊗ₖ Matrix.single f f 1 := by
  rw [entangled_compressions,entangled_compressions]
  have hk (X Y : DataMat) (σ : Matrix F F ℂ) : (X ⊗ₖ σ)-(Y ⊗ₖ σ)=(X-Y) ⊗ₖ σ := by
    ext a b; simp [Matrix.kronecker_apply,sub_mul]
  rw [hk]
  congr 1
  ext ⟨q,c⟩ ⟨r,d⟩
  fin_cases c <;> fin_cases d <;>
    simp [dataPoint,signedData,signedQ,FiniteQutritRetainedClock.embedClock,
      FiniteQutritRetainedClock.P,FiniteQutritRetainedClock.e,Matrix.single,Matrix.diagonal,
      Matrix.kronecker_apply,Matrix.smul_apply,smul_eq_mul]
  all_goals fin_cases q <;> fin_cases r <;> norm_num



theorem entangled_arm_compression (θ φ : ℝ) (f : F) (a : A) :
    extract F 1 1 θ a (entangledAttainer F θ φ f)-extract F 1 1 φ a (entangledAttainer F θ φ f)=
      ((if a=0 then Real.sin ((θ-φ)/2) else -Real.sin ((θ-φ)/2):ℝ):ℂ) •
        (signedData 0 ⊗ₖ Matrix.single f f 1) := by
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl
  · rw [compression_signed_difference,entangled_signed_compression]
    simp
  · rw [other_compression_difference,compression_signed_difference,entangled_signed_compression]
    simp

theorem entangled_branch_norm (θ φ : ℝ) (f : F) (a : A) (i : Fin 11) :
    traceNorm ((step F 1 1 θ (by norm_num)).branch S F 22 (outcomeEquiv (a,i))
      (entangledAttainer F θ φ f)-
      (step F 1 1 φ (by norm_num)).branch S F 22 (outcomeEquiv (a,i)) (entangledAttainer F θ φ f))=
      if i=FiniteQutritRetainedClock.noneLabel then eta θ φ else 0 := by
  rw [branch_action,branch_action,← insert_sub,← dataBranch_sub,entangled_arm_compression,
    measured_data_smul F,signed_data_action]
  by_cases hi : i=FiniteQutritRetainedClock.noneLabel
  · rw [if_pos hi,if_pos hi,FinitePersistentMeasuredHand.insert_smul,traceNorm_real_smul,
      insert_traceNorm,traceNorm_kronecker,signedData_norm,traceNorm_density_eq_one (single_density f)]
    simp only [mul_one]
    split <;> simp [eta]
  · rw [if_neg hi,if_neg hi,smul_zero]
    rw [insert_traceNorm,traceNorm_zero]

theorem entangled_attains (θ φ : ℝ) (f : F) :
    FiniteAdaptiveMapPerturbation.stepDistance S F 22
      (step F 1 1 θ (by norm_num)) (step F 1 1 φ (by norm_num))
      (entangledAttainer F θ φ f)=eta θ φ := by
  unfold FiniteAdaptiveMapPerturbation.stepDistance
  rw [← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type,entangled_branch_norm,Finset.sum_ite_eq',Finset.mem_univ,
    ite_true,Fin.sum_univ_two]
  ring


def recoveryData {ω : ℝ} (hω : 0<ω) (ℏ : ℝ) (hℏ : ℏ ≠ 0) (k : ℕ) (ks : List ℕ)
    (Y : ReducedMat F) : ReducedMat F :=
  FiniteClockControlledRetainedMemory.handTrace F
    (∑ h,run S F 22 (policyTree F ω ℏ hℏ (recoveryPolicy hω k ks)) h
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 1)))

theorem recoveryData_old {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k : ℕ) (ks : List ℕ)
    (Y : ReducedMat F) : recoveryData F hω ℏ hℏ k ks Y=
      FiniteQutritRetainedClock.amplifiedJointIterate F (ks.length+1) Y :=
  recovery_reduced F hω hℏ k ks Y

theorem recovery_even {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k n : ℕ)
    (ks : List ℕ) (hlen : ks.length+1=2*n) (Y : Matrix (Fin 3 × F) (Fin 3 × F) ℂ) :
    FiniteQutritRetainedClock.amplifiedReduction F
      (recoveryData F hω ℏ hℏ k ks (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y))=
      FiniteQutritAveragedTransfer.amplifiedIterate F n Y := by
  rw [recoveryData_old,hlen,FiniteQutritRetainedClock.spectator_reduced_even]

theorem recovery_odd {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k n : ℕ)
    (ks : List ℕ) (hlen : ks.length+1=2*n+1) (Y : Matrix (Fin 3 × F) (Fin 3 × F) ℂ) :
    FiniteQutritRetainedClock.amplifiedReduction F
      (recoveryData F hω ℏ hℏ k ks (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y))=
      FiniteQutritAveragedTransfer.amplifiedIterate F n Y := by
  rw [recoveryData_old,hlen,FiniteQutritRetainedClock.spectator_reduced_odd]

def recoveryJoint {ω : ℝ} (hω : 0<ω) (ℏ : ℝ) (hℏ : ℏ ≠ 0) (k : ℕ) (ks : List ℕ)
    (X : DataMat) : DataMat := fun b d => recoveryData Unit hω ℏ hℏ k ks
      (X ⊗ₖ (1:Matrix Unit Unit ℂ)) (b,()) (d,())

theorem recoveryJoint_old {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k : ℕ) (ks : List ℕ) (X : DataMat) :
    recoveryJoint hω ℏ hℏ k ks X=FiniteQutritRetainedClock.jointIterate (ks.length+1) X := by
  unfold recoveryJoint
  rw [recoveryData_old,FiniteQutritRetainedClock.amplified_iterate_product]
  ext b d
  simp

theorem recovery_quotient_even {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k n : ℕ)
    (ks : List ℕ) (hlen : ks.length+1=2*n) (q : FiniteQutritInvariantReconstruction.FeatureSpace) :
    FiniteQutritRetainedClock.D (recoveryJoint hω ℏ hℏ k ks
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q)))=
      FiniteQutritInvariantReconstruction.U (FiniteQutritAveragedTransfer.quotientIterate n q) := by
  rw [recoveryJoint_old,hlen,FiniteQutritRetainedClock.quotient_even]

theorem recovery_quotient_odd {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k n : ℕ)
    (ks : List ℕ) (hlen : ks.length+1=2*n+1) (q : FiniteQutritInvariantReconstruction.FeatureSpace) :
    FiniteQutritRetainedClock.D (recoveryJoint hω ℏ hℏ k ks
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q)))=
      FiniteQutritInvariantReconstruction.U (FiniteQutritAveragedTransfer.quotientIterate n q) := by
  rw [recoveryJoint_old,hlen,FiniteQutritRetainedClock.quotient_odd]

theorem recovery_nine_probe {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k : ℕ) :
    ∃ p : FiniteQutritRetainedClock.ProbeLabel,
      IsDensityOperator (FiniteQutritRetainedClock.densityProbe p) ∧
      IsDensityOperator (FiniteClockControlledRetainedMemory.insert Unit
        (prepareData 0 (FiniteQutritRetainedClock.densityProbe p)) (FiniteClockHandReadout.Q 1)) ∧
      FiniteQutritRetainedClock.E0 (FiniteQutritRetainedClock.D
        (recoveryJoint hω ℏ hℏ k [] (FiniteQutritRetainedClock.E0 (FiniteQutritRetainedClock.densityProbe p)))) ≠
      recoveryJoint hω ℏ hℏ k [] (FiniteQutritRetainedClock.E0 (FiniteQutritRetainedClock.densityProbe p)) := by
  obtain ⟨p,hp,hi,hd⟩ := FiniteClockControlledRetainedMemoryExamples.recovered_nine_probe_defect hω.ne' hℏ
  refine ⟨p,hp,?_,?_⟩
  · simpa only [FiniteClockHandReadout.rhoPlus_eq] using hi
  · rw [FiniteClockControlledRetainedMemoryExamples.recoveredJoint_old hω.ne' hℏ] at hd
    simpa only [recoveryJoint_old,List.length_nil,zero_add] using hd

theorem old_run_cast {m n : ℕ} (he : m=n) (h : History 11 n) (Y : ReducedMat F) :
    run B F 11 (FiniteQutritRetainedClock.recordTree F m)
      (cast (congrArg (History 11) he.symm) h) Y=
      run B F 11 (FiniteQutritRetainedClock.recordTree F n) h Y := by
  cases he
  rfl

theorem recovery_even_word {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k n : ℕ)
    (ks : List ℕ) (hlen : ks.length+1=2*n) (h : History 10 n)
    (Y : Matrix (Fin 3 × F) (Fin 3 × F) ℂ) :
    run S F 22 (policyTree F ω ℏ hℏ (recoveryPolicy hω k ks))
      (FiniteClockControlledRetainedMemory.injectRecord (ks.length+1)
        (cast (congrArg (History 11) hlen.symm) (FiniteQutritRetainedClock.evenRecord n h)))
      (FiniteClockControlledRetainedMemory.insert F (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y)
        (FiniteClockHandReadout.Q 1))=
      FiniteClockControlledRetainedMemory.insert F (FiniteQutritRetainedClock.amplifiedPreparation F 0
        ((FiniteQutritRetainedClock.tenWord n h ⊗ₖ (1:Matrix F F ℂ))*Y*
          (FiniteQutritRetainedClock.tenWord n h ⊗ₖ (1:Matrix F F ℂ))ᴴ)) (FiniteClockHandReadout.Q 0) := by
  rw [recovery_injected,old_run_cast F hlen,FiniteQutritRetainedClock.permitted_even_word]

theorem recovery_odd_word {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k n : ℕ)
    (ks : List ℕ) (hlen : ks.length+1=2*n+1) (h : History 10 n)
    (Y : Matrix (Fin 3 × F) (Fin 3 × F) ℂ) :
    run S F 22 (policyTree F ω ℏ hℏ (recoveryPolicy hω k ks))
      (FiniteClockControlledRetainedMemory.injectRecord (ks.length+1)
        (cast (congrArg (History 11) hlen.symm) (FiniteQutritRetainedClock.oddRecord n h)))
      (FiniteClockControlledRetainedMemory.insert F (FiniteQutritRetainedClock.amplifiedPreparation F 0 Y)
        (FiniteClockHandReadout.Q 1))=
      FiniteClockControlledRetainedMemory.insert F (FiniteQutritRetainedClock.amplifiedPreparation F 1
        ((FiniteQutritRetainedClock.tenWord n h ⊗ₖ (1:Matrix F F ℂ))*Y*
          (FiniteQutritRetainedClock.tenWord n h ⊗ₖ (1:Matrix F F ℂ))ᴴ)) (FiniteClockHandReadout.Q 0) := by
  rw [recovery_injected,old_run_cast F hlen,FiniteQutritRetainedClock.permitted_odd_word]

/-- Normalization of every actual future family after any actual prefix, including zero-mass prefixes. -/
theorem every_prefix_normalization {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n m : ℕ}
    (P : Policy n) (h : History 22 n) (Q : Policy m) (Z : FullMat F) :
    (∑ g, (run S F 22 (policyTree F ω ℏ hℏ Q) g
      (run S F 22 (policyTree F ω ℏ hℏ P) h Z)).trace.re)=
      (run S F 22 (policyTree F ω ℏ hℏ P) h Z).trace.re :=
  prefix_marginal S F 22 (policyTree F ω ℏ hℏ P) h (policyTree F ω ℏ hℏ Q) Z


theorem branch_linear {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (o : Fin 22)
    (c : ℂ) (X Y : FullMat F) :
    (step F ω ℏ t hℏ).branch S F 22 o (c • X+Y)=
      c • (step F ω ℏ t hℏ).branch S F 22 o X+(step F ω ℏ t hℏ).branch S F 22 o Y := by
  rw [Step.branch_add,Step.branch_smul]

theorem no_density_empty [IsEmpty F] (Z : FullMat F) : ¬IsDensityOperator Z := by
  rintro ⟨_,ht⟩
  have hz : Z.trace=0 := by simp [Matrix.trace]
  rw [hz] at ht
  exact zero_ne_one ht

theorem zero_mass_psd {Z : FullMat F} (hZ : Z.PosSemidef) (hm : Z.trace.re=0) : Z=0 := by
  apply hZ.trace_eq_zero_iff.mp
  apply Complex.ext
  · exact hm
  · exact trace_im_zero_of_posSemidef hZ

theorem zero_mass_records {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} (P : Policy n)
    (h : History 22 n) {Z : FullMat F} (hZ : Z.PosSemidef) (hm : Z.trace.re=0) :
    run S F 22 (policyTree F ω ℏ hℏ P) h Z=0 := by
  rw [zero_mass_psd F hZ hm,run_zero]

theorem posterior_reflection {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a b : A) (i : Fin 11)
    (Y : ReducedMat F) :
    (step F ω ℏ (-t) hℏ).branch S F 22 (outcomeEquiv (b,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a))=
    (step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (b,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)) := by
  simp only [branch_posterior,transition,FiniteClockHandReadout.p_reflection]

theorem posterior_scalar {ℏ : ℝ} (hℏ : ℏ ≠ 0) (t : ℝ) (a b : A) (i : Fin 11) (Y : ReducedMat F) :
    (step F 0 ℏ t hℏ).branch S F 22 (outcomeEquiv (b,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a))=
    if b=a then FiniteClockControlledRetainedMemory.insert F
      (FiniteClockControlledRetainedMemory.dataBranch F b i Y) (FiniteClockHandReadout.Q b) else 0 := by
  rw [branch_posterior]
  simp [transition,FiniteClockHandReadout.p]

theorem posterior_full_turn {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k : ℕ)
    (a b : A) (i : Fin 11) (Y : ReducedMat F) :
    (step F ω ℏ (fullTurnDuration hω k) hℏ).branch S F 22 (outcomeEquiv (b,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a))=
    if b=a then FiniteClockControlledRetainedMemory.insert F
      (FiniteClockControlledRetainedMemory.dataBranch F b i Y) (FiniteClockHandReadout.Q b) else 0 := by
  rw [branch_posterior]
  simp only [transition]
  rw [fullTurn_mass hω k]
  split <;> simp

theorem posterior_half_turn {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k : ℕ)
    (a b : A) (i : Fin 11) (Y : ReducedMat F) :
    (step F ω ℏ (oddHalfDuration hω k) hℏ).branch S F 22 (outcomeEquiv (b,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a))=
    if b=a then 0 else FiniteClockControlledRetainedMemory.insert F
      (FiniteClockControlledRetainedMemory.dataBranch F b i Y) (FiniteClockHandReadout.Q b) := by
  rw [branch_posterior]
  simp only [transition]
  rw [oddHalf_mass hω k]
  split <;> simp

def measuredCycle (ω ℏ t : ℝ) (hℏ : ℏ ≠ 0) (Z : FullMat F) : FullMat F :=
  ∑ o,(step F ω ℏ t hℏ).branch S F 22 o Z

theorem measuredCycle_sector {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (Y : ReducedMat F) (a : A) :
    measuredCycle F ω ℏ t hℏ (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a))=
    (transition ω t 0 a:ℂ) • FiniteClockControlledRetainedMemory.insert F
      (FiniteQutritRetainedClock.amplified F Y) (FiniteClockHandReadout.Q 0)+
    (transition ω t 1 a:ℂ) • FiniteClockControlledRetainedMemory.insert F
      (FiniteQutritRetainedClock.amplified F
        (krausMap (fun c => FiniteQutritRetainedClock.L c ⊗ₖ (1:Matrix F F ℂ)) Y))
      (FiniteClockHandReadout.Q 1) := by
  rw [measuredCycle,← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type,branch_posterior,← Finset.smul_sum,
    ← FiniteClockControlledRetainedMemory.insert_sum,Fin.sum_univ_two,
    dataBranch_keep_sum,dataBranch_reset_sum]

theorem measuredCycle_prepare_zero {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ)
    (X : FiniteQutritPhysicalMemory.Mat) (a : A) :
    measuredCycle Unit ω ℏ t hℏ
      (FiniteClockControlledRetainedMemory.insert Unit (prepareData 0 X) (FiniteClockHandReadout.Q a))=
      (transition ω t 0 a:ℂ) • FiniteClockControlledRetainedMemory.insert Unit
        (prepareData 1 X) (FiniteClockHandReadout.Q 0)+
      (transition ω t 1 a:ℂ) • FiniteClockControlledRetainedMemory.insert Unit
        (prepareData 1 X) (FiniteClockHandReadout.Q 1) := by
  rw [measuredCycle_sector,FiniteQutritRetainedClock.reset_amplified_action,old_reduce_prepare]
  simp only [prepareData] at *
  rw [← prepareData,amplified_prepare_zero]
  rfl

theorem measuredCycle_prepare_one {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ)
    (X : FiniteQutritPhysicalMemory.Mat) (a : A) :
    measuredCycle Unit ω ℏ t hℏ
      (FiniteClockControlledRetainedMemory.insert Unit (prepareData 1 X) (FiniteClockHandReadout.Q a))=
      (transition ω t 0 a:ℂ) • FiniteClockControlledRetainedMemory.insert Unit
        (prepareData 0 (FiniteQutritAveragedTransfer.transfer X)) (FiniteClockHandReadout.Q 0)+
      (transition ω t 1 a:ℂ) • FiniteClockControlledRetainedMemory.insert Unit
        (prepareData 1 X) (FiniteClockHandReadout.Q 1) := by
  rw [measuredCycle_sector,FiniteQutritRetainedClock.reset_amplified_action,old_reduce_prepare]
  rw [show FiniteQutritRetainedClock.amplifiedPreparation Unit 0 (unitQutrit X)=prepareData 0 X from rfl,
    amplified_prepare_zero,amplified_prepare_one]

theorem three_tick_states {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) :
    measuredCycle Unit ω ℏ 0 hℏ
      (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ
        (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (input FiniteClockHandReadout.rhoPlus)))=
      FiniteClockControlledRetainedMemory.insert Unit (prepareData 1 FiniteQutritRetainedClock.rho0)
        (FiniteClockHandReadout.Q 1) ∧
    measuredCycle Unit ω ℏ (Real.pi/ω) hℏ
      (measuredCycle Unit ω ℏ 0 hℏ
        (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (input FiniteClockHandReadout.rhoPlus)))=
      FiniteClockControlledRetainedMemory.insert Unit
        (prepareData 1 (FiniteQutritAveragedTransfer.transfer FiniteQutritRetainedClock.rho0))
        (FiniteClockHandReadout.Q 1) := by
  have hp := FiniteClockHandReadout.p_keep hω.ne'
  have hz := FiniteClockHandReadout.p_zero ω
  constructor <;> rw [input,FiniteClockHandReadout.rhoPlus_eq,measuredCycle_prepare_zero] <;>
    simp only [transition,hp,hz,if_pos rfl,ite_true,show (0:A) ≠ 1 by decide,if_false,
      sub_self,Complex.ofReal_one,Complex.ofReal_zero,one_smul,zero_smul,add_zero,zero_add]
  · rw [measuredCycle_prepare_one]
    simp only [transition,hp,if_pos rfl,ite_true,show (1:A) ≠ 0 by decide,if_false,
      sub_self,Complex.ofReal_one,Complex.ofReal_zero,one_smul,zero_smul,add_zero,zero_add]
    rw [measuredCycle_prepare_one]
    simp [transition,hz]
  · rw [measuredCycle_prepare_one]
    simp only [transition,hz,if_pos rfl,ite_true,show (1:A) ≠ 0 by decide,if_false,
      sub_zero,Complex.ofReal_one,Complex.ofReal_zero,one_smul,zero_smul,add_zero,zero_add]
    rw [measuredCycle_prepare_zero]
    simp [transition,hp]

theorem three_tick_events {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) :
    eventValue (measuredCycle Unit ω ℏ 0 hℏ
      (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ
        (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (input FiniteClockHandReadout.rhoPlus))))=1 ∧
    eventValue (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ
      (measuredCycle Unit ω ℏ 0 hℏ
        (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (input FiniteClockHandReadout.rhoPlus))))=4/5 := by
  rw [(three_tick_states hω hℏ).1,(three_tick_states hω hℏ).2,
    event_prepare 1 _ _ (FiniteClockHandReadout.Q_trace 1),
    event_prepare 1 _ _ (FiniteClockHandReadout.Q_trace 1),event0_entry,event0_entry,
    FiniteQutritRetainedClock.transfer_rho0]
  norm_num [FiniteQutritRetainedClock.rho0,FiniteQutritPhysicalMemory.projector]


def coarse (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) (t s : Duration) (fresh : Bool) (a b : A) : ℝ :=
  if fresh then
    ∑ i : Fin 11,∑ j : Fin 11,
      (run S Unit 22 (FiniteClockControlledRetainedMemory.policyTree Unit ω ℏ hℏ (twoPolicy t s))
        (outcomeEquiv (a,i),outcomeEquiv (b,j),()) (input FiniteClockHandReadout.rhoPlus)).trace.re
  else
    ∑ i : Fin 11,∑ j : Fin 11,
      (run S Unit 22 (policyTree Unit ω ℏ hℏ (twoPolicy t s))
        (outcomeEquiv (a,i),outcomeEquiv (b,j),()) (input FiniteClockHandReadout.rhoPlus)).trace.re


theorem weighted_table_coarse (w : A → A → ℝ) (a b : A) :
    (∑ i : Fin 11,∑ j : Fin 11,(weightedTable w a b i j).trace.re)=w a b := by
  have ht (i : Fin 11) : (∑ j : Fin 11,(weightedTable w a b i j).trace.re)=
      if i=FiniteQutritRetainedClock.noneLabel then w a b else 0 := by
    by_cases hi : i=FiniteQutritRetainedClock.noneLabel
    · simp only [weightedTable,hi,ite_true,Matrix.trace_smul,
        FiniteClockControlledRetainedMemory.insert_trace,FiniteClockHandReadout.Q_trace,mul_one,
        smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
        ← Finset.mul_sum,dataSecond_trace_sum,mul_one]
    · simp [weightedTable,hi]
  simp only [ht,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem coarse_formula {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) (t s : Duration)
    (fresh : Bool) (a b : A) :
    coarse ω ℏ hℏ t s fresh a b=FiniteClockHandReadout.mass ω t a *
      (if fresh then FiniteClockHandReadout.mass ω s b else transition ω s b a) := by
  cases fresh
  · simp only [coarse,Bool.false_eq_true,ite_false]
    simp_rw [two_round_table]
    exact weighted_table_coarse (fun a b => FiniteClockHandReadout.mass ω t a*transition ω s b a) a b
  · simp only [coarse,ite_true]
    simp_rw [fresh_two_round_table]
    exact weighted_table_coarse (fun a b => FiniteClockHandReadout.mass ω t a*FiniteClockHandReadout.mass ω s b) a b


theorem calibrated_coarse {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) :
    (fun a b => coarse ω ℏ hℏ (rightDuration hω) (leftDuration hω) false a b)=
      !![(9/16:ℝ),3/16;1/16,3/16] ∧
    (fun a b => coarse ω ℏ hℏ (rightDuration hω) (leftDuration hω) true a b)=
      !![(3/16:ℝ),9/16;1/16,3/16] := by
  have hp := FiniteClockHandReadout.p_right hω.ne'
  have hs := FiniteClockHandReadout.p_left hω.ne'
  constructor <;> ext a b <;> rw [coarse_formula] <;>
    simp only [FiniteClockHandReadout.mass,transition,rightDuration,leftDuration,Subtype.coe_mk,hp,hs] <;>
    fin_cases a <;> fin_cases b <;> norm_num

def microLive (k : Fin 10) : Prop :=
  let j := (finProdFinEquiv.symm k : Fin 5 × A).1
  let a := (finProdFinEquiv.symm k : Fin 5 × A).2
  (j.val=0 ∧ a.val=0) ∨ ((j.val=1 ∨ j.val=2) ∧ a.val=1) ∨ 3≤j.val

instance (k : Fin 10) : Decidable (microLive k) := inferInstanceAs (Decidable (
  ((finProdFinEquiv.symm k : Fin 5 × A).1.val=0 ∧ (finProdFinEquiv.symm k : Fin 5 × A).2.val=0) ∨
  (((finProdFinEquiv.symm k : Fin 5 × A).1.val=1 ∨ (finProdFinEquiv.symm k : Fin 5 × A).1.val=2) ∧
    (finProdFinEquiv.symm k : Fin 5 × A).2.val=1) ∨ 3≤(finProdFinEquiv.symm k : Fin 5 × A).1.val))

theorem micro_live_iff (k : Fin 10) : 0<(micro k).trace.re ↔ microLive k := by
  obtain ⟨⟨j,a⟩,rfl⟩ := (finProdFinEquiv : Fin 5 × A ≃ Fin 10).surjective k
  rw [micro_weight]
  simp only [microLive,Equiv.symm_apply_apply]
  fin_cases j <;> fin_cases a <;> norm_num [microWeight]

def structuralLeaf (h : (A × Fin 11) × (A × Fin 11)) : Prop :=
  h.1.2=FiniteQutritRetainedClock.noneLabel ∧
    ((h.2.1=0 ∧ h.2.2≠FiniteQutritRetainedClock.noneLabel) ∨
      (h.2.1=1 ∧ h.2.2=FiniteQutritRetainedClock.noneLabel))

instance (h : (A × Fin 11) × (A × Fin 11)) : Decidable (structuralLeaf h) :=
  inferInstanceAs (Decidable (h.1.2=FiniteQutritRetainedClock.noneLabel ∧
    ((h.2.1=0 ∧ h.2.2≠FiniteQutritRetainedClock.noneLabel) ∨
      (h.2.1=1 ∧ h.2.2=FiniteQutritRetainedClock.noneLabel))))

def liveLeaf (h : (A × Fin 11) × (A × Fin 11)) : Prop :=
  structuralLeaf h ∧ ∀ k, h.2.2=FiniteQutritRetainedClock.someLabel k → microLive k

instance (h : (A × Fin 11) × (A × Fin 11)) : Decidable (liveLeaf h) :=
  inferInstanceAs (Decidable (structuralLeaf h ∧ ∀ k,
    h.2.2=FiniteQutritRetainedClock.someLabel k → microLive k))

theorem quarter_zero_gap_distance {ω ℏ : ℝ} (hω : 0 < ω) (hℏ : ℏ ≠ 0) :
    |terminalProbability ω ℏ hℏ (twoPolicy (quarterDuration hω) zeroDuration)
      (input FiniteClockHandReadout.rhoPlus)-
      freshTerminalProbability ω ℏ hℏ
        (twoPolicy (quarterDuration hω) zeroDuration) (input FiniteClockHandReadout.rhoPlus)|=1/10 ∧
    FiniteAdaptiveMapPerturbation.outputDistance S Unit 22
      (policyTree Unit ω ℏ hℏ (twoPolicy (quarterDuration hω) zeroDuration))
      (FiniteClockControlledRetainedMemory.policyTree Unit ω ℏ hℏ (twoPolicy (quarterDuration hω) zeroDuration))
      (input FiniteClockHandReadout.rhoPlus) (input FiniteClockHandReadout.rhoPlus)=1/2 := by
  constructor
  · rw [(quarter_zero_events hω hℏ).1,(quarter_zero_events hω hℏ).2]
    norm_num
  · rw [recorded_distance_formula]
    simp only [FiniteClockHandReadout.mass,transition,quarterDuration,zeroDuration,Subtype.coe_mk,FiniteClockHandReadout.p_quarter hω.ne',FiniteClockHandReadout.p_zero]
    norm_num [Fin.sum_univ_two]


theorem cardinal_sum_indicator {D : Type*} [Fintype D] (p : D → Prop) [DecidablePred p] :
    Fintype.card {x // p x}=∑ x : D, if p x then 1 else 0 := by
  rw [Fintype.card_subtype,Finset.sum_boole]
  simp only [Nat.cast_id]

theorem micro_live_count : (∑ k : Fin 10,if microLive k then 1 else 0 : ℕ)=7 := by decide

theorem structural_leaf_count :
    Fintype.card {h : (A × Fin 11) × (A × Fin 11) // structuralLeaf h}=22 := by
  rw [cardinal_sum_indicator]
  simp only [Fintype.sum_prod_type]
  have hi (a : A) (i : Fin 11) :
      (∑ b : A,∑ j : Fin 11,if structuralLeaf ((a,i),(b,j)) then 1 else 0 : ℕ)=
        if i=FiniteQutritRetainedClock.noneLabel then 11 else 0 := by
    by_cases he : i=FiniteQutritRetainedClock.noneLabel
    · subst i
      simp only [Fin.sum_univ_two]
      rw [← FiniteQutritRetainedClock.labelEquiv.sum_comp,← FiniteQutritRetainedClock.labelEquiv.sum_comp]
      simp only [Fintype.sum_option]
      simp [structuralLeaf,FiniteQutritRetainedClock.noneLabel,FiniteQutritRetainedClock.someLabel]
    · simp [structuralLeaf,he]
  simp only [hi,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Fin.sum_univ_two]

theorem positive_leaf_count :
    Fintype.card {h : (A × Fin 11) × (A × Fin 11) // liveLeaf h}=16 := by
  rw [cardinal_sum_indicator]
  simp only [Fintype.sum_prod_type]
  have hi (a : A) (i : Fin 11) :
      (∑ b : A,∑ j : Fin 11,if liveLeaf ((a,i),(b,j)) then 1 else 0 : ℕ)=
        if i=FiniteQutritRetainedClock.noneLabel then 8 else 0 := by
    by_cases he : i=FiniteQutritRetainedClock.noneLabel
    · subst i
      simp only [Fin.sum_univ_two]
      rw [← FiniteQutritRetainedClock.labelEquiv.sum_comp,← FiniteQutritRetainedClock.labelEquiv.sum_comp]
      simp only [Fintype.sum_option]
      simp [liveLeaf,structuralLeaf,FiniteQutritRetainedClock.noneLabel,
        FiniteQutritRetainedClock.someLabel,micro_live_count,-Finset.sum_boole]
    · simp [liveLeaf,structuralLeaf,he]
  simp only [hi,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Fin.sum_univ_two]

theorem dynamic_zero_leaf_count :
    Fintype.card {h : (A × Fin 11) × (A × Fin 11) // structuralLeaf h ∧ ¬liveLeaf h}=6 := by
  rw [cardinal_sum_indicator]
  have hi (h : (A × Fin 11) × (A × Fin 11)) :
      (if structuralLeaf h ∧ ¬liveLeaf h then 1 else 0 : ℕ)=
        (if structuralLeaf h then 1 else 0)-(if liveLeaf h then 1 else 0) := by
    by_cases hs : structuralLeaf h <;> by_cases hl : liveLeaf h <;> simp [hs,hl]
  simp only [hi]
  rw [Finset.sum_tsub_distrib]
  · rw [← cardinal_sum_indicator,← cardinal_sum_indicator,structural_leaf_count,positive_leaf_count]
  · intro h _
    by_cases hl : liveLeaf h
    · simp [hl,hl.1]
    · simp [hl]

theorem complete_leaf_counts : Fintype.card (History 22 2)=484 ∧
    Fintype.card {h : (A × Fin 11) × (A × Fin 11) // ¬structuralLeaf h}=462 ∧
    Fintype.card {h : (A × Fin 11) × (A × Fin 11) // liveLeaf h}=16 ∧
    Fintype.card {h : (A × Fin 11) × (A × Fin 11) // structuralLeaf h ∧ ¬liveLeaf h}=6 := by
  refine ⟨history_card 22 2,?_,positive_leaf_count,dynamic_zero_leaf_count⟩
  rw [Fintype.card_subtype_compl,structural_leaf_count]
  norm_num


theorem projector_compress (a : A) (X : FiniteClockHandReadout.Mat) :
    FiniteClockHandReadout.Q a*X*FiniteClockHandReadout.Q a=
      (FiniteClockHandReadout.Q a*X).trace • FiniteClockHandReadout.Q a := by
  ext u v
  fin_cases a <;> fin_cases u <;> fin_cases v <;>
    simp [FiniteClockHandReadout.Q,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two,Matrix.vecMul,dotProduct] <;> ring

theorem extract_born (ω ℏ t : ℝ) (a : A) (Y : ReducedMat F) (σ : FiniteClockHandReadout.Mat) :
    extract F ω ℏ t a (FiniteClockControlledRetainedMemory.insert F Y σ)=
      (FiniteClockHandReadout.Q a*(FiniteClockHandReadout.U ω ℏ t*σ*(FiniteClockHandReadout.U ω ℏ t)ᴴ)).trace • Y := by
  rw [extract_product]
  have he : handOperator ω ℏ t a*σ*(handOperator ω ℏ t a)ᴴ=
      FiniteClockHandReadout.Q a*(FiniteClockHandReadout.U ω ℏ t*σ*(FiniteClockHandReadout.U ω ℏ t)ᴴ)*
        FiniteClockHandReadout.Q a := by
    simp only [handOperator,Matrix.conjTranspose_mul,FiniteClockHandReadout.Q_adjoint,Matrix.mul_assoc]
  rw [he,projector_compress]
  simp only [Matrix.smul_apply,smul_eq_mul,Q_last_diagonal]
  congr 1
  ring

theorem gibbs_extraction {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω β t : ℝ) (a : A) (Y : ReducedMat F) :
    extract F ω ℏ t a (FiniteClockControlledRetainedMemory.insert F Y
      (FiniteGibbsClock.gibbs (FiniteClockHandReadout.H ω ℏ) β))=(1/2:ℂ) • Y := by
  rw [extract_born,FiniteClockHandReadout.gibbs_stationary hℏ,
    FiniteClockHandReadout.gibbs_diagonal ω ℏ β,FiniteClockHandReadout.diagonal_born,
    ← FiniteClockHandReadout.gibbs_diagonal ω ℏ β,
    (FiniteGibbsClock.gibbs_density (FiniteClockHandReadout.H_hermitian ω ℏ) β).2,mul_one]

theorem gibbs_branches {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω β t : ℝ) (a : A) (i : Fin 11) (Y : ReducedMat F) :
    (step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteGibbsClock.gibbs (FiniteClockHandReadout.H ω ℏ) β))=
    (1/2:ℂ) • FiniteClockControlledRetainedMemory.insert F
      (FiniteClockControlledRetainedMemory.dataBranch F a i Y) (FiniteClockHandReadout.Q a) := by
  rw [branch_action,gibbs_extraction F hℏ,measured_data_smul,FinitePersistentMeasuredHand.insert_smul]

theorem gibbs_first_mass {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω β t : ℝ) (a : A)
    {Y : ReducedMat F} (hY : IsDensityOperator Y) :
    (∑ i : Fin 11,((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteGibbsClock.gibbs (FiniteClockHandReadout.H ω ℏ) β))).trace.re)=1/2 := by
  rw [← Complex.re_sum,arm_trace,gibbs_extraction F hℏ,Matrix.trace_smul,hY.2]
  norm_num

def handMarginal (Z : FullMat F) : FiniteClockHandReadout.Mat := fun a b =>
  ∑ d : B,∑ f : F,Z ((d,a),f) ((d,b),f)

theorem handMarginal_insert (Y : ReducedMat F) (σ : FiniteClockHandReadout.Mat) :
    handMarginal F (FiniteClockControlledRetainedMemory.insert F Y σ)=Y.trace • σ := by
  ext a b
  simp [handMarginal,FiniteClockControlledRetainedMemory.insert,Matrix.trace,Matrix.diag,
    Fintype.sum_prod_type,Finset.sum_mul,add_mul]

theorem handMarginal_sum {I : Type*} [Fintype I] (Z : I → FullMat F) :
    handMarginal F (∑ i,Z i)=∑ i,handMarginal F (Z i) := by
  ext a b
  simp only [handMarginal,Matrix.sum_apply]
  conv_lhs =>
    arg 2
    intro d
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem handMarginal_smul (c : ℂ) (Z : FullMat F) : handMarginal F (c • Z)=c • handMarginal F Z := by
  ext a b
  simp [handMarginal,Finset.mul_sum]

theorem measured_hand_actual {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    handMarginal Unit (measuredCycle Unit ω ℏ t hℏ (input FiniteClockHandReadout.rhoPlus))=
      FiniteClockHandReadout.measured ω ℏ t := by
  rw [measuredCycle,handMarginal_sum,← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type,first_branch,apply_ite,handMarginal_smul]
  have hz : handMarginal Unit (0:FullMat Unit)=0 := by ext a b; simp [handMarginal]
  have ha (a : A) : handMarginal Unit (afterFirstLabel a)=FiniteClockHandReadout.Q a := by
    rw [afterFirstLabel,handMarginal_insert,(prepareData_density 1 FiniteQutritRetainedClock.rho0_density).2,one_smul]
  simp only [hz,ha,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [FiniteClockHandReadout.measured,FiniteClockHandReadout.sandwich hℏ]

theorem actual_measurement_disturbance {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    traceDist (FiniteClockHandReadout.rho ω ℏ t)
      (handMarginal Unit (measuredCycle Unit ω ℏ t hℏ (input FiniteClockHandReadout.rhoPlus)))=
      |Real.sin (ω*t)|/2 := by
  rw [measured_hand_actual,FiniteClockHandReadout.measurement_disturbance hℏ]

theorem extraction_periodic (θ : ℝ) (a : A) (Z : FullMat F) :
    extract F 1 1 (θ+2*Real.pi) a Z=extract F 1 1 θ a Z := by
  ext x y
  simp only [extract_trig,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem universal_periodic_branch (θ : ℝ) (a : A) (i : Fin 11) (Z : FullMat F) :
    (step F 1 1 (θ+2*Real.pi) (by norm_num)).branch S F 22 (outcomeEquiv (a,i)) Z=
      (step F 1 1 θ (by norm_num)).branch S F 22 (outcomeEquiv (a,i)) Z := by
  rw [branch_action,branch_action,extraction_periodic]


theorem calibrated_weight_positive {ω : ℝ} (hω : 0<ω) (a b : A) :
    0<FiniteClockHandReadout.mass ω (rightDuration hω) a*transition ω (leftDuration hω) b a := by
  simp only [FiniteClockHandReadout.mass,transition,rightDuration,leftDuration,Subtype.coe_mk,
    FiniteClockHandReadout.p_right hω.ne',FiniteClockHandReadout.p_left hω.ne']
  fin_cases a <;> fin_cases b <;> norm_num

theorem calibrated_leaf_support {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0)
    (a b : A) (i j : Fin 11) :
    0<(run S Unit 22 (policyTree Unit ω ℏ hℏ (twoPolicy (rightDuration hω) (leftDuration hω)))
      (outcomeEquiv (a,i),outcomeEquiv (b,j),()) (input FiniteClockHandReadout.rhoPlus)).trace.re ↔
      liveLeaf ((a,i),(b,j)) := by
  rw [two_round_table,table_trace]
  by_cases hi : i=FiniteQutritRetainedClock.noneLabel
  · subst i
    rw [if_pos rfl,mul_pos_iff_of_pos_left (calibrated_weight_positive hω a b)]
    rcases (show b=0 ∨ b=1 by fin_cases b <;> decide) with rfl | rfl
    · rcases FiniteQutritRetainedClock.label_cases j with rfl | ⟨k,rfl⟩
      · simp [dataSecond,FiniteQutritRetainedClock.noneLabel,liveLeaf,structuralLeaf]
      · rw [dataSecond_micro_trace,micro_live_iff]
        simp [liveLeaf,structuralLeaf,FiniteQutritRetainedClock.noneLabel,FiniteQutritRetainedClock.someLabel]
    · rcases FiniteQutritRetainedClock.label_cases j with rfl | ⟨k,rfl⟩
      · rw [dataSecond_none_trace]
        simp [liveLeaf,structuralLeaf,FiniteQutritRetainedClock.noneLabel,FiniteQutritRetainedClock.someLabel]
      · simp [dataSecond,liveLeaf,structuralLeaf,FiniteQutritRetainedClock.noneLabel,
          FiniteQutritRetainedClock.someLabel]
  · simp [hi,liveLeaf,structuralLeaf]

theorem calibrated_zero_leaf {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0)
    (a b : A) (i j : Fin 11) (hn : ¬liveLeaf ((a,i),(b,j))) :
    run S Unit 22 (policyTree Unit ω ℏ hℏ (twoPolicy (rightDuration hω) (leftDuration hω)))
      (outcomeEquiv (a,i),outcomeEquiv (b,j),()) (input FiniteClockHandReadout.rhoPlus)=0 := by
  have hp := run_posSemidef S Unit 22
    (policyTree Unit ω ℏ hℏ (twoPolicy (rightDuration hω) (leftDuration hω)))
    (outcomeEquiv (a,i),outcomeEquiv (b,j),())
    (input_density FiniteClockHandReadout.rhoPlus_density).1
  apply zero_mass_psd Unit hp
  have hnn := (Complex.le_def.mp hp.trace_nonneg).1
  simp only [Complex.zero_re] at hnn
  have hnp := not_lt.mpr (le_of_not_gt (fun h => hn ((calibrated_leaf_support hω hℏ a b i j).mp h)))
  linarith


def jointChannel (ω ℏ t : ℝ) (X : JointMat) : JointMat :=
  ∑ o : Fin 22,krausMap (N ω ℏ t o) X

theorem joint_arm_product (ω ℏ t : ℝ) (a : A) (X : DataMat) (σ : FiniteClockHandReadout.Mat) :
    (∑ i : Fin 11,krausMap (N ω ℏ t (outcomeEquiv (a,i))) (X ⊗ₖ σ))=
      (∑ i : Fin 11,krausMap (FiniteClockControlledRetainedMemory.dataKraus a i) X) ⊗ₖ
        (handOperator ω ℏ t a*σ*(handOperator ω ℏ t a)ᴴ) := by
  simp only [krausMap,N,Equiv.symm_apply_apply,Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  ext ⟨b,u⟩ ⟨d,v⟩
  simp [Matrix.sum_apply,Finset.sum_mul,add_mul,Fin.sum_univ_two]

theorem hand_cogram {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) :
    handOperator ω ℏ t a*(handOperator ω ℏ t a)ᴴ=FiniteClockHandReadout.Q a := by
  have hu : FiniteClockHandReadout.U ω ℏ t*(FiniteClockHandReadout.U ω ℏ t)ᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp
      (FiniteClockHandReadout.U_unitary hℏ ω t)
  simp only [handOperator,Matrix.conjTranspose_mul,FiniteClockHandReadout.Q_adjoint,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (FiniteClockHandReadout.U ω ℏ t),hu,Matrix.one_mul,
    FiniteClockHandReadout.Q_mul,if_pos rfl]

theorem reset_data_one :
    (∑ i : Fin 11,krausMap (FiniteClockControlledRetainedMemory.dataKraus 1 i) (1:DataMat))=
      (2:ℂ) • ((1:FiniteQutritPhysicalMemory.Mat) ⊗ₖ FiniteQutritRetainedClock.P 1) := by
  rw [FiniteClockControlledRetainedMemory.data_action_reset,FiniteQutritRetainedClock.reset_one,map_smul]
  congr 1
  exact FiniteQutritRetainedClock.J_embed_zero 1

/-- Full channel on I12; the reset arm preserves its actual internal zero alternatives. -/
theorem jointChannel_one {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    jointChannel ω ℏ t 1=(1:DataMat) ⊗ₖ FiniteClockHandReadout.Q 0+
      (2:ℂ) • (((1:FiniteQutritPhysicalMemory.Mat) ⊗ₖ FiniteQutritRetainedClock.P 1) ⊗ₖ
        FiniteClockHandReadout.Q 1) := by
  rw [show (1:JointMat)=(1:DataMat) ⊗ₖ (1:FiniteClockHandReadout.Mat) from Matrix.one_kronecker_one.symm]
  rw [jointChannel,← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type,joint_arm_product,Matrix.mul_one,hand_cogram hℏ,Fin.sum_univ_two,
    FiniteClockControlledRetainedMemory.data_action_keep,FiniteQutritRetainedClock.J_one,
    reset_data_one,Matrix.smul_kronecker]

theorem jointChannel_nonunital {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) : jointChannel ω ℏ t 1≠1 := by
  intro he
  rw [jointChannel_one hℏ] at he
  have h := congrFun (congrFun he ((0,0),0)) ((0,0),0)
  norm_num [FiniteClockHandReadout.Q,FiniteQutritRetainedClock.P,FiniteQutritRetainedClock.e,
    Matrix.single,Matrix.one_apply] at h

/-- The actual amplified step agrees with the full joint channel on product spectators. -/
theorem measuredCycle_product {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ)
    (X : JointMat) (σ : Matrix F F ℂ) :
    measuredCycle F ω ℏ t hℏ (X ⊗ₖ σ)=jointChannel ω ℏ t X ⊗ₖ σ := by
  simp only [measuredCycle,step,localStep_branch,instrument,FiniteInstrument.branch,
    FiniteInstrument.lift,krausMap,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one,jointChannel]
  ext ⟨s,f⟩ ⟨r,g⟩
  simp [Matrix.sum_apply,Finset.sum_mul,add_mul,Fin.sum_univ_two] 
  apply Finset.sum_congr rfl
  intro o _
  exact Fin.sum_univ_two _



def threePolicy (t s r : Duration) : Policy 3 :=
  .node t (fun _ => .node s (fun _ => .node r (fun _ => .done)))

/-- Every one of 22³ actual records, retaining impossible hand and all old micro alternatives. -/
theorem three_round_table {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) (t s r : Duration)
    (a b c : A) (i j k : Fin 11) (Y : ReducedMat F) (d : A) :
    run S F 22 (policyTree F ω ℏ hℏ (threePolicy t s r))
      (outcomeEquiv (a,i),outcomeEquiv (b,j),outcomeEquiv (c,k),())
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q d))=
      ((transition ω t a d*transition ω s b a*transition ω r c b:ℝ):ℂ) •
        FiniteClockControlledRetainedMemory.insert F
          (FiniteClockControlledRetainedMemory.dataBranch F c k
            (FiniteClockControlledRetainedMemory.dataBranch F b j
              (FiniteClockControlledRetainedMemory.dataBranch F a i Y))) (FiniteClockHandReadout.Q c) := by
  change (step F ω ℏ r hℏ).branch S F 22 (outcomeEquiv (c,k))
    ((step F ω ℏ s hℏ).branch S F 22 (outcomeEquiv (b,j))
      ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i))
        (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q d))))=_
  rw [branch_posterior,Step.branch_smul,branch_posterior,Step.branch_smul,Step.branch_smul,branch_posterior,
    smul_smul,smul_smul,Complex.ofReal_mul,Complex.ofReal_mul]

theorem actual_branch_sum {I : Type*} [Fintype I] (D : Step S F 22) (o : Fin 22) (X : I → FullMat F) :
    D.branch S F 22 o (∑ i,X i)=∑ i,D.branch S F 22 o (X i) := by
  classical
  have hh (s : Finset I) : D.branch S F 22 o (∑ i∈s,X i)=∑ i∈s,D.branch S F 22 o (X i) := by
    induction s using Finset.induction_on with
    | empty => simp [Step.branch_zero]
    | @insert i s hi ih => simp only [Finset.sum_insert hi,Step.branch_add,ih]
  exact hh Finset.univ

theorem measuredCycle_sum {I : Type*} [Fintype I] {ℏ : ℝ} (hℏ : ℏ ≠ 0)
    (ω t : ℝ) (X : I → FullMat F) :
    measuredCycle F ω ℏ t hℏ (∑ i,X i)=∑ i,measuredCycle F ω ℏ t hℏ (X i) := by
  simp only [measuredCycle,actual_branch_sum]
  rw [Finset.sum_comm]

theorem three_round_sum {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) (t s r : Duration) (Z : FullMat F) :
    (∑ h,run S F 22 (policyTree F ω ℏ hℏ (threePolicy t s r)) h Z)=
      measuredCycle F ω ℏ r hℏ (measuredCycle F ω ℏ s hℏ (measuredCycle F ω ℏ t hℏ Z)) := by
  change (∑ h : Fin 22 × Fin 22 × Fin 22 × Unit,
    (step F ω ℏ r hℏ).branch S F 22 h.2.2.1
      ((step F ω ℏ s hℏ).branch S F 22 h.2.1 ((step F ω ℏ t hℏ).branch S F 22 h.1 Z)))=_
  simp only [Fintype.sum_prod_type,Fintype.sum_unique]
  simp only [measuredCycle,actual_branch_sum]
  symm
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    intro j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]


theorem three_duration_multiset (t : ℝ) : ([t,t,0]:List ℝ).Perm [t,0,t] := by
  exact List.Perm.cons _ (List.Perm.swap _ _ [])

theorem reset_three_states {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) :
    measuredCycle Unit ω ℏ 0 hℏ (resetOld
      (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (resetOld
        (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (resetOld (input FiniteClockHandReadout.rhoPlus))))))=
      FiniteClockControlledRetainedMemory.insert Unit (prepareData 1 FiniteQutritRetainedClock.rho0)
        (FiniteClockHandReadout.Q 1) ∧
    measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (resetOld
      (measuredCycle Unit ω ℏ 0 hℏ (resetOld
        (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (resetOld (input FiniteClockHandReadout.rhoPlus))))))=
      FiniteClockControlledRetainedMemory.insert Unit (prepareData 1 FiniteQutritRetainedClock.rho0)
        (FiniteClockHandReadout.Q 1) := by
  have hp := FiniteClockHandReadout.p_keep hω.ne'
  have hz := FiniteClockHandReadout.p_zero ω
  constructor <;> rw [input,FiniteClockHandReadout.rhoPlus_eq,resetOld_prepare,measuredCycle_prepare_zero] <;>
    simp only [transition,hp,show (0:A) ≠ 1 by decide,if_false,if_pos rfl,ite_true,
      sub_self,Complex.ofReal_one,Complex.ofReal_zero,one_smul,zero_smul,add_zero]
  · rw [resetOld_prepare,measuredCycle_prepare_zero]
    simp only [transition,hp,show (1:A) ≠ 0 by decide,if_false,if_pos rfl,ite_true,
      sub_self,Complex.ofReal_one,Complex.ofReal_zero,one_smul,zero_smul,zero_add]
    rw [resetOld_prepare,measuredCycle_prepare_zero]
    simp [transition,hz]
  · rw [resetOld_prepare,measuredCycle_prepare_zero]
    simp only [transition,hz,show (1:A) ≠ 0 by decide,if_false,if_pos rfl,ite_true,
      sub_zero,Complex.ofReal_one,Complex.ofReal_zero,one_smul,zero_smul,add_zero]
    rw [resetOld_prepare,measuredCycle_prepare_zero]
    simp [transition,hp]

theorem reset_three_events {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) :
    eventValue (measuredCycle Unit ω ℏ 0 hℏ (resetOld
      (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (resetOld
        (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (resetOld (input FiniteClockHandReadout.rhoPlus)))))))=1 ∧
    eventValue (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (resetOld
      (measuredCycle Unit ω ℏ 0 hℏ (resetOld
        (measuredCycle Unit ω ℏ (Real.pi/ω) hℏ (resetOld (input FiniteClockHandReadout.rhoPlus)))))))=1 := by
  rw [(reset_three_states hω hℏ).1,(reset_three_states hω hℏ).2,
    event_prepare 1 _ _ (FiniteClockHandReadout.Q_trace 1),event0_entry]
  norm_num [FiniteQutritRetainedClock.rho0,FiniteQutritPhysicalMemory.projector]


theorem adaptive_reachable_second {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (n : ℕ) :
    (∀ a : A,0<(run S Unit 22 (policyTree Unit ω ℏ hℏ
      (truncatePolicy (measuredAdaptivePolicy hω (n+1)) 1 (by omega)))
      (outcomeEquiv (a,FiniteQutritRetainedClock.noneLabel),())
      (input FiniteClockHandReadout.rhoPlus)).trace.re) ∧
    FiniteClockControlledRetainedMemory.durationAt (measuredAdaptivePolicy hω (n+1))
      ((0:Fin (n+1)).succ) (outcomeEquiv (0,FiniteQutritRetainedClock.noneLabel),()) ≠
    FiniteClockControlledRetainedMemory.durationAt (measuredAdaptivePolicy hω (n+1))
      ((0:Fin (n+1)).succ) (outcomeEquiv (1,FiniteQutritRetainedClock.noneLabel),()) := by
  constructor
  · intro a
    change 0<((step Unit ω ℏ (quarterDuration hω) hℏ).branch S Unit 22
      (outcomeEquiv (a,FiniteQutritRetainedClock.noneLabel)) (input FiniteClockHandReadout.rhoPlus)).trace.re
    rw [adaptive_first_masses hω hℏ]
    norm_num
  · rw [adaptive_second_duration,adaptive_second_duration]
    simp only [feedbackDuration,if_pos rfl,ite_true,show (1:A) ≠ 0 by decide,if_false]
    intro he
    have hv := congrArg Subtype.val he
    change Real.pi/(3*ω)=2*Real.pi/(3*ω) at hv
    have hd := (div_lt_div_iff_of_pos_right (by positivity : 0<3*ω)).2
      (show Real.pi<2*Real.pi by linarith [Real.pi_pos])
    exact (ne_of_lt hd) hv

theorem half_zero_gap {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) :
    |terminalProbability ω ℏ hℏ (twoPolicy (keepDuration hω) zeroDuration)
      (input FiniteClockHandReadout.rhoPlus)-freshTerminalProbability ω ℏ hℏ
        (twoPolicy (keepDuration hω) zeroDuration) (input FiniteClockHandReadout.rhoPlus)|=1/5 := by
  rw [(half_zero_events hω hℏ).1,(half_zero_events hω hℏ).2]
  norm_num

theorem scalar_initial_reset {ℏ : ℝ} (hℏ : ℏ ≠ 0) (t : ℝ) (a : A) (i : Fin 11) :
    (step Unit 0 ℏ t hℏ).branch S Unit 22 (outcomeEquiv (a,i))
      (input FiniteClockHandReadout.rhoPlus)=
      if a=1 ∧ i=FiniteQutritRetainedClock.noneLabel then afterFirstLabel 1 else 0 := by
  rw [first_branch]
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl <;>
    simp [FiniteClockHandReadout.mass,FiniteClockHandReadout.p]

theorem scalar_arbitrary_duration {ℏ : ℝ} (hℏ : ℏ ≠ 0) (t s : ℝ) (a : A) (i : Fin 11) (Z : FullMat F) :
    (step F 0 ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z=
      (step F 0 ℏ s hℏ).branch S F 22 (outcomeEquiv (a,i)) Z := by
  rw [branch_action,branch_action,extract_frequency F hℏ,extract_frequency F hℏ]
  simp only [zero_mul]

theorem universal_time_alias {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (t : ℝ)
    (a : A) (i : Fin 11) (Z : FullMat F) :
    (step F ω ℏ (t+2*Real.pi/ω) hℏ).branch S F 22 (outcomeEquiv (a,i)) Z=
      (step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z := by
  rw [branch_action,branch_action,extract_frequency F hℏ,extract_frequency F hℏ]
  have he : ω*(t+2*Real.pi/ω)=ω*t+2*Real.pi := by field_simp <;> ring
  rw [he,extraction_periodic]

theorem reset_data_nonunital :
    (∑ i : Fin 11,krausMap (FiniteClockControlledRetainedMemory.dataKraus 1 i) (1:DataMat))≠1 := by
  rw [reset_data_one]
  intro he
  have h := congrFun (congrFun he (0,0)) (0,0)
  norm_num [FiniteQutritRetainedClock.P,FiniteQutritRetainedClock.e,Matrix.single,Matrix.one_apply] at h

theorem bell_not_product : ¬∃ x : B → ℂ,∃ y : A → ℂ,
    ∀ b a,bellRect (b,a) ()=x b*y a := by
  rintro ⟨x,y,h⟩
  have he : bellRect ((0,0),0) ()*bellRect ((1,0),1) ()=
      bellRect ((0,0),1) ()*bellRect ((1,0),0) () := by
    rw [h,h,h,h]
    ring
  norm_num [bellRect] at he


def tensorVector (x : B → ℂ) (y : A → ℂ) : Matrix S Unit ℂ := fun z _ => x z.1*y z.2

theorem inverse_rotation_product (θ : ℝ) (x : B → ℂ) (y : A → ℂ) :
    (handRotation θ)ᴴ*tensorVector x y=
      tensorVector x (fun u => ∑ v : A,FiniteClockHandReadout.U 1 1 θ u v*y v) := by
  ext ⟨b,u⟩ f
  cases f
  simp [handRotation,tensorVector,Matrix.conjTranspose_kronecker,Matrix.mul_apply,
    Fintype.sum_prod_type,Matrix.one_apply,apply_ite,Finset.mul_sum,mul_assoc]
  ring

theorem rotatedBell_not_product (θ : ℝ) : ¬∃ x : B → ℂ,∃ y : A → ℂ,
    handRotation θ*bellRect=tensorVector x y := by
  rintro ⟨x,y,he⟩
  have hr : bellRect=(handRotation θ)ᴴ*tensorVector x y := by
    rw [← he,← Matrix.mul_assoc,handRotation_normalized,Matrix.one_mul]
  rw [inverse_rotation_product] at hr
  apply bell_not_product
  refine ⟨x,(fun u => ∑ v : A,FiniteClockHandReadout.U 1 1 θ u v*y v),?_⟩
  intro b a
  exact congrFun (congrFun hr (b,a)) ()

theorem rotatedBell_pure (θ : ℝ) : rotatedBell θ=
    (handRotation θ*bellRect)*(handRotation θ*bellRect)ᴴ := by
  simp only [rotatedBell,bell,Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem recovery_physical_even {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k n : ℕ)
    (ks : List ℕ) (hlen : ks.length+1=2*n) {q : FiniteQutritInvariantReconstruction.FeatureSpace}
    (hq : q∈FiniteQutritInvariantReconstruction.density) :
    IsDensityOperator (recoveryJoint hω ℏ hℏ k ks
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q))) ∧
    FiniteQutritRetainedClock.clockMarginal (recoveryJoint hω ℏ hℏ k ks
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q)))=FiniteQutritRetainedClock.P 0 := by
  rw [recoveryJoint_old,hlen]
  exact FiniteQutritRetainedClock.quotient_physical_even n hq

theorem recovery_physical_odd {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) (k n : ℕ)
    (ks : List ℕ) (hlen : ks.length+1=2*n+1) {q : FiniteQutritInvariantReconstruction.FeatureSpace}
    (hq : q∈FiniteQutritInvariantReconstruction.density) :
    IsDensityOperator (recoveryJoint hω ℏ hℏ k ks
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q))) ∧
    FiniteQutritRetainedClock.clockMarginal (recoveryJoint hω ℏ hℏ k ks
      (FiniteQutritRetainedClock.E0 (FiniteQutritInvariantReconstruction.U q)))=FiniteQutritRetainedClock.P 1 := by
  rw [recoveryJoint_old,hlen]
  exact FiniteQutritRetainedClock.quotient_physical_odd n hq

/-- This is a finite externally sequenced measured hand. No autonomous clock,
continuum limit, spectral gap or dimension12 minimum-memory assertion is made. -/
theorem carrier_dimensions : Fintype.card B=6 ∧ Fintype.card S=12 ∧
    (instrument 1 1 0 (by norm_num)).count=2 ∧ Fintype.card (Fin 22)=22 := by
  decide


theorem conditional_reset_channel {ℏ : ℝ} (hℏ : ℏ ≠ 0) (t : ℝ) (Y : ReducedMat F) :
    (∑ i : Fin 11,(step F 0 ℏ t hℏ).branch S F 22 (outcomeEquiv (1,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q 1)))=
      FiniteClockControlledRetainedMemory.insert F
        (FiniteQutritRetainedClock.amplified F
          (krausMap (fun c => FiniteQutritRetainedClock.L c ⊗ₖ (1:Matrix F F ℂ)) Y))
        (FiniteClockHandReadout.Q 1) := by
  simp only [posterior_scalar,if_pos rfl,ite_true]
  rw [← FiniteClockControlledRetainedMemory.insert_sum,dataBranch_reset_sum]

theorem conditional_reset_nonunital {ℏ : ℝ} (hℏ : ℏ ≠ 0) (t : ℝ) :
    (∑ i : Fin 11,(step Unit 0 ℏ t hℏ).branch S Unit 22 (outcomeEquiv (1,i))
      (FiniteClockControlledRetainedMemory.insert Unit ((1:DataMat) ⊗ₖ (1:Matrix Unit Unit ℂ))
        (FiniteClockHandReadout.Q 1)))≠
      FiniteClockControlledRetainedMemory.insert Unit ((1:DataMat) ⊗ₖ (1:Matrix Unit Unit ℂ))
        (FiniteClockHandReadout.Q 1) := by
  rw [conditional_reset_channel,reset_product,FiniteQutritRetainedClock.amplified_product]
  have hr := reset_data_one
  rw [FiniteClockControlledRetainedMemory.data_action_reset] at hr
  rw [hr]
  intro he
  have hh := congrFun (congrFun he (((0,0),1),())) (((0,0),1),())
  norm_num [FiniteClockControlledRetainedMemory.insert,FiniteClockHandReadout.Q,
    FiniteQutritRetainedClock.P,FiniteQutritRetainedClock.e,Matrix.single,Matrix.one_apply] at hh

theorem gibbs_posterior_changes (ω ℏ β : ℝ) (a : A) :
    FiniteClockHandReadout.Q a≠FiniteGibbsClock.gibbs (FiniteClockHandReadout.H ω ℏ) β := by
  intro he
  rw [FiniteClockHandReadout.gibbs_diagonal] at he
  have h := congrFun (congrFun he 0) 1
  fin_cases a <;> norm_num [FiniteClockHandReadout.Q,Matrix.diagonal] at h

theorem weighted_table_trace (w : A → A → ℝ) (a b : A) (i j : Fin 11) :
    (weightedTable w a b i j).trace.re=
      if i=FiniteQutritRetainedClock.noneLabel then w a b*(dataSecond b j).trace.re else 0 := by
  unfold weightedTable
  split
  · simp [Matrix.trace_smul,FiniteClockControlledRetainedMemory.insert_trace,
      FiniteClockHandReadout.Q_trace,Complex.mul_re]
  · simp

theorem calibrated_fresh_weight_positive {ω : ℝ} (hω : 0<ω) (a b : A) :
    0<FiniteClockHandReadout.mass ω (rightDuration hω) a*FiniteClockHandReadout.mass ω (leftDuration hω) b := by
  simp only [FiniteClockHandReadout.mass,rightDuration,leftDuration,Subtype.coe_mk,
    FiniteClockHandReadout.p_right hω.ne',FiniteClockHandReadout.p_left hω.ne']
  fin_cases a <;> fin_cases b <;> norm_num

theorem calibrated_fresh_leaf_support {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0)
    (a b : A) (i j : Fin 11) :
    0<(run S Unit 22 (FiniteClockControlledRetainedMemory.policyTree Unit ω ℏ hℏ
      (twoPolicy (rightDuration hω) (leftDuration hω)))
      (outcomeEquiv (a,i),outcomeEquiv (b,j),()) (input FiniteClockHandReadout.rhoPlus)).trace.re ↔
      liveLeaf ((a,i),(b,j)) := by
  have hp := calibrated_leaf_support hω hℏ a b i j
  rw [two_round_table,table_trace] at hp
  rw [fresh_two_round_table,weighted_table_trace]
  by_cases hi : i=FiniteQutritRetainedClock.noneLabel
  · rw [if_pos hi,mul_pos_iff_of_pos_left (calibrated_weight_positive hω a b)] at hp
    rw [if_pos hi,mul_pos_iff_of_pos_left (calibrated_fresh_weight_positive hω a b)]
    exact hp
  · simp only [hi,ite_false] at hp ⊢
    exact hp

theorem actual_positive_history_count {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) :
    Fintype.card {h : History 22 2 // 0<(run S Unit 22
      (policyTree Unit ω ℏ hℏ (twoPolicy (rightDuration hω) (leftDuration hω))) h
      (input FiniteClockHandReadout.rhoPlus)).trace.re}=16 := by
  let e := twoHistoryEquiv.subtypeEquiv (p:=liveLeaf)
    (q:=fun h => 0<(run S Unit 22 (policyTree Unit ω ℏ hℏ
      (twoPolicy (rightDuration hω) (leftDuration hω))) h (input FiniteClockHandReadout.rhoPlus)).trace.re)
    (fun h => (calibrated_leaf_support hω hℏ h.1.1 h.2.1 h.1.2 h.2.2).symm)
  have hc := Fintype.card_congr e
  rw [positive_leaf_count] at hc
  exact hc.symm

theorem actual_fresh_positive_history_count {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0) :
    Fintype.card {h : History 22 2 // 0<(run S Unit 22
      (FiniteClockControlledRetainedMemory.policyTree Unit ω ℏ hℏ
        (twoPolicy (rightDuration hω) (leftDuration hω))) h
      (input FiniteClockHandReadout.rhoPlus)).trace.re}=16 := by
  let e := twoHistoryEquiv.subtypeEquiv (p:=liveLeaf)
    (q:=fun h => 0<(run S Unit 22 (FiniteClockControlledRetainedMemory.policyTree Unit ω ℏ hℏ
      (twoPolicy (rightDuration hω) (leftDuration hω))) h (input FiniteClockHandReadout.rhoPlus)).trace.re)
    (fun h => (calibrated_fresh_leaf_support hω hℏ h.1.1 h.2.1 h.1.2 h.2.2).symm)
  have hc := Fintype.card_congr e
  rw [positive_leaf_count] at hc
  exact hc.symm

theorem identical_recorded_family {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} (P : Policy n) (Z : FullMat F) :
    FiniteAdaptiveMapPerturbation.outputDistance S F 22
      (policyTree F ω ℏ hℏ P) (policyTree F ω ℏ hℏ P) Z Z=0 := by
  simp [FiniteAdaptiveMapPerturbation.outputDistance,traceNorm_zero]

theorem identical_readout_half {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} (P : Policy n)
    {Z : FullMat F} (hZ : IsDensityOperator Z) (R : History 22 n → FullMat F) :
    FiniteAdaptiveReadoutDiscrimination.readoutError
      (fun h => run S F 22 (policyTree F ω ℏ hℏ P) h Z)
      (fun h => run S F 22 (policyTree F ω ℏ hℏ P) h Z) R=1/2 :=
  FiniteAdaptiveReadoutRobustness.identical_family_error
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ P) hZ) R


def resetOldStep (ω ℏ t : ℝ) (hℏ : ℏ ≠ 0) : Step S Unit 22 where
  count := 2
  evolution := fun c => (FiniteQutritRetainedClock.L c ⊗ₖ (1:Matrix A A ℂ)) ⊗ₖ (1:Matrix Unit Unit ℂ)
  normalized := resetOld_normalized
  instrument := instrument ω ℏ t hℏ

theorem resetOldStep_branch {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (o : Fin 22) (Z : FullMat Unit) :
    (resetOldStep ω ℏ t hℏ).branch S Unit 22 o Z=
      (step Unit ω ℏ t hℏ).branch S Unit 22 o (resetOld Z) := by
  simp only [resetOldStep,Step.branch,step,localStep,resetOld,krausMap,
    Matrix.mul_one,Matrix.one_mul,Matrix.conjTranspose_one,Fintype.sum_unique]
  rfl

def resetThreeTree (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) (t s r : Duration) : Tree S Unit 22 3 :=
  .node (resetOldStep ω ℏ t hℏ) (fun _ =>
    .node (resetOldStep ω ℏ s hℏ) (fun _ =>
      .node (resetOldStep ω ℏ r hℏ) (fun _ => .done)))

theorem reset_prepared_branch {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ)
    (c a b : A) (i : Fin 11) :
    (resetOldStep ω ℏ t hℏ).branch S Unit 22 (outcomeEquiv (b,i))
      (FiniteClockControlledRetainedMemory.insert Unit (prepareData c FiniteQutritRetainedClock.rho0)
        (FiniteClockHandReadout.Q a))=
      if i=FiniteQutritRetainedClock.noneLabel then (transition ω t b a:ℂ) • afterFirstLabel b else 0 := by
  rw [resetOldStep_branch,resetOld_prepare,branch_posterior,data_first]
  split
  · rfl
  · rw [FiniteClockControlledRetainedMemoryExamples.insert_zero,smul_zero]

/-- Actual reset-old-before-each tree retains all micro records; it does not replace the hand. -/
theorem reset_three_record_table {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) (t s r : Duration)
    (a b c : A) (i j k : Fin 11) :
    run S Unit 22 (resetThreeTree ω ℏ hℏ t s r)
      (outcomeEquiv (a,i),outcomeEquiv (b,j),outcomeEquiv (c,k),())
      (input FiniteClockHandReadout.rhoPlus)=
      if i=FiniteQutritRetainedClock.noneLabel ∧ j=FiniteQutritRetainedClock.noneLabel ∧
          k=FiniteQutritRetainedClock.noneLabel then
        ((transition ω t a 1*transition ω s b a*transition ω r c b:ℝ):ℂ) • afterFirstLabel c else 0 := by
  change (resetOldStep ω ℏ r hℏ).branch S Unit 22 (outcomeEquiv (c,k))
    ((resetOldStep ω ℏ s hℏ).branch S Unit 22 (outcomeEquiv (b,j))
      ((resetOldStep ω ℏ t hℏ).branch S Unit 22 (outcomeEquiv (a,i))
        (input FiniteClockHandReadout.rhoPlus)))=_
  rw [input,FiniteClockHandReadout.rhoPlus_eq,reset_prepared_branch]
  by_cases hi : i=FiniteQutritRetainedClock.noneLabel
  · rw [if_pos hi,Step.branch_smul,afterFirstLabel,reset_prepared_branch]
    by_cases hj : j=FiniteQutritRetainedClock.noneLabel
    · rw [if_pos hj,Step.branch_smul,Step.branch_smul,afterFirstLabel,reset_prepared_branch]
      by_cases hk : k=FiniteQutritRetainedClock.noneLabel
      · rw [if_pos hk,if_pos ⟨hi,hj,hk⟩,smul_smul,smul_smul,Complex.ofReal_mul,Complex.ofReal_mul]
      · simp only [hk,ite_false,smul_zero,and_false]
    · simp [hj,Step.branch_zero,smul_zero]
  · simp [hi,Step.branch_zero]


theorem order_hand_words {ω : ℝ} (hω : 0<ω) (a b c : A) :
    transition ω (keepDuration hω) a 1*transition ω (keepDuration hω) b a*transition ω 0 c b=
      (if a=0 ∧ b=1 ∧ c=1 then 1 else 0) ∧
    transition ω (keepDuration hω) a 1*transition ω 0 b a*transition ω (keepDuration hω) c b=
      (if a=0 ∧ b=0 ∧ c=1 then 1 else 0) := by
  simp only [transition,keepDuration,Subtype.coe_mk,FiniteClockHandReadout.p_keep hω.ne',
    FiniteClockHandReadout.p_zero]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num

theorem order_first_records {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0)
    (a b c : A) (i j k : Fin 11) :
    run S Unit 22 (policyTree Unit ω ℏ hℏ
      (threePolicy (keepDuration hω) (keepDuration hω) zeroDuration))
      (outcomeEquiv (a,i),outcomeEquiv (b,j),outcomeEquiv (c,k),()) (input FiniteClockHandReadout.rhoPlus)=
      (if a=0 ∧ b=1 ∧ c=1 then (1:ℂ) else 0) •
        FiniteClockControlledRetainedMemory.insert Unit
          (FiniteClockControlledRetainedMemory.dataBranch Unit c k
            (FiniteClockControlledRetainedMemory.dataBranch Unit b j
              (FiniteClockControlledRetainedMemory.dataBranch Unit a i (prepareData 0 FiniteQutritRetainedClock.rho0))))
          (FiniteClockHandReadout.Q c) := by
  rw [input,FiniteClockHandReadout.rhoPlus_eq,three_round_table]
  have hh := (order_hand_words hω a b c).1
  change transition ω (keepDuration hω) a 1*transition ω (keepDuration hω) b a*
    transition ω (zeroDuration:ℝ) c b=_ at hh
  rw [hh]
  split <;> rfl

theorem order_second_records {ω ℏ : ℝ} (hω : 0<ω) (hℏ : ℏ ≠ 0)
    (a b c : A) (i j k : Fin 11) :
    run S Unit 22 (policyTree Unit ω ℏ hℏ
      (threePolicy (keepDuration hω) zeroDuration (keepDuration hω)))
      (outcomeEquiv (a,i),outcomeEquiv (b,j),outcomeEquiv (c,k),()) (input FiniteClockHandReadout.rhoPlus)=
      (if a=0 ∧ b=0 ∧ c=1 then (1:ℂ) else 0) •
        FiniteClockControlledRetainedMemory.insert Unit
          (FiniteClockControlledRetainedMemory.dataBranch Unit c k
            (FiniteClockControlledRetainedMemory.dataBranch Unit b j
              (FiniteClockControlledRetainedMemory.dataBranch Unit a i (prepareData 0 FiniteQutritRetainedClock.rho0))))
          (FiniteClockHandReadout.Q c) := by
  rw [input,FiniteClockHandReadout.rhoPlus_eq,three_round_table]
  have hh := (order_hand_words hω a b c).2
  change transition ω (keepDuration hω) a 1*transition ω (zeroDuration:ℝ) b a*
    transition ω (keepDuration hω) c b=_ at hh
  rw [hh]
  split <;> rfl


theorem zero_branch_guard {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (o : Fin 22)
    {Z : FullMat F} (hZ : Z.PosSemidef)
    (hm : ((step F ω ℏ t hℏ).branch S F 22 o Z).trace.re=0) :
    (step F ω ℏ t hℏ).branch S F 22 o Z=0 :=
  zero_mass_psd F (branch_positive F hℏ ω t o hZ) hm

end SKEFTHawking.QuantumNetwork.FinitePersistentMeasuredHandExamples
