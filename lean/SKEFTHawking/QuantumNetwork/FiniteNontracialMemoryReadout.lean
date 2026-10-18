import SKEFTHawking.QuantumNetwork.FiniteNontracialEnvironmentLift
import SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness

/-! Actual diagonal retained-memory trees and attained physical readout.
The system/environment order is S × E. Four depth-two histories are retained.
The Flip channel applies X on E before the actual schedule. No branch mass
is divided out. Physical readout uses the existing computational E projectors.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteNontracialMemoryReadout
open Matrix FiniteInterventionProcess FiniteMemoryProcess
open FiniteAdaptiveMapPerturbation FiniteAdaptiveReadoutDiscrimination FiniteAdaptiveReadoutRobustness
open FiniteNontracialSchedule (Schedule alpha G D)
open scoped BigOperators Kronecker ComplexOrder

abbrev Q := Fin 2
abbrev MatQ := Matrix Q Q ℂ
abbrev MatJoint := Matrix (Q × Q) (Q × Q) ℂ
abbrev H := History 2 2
def keepStep (s : Schedule) : Step Q Q 2 :=
 FiniteNontracialEnvironmentLift.scheduleStep s (FiniteInstrument.prepare 0)
def flipKraus (s : Schedule) :=
 composeKraus (FiniteNontracialEnvironmentLift.scheduleKraus s) environmentXKraus
theorem flip_normalized (s : Schedule) : IsKrausChannel (flipKraus s) :=
 isKrausChannel_composeKraus (FiniteNontracialEnvironmentLift.schedule_normalized s) environmentX_normalized
def flipStep (s : Schedule) : Step Q Q 2 :=
 realizedStep Q Q 2 (flipKraus s) (flip_normalized s) (FiniteInstrument.prepare 0)
def keepTree (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (keepStep s) (fun _ => .done))
def flipTree (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (flipStep s) (fun _ => .done))
def keepFamily (s : Schedule) (h : H) : MatJoint := run Q Q 2 (keepTree s) h correlatedInput
def flipFamily (s : Schedule) (h : H) : MatJoint := run Q Q 2 (flipTree s) h correlatedInput

theorem keepStep_tensor (s : Schedule) (a c : Q) (B : MatQ) :
 (keepStep s).branch Q Q 2 a (basisState c ⊗ₖ B) =
 if a=0 then basisState 0 ⊗ₖ FiniteNontracialSchedule.state s B else 0 := by
 rw [keepStep, FiniteNontracialEnvironmentLift.scheduleStep_branch,
  FiniteNontracialEnvironmentLift.schedule_product, lift_branch_tensor, prepare_basis]
 split_ifs <;> simp_all
theorem flipStep_basis (s : Schedule) (a c e : Q) :
 (flipStep s).branch Q Q 2 a (basisState c ⊗ₖ basisState e) =
 if a=0 then basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState (1-e)) else 0 := by
 change ((FiniteInstrument.prepare 0).lift Q).branch a (krausMap (flipKraus s) _) = _
 rw [flipKraus, krausMap_composeKraus, environmentX_basis]
 change (keepStep s).branch Q Q 2 a (basisState c ⊗ₖ basisState (1-e)) = _
 exact keepStep_tensor s a c _
theorem keep_run (s : Schedule) (i j : Q) :
 keepFamily s (i,j,()) =
 if j=0 then (1/2:ℂ) • (basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState i)) else 0 := by
 change (keepStep s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput) = _
 rw [readStep_correlated, Step.branch_smul, keepStep_tensor]
 split_ifs <;> simp
theorem flip_run (s : Schedule) (i j : Q) :
 flipFamily s (i,j,()) =
 if j=0 then (1/2:ℂ) • (basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState (1-i))) else 0 := by
 change (flipStep s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput) = _
 rw [readStep_correlated, Step.branch_smul, flipStep_basis]
 split_ifs <;> simp
theorem keep_valid (s : Schedule) : IsBranchFamily (keepFamily s) := run_family _ correlatedInput_density
theorem flip_valid (s : Schedule) : IsBranchFamily (flipFamily s) := run_family _ correlatedInput_density
theorem keep_run_history (s : Schedule) (h : H) :
 keepFamily s h =
 if h.2.1=0 then (1/2:ℂ) • (basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState h.1)) else 0 := by
 rcases h with ⟨i,j,⟨⟩⟩
 exact keep_run s i j
theorem flip_run_history (s : Schedule) (h : H) :
 flipFamily s h =
 if h.2.1=0 then (1/2:ℂ) • (basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState (1-h.1))) else 0 := by
 rcases h with ⟨i,j,⟨⟩⟩
 exact flip_run s i j
theorem branch_traces (s : Schedule) (h : H) :
 (keepFamily s h).trace = (if h.2.1=0 then (1/2:ℂ) else 0) ∧
 (flipFamily s h).trace = (if h.2.1=0 then (1/2:ℂ) else 0) := by
 rw [keep_run_history, flip_run_history]
 split_ifs <;> simp [Matrix.trace_smul, Matrix.trace_kronecker,
  FiniteNontracialSchedule.state_trace, (basisState_density 0).2,
  (basisState_density h.1).2, (basisState_density (1-h.1)).2]
theorem basis_diagonal (i : Q) :
 NontracialReflectionDynamics.diagonalPart (basisState i) = basisState i := by
 ext a b
 fin_cases i <;> fin_cases a <;> fin_cases b <;>
  simp [NontracialReflectionDynamics.diagonalPart, basisState]
theorem basis_state (s : Schedule) (i : Q) :
 FiniteNontracialSchedule.state s (basisState i) =
 ((1-alpha s:ℝ):ℂ) • NontracialPauliReflection.rhoN + (alpha s:ℂ) • basisState i := by
 rw [FiniteNontracialSchedule.state_convex_formula, (basisState_density i).2, basis_diagonal]
 simp only [one_smul, Complex.ofReal_sub, Complex.ofReal_one]
 module


theorem same_history (s : Schedule) (h : H) :
 (keepFamily s h).trace.re = (flipFamily s h).trace.re :=
 congrArg Complex.re ((branch_traces s h).1.trans (branch_traces s h).2.symm)
theorem weights (s : Schedule) (i j : Q) :
 weight Q Q 2 (keepTree s) (i,j,()) correlatedInput = (if j=0 then 1/2 else 0) ∧
 weight Q Q 2 (flipTree s) (i,j,()) correlatedInput = (if j=0 then 1/2 else 0) := by
 change (keepFamily s (i,j,())).trace.re = _ ∧ (flipFamily s (i,j,())).trace.re = _
 rw [(branch_traces s (i,j,())).1, (branch_traces s (i,j,())).2]
 split_ifs <;> norm_num
theorem history_error (s : Schedule) (a : H → ℝ) :
 historyError (keepFamily s) (flipFamily s) a = 1/2 :=
 historyError_same_law (keep_valid s) (same_history s) a
theorem branch_marginals (s : Schedule) (h : H) :
 FiniteNontracialEnvironmentLift.ptrace2 (keepFamily s h) =
 (if h.2.1=0 then (1/2:ℂ) • basisState 0 else 0) ∧
 FiniteNontracialEnvironmentLift.ptrace2 (flipFamily s h) =
 (if h.2.1=0 then (1/2:ℂ) • basisState 0 else 0) := by
 have hz : FiniteNontracialEnvironmentLift.ptrace2 (0 : MatJoint) = 0 := by
  ext a b; simp [FiniteNontracialEnvironmentLift.ptrace2]
 rw [keep_run_history, flip_run_history]
 split_ifs <;> simp [hz, FiniteNontracialEnvironmentLift.ptrace2_smul,
  FiniteNontracialEnvironmentLift.ptrace2_kronecker,
  FiniteNontracialSchedule.state_trace, (basisState_density h.1).2,
  (basisState_density (1-h.1)).2]
abbrev population := NontracialPauliReflection.weights
theorem physical_table (s : Schedule) (i j b : Q) :
 readoutTable correlationReadout (keepFamily s) (i,j,()) b =
 (if j=0 then (if b=0 then (alpha s+(1-alpha s)*population i)/2
 else (1-alpha s)*population (1-i)/2) else 0) ∧
 readoutTable correlationReadout (flipFamily s) (i,j,()) b =
 (if j=0 then (if b=0 then (1-alpha s)*population i/2
 else (alpha s+(1-alpha s)*population (1-i))/2) else 0) := by
 fin_cases b
 · change (correlationReadout _).weight 0 _ = _ ∧ (correlationReadout _).weight 0 _ = _
   rw [correlationReadout_weight_zero, correlationReadout_weight_zero, keep_run, flip_run]
   fin_cases i <;> fin_cases j <;>
    norm_num [basis_state, correlationEffect, Matrix.mul_apply, Matrix.trace,
     Matrix.kronecker_apply, basisState, Matrix.one_apply, Fintype.sum_prod_type,
     Fin.sum_univ_two, NontracialPauliReflection.rhoN, population,
     NontracialPauliReflection.weights, Matrix.smul_apply, Matrix.add_apply,
     smul_eq_mul, Complex.ofReal_sub]
   <;> constructor <;> ring
 · change (correlationReadout _).weight 1 _ = _ ∧ (correlationReadout _).weight 1 _ = _
   rw [correlationReadout_weight_one, correlationReadout_weight_one, keep_run, flip_run]
   fin_cases i <;> fin_cases j <;>
    norm_num [basis_state, correlationEffect, Matrix.mul_apply, Matrix.trace,
     Matrix.kronecker_apply, basisState, Matrix.one_apply, Fintype.sum_prod_type,
     Fin.sum_univ_two, NontracialPauliReflection.rhoN, population,
     NontracialPauliReflection.weights, Matrix.smul_apply, Matrix.add_apply,
     smul_eq_mul, Complex.ofReal_sub]
   <;> constructor <;> ring

theorem physical_table_history (s : Schedule) (h : H) (b : Q) :
 readoutTable correlationReadout (keepFamily s) h b =
 (if h.2.1=0 then (if b=0 then (alpha s+(1-alpha s)*population h.1)/2
 else (1-alpha s)*population (1-h.1)/2) else 0) ∧
 readoutTable correlationReadout (flipFamily s) h b =
 (if h.2.1=0 then (if b=0 then (1-alpha s)*population h.1/2
 else (alpha s+(1-alpha s)*population (1-h.1))/2) else 0) := by
 rcases h with ⟨i,j,⟨⟩⟩
 exact physical_table s i j b
theorem keep_noise (s : Schedule) :
 keepFamily s = FiniteNontracialEnvironmentLift.scheduleFamily s
 (fun h => run Q Q 2 correlationKeep h correlatedInput) := by
 funext h
 rcases h with ⟨i,j,⟨⟩⟩
 change keepFamily s (i,j,()) = FiniteNontracialEnvironmentLift.scheduleState s
  (run Q Q 2 correlationKeep (i,j,()) correlatedInput)
 rw [keep_run, correlationKeep_run]
 unfold FiniteNontracialEnvironmentLift.scheduleState
 split_ifs
 · rw [krausMap_smul]
   congr 1
   exact (FiniteNontracialEnvironmentLift.schedule_product s _ _).symm
 · simp [krausMap]
theorem flip_noise (s : Schedule) :
 flipFamily s = FiniteNontracialEnvironmentLift.scheduleFamily s
 (fun h => run Q Q 2 correlationFlip h correlatedInput) := by
 funext h
 rcases h with ⟨i,j,⟨⟩⟩
 change flipFamily s (i,j,()) = FiniteNontracialEnvironmentLift.scheduleState s
  (run Q Q 2 correlationFlip (i,j,()) correlatedInput)
 rw [flip_run, correlationFlip_run]
 unfold FiniteNontracialEnvironmentLift.scheduleState
 split_ifs
 · rw [krausMap_smul]
   congr 1
   exact (FiniteNontracialEnvironmentLift.schedule_product s _ _).symm
 · simp [krausMap]
theorem terminal (s : Schedule) :
 terminalState Q Q 2 (keepTree s) correlatedInput =
 basisState 0 ⊗ₖ FiniteNontracialSchedule.state s ((1/2:ℂ) • (1:MatQ)) ∧
 terminalState Q Q 2 (flipTree s) correlatedInput =
 basisState 0 ⊗ₖ FiniteNontracialSchedule.state s ((1/2:ℂ) • (1:MatQ)) := by
 change (∑ h, keepFamily s h) = _ ∧ (∑ h, flipFamily s h) = _
 rw [keep_noise, flip_noise]
 change (∑ h, FiniteNontracialEnvironmentLift.liftState (FiniteNontracialSchedule.scheduleKraus s)
   (run Q Q 2 correlationKeep h correlatedInput)) = _ ∧
  (∑ h, FiniteNontracialEnvironmentLift.liftState (FiniteNontracialSchedule.scheduleKraus s)
   (run Q Q 2 correlationFlip h correlatedInput)) = _
 rw [← FiniteNontracialEnvironmentLift.liftState_sum, ← FiniteNontracialEnvironmentLift.liftState_sum]
 change FiniteNontracialEnvironmentLift.scheduleState s
  (terminalState Q Q 2 correlationKeep correlatedInput) = _ ∧
  FiniteNontracialEnvironmentLift.scheduleState s
  (terminalState Q Q 2 correlationFlip correlatedInput) = _
 rw [correlation_terminal.1, correlation_terminal.2,
  FiniteNontracialEnvironmentLift.schedule_product]
 exact ⟨rfl,rfl⟩
theorem table_normalized (s : Schedule) :
 (∀ h b, 0 ≤ readoutTable correlationReadout (keepFamily s) h b) ∧
 (∑ h, ∑ b, readoutTable correlationReadout (keepFamily s) h b)=1 ∧
 (∀ h b, 0 ≤ readoutTable correlationReadout (flipFamily s) h b) ∧
 (∑ h, ∑ b, readoutTable correlationReadout (flipFamily s) h b)=1 :=
 ⟨readoutTable_nonneg _ (keep_valid s), readoutTable_total _ (keep_valid s),
 readoutTable_nonneg _ (flip_valid s), readoutTable_total _ (flip_valid s)⟩
theorem instrument_error (s : Schedule) :
 instrumentError (keepFamily s) (flipFamily s) correlationReadout = (1-alpha s)/2 := by
 unfold instrumentError
 change ((∑ h : Q × (Q × Unit), _) + (∑ h : Q × (Q × Unit), _))/2 = _
 simp_rw [(physical_table_history s _ 0).2, (physical_table_history s _ 1).1]
 norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique,
  population, NontracialPauliReflection.weights]
 ring
theorem effect_error (s : Schedule) :
 readoutError (keepFamily s) (flipFamily s) correlationEffect = (1-alpha s)/2 := by
 have hh := instrument_error s
 simpa only [instrumentError, readoutTable, correlationReadout_weight_zero,
  correlationReadout_weight_one, readoutError] using hh

theorem original_marginals (h : H) :
 FiniteNontracialEnvironmentLift.ptrace2 (run Q Q 2 correlationKeep h correlatedInput) =
 FiniteNontracialEnvironmentLift.ptrace2 (run Q Q 2 correlationFlip h correlatedInput) := by
 rw [correlationKeep_run_history, correlationFlip_run_history]
 split_ifs
 · rw [FiniteNontracialEnvironmentLift.ptrace2_smul, FiniteNontracialEnvironmentLift.ptrace2_smul,
   FiniteNontracialEnvironmentLift.ptrace2_kronecker, FiniteNontracialEnvironmentLift.ptrace2_kronecker,
   (basisState_density h.1).2, (basisState_density (1-h.1)).2]
 · rfl
theorem original_distance :
 branchDistance (fun h => run Q Q 2 correlationKeep h correlatedInput)
 (fun h => run Q Q 2 correlationFlip h correlatedInput) = 1 := by
 have he : branchDistance (fun h => run Q Q 2 correlationKeep h correlatedInput)
  (fun h => run Q Q 2 correlationFlip h correlatedInput) =
  outputDistance Q Q 2 correlationKeep correlationFlip correlatedInput correlatedInput := by
  simp only [branchDistance, outputDistance, traceDist, div_eq_mul_inv,
   one_mul, mul_comm, Finset.mul_sum]
 exact he.trans correlation_outputDistance_one
/-- The upper bound consumes normalized actual families and every cut marginal. -/
theorem distance_upper (s : Schedule) :
 branchDistance (keepFamily s) (flipFamily s) ≤ alpha s := by
 rw [keep_noise, flip_noise]
 have hh := FiniteNontracialEnvironmentLift.scheduleFamily_contraction s
  (run_family correlationKeep correlatedInput_density) (run_family correlationFlip correlatedInput_density)
  original_marginals
 simpa only [original_distance, mul_one] using hh
/-- The lower bound is certified by the actual computational-basis readout. -/
theorem distance_lower (s : Schedule) :
 alpha s ≤ branchDistance (keepFamily s) (flipFamily s) := by
 have hh := readoutError_lower (keep_valid s) (flip_valid s)
  (fun h => isBinaryPOVM_of_projection (correlationEffect_hermitian h) (correlationEffect_idem h))
 rw [effect_error] at hh
 linarith
theorem branch_distance (s : Schedule) :
 branchDistance (keepFamily s) (flipFamily s) = alpha s :=
 le_antisymm (distance_upper s) (distance_lower s)
theorem output_distance (s : Schedule) :
 outputDistance Q Q 2 (keepTree s) (flipTree s) correlatedInput correlatedInput = alpha s := by
 have hh := branch_distance s
 simpa only [branchDistance, keepFamily, flipFamily, outputDistance, traceDist,
  div_eq_mul_inv, one_mul, mul_comm, Finset.mul_sum] using hh
theorem all_effect_isLeast (s : Schedule) :
 IsLeast {x : ℝ | ∃ F : H → MatJoint, (∀ h, IsBinaryPOVM (F h)) ∧
 readoutError (keepFamily s) (flipFamily s) F=x} ((1-alpha s)/2) := by
 have hh := readoutError_isLeast (keep_valid s) (flip_valid s)
 simpa only [branch_distance] using hh
theorem physical_attainment (s : Schedule) :
 (∀ h, IsBinaryPOVM (correlationEffect h)) ∧
 readoutError (keepFamily s) (flipFamily s) correlationEffect=(1-alpha s)/2 ∧
 instrumentError (keepFamily s) (flipFamily s) correlationReadout=(1-alpha s)/2 :=
 ⟨fun h => isBinaryPOVM_of_projection (correlationEffect_hermitian h) (correlationEffect_idem h),
 effect_error s, instrument_error s⟩
theorem history_isLeast (s : Schedule) :
 IsLeast {x : ℝ | ∃ a : H → ℝ, (∀ h, 0≤a h ∧ a h≤1) ∧
 historyError (keepFamily s) (flipFamily s) a=x} (1/2) := by
 constructor
 · exact ⟨fun _ => 0, fun _ => ⟨le_rfl, by norm_num⟩, history_error s _⟩
 · rintro x ⟨a,_,rfl⟩
   rw [history_error]
theorem terminal_error (s : Schedule) (F : MatJoint) :
 readoutError (keepFamily s) (flipFamily s) (fun _ => F)=1/2 := by
 apply constant_error_same_terminal (keep_valid s)
 change terminalState Q Q 2 (keepTree s) correlatedInput =
  terminalState Q Q 2 (flipTree s) correlatedInput
 exact (terminal s).1.trans (terminal s).2.symm
theorem branch_difference (s : Schedule) (i j : Q) :
 keepFamily s (i,j,()) - flipFamily s (i,j,()) =
 if j=0 then (alpha s/2:ℝ) •
  (basisState 0 ⊗ₖ (basisState i-basisState (1-i))) else 0 := by
 rw [keep_run, flip_run]
 split_ifs
 · rw [basis_state, basis_state]
   ext ⟨a,e⟩ ⟨b,f⟩
   simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.kronecker_apply,
    Matrix.add_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_ofNat]
   ring
 · simp
theorem histories_exhaustive (h : H) :
 h=(0,0,()) ∨ h=(0,1,()) ∨ h=(1,0,()) ∨ h=(1,1,()) := by
 rcases h with ⟨i,j,⟨⟩⟩
 fin_cases i <;> fin_cases j
 · exact Or.inl rfl
 · exact Or.inr (Or.inl rfl)
 · exact Or.inr (Or.inr (Or.inl rfl))
 · exact Or.inr (Or.inr (Or.inr rfl))
theorem impossible_branches (s : Schedule) (i : Q) :
 keepFamily s (i,1,())=0 ∧ flipFamily s (i,1,())=0 := by
 rw [keep_run, flip_run]; norm_num
theorem strict_error (s : Schedule) (hG : 0<G s) :
 0 < instrumentError (keepFamily s) (flipFamily s) correlationReadout ∧
 instrumentError (keepFamily s) (flipFamily s) correlationReadout < 1/2 := by
 rw [instrument_error]
 have ha : 0<alpha s := Real.exp_pos _
 have hb : alpha s<1 := by
  unfold alpha; rw [Real.exp_lt_one_iff]; linarith
 constructor <;> linarith
theorem history_improvement (s : Schedule) (a : H → ℝ) :
 historyError (keepFamily s) (flipFamily s) a -
 instrumentError (keepFamily s) (flipFamily s) correlationReadout=alpha s/2 := by
 rw [history_error, instrument_error]; ring
theorem terminal_improvement (s : Schedule) (F : MatJoint) :
 readoutError (keepFamily s) (flipFamily s) (fun _ => F) -
 instrumentError (keepFamily s) (flipFamily s) correlationReadout=alpha s/2 := by
 rw [terminal_error, instrument_error]; ring

/-- Literal numeric population table has total one independently of its positivity proof. -/
theorem literal_table_sums (s : Schedule) :
 (∑ h : H, ∑ b : Q,
  if h.2.1=0 then (if b=0 then (alpha s+(1-alpha s)*population h.1)/2
   else (1-alpha s)*population (1-h.1)/2) else 0)=1 ∧
 (∑ h : H, ∑ b : Q,
  if h.2.1=0 then (if b=0 then (1-alpha s)*population h.1/2
   else (alpha s+(1-alpha s)*population (1-h.1))/2) else 0)=1 := by
 change (∑ h : Q × (Q × Unit), ∑ b : Q, _)=1 ∧
  (∑ h : Q × (Q × Unit), ∑ b : Q, _)=1
 norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique,
  population, NontracialPauliReflection.weights]
 constructor <;> ring
theorem branch_difference_signed (s : Schedule) :
 keepFamily s (0,0,()) - flipFamily s (0,0,()) =
 (alpha s/2:ℝ) • (basisState 0 ⊗ₖ (basisState 0-basisState 1)) ∧
 keepFamily s (1,0,()) - flipFamily s (1,0,()) =
 -(alpha s/2:ℝ) • (basisState 0 ⊗ₖ (basisState 0-basisState 1)) := by
 rw [branch_difference, branch_difference]
 norm_num
 ext ⟨a,e⟩ ⟨b,f⟩
 simp only [Matrix.smul_apply, Matrix.kronecker_apply, Matrix.sub_apply,
  Matrix.neg_apply, Complex.real_smul]
 ring
theorem same_marginal (s : Schedule) (h : H) :
 FiniteNontracialEnvironmentLift.ptrace2 (keepFamily s h) =
 FiniteNontracialEnvironmentLift.ptrace2 (flipFamily s h) :=
 (branch_marginals s h).1.trans (branch_marginals s h).2.symm
theorem impossible_table (s : Schedule) (i b : Q) :
 readoutTable correlationReadout (keepFamily s) (i,1,()) b=0 ∧
 readoutTable correlationReadout (flipFamily s) (i,1,()) b=0 := by
 have hh := physical_table s i 1 b
 simpa using hh
theorem populations_exact : population 0=16/25 ∧ population 1=9/25 := by
 norm_num [population, NontracialPauliReflection.weights]
theorem history_constant_attains (s : Schedule) :
 historyError (keepFamily s) (flipFamily s) (fun _ => 0)=1/2 := history_error s _
theorem improvement_positive (s : Schedule) :
 0<alpha s/2 ∧
 instrumentError (keepFamily s) (flipFamily s) correlationReadout <
 historyError (keepFamily s) (flipFamily s) (fun _ => 0) := by
 have ha : 0<alpha s := Real.exp_pos _
 rw [instrument_error, history_error]
 constructor <;> linarith
theorem zero_dose_families (s : Schedule) (hG : G s=0) (hD : D s=0) :
 keepFamily s=(fun h => run Q Q 2 correlationKeep h correlatedInput) ∧
 flipFamily s=(fun h => run Q Q 2 correlationFlip h correlatedInput) := by
 rw [keep_noise, flip_noise]
 constructor <;> funext h <;>
  exact (FiniteNontracialEnvironmentLift.schedule_zero_dose s hG hD _).1
theorem zero_reset_dose_endpoints (s : Schedule) (hG : G s=0) :
 branchDistance (keepFamily s) (flipFamily s)=1 ∧
 outputDistance Q Q 2 (keepTree s) (flipTree s) correlatedInput correlatedInput=1 ∧
 instrumentError (keepFamily s) (flipFamily s) correlationReadout=0 := by
 have ha : alpha s=1 := by simp [FiniteNontracialSchedule.alpha,hG]
 rw [branch_distance, output_distance, instrument_error, ha]
 norm_num
theorem empty_endpoints :
 branchDistance (keepFamily []) (flipFamily [])=1 ∧
 outputDistance Q Q 2 (keepTree []) (flipTree []) correlatedInput correlatedInput=1 ∧
 instrumentError (keepFamily []) (flipFamily []) correlationReadout=0 :=
 zero_reset_dose_endpoints [] (by simp [FiniteNontracialSchedule.G])
theorem zero_duration_endpoints (s : Schedule) (hz : ∀ h∈s, h.duration=0) :
 branchDistance (keepFamily s) (flipFamily s)=1 ∧
 outputDistance Q Q 2 (keepTree s) (flipTree s) correlatedInput correlatedInput=1 ∧
 instrumentError (keepFamily s) (flipFamily s) correlationReadout=0 :=
 zero_reset_dose_endpoints s (FiniteNontracialSchedule.zero_duration_doses s hz).1
theorem zero_rate_endpoints (s : Schedule) (hz : ∀ h∈s, h.gamma=0 ∧ h.eta=0) :
 branchDistance (keepFamily s) (flipFamily s)=1 ∧
 outputDistance Q Q 2 (keepTree s) (flipTree s) correlatedInput correlatedInput=1 ∧
 instrumentError (keepFamily s) (flipFamily s) correlationReadout=0 :=
 zero_reset_dose_endpoints s (FiniteNontracialSchedule.zero_rate_doses s hz).1

/-- The fixed physical rule reads the retained E computational basis selected by i.
Outcome zero chooses Keep; outcome one chooses Flip. -/
theorem computational_effect (i j : Q) :
 correlationEffect (i,j,())=(1:MatQ) ⊗ₖ basisState i := rfl
theorem computational_readout_branches (h : H) (X : MatJoint) :
 (correlationReadout h).branch 0 X=correlationEffect h * X * correlationEffect h ∧
 (correlationReadout h).branch 1 X=(1-correlationEffect h)*X*(1-correlationEffect h) :=
 ⟨projectiveReadout_branch_zero _ _ _ _, projectiveReadout_branch_one _ _ _ _⟩
theorem terminal_binary_isLeast (s : Schedule) :
 IsLeast {x : ℝ | ∃ F : MatJoint, IsBinaryPOVM F ∧
  readoutError (keepFamily s) (flipFamily s) (fun _ => F)=x} (1/2) := by
 constructor
 · refine ⟨correlationEffect (0,0,()), ?_, terminal_error s _⟩
   exact isBinaryPOVM_of_projection (correlationEffect_hermitian _) (correlationEffect_idem _)
 · rintro x ⟨F,_,rfl⟩
   rw [terminal_error]
end SKEFTHawking.QuantumNetwork.FiniteNontracialMemoryReadout




