import SKEFTHawking.QuantumNetwork.FiniteNontracialMemoryReadout
import SKEFTHawking.QuantumNetwork.FiniteNontracialCoherentReadout
import SKEFTHawking.FiniteNontracialScheduleTransfer

/-! Physical controls for the same certified finite memory experiments.
S × E depth-two histories and (Fin 2) × Unit reflection histories remain
separate. All branches are unnormalized, including impossible histories.
Schedules carry finite doses, with no measured-clock or norm-identification claim. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteNontracialMemoryScheduleControls
open Matrix FiniteMemoryProcess FiniteInterventionProcess
open FiniteAdaptiveMapPerturbation FiniteAdaptiveReadoutDiscrimination FiniteAdaptiveReadoutRobustness
open FiniteNontracialMemoryReadout
open FiniteNontracialSchedule (Schedule alpha beta G D)
open NontracialPauliReflection (rhoN weights Phi Psi)
open SKEFTHawking.FinitePositiveKernel.GibbsObservable
open scoped BigOperators Kronecker ComplexOrder

/-- A1: same actual zero-dose maps and families, rather than an identity observation. -/
theorem zero_dose_maps (s : Schedule) (hG : G s=0) (hD : D s=0) (X : MatJoint) :
 FiniteNontracialEnvironmentLift.scheduleState s X=X ∧
 FiniteNontracialEnvironmentLift.scheduleObservable s X=X :=
 FiniteNontracialEnvironmentLift.schedule_zero_dose s hG hD X
theorem zero_dose_tables (s : Schedule) (hG : G s=0) (i j b : Q) :
 readoutTable correlationReadout (keepFamily s) (i,j,()) b=
  (if j=0 ∧ b=0 then 1/2 else 0) ∧
 readoutTable correlationReadout (flipFamily s) (i,j,()) b=
  (if j=0 ∧ b=1 then 1/2 else 0) := by
 have ha : alpha s=1 := by simp [FiniteNontracialSchedule.alpha,hG]
 rw [(physical_table s i j b).1,(physical_table s i j b).2,ha]
 fin_cases j <;> fin_cases b <;> norm_num
theorem zero_dose_optimum (s : Schedule) (hG : G s=0) :
 IsLeast {x : ℝ | ∃ F : H → MatJoint, (∀ h, IsBinaryPOVM (F h)) ∧
  readoutError (keepFamily s) (flipFamily s) F=x} 0 := by
 have ha : alpha s=1 := by simp [FiniteNontracialSchedule.alpha,hG]
 simpa only [ha,sub_self,zero_div] using all_effect_isLeast s
theorem zero_dose_pair (s : Schedule) (hG : G s=0) (hD : D s=0) :
 keepFamily s=(fun h => run Q Q 2 correlationKeep h correlatedInput) ∧
 flipFamily s=(fun h => run Q Q 2 correlationFlip h correlatedInput) ∧
 (∀ Z,krausMap (FiniteNontracialCoherentReadout.evolution s) Z=swapJoint Z) ∧
 (∀ X,FiniteNontracialCoherentReadout.family s X=FiniteNontracialCoherentReadout.family [] X) ∧
 branchDistance (keepFamily s) (flipFamily s)=1 ∧
 instrumentError (keepFamily s) (flipFamily s) correlationReadout=0 ∧
 outputDistance Q Q 2 (FiniteNontracialCoherentReadout.tree s) (FiniteNontracialCoherentReadout.tree s)
  (FiniteNontracialCoherentReadout.input qubitX) (FiniteNontracialCoherentReadout.input qubitY)=invSqrtTwo ∧
 instrumentError (FiniteNontracialCoherentReadout.family s qubitX)
  (FiniteNontracialCoherentReadout.family s qubitY) FiniteNontracialCoherentReadout.decisionReadout=
  (1-invSqrtTwo)/2 := by
 refine ⟨(zero_dose_families s hG hD).1,(zero_dose_families s hG hD).2,
  FiniteNontracialCoherentReadout.zero_dose_evolution s hG hD,
  FiniteNontracialCoherentReadout.zero_dose_family s hG hD,
  (zero_reset_dose_endpoints s hG).1,(zero_reset_dose_endpoints s hG).2.2,?_,?_⟩
 · rw [FiniteNontracialCoherentReadout.tree_output_distance,
   FiniteNontracialCoherentReadout.zero_dose_beta s hG hD,one_mul]
 · rw [FiniteNontracialCoherentReadout.decision_attains,
   FiniteNontracialCoherentReadout.zero_dose_beta s hG hD,one_mul]
theorem zero_duration_pair (s : Schedule) (hz : ∀ h∈s,h.duration=0) :
 branchDistance (keepFamily s) (flipFamily s)=1 ∧
 outputDistance Q Q 2 (FiniteNontracialCoherentReadout.tree s) (FiniteNontracialCoherentReadout.tree s)
  (FiniteNontracialCoherentReadout.input qubitX) (FiniteNontracialCoherentReadout.input qubitY)=invSqrtTwo :=
 ⟨(zero_duration_endpoints s hz).1,(FiniteNontracialCoherentReadout.zero_duration_controls s hz).2.2.1⟩
theorem zero_rate_pair (s : Schedule) (hz : ∀ h∈s,h.gamma=0 ∧ h.eta=0) :
 branchDistance (keepFamily s) (flipFamily s)=1 ∧
 outputDistance Q Q 2 (FiniteNontracialCoherentReadout.tree s) (FiniteNontracialCoherentReadout.tree s)
  (FiniteNontracialCoherentReadout.input qubitX) (FiniteNontracialCoherentReadout.input qubitY)=invSqrtTwo :=
 ⟨(zero_rate_endpoints s hz).1,(FiniteNontracialCoherentReadout.zero_rates_controls s hz).2.2.1⟩
theorem pure_dephasing_pair (s : Schedule) (hG : G s=0) (hD : 0<D s) :
 alpha s=1 ∧ beta s<1 ∧
 branchDistance (keepFamily s) (flipFamily s)=1 ∧
 instrumentError (keepFamily s) (flipFamily s) correlationReadout=0 ∧
 outputDistance Q Q 2 (FiniteNontracialCoherentReadout.tree s) (FiniteNontracialCoherentReadout.tree s)
  (FiniteNontracialCoherentReadout.input qubitX) (FiniteNontracialCoherentReadout.input qubitY)< invSqrtTwo ∧
 (1-invSqrtTwo)/2 < instrumentError (FiniteNontracialCoherentReadout.family s qubitX)
  (FiniteNontracialCoherentReadout.family s qubitY) FiniteNontracialCoherentReadout.decisionReadout :=
 ⟨(FiniteNontracialCoherentReadout.pure_dephasing_controls s hG hD).1,
  (FiniteNontracialCoherentReadout.pure_dephasing_controls s hG hD).2.1,
  (zero_reset_dose_endpoints s hG).1,(zero_reset_dose_endpoints s hG).2.2,
  (FiniteNontracialCoherentReadout.pure_dephasing_controls s hG hD).2.2⟩

/-- A2: full numeric physical diagonal tables; the j=1 rows are never discarded. -/
def logTwoKeep : Matrix Q Q ℝ := !![41/100,9/100;34/100,16/100]
def logTwoFlip : Matrix Q Q ℝ := !![16/100,34/100;9/100,41/100]
theorem logTwo_diagonal_tables (i j b : Q) :
 readoutTable correlationReadout (keepFamily [FiniteNontracialSchedule.logTwoSlice]) (i,j,()) b=
 (if j=0 then logTwoKeep i b else 0) ∧
 readoutTable correlationReadout (flipFamily [FiniteNontracialSchedule.logTwoSlice]) (i,j,()) b=
 (if j=0 then logTwoFlip i b else 0) := by
 rw [(physical_table _ i j b).1,(physical_table _ i j b).2,
  FiniteNontracialSchedule.logTwo_coefficients.1]
 fin_cases i <;> fin_cases j <;> fin_cases b <;>
  norm_num [population,NontracialPauliReflection.weights,logTwoKeep,logTwoFlip]
theorem logTwo_pair :
 branchDistance (keepFamily [FiniteNontracialSchedule.logTwoSlice])
  (flipFamily [FiniteNontracialSchedule.logTwoSlice])=1/2 ∧
 instrumentError (keepFamily [FiniteNontracialSchedule.logTwoSlice])
  (flipFamily [FiniteNontracialSchedule.logTwoSlice]) correlationReadout=1/4 ∧
 outputDistance Q Q 2 (FiniteNontracialCoherentReadout.tree [FiniteNontracialSchedule.logTwoSlice])
  (FiniteNontracialCoherentReadout.tree [FiniteNontracialSchedule.logTwoSlice])
  (FiniteNontracialCoherentReadout.input qubitX) (FiniteNontracialCoherentReadout.input qubitY)=invSqrtTwo/4 ∧
 instrumentError (FiniteNontracialCoherentReadout.family [FiniteNontracialSchedule.logTwoSlice] qubitX)
  (FiniteNontracialCoherentReadout.family [FiniteNontracialSchedule.logTwoSlice] qubitY)
  FiniteNontracialCoherentReadout.decisionReadout=(1-invSqrtTwo/4)/2 := by
 rw [branch_distance,instrument_error,FiniteNontracialSchedule.logTwo_coefficients.1]
 norm_num
 exact FiniteNontracialCoherentReadout.logTwo_controls.2.2.2
theorem dephasingLogTwo_diagonal_tables (i j b : Q) :
 readoutTable correlationReadout (keepFamily [FiniteNontracialCoherentReadout.dephasingLogTwoSlice])
  (i,j,()) b=(if j=0 ∧ b=0 then 1/2 else 0) ∧
 readoutTable correlationReadout (flipFamily [FiniteNontracialCoherentReadout.dephasingLogTwoSlice])
  (i,j,()) b=(if j=0 ∧ b=1 then 1/2 else 0) := by
 apply zero_dose_tables
 simp [FiniteNontracialSchedule.G,FiniteNontracialCoherentReadout.dephasingLogTwoSlice]
theorem dephasingLogTwo_pair :
 branchDistance (keepFamily [FiniteNontracialCoherentReadout.dephasingLogTwoSlice])
  (flipFamily [FiniteNontracialCoherentReadout.dephasingLogTwoSlice])=1 ∧
 instrumentError (keepFamily [FiniteNontracialCoherentReadout.dephasingLogTwoSlice])
  (flipFamily [FiniteNontracialCoherentReadout.dephasingLogTwoSlice]) correlationReadout=0 ∧
 outputDistance Q Q 2 (FiniteNontracialCoherentReadout.tree [FiniteNontracialCoherentReadout.dephasingLogTwoSlice])
  (FiniteNontracialCoherentReadout.tree [FiniteNontracialCoherentReadout.dephasingLogTwoSlice])
  (FiniteNontracialCoherentReadout.input qubitX) (FiniteNontracialCoherentReadout.input qubitY)=invSqrtTwo/2 ∧
 instrumentError (FiniteNontracialCoherentReadout.family [FiniteNontracialCoherentReadout.dephasingLogTwoSlice] qubitX)
  (FiniteNontracialCoherentReadout.family [FiniteNontracialCoherentReadout.dephasingLogTwoSlice] qubitY)
  FiniteNontracialCoherentReadout.decisionReadout=(1-invSqrtTwo/2)/2 := by
 rw [branch_distance,instrument_error,FiniteNontracialCoherentReadout.dephasingLogTwo_coefficients.1]
 norm_num
 exact FiniteNontracialCoherentReadout.dephasingLogTwo_controls.2.2.2

/-- A3: all-complex D=0 reset actions are separately the state and observable actions. -/
theorem zero_dephasing_actions (s : Schedule) (hD : D s=0) (X : MatQ) :
 FiniteNontracialSchedule.state s X=Phi (alpha s) X ∧
 FiniteNontracialSchedule.observable s X=Psi (alpha s) X :=
 FiniteNontracialSchedule.zero_dephasing_actions s hD X
theorem zero_dephasing_coefficients (s : Schedule) (hD : D s=0) : beta s=alpha s := by
 simp [FiniteNontracialSchedule.beta,FiniteNontracialSchedule.alpha,hD]
theorem zero_dephasing_constant_difference (s : Schedule) (hD : D s=0) :
 FiniteNontracialSchedule.state s 1-FiniteNontracialSchedule.observable s 1 =
 ((7*(1-alpha s)/25:ℝ):ℂ) • (basisState 0-basisState 1) := by
 rw [(zero_dephasing_actions s hD 1).1,(zero_dephasing_actions s hD 1).2]
 ext i j; fin_cases i <;> fin_cases j <;>
  norm_num [Phi,Psi,rhoN,basisState,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,
   Matrix.one_apply,Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,
   smul_eq_mul,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_sub]
  <;> ring

theorem zero_dephasing_constant_distinct (s : Schedule) (hD : D s=0) (hG : 0<G s) :
 FiniteNontracialSchedule.state s 1 ≠ FiniteNontracialSchedule.observable s 1 := by
 intro he
 have hz := zero_dephasing_constant_difference s hD
 rw [he,sub_self] at hz
 have h := congrArg (fun M : MatQ => (M 0 0).re) hz
 norm_num [basisState,Matrix.smul_apply,Matrix.sub_apply,Complex.ofReal_div,
  Complex.ofReal_mul,Complex.ofReal_sub] at h
 have ha : alpha s<1 := by
  rw [FiniteNontracialSchedule.alpha,Real.exp_lt_one_iff]; linarith
 linarith

/-- A4: the full Gibbs reset follows either certified evolution, before common prepare0. -/
def resetKeepKraus (s : Schedule) :=
 composeKraus (FiniteNontracialEnvironmentLift.liftKraus FiniteNontracialEnvironmentLift.gibbsResetKraus)
  (FiniteNontracialEnvironmentLift.scheduleKraus s)
def resetFlipKraus (s : Schedule) :=
 composeKraus (FiniteNontracialEnvironmentLift.liftKraus FiniteNontracialEnvironmentLift.gibbsResetKraus)
  (flipKraus s)
theorem resetKeep_normalized (s : Schedule) : IsKrausChannel (resetKeepKraus s) :=
 isKrausChannel_composeKraus FiniteNontracialEnvironmentLift.gibbsReset_normalized
  (FiniteNontracialEnvironmentLift.schedule_normalized s)
theorem resetFlip_normalized (s : Schedule) : IsKrausChannel (resetFlipKraus s) :=
 isKrausChannel_composeKraus FiniteNontracialEnvironmentLift.gibbsReset_normalized (flip_normalized s)
def resetKeepStep (s : Schedule) : Step Q Q 2 :=
 realizedStep Q Q 2 (resetKeepKraus s) (resetKeep_normalized s) (FiniteInstrument.prepare 0)
def resetFlipStep (s : Schedule) : Step Q Q 2 :=
 realizedStep Q Q 2 (resetFlipKraus s) (resetFlip_normalized s) (FiniteInstrument.prepare 0)
def resetKeepTree (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (resetKeepStep s) (fun _ => .done))
def resetFlipTree (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (resetFlipStep s) (fun _ => .done))
def resetKeepFamily (s : Schedule) (h : H) : MatJoint := run Q Q 2 (resetKeepTree s) h correlatedInput
def resetFlipFamily (s : Schedule) (h : H) : MatJoint := run Q Q 2 (resetFlipTree s) h correlatedInput
theorem resetKeep_tensor (s : Schedule) (i j : Q) :
 (resetKeepStep s).branch Q Q 2 j (basisState i ⊗ₖ basisState i)=
 if j=0 then basisState 0 ⊗ₖ rhoN else 0 := by
 change ((FiniteInstrument.prepare 0).lift Q).branch j (krausMap (resetKeepKraus s) _) = _
 rw [resetKeepKraus,krausMap_composeKraus]
 change ((FiniteInstrument.prepare 0).lift Q).branch j
  (FiniteNontracialEnvironmentLift.gibbsReset (FiniteNontracialEnvironmentLift.scheduleState s _))=_
 rw [FiniteNontracialEnvironmentLift.gibbsReset_eq,
  FiniteNontracialEnvironmentLift.schedule_spectator,
  FiniteNontracialEnvironmentLift.ptrace2_kronecker,(basisState_density i).2,one_smul,
  lift_branch_tensor,prepare_basis]
 split_ifs <;> simp_all
theorem resetFlip_tensor (s : Schedule) (i j : Q) :
 (resetFlipStep s).branch Q Q 2 j (basisState i ⊗ₖ basisState i)=
 if j=0 then basisState 0 ⊗ₖ rhoN else 0 := by
 change ((FiniteInstrument.prepare 0).lift Q).branch j (krausMap (resetFlipKraus s) _) = _
 rw [resetFlipKraus,krausMap_composeKraus,flipKraus,krausMap_composeKraus,environmentX_basis]
 change ((FiniteInstrument.prepare 0).lift Q).branch j
  (FiniteNontracialEnvironmentLift.gibbsReset (FiniteNontracialEnvironmentLift.scheduleState s _))=_
 rw [FiniteNontracialEnvironmentLift.gibbsReset_eq,
  FiniteNontracialEnvironmentLift.schedule_spectator,
  FiniteNontracialEnvironmentLift.ptrace2_kronecker,(basisState_density (1-i)).2,one_smul,
  lift_branch_tensor,prepare_basis]
 split_ifs <;> simp_all
theorem reset_branches (s : Schedule) (i j : Q) :
 resetKeepFamily s (i,j,())=(if j=0 then (1/2:ℂ) • (basisState 0 ⊗ₖ rhoN) else 0) ∧
 resetFlipFamily s (i,j,())=(if j=0 then (1/2:ℂ) • (basisState 0 ⊗ₖ rhoN) else 0) := by
 change (resetKeepStep s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput)=_ ∧
  (resetFlipStep s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput)=_
 rw [readStep_correlated,Step.branch_smul,Step.branch_smul,resetKeep_tensor,resetFlip_tensor]
 split_ifs <;> simp
theorem reset_families_equal (s : Schedule) : resetKeepFamily s=resetFlipFamily s := by
 funext h; rcases h with ⟨i,j,⟨⟩⟩
 exact (reset_branches s i j).1.trans (reset_branches s i j).2.symm
theorem resetKeep_valid (s : Schedule) : IsBranchFamily (resetKeepFamily s) :=
 run_family _ correlatedInput_density
theorem resetFlip_valid (s : Schedule) : IsBranchFamily (resetFlipFamily s) :=
 run_family _ correlatedInput_density
theorem reset_tables (s : Schedule) (i j b : Q) :
 readoutTable correlationReadout (resetKeepFamily s) (i,j,()) b=
 (if j=0 then (if b=0 then population i/2 else population (1-i)/2) else 0) ∧
 readoutTable correlationReadout (resetFlipFamily s) (i,j,()) b=
 (if j=0 then (if b=0 then population i/2 else population (1-i)/2) else 0) := by
 fin_cases b
 · change (correlationReadout _).weight 0 _ = _ ∧ (correlationReadout _).weight 0 _ = _
   rw [correlationReadout_weight_zero,correlationReadout_weight_zero,
    (reset_branches s i j).1,(reset_branches s i j).2]
   fin_cases i <;> fin_cases j <;>
    norm_num [correlationEffect,Matrix.mul_apply,Matrix.trace,Matrix.kronecker_apply,basisState,
     Matrix.one_apply,Fintype.sum_prod_type,Fin.sum_univ_two,rhoN,population,
     NontracialPauliReflection.weights]
 · change (correlationReadout _).weight 1 _ = _ ∧ (correlationReadout _).weight 1 _ = _
   rw [correlationReadout_weight_one,correlationReadout_weight_one,
    (reset_branches s i j).1,(reset_branches s i j).2]
   fin_cases i <;> fin_cases j <;>
    norm_num [correlationEffect,Matrix.mul_apply,Matrix.trace,Matrix.kronecker_apply,basisState,
     Matrix.one_apply,Fintype.sum_prod_type,Fin.sum_univ_two,rhoN,population,
     NontracialPauliReflection.weights]

theorem same_instrument_error {A : H → MatJoint} (hA : IsBranchFamily A)
 (I : H → FiniteInstrument (Q×Q) 2) : instrumentError A A I=1/2 := by
 have ht := readoutTable_total I hA
 simp only [Fin.sum_univ_two] at ht
 unfold instrumentError
 rw [← Finset.sum_add_distrib,ht]
theorem reset_laws (s : Schedule) :
 (∀ h a,0≤readoutTable correlationReadout (resetKeepFamily s) h a) ∧
 (∑ h,∑ a,readoutTable correlationReadout (resetKeepFamily s) h a)=1 ∧
 (∀ h a,0≤readoutTable correlationReadout (resetFlipFamily s) h a) ∧
 (∑ h,∑ a,readoutTable correlationReadout (resetFlipFamily s) h a)=1 :=
 ⟨readoutTable_nonneg _ (resetKeep_valid s),readoutTable_total _ (resetKeep_valid s),
  readoutTable_nonneg _ (resetFlip_valid s),readoutTable_total _ (resetFlip_valid s)⟩
theorem reset_distance (s : Schedule) : branchDistance (resetKeepFamily s) (resetFlipFamily s)=0 := by
 rw [← reset_families_equal]; exact branchDistance_self _
theorem reset_output_distance (s : Schedule) :
 outputDistance Q Q 2 (resetKeepTree s) (resetFlipTree s) correlatedInput correlatedInput=0 := by
 rw [← tree_branchDistance]
 exact reset_distance s
theorem reset_every_effect (s : Schedule) (E : H → MatJoint) :
 readoutError (resetKeepFamily s) (resetFlipFamily s) E=1/2 := by
 rw [← reset_families_equal,readoutError_eq _ _ _ (resetKeep_valid s).2]; simp
theorem reset_every_readout (s : Schedule) (I : H → FiniteInstrument (Q×Q) 2) :
 instrumentError (resetKeepFamily s) (resetFlipFamily s) I=1/2 := by
 rw [← reset_families_equal]; exact same_instrument_error (resetKeep_valid s) I
theorem reset_every_history (s : Schedule) (a : H → ℝ) :
 historyError (resetKeepFamily s) (resetFlipFamily s) a=1/2 := by
 rw [← reset_families_equal]
 exact historyError_same_law (resetKeep_valid s) (fun _ => rfl) a
theorem reset_all_effect_isLeast (s : Schedule) :
 IsLeast {x : ℝ | ∃ E : H → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
 readoutError (resetKeepFamily s) (resetFlipFamily s) E=x} (1/2) := by
 simpa only [reset_distance,sub_zero] using readoutError_isLeast (resetKeep_valid s) (resetFlip_valid s)
theorem reset_history_isLeast (s : Schedule) :
 IsLeast {x : ℝ | ∃ a : H → ℝ,(∀ h,a h∈Set.Icc (0:ℝ) 1) ∧
 historyError (resetKeepFamily s) (resetFlipFamily s) a=x} (1/2) := by
 constructor
 · exact ⟨fun _ => 0,fun _ => ⟨le_rfl,by norm_num⟩,reset_every_history s _⟩
 · rintro x ⟨a,_,rfl⟩; rw [reset_every_history]
theorem reset_named_attainment (s : Schedule) :
 instrumentError (resetKeepFamily s) (resetFlipFamily s) correlationReadout=1/2 ∧
 readoutError (resetKeepFamily s) (resetFlipFamily s) correlationEffect=1/2 ∧
 historyError (resetKeepFamily s) (resetFlipFamily s) (fun _ => 0)=1/2 :=
 ⟨reset_every_readout s _,reset_every_effect s _,reset_every_history s _⟩
/-- The history-only constant decision has its own normalized scalar projective instrument. -/
def constantReadout (_ : H) : FiniteInstrument (Q×Q) 2 :=
 projectiveReadout 0 (by simp [Matrix.IsHermitian]) (by simp)
theorem constantReadout_attains (s : Schedule) :
 instrumentError (resetKeepFamily s) (resetFlipFamily s) constantReadout=1/2 :=
 reset_every_readout s _
theorem reset_pair (s : Schedule) :
 branchDistance (resetKeepFamily s) (resetFlipFamily s)=0 ∧
 branchDistance (FiniteNontracialCoherentReadout.resetFamily s qubitX)
  (FiniteNontracialCoherentReadout.resetFamily s qubitY)=0 ∧
 instrumentError (resetKeepFamily s) (resetFlipFamily s) correlationReadout=1/2 ∧
 instrumentError (FiniteNontracialCoherentReadout.resetFamily s qubitX)
  (FiniteNontracialCoherentReadout.resetFamily s qubitY)
  FiniteNontracialCoherentReadout.decisionReadout=1/2 :=
 ⟨reset_distance s,FiniteNontracialCoherentReadout.reset_distance s,
  reset_every_readout s _,FiniteNontracialCoherentReadout.reset_every_readout s _⟩

/-- A5: S reset occurs after readStep has already recorded i. -/
def systemKeepKraus (s : Schedule) :=
 composeKraus (FiniteNontracialEnvironmentLift.scheduleKraus s) (tensorKraus resetKraus)
def systemFlipKraus (s : Schedule) := composeKraus (flipKraus s) (tensorKraus resetKraus)
theorem systemKeep_normalized (s : Schedule) : IsKrausChannel (systemKeepKraus s) :=
 isKrausChannel_composeKraus (FiniteNontracialEnvironmentLift.schedule_normalized s) resetSystem_normalized
theorem systemFlip_normalized (s : Schedule) : IsKrausChannel (systemFlipKraus s) :=
 isKrausChannel_composeKraus (flip_normalized s) resetSystem_normalized
def systemKeepStep (s : Schedule) : Step Q Q 2 :=
 realizedStep Q Q 2 (systemKeepKraus s) (systemKeep_normalized s) (FiniteInstrument.prepare 0)
def systemFlipStep (s : Schedule) : Step Q Q 2 :=
 realizedStep Q Q 2 (systemFlipKraus s) (systemFlip_normalized s) (FiniteInstrument.prepare 0)
def systemKeepTree (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (systemKeepStep s) (fun _ => .done))
def systemFlipTree (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (systemFlipStep s) (fun _ => .done))
def systemKeepFamily (s : Schedule) (h : H) : MatJoint := run Q Q 2 (systemKeepTree s) h correlatedInput
def systemFlipFamily (s : Schedule) (h : H) : MatJoint := run Q Q 2 (systemFlipTree s) h correlatedInput
theorem system_keep_tensor (s : Schedule) (i j : Q) :
 (systemKeepStep s).branch Q Q 2 j (basisState i ⊗ₖ basisState i)=
 if j=0 then basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState i) else 0 := by
 change ((FiniteInstrument.prepare 0).lift Q).branch j (krausMap (systemKeepKraus s) _) = _
 rw [systemKeepKraus,krausMap_composeKraus]
 change (keepStep s).branch Q Q 2 j (resetSystem (basisState i ⊗ₖ basisState i))=_
 rw [resetSystem_basis]
 exact keepStep_tensor s j 0 _
theorem system_flip_tensor (s : Schedule) (i j : Q) :
 (systemFlipStep s).branch Q Q 2 j (basisState i ⊗ₖ basisState i)=
 if j=0 then basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState (1-i)) else 0 := by
 change ((FiniteInstrument.prepare 0).lift Q).branch j (krausMap (systemFlipKraus s) _) = _
 rw [systemFlipKraus,krausMap_composeKraus]
 change (flipStep s).branch Q Q 2 j (resetSystem (basisState i ⊗ₖ basisState i))=_
 rw [resetSystem_basis]
 exact flipStep_basis s j 0 i
theorem system_families_preserved (s : Schedule) :
 systemKeepFamily s=keepFamily s ∧ systemFlipFamily s=flipFamily s := by
 constructor <;> funext h <;> rcases h with ⟨i,j,⟨⟩⟩
 · change (systemKeepStep s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput)=_
   rw [readStep_correlated,Step.branch_smul,system_keep_tensor,keep_run]
   split_ifs <;> simp
 · change (systemFlipStep s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput)=_
   rw [readStep_correlated,Step.branch_smul,system_flip_tensor,flip_run]
   split_ifs <;> simp
theorem system_tables (s : Schedule) (i j b : Q) :
 readoutTable correlationReadout (systemKeepFamily s) (i,j,()) b=
  (if j=0 then (if b=0 then (alpha s+(1-alpha s)*population i)/2
   else (1-alpha s)*population (1-i)/2) else 0) ∧
 readoutTable correlationReadout (systemFlipFamily s) (i,j,()) b=
  (if j=0 then (if b=0 then (1-alpha s)*population i/2
   else (alpha s+(1-alpha s)*population (1-i))/2) else 0) := by
 rw [(system_families_preserved s).1,(system_families_preserved s).2]
 exact physical_table s i j b
theorem system_controls (s : Schedule) :
 branchDistance (systemKeepFamily s) (systemFlipFamily s)=alpha s ∧
 instrumentError (systemKeepFamily s) (systemFlipFamily s) correlationReadout=(1-alpha s)/2 := by
 rw [(system_families_preserved s).1,(system_families_preserved s).2]
 exact ⟨branch_distance s,instrument_error s⟩
theorem system_all_effect_isLeast (s : Schedule) :
 IsLeast {x : ℝ | ∃ F : H → MatJoint,(∀ h,IsBinaryPOVM (F h)) ∧
 readoutError (systemKeepFamily s) (systemFlipFamily s) F=x} ((1-alpha s)/2) := by
 rw [(system_families_preserved s).1,(system_families_preserved s).2]
 exact all_effect_isLeast s
theorem system_pair (s : Schedule) :
 branchDistance (systemKeepFamily s) (systemFlipFamily s)=alpha s ∧
 outputDistance Q Q 2 (FiniteNontracialCoherentReadout.systemPrepareTree s)
  (FiniteNontracialCoherentReadout.systemPrepareTree s)
  (FiniteNontracialCoherentReadout.input qubitX) (FiniteNontracialCoherentReadout.input qubitY)=beta s*invSqrtTwo :=
 ⟨(system_controls s).1,(FiniteNontracialCoherentReadout.system_prepare_controls s).1⟩

/-- A6: both hypotheses use this SAME tree and identical stationary input. -/
def stationaryInput : MatJoint := basisState 0 ⊗ₖ rhoN
theorem stationaryInput_density : IsDensityOperator stationaryInput :=
 FiniteNontracialCoherentReadout.input_density NontracialPauliReflection.rhoN_density
def stationaryFamily (s : Schedule) (h : H) : MatJoint := run Q Q 2 (keepTree s) h stationaryInput
theorem stationary_branch (s : Schedule) (i j : Q) :
 stationaryFamily s (i,j,())=(if i=0 ∧ j=0 then stationaryInput else 0) := by
 change (keepStep s).branch Q Q 2 j (readStep.branch Q Q 2 i stationaryInput)=_
 rw [readStep,localStep_branch]
 unfold stationaryInput
 rw [lift_branch_tensor,computational_basis]
 fin_cases i <;> fin_cases j <;>
  simp [keepStep_tensor,FiniteNontracialSchedule.state_stationary,Step.branch_zero]
theorem stationary_valid (s : Schedule) : IsBranchFamily (stationaryFamily s) :=
 run_family _ stationaryInput_density
theorem stationary_tables (s : Schedule) (i j b : Q) :
 readoutTable correlationReadout (stationaryFamily s) (i,j,()) b=
 (if i=0 ∧ j=0 then population b else 0) := by
 fin_cases b
 · change (correlationReadout _).weight 0 _=_
   rw [correlationReadout_weight_zero,stationary_branch]
   fin_cases i <;> fin_cases j <;>
    norm_num [stationaryInput,correlationEffect,Matrix.mul_apply,Matrix.trace,Matrix.kronecker_apply,
     basisState,Matrix.one_apply,Fintype.sum_prod_type,Fin.sum_univ_two,rhoN,population,
     NontracialPauliReflection.weights]
 · change (correlationReadout _).weight 1 _=_
   rw [correlationReadout_weight_one,stationary_branch]
   fin_cases i <;> fin_cases j <;>
    norm_num [stationaryInput,correlationEffect,Matrix.mul_apply,Matrix.trace,Matrix.kronecker_apply,
     basisState,Matrix.one_apply,Fintype.sum_prod_type,Fin.sum_univ_two,rhoN,population,
     NontracialPauliReflection.weights]
theorem stationary_laws (s : Schedule) :
 (∀ h a,0≤readoutTable correlationReadout (stationaryFamily s) h a) ∧
 (∑ h,∑ a,readoutTable correlationReadout (stationaryFamily s) h a)=1 :=
 ⟨readoutTable_nonneg _ (stationary_valid s),readoutTable_total _ (stationary_valid s)⟩
theorem stationary_every_effect (s : Schedule) (E : H → MatJoint) :
 readoutError (stationaryFamily s) (stationaryFamily s) E=1/2 := by
 rw [readoutError_eq _ _ _ (stationary_valid s).2]; simp
theorem stationary_every_readout (s : Schedule) (I : H → FiniteInstrument (Q×Q) 2) :
 instrumentError (stationaryFamily s) (stationaryFamily s) I=1/2 :=
 same_instrument_error (stationary_valid s) I
theorem stationary_every_history (s : Schedule) (a : H → ℝ) :
 historyError (stationaryFamily s) (stationaryFamily s) a=1/2 :=
 historyError_same_law (stationary_valid s) (fun _ => rfl) a
theorem stationary_all_effect_isLeast (s : Schedule) :
 IsLeast {x : ℝ | ∃ E : H → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
 readoutError (stationaryFamily s) (stationaryFamily s) E=x} (1/2) := by
 simpa only [branchDistance_self,sub_zero] using readoutError_isLeast (stationary_valid s) (stationary_valid s)
theorem stationary_history_isLeast (s : Schedule) :
 IsLeast {x : ℝ | ∃ a : H → ℝ,(∀ h,a h∈Set.Icc (0:ℝ) 1) ∧
 historyError (stationaryFamily s) (stationaryFamily s) a=x} (1/2) := by
 constructor
 · exact ⟨fun _ => 0,fun _ => ⟨le_rfl,by norm_num⟩,stationary_every_history s _⟩
 · rintro x ⟨a,_,rfl⟩;rw [stationary_every_history]
theorem stationary_distances (s : Schedule) :
 branchDistance (stationaryFamily s) (stationaryFamily s)=0 ∧
 outputDistance Q Q 2 (keepTree s) (keepTree s) stationaryInput stationaryInput=0 := by
 constructor
 · exact branchDistance_self _
 · rw [← tree_branchDistance];exact branchDistance_self _
theorem rhoN_not_X_invariant : pauliX*rhoN*pauliX ≠ rhoN := by
 intro he
 have h:=congrArg (fun X : MatQ => X 0 0) he
 norm_num [pauliX,rhoN,Matrix.mul_apply,Fin.sum_univ_two] at h
theorem finite_diagonal_states_distinct (s : Schedule) :
 FiniteNontracialSchedule.state s (basisState 0) ≠ FiniteNontracialSchedule.state s (basisState 1) := by
 intro he
 rw [basis_state,basis_state] at he
 have h:=congrArg (fun X : MatQ => (X 0 0).re) he
 norm_num [rhoN,basisState,Matrix.smul_apply,Matrix.add_apply,Complex.ofReal_sub] at h
 have ha : 0<alpha s := Real.exp_pos _
 linarith
theorem finite_diagonal_branches_distinct (s : Schedule) :
 keepFamily s (0,0,()) ≠ flipFamily s (0,0,()) := by
 intro he
 have h:=congrArg (fun X : MatJoint => (X (0,0) (0,0)).re) he
 rw [keep_run,flip_run] at h
 norm_num [basis_state,rhoN,basisState,Matrix.smul_apply,Matrix.add_apply,Matrix.kronecker_apply,
  smul_eq_mul,Complex.ofReal_sub] at h
 have ha : 0<alpha s := Real.exp_pos _
 linarith

/-- A7: both actual normalized joint orders, with distinct forward chronology. -/
def XafterKraus (s : Schedule) :=
 composeKraus environmentXKraus (FiniteNontracialEnvironmentLift.scheduleKraus s)
theorem Xafter_normalized (s : Schedule) : IsKrausChannel (XafterKraus s) :=
 isKrausChannel_composeKraus environmentX_normalized (FiniteNontracialEnvironmentLift.schedule_normalized s)
theorem noise_after_X (s : Schedule) (X : MatJoint) :
 krausMap (flipKraus s) X=
 FiniteNontracialEnvironmentLift.scheduleState s (krausMap environmentXKraus X) :=
 krausMap_composeKraus _ _ _
theorem X_after_noise (s : Schedule) (X : MatJoint) :
 krausMap (XafterKraus s) X=
 krausMap environmentXKraus (FiniteNontracialEnvironmentLift.scheduleState s X) :=
 krausMap_composeKraus _ _ _
theorem joint_heisenberg_compose {a b : ℕ} (L : Fin b → MatJoint) (K : Fin a → MatJoint)
 (A : MatJoint) : Channel.heisenberg (composeKraus L K) A=
 Channel.heisenberg K (Channel.heisenberg L A) := by
 unfold Channel.heisenberg composeKraus
 rw [finProdFinEquiv.symm.sum_comp
  (fun p : Fin b × Fin a => (L p.1*K p.2)ᴴ*A*(L p.1*K p.2)),
  Fintype.sum_prod_type,Finset.sum_comm]
 simp only [Matrix.mul_sum,Matrix.sum_mul]
 refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
 rw [Matrix.conjTranspose_mul]
 noncomm_ring
theorem observable_orders (s : Schedule) (A : MatJoint) :
 Channel.heisenberg (flipKraus s) A=
 Channel.heisenberg environmentXKraus (FiniteNontracialEnvironmentLift.scheduleObservable s A) ∧
 Channel.heisenberg (XafterKraus s) A=
 FiniteNontracialEnvironmentLift.scheduleObservable s (Channel.heisenberg environmentXKraus A) :=
 ⟨joint_heisenberg_compose _ _ _,joint_heisenberg_compose _ _ _⟩
theorem both_order_trace_duality (s : Schedule) (A X : MatJoint) :
 (A*krausMap (flipKraus s) X).trace=(Channel.heisenberg (flipKraus s) A*X).trace ∧
 (A*krausMap (XafterKraus s) X).trace=(Channel.heisenberg (XafterKraus s) A*X).trace := by
 constructor <;> rw [Matrix.trace_mul_comm,← Channel.trace_duality,Matrix.trace_mul_comm]
theorem environmentX_product (A B : MatQ) :
 krausMap environmentXKraus (A ⊗ₖ B)=A ⊗ₖ (pauliX*B*pauliX) := by
 rw [environmentX_action]
 simp only [environmentX,← Matrix.mul_kronecker_mul,one_mul,mul_one]
theorem order_products (s : Schedule) :
 krausMap (flipKraus s) (basisState 0 ⊗ₖ basisState 0)=
 basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState 1) ∧
 krausMap (XafterKraus s) (basisState 0 ⊗ₖ basisState 0)=
 basisState 0 ⊗ₖ (pauliX*FiniteNontracialSchedule.state s (basisState 0)*pauliX) := by
 constructor
 · rw [noise_after_X,environmentX_basis,FiniteNontracialEnvironmentLift.schedule_product];rfl
 · rw [X_after_noise,FiniteNontracialEnvironmentLift.schedule_product,environmentX_product]
theorem order_qubit_difference (s : Schedule) :
 FiniteNontracialSchedule.state s (basisState 1)-
  pauliX*FiniteNontracialSchedule.state s (basisState 0)*pauliX=
 ((7*(1-alpha s)/25:ℝ):ℂ) • (basisState 0-basisState 1) := by
 rw [basis_state,basis_state]
 ext i j;fin_cases i <;> fin_cases j <;>
  norm_num [pauliX,rhoN,basisState,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,
   Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,smul_eq_mul,
   Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_div]
  <;> ring
theorem order_distance (s : Schedule) :
 traceDist (krausMap (flipKraus s) (basisState 0 ⊗ₖ basisState 0))
 (krausMap (XafterKraus s) (basisState 0 ⊗ₖ basisState 0))=7*(1-alpha s)/25 := by
 rw [(order_products s).1,(order_products s).2,
  FiniteAdaptiveProcessRobustness.traceDist_tensor_left (basisState_density 0)]
 unfold traceDist
 rw [order_qubit_difference,traceNorm_smul_nonneg (by
  have ha := (FiniteNontracialSchedule.coefficients s).2.2
  positivity)]
 have hd : traceDist (basisState 0) (basisState 1)=1 := by
  rw [traceDist_comm];exact basis_one_zero_distance
 unfold traceDist at hd
 calc
  _ = (7*(1-alpha s)/25)*(1/2*traceNorm (basisState 0-basisState 1)) := by ring
  _ = _ := by rw [hd,mul_one]
theorem order_distance_strict (s : Schedule) (hG : 0<G s) :
 0 < traceDist (krausMap (flipKraus s) (basisState 0 ⊗ₖ basisState 0))
 (krausMap (XafterKraus s) (basisState 0 ⊗ₖ basisState 0)) := by
 rw [order_distance]
 have ha : alpha s<1 := by
  rw [FiniteNontracialSchedule.alpha,Real.exp_lt_one_iff];linarith
 positivity

/-- A8: literal imaginary matrix unit. All identities below are complex algebra. -/
def imaginary : MatQ := Matrix.single 0 1 Complex.I
theorem imaginary_trace : imaginary.trace=0 := by
 norm_num [imaginary,Matrix.single,Matrix.trace,Fin.sum_univ_two]
theorem imaginary_diagonal : NontracialReflectionDynamics.diagonalPart imaginary=0 := by
 ext i j;fin_cases i <;> fin_cases j <;>
  norm_num [imaginary,Matrix.single,NontracialReflectionDynamics.diagonalPart]
theorem imaginary_weighted_trace : (rhoN*imaginary).trace=0 := by
 norm_num [imaginary,Matrix.single,rhoN,Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,
  Fin.sum_univ_two,vecHead,vecTail]
theorem imaginary_not_hermitian : ¬imaginary.IsHermitian := by
 intro h
 have he:=congrArg (fun M : MatQ => M 0 1) h.eq
 have hi:=congrArg Complex.im he
 norm_num [imaginary,Matrix.single,Matrix.conjTranspose_apply] at hi
theorem imaginary_not_density : ¬IsDensityOperator imaginary := by
 intro h;exact imaginary_not_hermitian h.1.isHermitian
theorem imaginary_not_PSD : ¬imaginary.PosSemidef := by
 intro h;exact imaginary_not_hermitian h.isHermitian
theorem imaginary_state (s : Schedule) :
 FiniteNontracialSchedule.state s imaginary=(beta s:ℂ) • imaginary :=
 FiniteNontracialSchedule.imaginary_offDiagonal s
theorem imaginary_observable (s : Schedule) :
 FiniteNontracialSchedule.observable s imaginary=(beta s:ℂ) • imaginary := by
 rw [FiniteNontracialSchedule.observable_formula]
 simp only [FiniteNontracialSchedule.observableForm,imaginary_weighted_trace,imaginary_diagonal,
  zero_smul,sub_zero,smul_zero,zero_add]
theorem imaginary_generator (γ η : ℝ) (hγ : 0≤γ) (hη : 0≤η) :
 FiniteNontracialSchedule.generator γ η imaginary= (-(γ+η):ℝ) • imaginary := by
 rw [FiniteNontracialSchedule.generator_formula γ η hγ hη,
  imaginary_trace,imaginary_diagonal]
 simp only [zero_smul,zero_sub]
 module
theorem imaginary_GKSL (γ η t : ℝ) (hγ : 0≤γ) (hη : 0≤η) (ht : 0≤t) :
 NontracialReflectionDynamics.state γ η t imaginary=
 (SKEFTHawking.OpenSystems.lindbladPropagatorAction 0
  (SKEFTHawking.FinitePositiveKernel.GibbsBlockRelaxation.jumps
   NontracialReflectionDynamics.signature NontracialPauliReflection.weights γ η) t) imaginary :=
 FiniteNontracialSchedule.primitive_propagator γ η t hγ hη ht _
theorem imaginary_trace_duality (s : Schedule) (A : MatQ) :
 (A*FiniteNontracialSchedule.state s imaginary).trace=
 (FiniteNontracialSchedule.observable s A*imaginary).trace :=
 FiniteNontracialSchedule.trace_dual s A imaginary
theorem imaginary_joint_state (s : Schedule) :
 FiniteNontracialEnvironmentLift.scheduleState s (basisState 0 ⊗ₖ imaginary)=
 (beta s:ℂ) • (basisState 0 ⊗ₖ imaginary) :=
 FiniteNontracialEnvironmentLift.schedule_imaginary_tensor s _
theorem imaginary_joint_not_hermitian : ¬(basisState 0 ⊗ₖ imaginary).IsHermitian :=
 FiniteNontracialEnvironmentLift.imaginary_tensor_not_hermitian
theorem imaginary_joint_effect_duality (s : Schedule) (A : MatJoint) :
 (A*FiniteNontracialEnvironmentLift.scheduleState s (basisState 0 ⊗ₖ imaginary)).trace=
 (FiniteNontracialEnvironmentLift.scheduleObservable s A*(basisState 0 ⊗ₖ imaginary)).trace :=
 FiniteNontracialEnvironmentLift.schedule_trace_dual s A _
/-- Actual arity-six effects stay on (Fin 2) × Unit, distinct from physical Joint. -/
theorem imaginary_reflection_run (p : NontracialHistoryConsistency.Gap)
 (rs : List NontracialHistoryConsistency.Gap) (s : Schedule)
 (u : NontracialHistoryConsistency.Labels rs) :
 (run (Fin 2) Unit 6 (NontracialScheduleTransfer.positiveTree p s rs) u
  (GibbsMultilevelReflection.joint imaginary)).trace=
 (Psi (p.value*p.value)
  (FiniteNontracialSchedule.observable s (NontracialHistoryConsistency.historyEffect rs u))*imaginary).trace :=
 NontracialScheduleTransfer.positive_trace p rs s u imaginary
theorem imaginary_reflection_half_run (p : NontracialHistoryConsistency.Gap)
 (rs : List NontracialHistoryConsistency.Gap) (s : Schedule)
 (u : NontracialHistoryConsistency.Labels rs) :
 (run (Fin 2) Unit 6 (NontracialScheduleTransfer.halfPositiveTree p s rs) u
  (GibbsMultilevelReflection.joint imaginary)).trace=
 (FiniteNontracialSchedule.observable (NontracialScheduleTransfer.halfSchedule s)
  (Psi p.value (NontracialHistoryConsistency.historyEffect rs u))*imaginary).trace :=
 NontracialScheduleTransfer.half_positive_trace p rs s u imaginary
theorem imaginary_reflection_effect (p : NontracialHistoryConsistency.Gap)
 (rs : List NontracialHistoryConsistency.Gap) (s : Schedule)
 (u : NontracialHistoryConsistency.Labels rs) :
 (FiniteAdaptiveProcessRobustness.effect (NontracialScheduleTransfer.positiveTree p s rs)
  (PauliHistoryConsistency.indicatorScore u)*GibbsMultilevelReflection.joint imaginary).trace=
 (GibbsMultilevelReflection.joint (Psi (p.value*p.value)
  (FiniteNontracialSchedule.observable s (NontracialHistoryConsistency.historyEffect rs u)))*
  GibbsMultilevelReflection.joint imaginary).trace := by
 rw [NontracialScheduleTransfer.unsplit_effect]
theorem imaginary_reflection_half_effect (p : NontracialHistoryConsistency.Gap)
 (rs : List NontracialHistoryConsistency.Gap) (s : Schedule)
 (u : NontracialHistoryConsistency.Labels rs) :
 (FiniteAdaptiveProcessRobustness.effect (NontracialScheduleTransfer.halfPositiveTree p s rs)
  (PauliHistoryConsistency.indicatorScore u)*GibbsMultilevelReflection.joint imaginary).trace=
 (GibbsMultilevelReflection.joint
  (FiniteNontracialSchedule.observable (NontracialScheduleTransfer.halfSchedule s)
   (Psi p.value (NontracialHistoryConsistency.historyEffect rs u)))*
  GibbsMultilevelReflection.joint imaginary).trace := by
 rw [NontracialScheduleTransfer.half_split_effect]

/-- Every table of both named experiments is a normalized physical law. -/
theorem paired_laws (s : Schedule) :
 ((∀ h a,0≤readoutTable correlationReadout (keepFamily s) h a) ∧
  (∑ h,∑ a,readoutTable correlationReadout (keepFamily s) h a)=1 ∧
  (∀ h a,0≤readoutTable correlationReadout (flipFamily s) h a) ∧
  (∑ h,∑ a,readoutTable correlationReadout (flipFamily s) h a)=1) ∧
 ((∀ h a,0≤readoutTable FiniteNontracialCoherentReadout.decisionReadout
   (FiniteNontracialCoherentReadout.family s qubitX) h a) ∧
  (∑ h,∑ a,readoutTable FiniteNontracialCoherentReadout.decisionReadout
   (FiniteNontracialCoherentReadout.family s qubitX) h a)=1 ∧
  (∀ h a,0≤readoutTable FiniteNontracialCoherentReadout.decisionReadout
   (FiniteNontracialCoherentReadout.family s qubitY) h a) ∧
  (∑ h,∑ a,readoutTable FiniteNontracialCoherentReadout.decisionReadout
   (FiniteNontracialCoherentReadout.family s qubitY) h a)=1) :=
 ⟨table_normalized s,FiniteNontracialCoherentReadout.decision_laws s⟩
theorem logTwo_complete_tables (i j b : Q) (h : FiniteNontracialCoherentReadout.Hist) (a : Q) :
 readoutTable correlationReadout (keepFamily [FiniteNontracialSchedule.logTwoSlice])
  (i,j,()) b=(if j=0 then logTwoKeep i b else 0) ∧
 readoutTable correlationReadout (flipFamily [FiniteNontracialSchedule.logTwoSlice])
  (i,j,()) b=(if j=0 then logTwoFlip i b else 0) ∧
 readoutTable FiniteNontracialCoherentReadout.decisionReadout
  (FiniteNontracialCoherentReadout.family [FiniteNontracialSchedule.logTwoSlice] qubitX) h a=
  (if a=h.1 then (if h.1=0 then (1+invSqrtTwo/4)/2 else (1-invSqrtTwo/4)/2) else 0) ∧
 readoutTable FiniteNontracialCoherentReadout.decisionReadout
  (FiniteNontracialCoherentReadout.family [FiniteNontracialSchedule.logTwoSlice] qubitY) h a=
  (if a=h.1 then (if h.1=0 then (1-invSqrtTwo/4)/2 else (1+invSqrtTwo/4)/2) else 0) :=
 ⟨(logTwo_diagonal_tables i j b).1,(logTwo_diagonal_tables i j b).2,
  FiniteNontracialCoherentReadout.logTwo_tables h a⟩
theorem dephasingLogTwo_complete_tables (i j b : Q) (h : FiniteNontracialCoherentReadout.Hist) (a : Q) :
 readoutTable correlationReadout (keepFamily [FiniteNontracialCoherentReadout.dephasingLogTwoSlice])
  (i,j,()) b=(if j=0 ∧ b=0 then 1/2 else 0) ∧
 readoutTable correlationReadout (flipFamily [FiniteNontracialCoherentReadout.dephasingLogTwoSlice])
  (i,j,()) b=(if j=0 ∧ b=1 then 1/2 else 0) ∧
 readoutTable FiniteNontracialCoherentReadout.decisionReadout
  (FiniteNontracialCoherentReadout.family [FiniteNontracialCoherentReadout.dephasingLogTwoSlice] qubitX) h a=
  (if a=h.1 then (if h.1=0 then (1+invSqrtTwo/2)/2 else (1-invSqrtTwo/2)/2) else 0) ∧
 readoutTable FiniteNontracialCoherentReadout.decisionReadout
  (FiniteNontracialCoherentReadout.family [FiniteNontracialCoherentReadout.dephasingLogTwoSlice] qubitY) h a=
  (if a=h.1 then (if h.1=0 then (1-invSqrtTwo/2)/2 else (1+invSqrtTwo/2)/2) else 0) :=
 ⟨(dephasingLogTwo_diagonal_tables i j b).1,(dephasingLogTwo_diagonal_tables i j b).2,
  FiniteNontracialCoherentReadout.dephasingLogTwo_tables h a⟩
theorem zero_dose_complete_tables (s : Schedule) (hG : G s=0) (hD : D s=0)
 (i j b : Q) (h : FiniteNontracialCoherentReadout.Hist) (a : Q) :
 readoutTable correlationReadout (keepFamily s) (i,j,()) b=(if j=0 ∧ b=0 then 1/2 else 0) ∧
 readoutTable correlationReadout (flipFamily s) (i,j,()) b=(if j=0 ∧ b=1 then 1/2 else 0) ∧
 readoutTable FiniteNontracialCoherentReadout.decisionReadout
  (FiniteNontracialCoherentReadout.family s qubitX) h a=
  (if a=h.1 then (if h.1=0 then (1+invSqrtTwo)/2 else (1-invSqrtTwo)/2) else 0) ∧
 readoutTable FiniteNontracialCoherentReadout.decisionReadout
  (FiniteNontracialCoherentReadout.family s qubitY) h a=
  (if a=h.1 then (if h.1=0 then (1-invSqrtTwo)/2 else (1+invSqrtTwo)/2) else 0) := by
 refine ⟨(zero_dose_tables s hG i j b).1,(zero_dose_tables s hG i j b).2,?_,?_⟩
 · rw [FiniteNontracialCoherentReadout.readoutTableA]
   simp only [FiniteNontracialCoherentReadout.probabilityA,
    FiniteNontracialCoherentReadout.zero_dose_beta s hG hD,one_mul]
 · rw [FiniteNontracialCoherentReadout.readoutTableB]
   simp only [FiniteNontracialCoherentReadout.probabilityB,
    FiniteNontracialCoherentReadout.zero_dose_beta s hG hD,one_mul]
theorem zero_duration_maps (s : Schedule) (hz : ∀ h∈s,h.duration=0) (X : MatJoint) :
 FiniteNontracialEnvironmentLift.scheduleState s X=X ∧
 FiniteNontracialEnvironmentLift.scheduleObservable s X=X :=
 zero_dose_maps s (FiniteNontracialSchedule.zero_duration_doses s hz).1
  (FiniteNontracialSchedule.zero_duration_doses s hz).2 X
theorem zero_rate_maps (s : Schedule) (hz : ∀ h∈s,h.gamma=0 ∧ h.eta=0) (X : MatJoint) :
 FiniteNontracialEnvironmentLift.scheduleState s X=X ∧
 FiniteNontracialEnvironmentLift.scheduleObservable s X=X :=
 zero_dose_maps s (FiniteNontracialSchedule.zero_rate_doses s hz).1
  (FiniteNontracialSchedule.zero_rate_doses s hz).2 X
theorem empty_maps (X : MatJoint) :
 FiniteNontracialEnvironmentLift.scheduleState [] X=X ∧
 FiniteNontracialEnvironmentLift.scheduleObservable [] X=X := zero_dose_maps [] rfl rfl X
theorem zero_dephasing_reference (s : Schedule) (hD : D s=0) :
 FiniteNontracialSchedule.state s rhoN=rhoN ∧ FiniteNontracialSchedule.observable s 1=1 := by
 refine ⟨FiniteNontracialSchedule.state_stationary s,?_⟩
 rw [(zero_dephasing_actions s hD 1).2]
 simp only [Psi,mul_one,NontracialPauliReflection.rhoN_density.2,one_smul]
 module

theorem reset_weights (s : Schedule) (i j : Q) :
 weight Q Q 2 (resetKeepTree s) (i,j,()) correlatedInput=(if j=0 then 1/2 else 0) ∧
 weight Q Q 2 (resetFlipTree s) (i,j,()) correlatedInput=(if j=0 then 1/2 else 0) := by
 change (resetKeepFamily s (i,j,())).trace.re=_ ∧ (resetFlipFamily s (i,j,())).trace.re=_
 rw [(reset_branches s i j).1,(reset_branches s i j).2]
 split_ifs <;> simp [Matrix.trace_smul,Matrix.trace_kronecker,(basisState_density 0).2,
  NontracialPauliReflection.rhoN_density.2]
theorem reset_terminal (s : Schedule) :
 terminalState Q Q 2 (resetKeepTree s) correlatedInput=stationaryInput ∧
 terminalState Q Q 2 (resetFlipTree s) correlatedInput=stationaryInput := by
 have hk : ∀ h : H, resetKeepFamily s h=if h.2.1=0 then (1/2:ℂ) • stationaryInput else 0 := by
  rintro ⟨i,j,⟨⟩⟩;exact (reset_branches s i j).1
 have hf : ∀ h : H, resetFlipFamily s h=if h.2.1=0 then (1/2:ℂ) • stationaryInput else 0 := by
  rintro ⟨i,j,⟨⟩⟩;exact (reset_branches s i j).2
 change (∑ h,resetKeepFamily s h)=_ ∧ (∑ h,resetFlipFamily s h)=_
 simp_rw [hk,hf]
 change (∑ h : Q × (Q × Unit), _)=_ ∧ (∑ h : Q × (Q × Unit), _)=_
 simp only [Fintype.sum_prod_type,Fin.sum_univ_two,Fintype.sum_unique]
 norm_num
 module
theorem reset_complete_tables (s : Schedule) (i j b : Q)
 (h : FiniteNontracialCoherentReadout.Hist) (a : Q) :
 readoutTable correlationReadout (resetKeepFamily s) (i,j,()) b=
  (if j=0 then (if b=0 then population i/2 else population (1-i)/2) else 0) ∧
 readoutTable correlationReadout (resetFlipFamily s) (i,j,()) b=
  (if j=0 then (if b=0 then population i/2 else population (1-i)/2) else 0) ∧
 readoutTable FiniteNontracialCoherentReadout.decisionReadout
  (FiniteNontracialCoherentReadout.resetFamily s qubitX) h a=(if a=h.1 then 1/2 else 0) ∧
 readoutTable FiniteNontracialCoherentReadout.decisionReadout
  (FiniteNontracialCoherentReadout.resetFamily s qubitY) h a=(if a=h.1 then 1/2 else 0) :=
 ⟨(reset_tables s i j b).1,(reset_tables s i j b).2,FiniteNontracialCoherentReadout.reset_tables s h a⟩
theorem constantReadout_normalized (h : H) :
 (∑ a,∑ k,((constantReadout h).operators a k)ᴴ*(constantReadout h).operators a k)=1 :=
 (constantReadout h).normalized
theorem reset_effect_admissible (h : H) : IsBinaryPOVM (correlationEffect h) :=
 isBinaryPOVM_of_projection (correlationEffect_hermitian h) (correlationEffect_idem h)
theorem reset_literally_impossible (s : Schedule) (i b : Q) :
 resetKeepFamily s (i,1,())=0 ∧ resetFlipFamily s (i,1,())=0 ∧
 readoutTable correlationReadout (resetKeepFamily s) (i,1,()) b=0 ∧
 readoutTable correlationReadout (resetFlipFamily s) (i,1,()) b=0 := by
 have hh:=reset_branches s i 1
 have ht:=reset_tables s i 1 b
 simpa using And.intro hh.1 (And.intro hh.2 ht)
theorem reset_before_X_does_not_erase :
 krausMap environmentXKraus (FiniteNontracialEnvironmentLift.gibbsReset (basisState 0 ⊗ₖ basisState 0)) ≠
 FiniteNontracialEnvironmentLift.gibbsReset (basisState 0 ⊗ₖ basisState 0) := by
 rw [FiniteNontracialEnvironmentLift.gibbsReset_eq,
  FiniteNontracialEnvironmentLift.ptrace2_kronecker,(basisState_density 0).2,one_smul,
  environmentX_product]
 intro he
 have h:=congrArg (fun X : MatJoint => X (0,0) (0,0)) he
 norm_num [Matrix.kronecker_apply,basisState,pauliX,rhoN,Matrix.mul_apply,Fin.sum_univ_two] at h
theorem system_effect_attainment (s : Schedule) :
 readoutError (systemKeepFamily s) (systemFlipFamily s) correlationEffect=(1-alpha s)/2 := by
 rw [(system_families_preserved s).1,(system_families_preserved s).2]
 exact effect_error s
theorem stationary_named_attainment (s : Schedule) :
 readoutError (stationaryFamily s) (stationaryFamily s) correlationEffect=1/2 ∧
 instrumentError (stationaryFamily s) (stationaryFamily s) constantReadout=1/2 ∧
 historyError (stationaryFamily s) (stationaryFamily s) (fun _ => 0)=1/2 :=
 ⟨stationary_every_effect s _,stationary_every_readout s _,stationary_every_history s _⟩
theorem stationary_complex_pair (s : Schedule) :
 branchDistance (stationaryFamily s) (stationaryFamily s)=0 ∧
 outputDistance Q Q 2 (FiniteNontracialCoherentReadout.tree s) (FiniteNontracialCoherentReadout.tree s)
  (FiniteNontracialCoherentReadout.input rhoN) (FiniteNontracialCoherentReadout.input rhoN)=0 :=
 ⟨(stationary_distances s).1,
  (FiniteNontracialCoherentReadout.identical_controls s NontracialPauliReflection.rhoN_density).1⟩
theorem rhoN_flip_difference :
 rhoN-pauliX*rhoN*pauliX=(7/25:ℂ) • (basisState 0-basisState 1) := by
 ext i j;fin_cases i <;> fin_cases j <;>
  norm_num [rhoN,pauliX,basisState,Matrix.mul_apply,Matrix.vecMul,dotProduct,
   Fin.sum_univ_two,Matrix.sub_apply]
theorem order_reset_component (s : Schedule) :
 FiniteNontracialSchedule.state s (basisState 1)-
  pauliX*FiniteNontracialSchedule.state s (basisState 0)*pauliX=
 ((1-alpha s:ℝ):ℂ) • (rhoN-pauliX*rhoN*pauliX) := by
 rw [order_qubit_difference,rhoN_flip_difference,smul_smul]
 congr 1
 push_cast
 ring
theorem orders_distinct (s : Schedule) (hG : 0<G s) :
 krausMap (flipKraus s) (basisState 0 ⊗ₖ basisState 0) ≠
 krausMap (XafterKraus s) (basisState 0 ⊗ₖ basisState 0) := by
 intro he
 have hh:=order_distance_strict s hG
 rw [he,traceDist_self] at hh
 exact lt_irrefl _ hh

theorem paired_all_effect_optima (s : Schedule) :
 IsLeast {x : ℝ | ∃ E : H → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
  readoutError (keepFamily s) (flipFamily s) E=x} ((1-alpha s)/2) ∧
 IsLeast {x : ℝ | ∃ E : FiniteNontracialCoherentReadout.Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
  readoutError (FiniteNontracialCoherentReadout.family s qubitX)
   (FiniteNontracialCoherentReadout.family s qubitY) E=x} ((1-beta s*invSqrtTwo)/2) :=
 ⟨all_effect_isLeast s,FiniteNontracialCoherentReadout.all_effect_isLeast s⟩
theorem reset_readout_isLeast (s : Schedule) :
 IsLeast {x : ℝ | ∃ I : H → FiniteInstrument (Q×Q) 2,
  instrumentError (resetKeepFamily s) (resetFlipFamily s) I=x} (1/2) := by
 constructor
 · exact ⟨correlationReadout,reset_every_readout s _⟩
 · rintro x ⟨I,rfl⟩;rw [reset_every_readout]
theorem stationary_readout_isLeast (s : Schedule) :
 IsLeast {x : ℝ | ∃ I : H → FiniteInstrument (Q×Q) 2,
  instrumentError (stationaryFamily s) (stationaryFamily s) I=x} (1/2) := by
 constructor
 · exact ⟨constantReadout,stationary_every_readout s _⟩
 · rintro x ⟨I,rfl⟩;rw [stationary_every_readout]
theorem reset_complex_optimum_pair (s : Schedule) :
 IsLeast {x : ℝ | ∃ E : H → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
  readoutError (resetKeepFamily s) (resetFlipFamily s) E=x} (1/2) ∧
 IsLeast {x : ℝ | ∃ E : FiniteNontracialCoherentReadout.Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
  readoutError (FiniteNontracialCoherentReadout.resetFamily s qubitX)
   (FiniteNontracialCoherentReadout.resetFamily s qubitY) E=x} (1/2) :=
 ⟨reset_all_effect_isLeast s,FiniteNontracialCoherentReadout.reset_all_effect_isLeast s⟩
theorem system_laws (s : Schedule) :
 (∀ h a,0≤readoutTable correlationReadout (systemKeepFamily s) h a) ∧
 (∑ h,∑ a,readoutTable correlationReadout (systemKeepFamily s) h a)=1 ∧
 (∀ h a,0≤readoutTable correlationReadout (systemFlipFamily s) h a) ∧
 (∑ h,∑ a,readoutTable correlationReadout (systemFlipFamily s) h a)=1 := by
 rw [(system_families_preserved s).1,(system_families_preserved s).2]
 exact table_normalized s
theorem system_output_distance (s : Schedule) :
 outputDistance Q Q 2 (systemKeepTree s) (systemFlipTree s) correlatedInput correlatedInput=alpha s := by
 rw [← tree_branchDistance]
 exact (system_controls s).1
theorem zero_dose_complex_optimum (s : Schedule) (hG : G s=0) (hD : D s=0) :
 IsLeast {x : ℝ | ∃ E : FiniteNontracialCoherentReadout.Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
  readoutError (FiniteNontracialCoherentReadout.family s qubitX)
   (FiniteNontracialCoherentReadout.family s qubitY) E=x} ((1-invSqrtTwo)/2) := by
 simpa only [FiniteNontracialCoherentReadout.zero_dose_beta s hG hD,one_mul] using
  FiniteNontracialCoherentReadout.all_effect_isLeast s
/-- Positivity is finite: genuine full reset is a distinct constructor. -/
theorem finite_retention_positive (s : Schedule) : 0<beta s ∧ 0<alpha s :=
 ⟨(FiniteNontracialSchedule.coefficients s).1,Real.exp_pos _⟩
theorem reset_literal_table_sum :
 (∑ h : H,∑ b : Q,
  if h.2.1=0 then (if b=0 then population h.1/2 else population (1-h.1)/2) else 0)=1 := by
 change (∑ h : Q × (Q × Unit),∑ b : Q,_)=1
 norm_num [Fintype.sum_prod_type,Fin.sum_univ_two,Fintype.sum_unique,
  population,NontracialPauliReflection.weights]
theorem imaginary_central_branch (p : NontracialHistoryConsistency.Gap)
 (s : Schedule) (a : Fin 6) :
 (NontracialScheduleTransfer.centralStep p s).branch (Fin 2) Unit 6 a
  (GibbsMultilevelReflection.joint imaginary)=
 GibbsMultilevelReflection.joint
  (NontracialPauliReflection.instrument.branch a
   (FiniteNontracialSchedule.state s (Phi (p.value*p.value) imaginary))) :=
 NontracialScheduleTransfer.centralStep_branch p s a imaginary
end SKEFTHawking.QuantumNetwork.FiniteNontracialMemoryScheduleControls
