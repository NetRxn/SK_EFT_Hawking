import SKEFTHawking.QuantumNetwork.FiniteNontracialThermalPhase

/-! Actual phase-covariant and fixed coherent observations on the physical Q × Q carrier.
All branches remain unnormalized. The diagonal controls retain their recorded chronology;
the independent reflection quotient controls keep their separate carrier and six outcomes.
The exact GKSL witness uses chosen mathematical parameters, with no calibration claim. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteNontracialPhaseReadout
open SKEFTHawking.FinitePositiveKernel.GibbsObservable
open Matrix FiniteMemoryProcess FiniteMemoryCoarseGraining FiniteInterventionProcess
open FiniteAdaptiveMapPerturbation FiniteAdaptiveReadoutDiscrimination FiniteAdaptiveReadoutRobustness
open FiniteNontracialSchedule (alpha beta G D)
open NontracialPauliReflection (rhoN rhoN_trace rhoN_density)
open FiniteNontracialThermalPhase
open scoped BigOperators Kronecker ComplexOrder
abbrev Q := Fin 2
abbrev MatQ := Matrix Q Q ℂ
abbrev MatJoint := Matrix (Q × Q) (Q × Q) ℂ
abbrev Hist := History 2 1
def projector (φ : ℝ) : MatQ := C φ qubitProjector
theorem projector_hermitian (φ : ℝ) : (projector φ).IsHermitian :=
 C_hermitian φ qubitProjector_hermitian
theorem projector_idem (φ : ℝ) : projector φ * projector φ = projector φ := by
 rw [projector, ← C_mul, qubitProjector_idem]
def readout (φ : ℝ) : FiniteInstrument Q 2 :=
 projectiveReadout (projector φ) (projector_hermitian φ) (projector_idem φ)
def readProjection (φ : ℝ) (a : Q) : MatQ :=
 C φ (FiniteNontracialCoherentReadout.readProjection a)
theorem readProjection_complement (φ : ℝ) :
 readProjection φ 1 = 1 - projector φ := by
 simp only [readProjection, FiniteNontracialCoherentReadout.readProjection]
 norm_num
 rw [C_sub, C_one]
 rfl
theorem compression (φ : ℝ) (a : Q) (X : MatQ) :
 readProjection φ a * X * readProjection φ a =
   (readProjection φ a * X).trace • readProjection φ a := by
 have hi : C φ (C (-φ) X) = X := by simpa using C_inverse (-φ) X
 conv_lhs => arg 1; arg 2; rw [← hi]
 rw [readProjection, ← C_mul, ← C_mul,
   FiniteNontracialCoherentReadout.readProjection_compression, C_smul]
 congr 1
 rw [← C_trace φ (FiniteNontracialCoherentReadout.readProjection a * C (-φ) X),
   C_mul, hi]
theorem readout_branch (φ : ℝ) (a : Q) (X : MatQ) :
 (readout φ).branch a X = (readProjection φ a * X).trace • readProjection φ a := by
 fin_cases a
 · change (readout φ).branch 0 X = _
   rw [readout, projectiveReadout_branch_zero]
   exact compression φ 0 X
 · change (readout φ).branch 1 X = _
   rw [readout, projectiveReadout_branch_one, ← readProjection_complement]
   exact compression φ 1 X

theorem C_pauliX (θ : ℝ) :
 C θ pauliX = (Real.cos θ : ℂ) • pauliX - (Real.sin θ : ℂ) • pauliY := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  norm_num [C_entry, pauliX, pauliY, Complex.exp_mul_I, mul_comm Complex.I]
 all_goals norm_num [← neg_mul, Complex.exp_mul_I]
 all_goals ring_nf
theorem C_pauliY (θ : ℝ) :
 C θ pauliY = (Real.sin θ : ℂ) • pauliX + (Real.cos θ : ℂ) • pauliY := by
 ext i j
 fin_cases i <;> fin_cases j <;>
  norm_num [C_entry, pauliX, pauliY, Complex.exp_mul_I, mul_comm Complex.I] <;>
  norm_num [← neg_mul, Complex.exp_mul_I] <;> ring_nf <;> norm_num [Complex.I_sq]
def evolution (θ : ℝ) (s : Schedule) :=
 composeKraus swapKraus (freeLiftKraus θ s)
theorem evolution_normalized (θ : ℝ) (s : Schedule) : IsKrausChannel (evolution θ s) :=
 isKrausChannel_composeKraus swapKraus_normalized (free_lift_normalized θ s)
def observedTree (θ : ℝ) (s : Schedule) (I : FiniteInstrument Q 2) : Tree Q Q 2 1 :=
 .node (realizedStep Q Q 2 (evolution θ s) (evolution_normalized θ s) I) (fun _ => .done)
def family (θ φ : ℝ) (s : Schedule) (X : MatQ) (h : Hist) : MatJoint :=
 run Q Q 2 (observedTree θ s (readout φ)) h (FiniteNontracialCoherentReadout.input X)
theorem observed_branch (θ : ℝ) (s : Schedule) (I : FiniteInstrument Q 2) (a : Q) (X : MatQ) :
 run Q Q 2 (observedTree θ s I) (a,()) (FiniteNontracialCoherentReadout.input X) =
 I.branch a (freeState θ s X) ⊗ₖ basisState 0 := by
 change (I.lift Q).branch a (krausMap (evolution θ s) (FiniteNontracialCoherentReadout.input X)) = _
 rw [evolution, krausMap_composeKraus]
 change (I.lift Q).branch a (swapJoint (krausMap (freeLiftKraus θ s)
  (FiniteNontracialCoherentReadout.input X))) = _
 rw [FiniteNontracialCoherentReadout.input, free_lift_product, swap_tensor, lift_branch_tensor]
theorem family_valid (θ φ : ℝ) (s : Schedule) {X : MatQ} (hX : IsDensityOperator X) :
 IsBranchFamily (family θ φ s X) :=
 run_family _ (FiniteNontracialCoherentReadout.input_density hX)
theorem familyA_valid (θ φ : ℝ) (s : Schedule) :
 IsBranchFamily (family θ φ s qubitX) := family_valid θ φ s qubitX_density
theorem familyB_valid (θ φ : ℝ) (s : Schedule) :
 IsBranchFamily (family θ φ s qubitY) := family_valid θ φ s qubitY_density
def probabilityA (θ : ℝ) (s : Schedule) (a : Q) : ℝ :=
 if a=0 then (1+beta s*invSqrtTwo*(Real.cos θ+Real.sin θ))/2
 else (1-beta s*invSqrtTwo*(Real.cos θ+Real.sin θ))/2
def probabilityB (θ : ℝ) (s : Schedule) (a : Q) : ℝ :=
 if a=0 then (1+beta s*invSqrtTwo*(Real.sin θ-Real.cos θ))/2
 else (1-beta s*invSqrtTwo*(Real.sin θ-Real.cos θ))/2
theorem trace_probabilityA (θ : ℝ) (s : Schedule) (a : Q) :
 (FiniteNontracialCoherentReadout.readProjection a * freeState θ s qubitX).trace =
 (probabilityA θ s a : ℂ) := by
 rw [free_state, FiniteNontracialCoherentReadout.schedule_qubitX, C_add, C_add,
   C_smul, C_rho, C_smul, C_smul, C_one, C_smul, C_smul, C_pauliX]
 fin_cases a <;>
  norm_num [FiniteNontracialCoherentReadout.readProjection, probabilityA,
   qubitProjector, qubitDirection, rhoN, pauliX, pauliY, Matrix.trace,
   Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
   Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div] <;>
  ring_nf <;> norm_num [Complex.I_sq] <;> ring
theorem trace_probabilityB (θ : ℝ) (s : Schedule) (a : Q) :
 (FiniteNontracialCoherentReadout.readProjection a * freeState θ s qubitY).trace =
 (probabilityB θ s a : ℂ) := by
 rw [free_state, FiniteNontracialCoherentReadout.schedule_qubitY, C_add, C_add,
   C_smul, C_rho, C_smul, C_smul, C_one, C_smul, C_smul, C_pauliY]
 fin_cases a <;>
  norm_num [FiniteNontracialCoherentReadout.readProjection, probabilityB,
   qubitProjector, qubitDirection, rhoN, pauliX, pauliY, Matrix.trace,
   Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
   Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div] <;>
  ring_nf <;> norm_num [Complex.I_sq] <;> ring



theorem rotated_trace (θ φ : ℝ) (s : Schedule) (a : Q) (X : MatQ) :
 (readProjection φ a * freeState θ s X).trace =
 (FiniteNontracialCoherentReadout.readProjection a * freeState (θ-φ) s X).trace := by
 rw [readProjection, free_state, free_state]
 have h : C θ (FiniteNontracialSchedule.state s X) =
   C φ (C (θ-φ) (FiniteNontracialSchedule.state s X)) := by
  rw [← C_group]
  congr 1
  ring
 rw [h, ← C_mul, C_trace]
theorem familyA_branch (θ φ : ℝ) (s : Schedule) (h : Hist) :
 family θ φ s qubitX h = (probabilityA (θ-φ) s h.1 : ℂ) •
   (readProjection φ h.1 ⊗ₖ basisState 0) := by
 rcases h with ⟨a,⟨⟩⟩
 change run Q Q 2 (observedTree θ s (readout φ)) (a,()) (FiniteNontracialCoherentReadout.input qubitX)=_
 rw [observed_branch, readout_branch, rotated_trace, trace_probabilityA, Matrix.smul_kronecker]
theorem familyB_branch (θ φ : ℝ) (s : Schedule) (h : Hist) :
 family θ φ s qubitY h = (probabilityB (θ-φ) s h.1 : ℂ) •
   (readProjection φ h.1 ⊗ₖ basisState 0) := by
 rcases h with ⟨a,⟨⟩⟩
 change run Q Q 2 (observedTree θ s (readout φ)) (a,()) (FiniteNontracialCoherentReadout.input qubitY)=_
 rw [observed_branch, readout_branch, rotated_trace, trace_probabilityB, Matrix.smul_kronecker]
theorem readProjection_trace (φ : ℝ) (a : Q) : (readProjection φ a).trace=1 := by
 rw [readProjection, C_trace, FiniteNontracialCoherentReadout.readProjection_trace]
theorem readProjection_density (φ : ℝ) (a : Q) : IsDensityOperator (readProjection φ a) := by
 refine ⟨?_, readProjection_trace φ a⟩
 apply C_posSemidef
 have h := qubitReadout.branch_posSemidef a (Matrix.PosSemidef.one : (1:MatQ).PosSemidef)
 rw [FiniteNontracialCoherentReadout.readout_branch, Matrix.mul_one,
  FiniteNontracialCoherentReadout.readProjection_trace, one_smul] at h
 exact h
theorem support_density (φ : ℝ) (a : Q) :
 IsDensityOperator (readProjection φ a ⊗ₖ basisState 0) :=
 ⟨(readProjection_density φ a).1.kronecker (basisState_density 0).1,
  by rw [Matrix.trace_kronecker, (readProjection_density φ a).2, (basisState_density 0).2, one_mul]⟩
theorem familyA_trace (θ φ : ℝ) (s : Schedule) (h : Hist) :
 (family θ φ s qubitX h).trace = (probabilityA (θ-φ) s h.1 : ℂ) := by
 rw [familyA_branch, Matrix.trace_smul, (support_density φ h.1).2, smul_eq_mul, mul_one]
theorem familyB_trace (θ φ : ℝ) (s : Schedule) (h : Hist) :
 (family θ φ s qubitY h).trace = (probabilityB (θ-φ) s h.1 : ℂ) := by
 rw [familyB_branch, Matrix.trace_smul, (support_density φ h.1).2, smul_eq_mul, mul_one]
theorem probability_nonnegative (θ : ℝ) (s : Schedule) (a : Q) :
 0 ≤ probabilityA θ s a ∧ 0 ≤ probabilityB θ s a := by
 have hA := (familyA_valid θ 0 s).1 (a,())
 have hB := (familyB_valid θ 0 s).1 (a,())
 have ha := hA.trace_nonneg
 have hb := hB.trace_nonneg
 rw [familyA_trace, sub_zero] at ha
 rw [familyB_trace, sub_zero] at hb
 exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
theorem full_laws (θ φ : ℝ) (s : Schedule) :
 (∀ h, 0 ≤ (family θ φ s qubitX h).trace.re) ∧ (∑ h, (family θ φ s qubitX h).trace.re)=1 ∧
 (∀ h, 0 ≤ (family θ φ s qubitY h).trace.re) ∧ (∑ h, (family θ φ s qubitY h).trace.re)=1 := by
 refine ⟨?_, (familyA_valid θ φ s).2, ?_, (familyB_valid θ φ s).2⟩
 · intro h; rw [familyA_trace, Complex.ofReal_re]; exact (probability_nonnegative _ _ _).1
 · intro h; rw [familyB_trace, Complex.ofReal_re]; exact (probability_nonnegative _ _ _).2
theorem probability_difference (θ : ℝ) (s : Schedule) (a : Q) :
 probabilityA θ s a - probabilityB θ s a =
 if a=0 then beta s*invSqrtTwo*Real.cos θ else -(beta s*invSqrtTwo*Real.cos θ) := by
 unfold probabilityA probabilityB
 split_ifs <;> ring
theorem support_norm (φ : ℝ) (a : Q) :
 traceNorm (readProjection φ a ⊗ₖ basisState 0)=1 := by
 rw [traceNorm_eq_physlib]
 have h := (support_density φ a).1.traceNorm_eq_trace
 rw [(support_density φ a).2] at h
 exact_mod_cast congrArg Complex.re h
theorem branch_distance (θ φ : ℝ) (s : Schedule) (h : Hist) :
 traceDist (family θ φ s qubitX h) (family θ φ s qubitY h) =
 |probabilityA (θ-φ) s h.1-probabilityB (θ-φ) s h.1|/2 := by
 rcases h with ⟨a,⟨⟩⟩
 rw [familyA_branch, familyB_branch]
 unfold traceDist
 rw [← sub_smul, ← Complex.ofReal_sub, traceNorm_eq_physlib, Matrix.traceNorm_smul, ← traceNorm_eq_physlib, support_norm, Complex.norm_real,
  Real.norm_eq_abs]
 ring
theorem observed_distance (θ φ : ℝ) (s : Schedule) :
 branchDistance (family θ φ s qubitX) (family θ φ s qubitY) =
 beta s*invSqrtTwo*|Real.cos (θ-φ)| := by
 unfold branchDistance
 simp only [branch_distance, probability_difference]
 change (∑ h : Q × Unit, |if h.1=0 then beta s*invSqrtTwo*Real.cos (θ-φ)
   else -(beta s*invSqrtTwo*Real.cos (θ-φ))|/2)=_
 norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, abs_mul,
  abs_of_pos (FiniteNontracialCoherentReadout.separation_bounds s).1]
theorem observed_variation (θ φ : ℝ) (s : Schedule) :
 familyHistoryVariation (family θ φ s qubitX) (family θ φ s qubitY) =
 beta s*invSqrtTwo*|Real.cos (θ-φ)| := by
 unfold familyHistoryVariation
 simp only [familyA_trace, familyB_trace, Complex.ofReal_re, probability_difference]
 change (∑ h : Q × Unit, |if h.1=0 then beta s*invSqrtTwo*Real.cos (θ-φ)
   else -(beta s*invSqrtTwo*Real.cos (θ-φ))|)/2=_
 norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, abs_mul,
  abs_of_pos (FiniteNontracialCoherentReadout.separation_bounds s).1]


theorem first_event_separation (θ φ : ℝ) (s : Schedule) :
 (family θ φ s qubitX (0,())).trace.re -
 (family θ φ s qubitY (0,())).trace.re = beta s*invSqrtTwo*Real.cos (θ-φ) := by
 rw [familyA_trace, familyB_trace, Complex.ofReal_re, Complex.ofReal_re, probability_difference]
 simp
theorem observed_distance_lower (θ φ : ℝ) (s : Schedule) :
 beta s*invSqrtTwo*|Real.cos (θ-φ)| ≤
 branchDistance (family θ φ s qubitX) (family θ φ s qubitY) := by
 rw [← observed_variation]
 exact familyHistoryVariation_le_branchDistance (familyA_valid θ φ s) (familyB_valid θ φ s)
theorem observed_distance_upper (θ φ : ℝ) (s : Schedule) :
 branchDistance (family θ φ s qubitX) (family θ φ s qubitY) ≤
 beta s*invSqrtTwo*|Real.cos (θ-φ)| := le_of_eq (observed_distance θ φ s)
theorem pre_qubit_distance (θ : ℝ) (s : Schedule) :
 traceDist (freeState θ s qubitX) (freeState θ s qubitY)=beta s*invSqrtTwo := by
 rw [free_distance qubitX_density.1.isHermitian qubitY_density.1.isHermitian,
  FiniteNontracialCoherentReadout.pre_qubit_distance]
theorem pre_joint_distance (θ : ℝ) (s : Schedule) :
 traceDist (krausMap (freeLiftKraus θ s) (FiniteNontracialCoherentReadout.input qubitX))
  (krausMap (freeLiftKraus θ s) (FiniteNontracialCoherentReadout.input qubitY))=
 beta s*invSqrtTwo := by
 rw [FiniteNontracialCoherentReadout.input, FiniteNontracialCoherentReadout.input,
  free_lift_product, free_lift_product,
  FiniteAdaptiveProcessRobustness.traceDist_tensor_left (basisState_density 0), pre_qubit_distance]
theorem tree_output_distance (θ φ : ℝ) (s : Schedule) :
 outputDistance Q Q 2 (observedTree θ s (readout φ)) (observedTree θ s (readout φ))
  (FiniteNontracialCoherentReadout.input qubitX) (FiniteNontracialCoherentReadout.input qubitY)=
 beta s*invSqrtTwo*|Real.cos (θ-φ)| := by
 rw [← tree_branchDistance]
 exact observed_distance θ φ s
theorem tree_history_variation (θ φ : ℝ) (s : Schedule) :
 historyVariation Q Q 2 (observedTree θ s (readout φ)) (observedTree θ s (readout φ))
  (FiniteNontracialCoherentReadout.input qubitX) (FiniteNontracialCoherentReadout.input qubitY)=
 beta s*invSqrtTwo*|Real.cos (θ-φ)| := by
 rw [← tree_familyHistoryVariation]
 exact observed_variation θ φ s
def decisionLabel (rev : Bool) (h : Hist) : Q :=
 if rev then (if h.1=0 then 1 else 0) else h.1
def decisionScore (rev : Bool) (h : Hist) : ℝ := if decisionLabel rev h=0 then 1 else 0
def decisionProjection (rev : Bool) (h : Hist) : MatJoint := if decisionLabel rev h=0 then 1 else 0
theorem decisionProjection_hermitian (rev : Bool) (h : Hist) : (decisionProjection rev h).IsHermitian := by
 unfold decisionProjection; split_ifs <;> simp
theorem decisionProjection_idem (rev : Bool) (h : Hist) :
 decisionProjection rev h*decisionProjection rev h=decisionProjection rev h := by
 unfold decisionProjection; split_ifs <;> simp
def decisionReadout (rev : Bool) (h : Hist) : FiniteInstrument (Q × Q) 2 :=
 projectiveReadout (decisionProjection rev h) (decisionProjection_hermitian rev h) (decisionProjection_idem rev h)
theorem decisionProjection_admissible (rev : Bool) (h : Hist) : IsBinaryPOVM (decisionProjection rev h) := by
 unfold decisionProjection
 split_ifs
 · exact ⟨Matrix.PosSemidef.one, by simpa only [sub_self] using (Matrix.PosSemidef.zero : (0:MatJoint).PosSemidef)⟩
 · exact ⟨Matrix.PosSemidef.zero, by simpa only [sub_zero] using (Matrix.PosSemidef.one : (1:MatJoint).PosSemidef)⟩
theorem decisionScore_admissible (rev : Bool) : ∀ h, decisionScore rev h∈Set.Icc (0:ℝ) 1 := by
 intro h; unfold decisionScore; split_ifs <;> norm_num
theorem decisionReadout_weight (rev : Bool) (h : Hist) (a : Q) (Z : MatJoint) :
 (decisionReadout rev h).weight a Z = if a=decisionLabel rev h then Z.trace.re else 0 := by
 rcases h with ⟨h,⟨⟩⟩
 cases rev <;> fin_cases h <;> fin_cases a <;>
  norm_num [decisionReadout,decisionProjection,decisionLabel, projectiveReadout_weight_zero,
   projectiveReadout_weight_one]
theorem readoutTableA (θ φ : ℝ) (s : Schedule) (rev : Bool) (h : Hist) (a : Q) :
 readoutTable (decisionReadout rev) (family θ φ s qubitX) h a =
 if a=decisionLabel rev h then probabilityA (θ-φ) s h.1 else 0 := by
 rw [readoutTable, decisionReadout_weight, familyA_trace, Complex.ofReal_re]
theorem readoutTableB (θ φ : ℝ) (s : Schedule) (rev : Bool) (h : Hist) (a : Q) :
 readoutTable (decisionReadout rev) (family θ φ s qubitY) h a =
 if a=decisionLabel rev h then probabilityB (θ-φ) s h.1 else 0 := by
 rw [readoutTable, decisionReadout_weight, familyB_trace, Complex.ofReal_re]
theorem decision_laws (θ φ : ℝ) (s : Schedule) (rev : Bool) :
 (∀ h a, 0≤readoutTable (decisionReadout rev) (family θ φ s qubitX) h a) ∧
 (∑ h, ∑ a, readoutTable (decisionReadout rev) (family θ φ s qubitX) h a)=1 ∧
 (∀ h a, 0≤readoutTable (decisionReadout rev) (family θ φ s qubitY) h a) ∧
 (∑ h, ∑ a, readoutTable (decisionReadout rev) (family θ φ s qubitY) h a)=1 :=
 ⟨readoutTable_nonneg _ (familyA_valid θ φ s), readoutTable_total _ (familyA_valid θ φ s),
  readoutTable_nonneg _ (familyB_valid θ φ s), readoutTable_total _ (familyB_valid θ φ s)⟩
theorem decision_attains (θ φ : ℝ) (s : Schedule) (rev : Bool) :
 instrumentError (family θ φ s qubitX) (family θ φ s qubitY) (decisionReadout rev)=
 if rev then (1+beta s*invSqrtTwo*Real.cos (θ-φ))/2
 else (1-beta s*invSqrtTwo*Real.cos (θ-φ))/2 := by
 unfold instrumentError
 simp only [readoutTableA, readoutTableB]
 change ((∑ h : Q × Unit, if (0:Q)=decisionLabel rev h then probabilityB (θ-φ) s h.1 else 0)+
  (∑ h : Q × Unit, if (1:Q)=decisionLabel rev h then probabilityA (θ-φ) s h.1 else 0))/2=_
 cases rev <;> norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, decisionLabel, probabilityA, probabilityB] <;> ring
theorem decision_effect_realizes (θ φ : ℝ) (s : Schedule) (rev : Bool) :
 readoutError (family θ φ s qubitX) (family θ φ s qubitY) (decisionProjection rev)=
 instrumentError (family θ φ s qubitX) (family θ φ s qubitY) (decisionReadout rev) := by
 simp only [readoutError,instrumentError,readoutTable,decisionReadout,
  projectiveReadout_weight_zero,projectiveReadout_weight_one]
theorem decisionScore_attains (θ φ : ℝ) (s : Schedule) (rev : Bool) :
 historyError (family θ φ s qubitX) (family θ φ s qubitY) (decisionScore rev)=
 if rev then (1+beta s*invSqrtTwo*Real.cos (θ-φ))/2
 else (1-beta s*invSqrtTwo*Real.cos (θ-φ))/2 := by
 rw [← historyError_scalar_effect]
 have he : (fun h => (decisionScore rev h:ℂ) • (1:MatJoint))=decisionProjection rev := by
  funext h; unfold decisionScore decisionProjection; split_ifs <;> simp
 rw [he, decision_effect_realizes, decision_attains]
def optimalReversal (θ φ : ℝ) : Bool := decide (Real.cos (θ-φ)<0)
theorem optimal_attains (θ φ : ℝ) (s : Schedule) :
 instrumentError (family θ φ s qubitX) (family θ φ s qubitY) (decisionReadout (optimalReversal θ φ))=
 (1-beta s*invSqrtTwo*|Real.cos (θ-φ)|)/2 := by
 rw [decision_attains]
 by_cases h : Real.cos (θ-φ)<0
 · simp [optimalReversal,h,abs_of_neg h]
 · simp [optimalReversal,h,abs_of_nonneg (le_of_not_gt h)]
theorem optimalScore_attains (θ φ : ℝ) (s : Schedule) :
 historyError (family θ φ s qubitX) (family θ φ s qubitY) (decisionScore (optimalReversal θ φ))=
 (1-beta s*invSqrtTwo*|Real.cos (θ-φ)|)/2 := by
 rw [decisionScore_attains, ← decision_attains]
 exact optimal_attains θ φ s
theorem all_effect_isLeast (θ φ : ℝ) (s : Schedule) :
 IsLeast {x : ℝ | ∃ E : Hist → MatJoint, (∀ h, IsBinaryPOVM (E h)) ∧
  readoutError (family θ φ s qubitX) (family θ φ s qubitY) E=x}
  ((1-beta s*invSqrtTwo*|Real.cos (θ-φ)|)/2) := by
 simpa only [observed_distance] using readoutError_isLeast (familyA_valid θ φ s) (familyB_valid θ φ s)
theorem randomized_isLeast (θ φ : ℝ) (s : Schedule) :
 IsLeast {x : ℝ | ∃ a : Hist → ℝ, (∀ h, a h∈Set.Icc (0:ℝ) 1) ∧
  historyError (family θ φ s qubitX) (family θ φ s qubitY) a=x}
  ((1-beta s*invSqrtTwo*|Real.cos (θ-φ)|)/2) := by
 simpa only [observed_variation] using historyError_isLeast (familyA_valid θ φ s) (familyB_valid θ φ s)


theorem probability_zero (s : Schedule) (a : Q) :
 probabilityA 0 s a=FiniteNontracialCoherentReadout.probabilityA s a ∧
 probabilityB 0 s a=FiniteNontracialCoherentReadout.probabilityB s a := by
 fin_cases a <;> norm_num [probabilityA, probabilityB,
  FiniteNontracialCoherentReadout.probabilityA, FiniteNontracialCoherentReadout.probabilityB]
 all_goals ring
theorem covariant_full_laws (θ : ℝ) (s : Schedule) :
 (∀ h, 0 < (family θ θ s qubitX h).trace.re) ∧ (∑ h, (family θ θ s qubitX h).trace.re)=1 ∧
 (∀ h, 0 < (family θ θ s qubitY h).trace.re) ∧ (∑ h, (family θ θ s qubitY h).trace.re)=1 := by
 refine ⟨?_,(familyA_valid θ θ s).2,?_,(familyB_valid θ θ s).2⟩
 · intro h; rw [familyA_trace,Complex.ofReal_re,sub_self,(probability_zero s h.1).1]
   exact FiniteNontracialCoherentReadout.probabilityA_positive s _
 · intro h; rw [familyB_trace,Complex.ofReal_re,sub_self,(probability_zero s h.1).2]
   exact FiniteNontracialCoherentReadout.probabilityB_positive s _
theorem covariant_branches (θ : ℝ) (s : Schedule) (h : Hist) :
 family θ θ s qubitX h = (FiniteNontracialCoherentReadout.probabilityA s h.1:ℂ) •
  (readProjection θ h.1 ⊗ₖ basisState 0) ∧
 family θ θ s qubitY h = (FiniteNontracialCoherentReadout.probabilityB s h.1:ℂ) •
  (readProjection θ h.1 ⊗ₖ basisState 0) := by
 rw [familyA_branch,familyB_branch,sub_self,(probability_zero s h.1).1,(probability_zero s h.1).2]
 exact ⟨rfl,rfl⟩
theorem covariant_distances (θ : ℝ) (s : Schedule) :
 branchDistance (family θ θ s qubitX) (family θ θ s qubitY)=beta s*invSqrtTwo ∧
 familyHistoryVariation (family θ θ s qubitX) (family θ θ s qubitY)=beta s*invSqrtTwo := by
 simp [observed_distance,observed_variation]
theorem covariant_attains (θ : ℝ) (s : Schedule) :
 instrumentError (family θ θ s qubitX) (family θ θ s qubitY) (decisionReadout false)=
 (1-beta s*invSqrtTwo)/2 := by simp [decision_attains]
theorem quarter_probabilities (s : Schedule) (a : Q) :
 probabilityA (Real.pi/2) s a=FiniteNontracialCoherentReadout.probabilityA s a ∧
 probabilityB (Real.pi/2) s a=FiniteNontracialCoherentReadout.probabilityA s a := by
 fin_cases a <;> norm_num [probabilityA,probabilityB,FiniteNontracialCoherentReadout.probabilityA]
theorem quarter_family_equal (s : Schedule) :
 family (Real.pi/2) 0 s qubitX = family (Real.pi/2) 0 s qubitY := by
 funext h
 rw [familyA_branch,familyB_branch,sub_zero,(quarter_probabilities s h.1).1,
  (quarter_probabilities s h.1).2]
theorem quarter_erasure (s : Schedule) :
 branchDistance (family (Real.pi/2) 0 s qubitX) (family (Real.pi/2) 0 s qubitY)=0 ∧
 familyHistoryVariation (family (Real.pi/2) 0 s qubitX) (family (Real.pi/2) 0 s qubitY)=0 ∧
 0<traceDist (freeState (Real.pi/2) s qubitX) (freeState (Real.pi/2) s qubitY) := by
 simp only [observed_distance,observed_variation,sub_zero,Real.cos_pi_div_two,abs_zero,mul_zero,
  pre_qubit_distance,true_and]
 exact (FiniteNontracialCoherentReadout.separation_bounds s).1
theorem quarter_every_effect (s : Schedule) (E : Hist → MatJoint) :
 readoutError (family (Real.pi/2) 0 s qubitX) (family (Real.pi/2) 0 s qubitY) E=1/2 := by
 rw [← quarter_family_equal]
 exact FiniteNontracialCoherentReadout.readoutError_same (familyA_valid _ _ _) E
theorem quarter_every_readout (s : Schedule) (I : Hist → FiniteInstrument (Q × Q) 2) :
 instrumentError (family (Real.pi/2) 0 s qubitX) (family (Real.pi/2) 0 s qubitY) I=1/2 := by
 rw [← quarter_family_equal]
 exact FiniteNontracialCoherentReadout.instrumentError_same (familyA_valid _ _ _) I
theorem quarter_every_history (s : Schedule) (a : Hist → ℝ) :
 historyError (family (Real.pi/2) 0 s qubitX) (family (Real.pi/2) 0 s qubitY) a=1/2 :=
 historyError_same_law (familyA_valid _ _ _) (fun h =>
  congrArg (fun Z : MatJoint => Z.trace.re) (congrFun (quarter_family_equal s) h)) a
theorem half_rule_worse (s : Schedule) :
 instrumentError (family Real.pi 0 s qubitX) (family Real.pi 0 s qubitY) (decisionReadout false)=
 (1+beta s*invSqrtTwo)/2 ∧
 1/2 < instrumentError (family Real.pi 0 s qubitX) (family Real.pi 0 s qubitY) (decisionReadout false) ∧
 instrumentError (family Real.pi 0 s qubitX) (family Real.pi 0 s qubitY) (decisionReadout true)=
 (1-beta s*invSqrtTwo)/2 := by
 simp only [decision_attains,sub_zero,Real.cos_pi,mul_neg_one,Bool.false_eq_true,if_false,if_true,sub_neg_eq_add]
 constructor
 · trivial
 constructor
 · linarith [(FiniteNontracialCoherentReadout.separation_bounds s).1]
 · ring
theorem zero_cosine_tie (θ φ : ℝ) (s : Schedule) (hz : Real.cos (θ-φ)=0) (rev : Bool) :
 instrumentError (family θ φ s qubitX) (family θ φ s qubitY) (decisionReadout rev)=1/2 := by
 rw [decision_attains,hz]; cases rev <;> simp
theorem zero_readout : readout 0=qubitReadout := by
 unfold readout projector
 simp only [C_zero]
 rfl
theorem zero_family (s : Schedule) (X : MatQ) :
 family 0 0 s X=FiniteNontracialCoherentReadout.family s X := by
 funext h
 rcases h with ⟨a,⟨⟩⟩
 change run Q Q 2 (observedTree 0 s (readout 0)) (a,()) _=_
 rw [observed_branch,zero_readout,free_state,C_zero]
 exact (FiniteNontracialCoherentReadout.observed_branch s qubitReadout a X).symm
theorem period_family (s : Schedule) (X : MatQ) :
 family (2*Real.pi) 0 s X=FiniteNontracialCoherentReadout.family s X := by
 funext h
 rcases h with ⟨a,⟨⟩⟩
 change run Q Q 2 (observedTree (2*Real.pi) s (readout 0)) (a,()) _=_
 rw [observed_branch,zero_readout,free_state,C_full_period]
 exact (FiniteNontracialCoherentReadout.observed_branch s qubitReadout a X).symm
theorem eighth_empty_probability :
 probabilityA (Real.pi/4) [] 0=1 ∧ probabilityA (Real.pi/4) [] 1=0 := by
 have h : invSqrtTwo*Real.sqrt 2=1 := by
  unfold invSqrtTwo
  field_simp
 norm_num [probabilityA,FiniteNontracialSchedule.beta,FiniteNontracialSchedule.G,
  FiniteNontracialSchedule.D,Real.cos_pi_div_four,Real.sin_pi_div_four]
 constructor <;> nlinarith
theorem eighth_impossible_branch :
 family (Real.pi/4) 0 [] qubitX (1,())=0 := by
 rw [familyA_branch,sub_zero,eighth_empty_probability.2]
 simp
theorem eighth_impossible_table (rev : Bool) (a : Q) :
 readoutTable (decisionReadout rev) (family (Real.pi/4) 0 [] qubitX) (1,()) a=0 := by
 rw [readoutTableA,sub_zero,eighth_empty_probability.2]
 split_ifs <;> rfl
def erasureFamily (θ : ℝ) (s : Schedule) (X : MatQ) (h : Hist) : MatJoint :=
 run Q Q 2 (observedTree θ s FiniteInstrument.computational) h (FiniteNontracialCoherentReadout.input X)
theorem computational_branch (θ : ℝ) (s : Schedule) (X : MatQ) (h : Hist) :
 erasureFamily θ s X h=FiniteNontracialCoherentReadout.erasureFamily s X h := by
 rcases h with ⟨a,⟨⟩⟩
 change run Q Q 2 (observedTree θ s FiniteInstrument.computational) (a,()) _=_
 rw [observed_branch,FiniteNontracialCoherentReadout.computational_compression,free_state,C_entry]
 simp only [sub_self,mul_zero,Complex.exp_zero,one_mul]
 exact (by
  rw [FiniteNontracialCoherentReadout.erasureFamily,FiniteNontracialCoherentReadout.erasureTree,
   FiniteNontracialCoherentReadout.observed_branch,
   FiniteNontracialCoherentReadout.computational_compression])
theorem computational_erasure (θ : ℝ) (s : Schedule) :
 erasureFamily θ s qubitX=erasureFamily θ s qubitY := by
 funext h
 rw [computational_branch,computational_branch,
  FiniteNontracialCoherentReadout.erasure_family_equal]


def timedEvolution (b ℏ : ℝ) (s : Schedule) :=
 composeKraus swapKraus (timedLiftKraus b ℏ s)
theorem timedEvolution_normalized (b ℏ : ℝ) (s : Schedule) :
 IsKrausChannel (timedEvolution b ℏ s) :=
 isKrausChannel_composeKraus swapKraus_normalized (timed_lift_normalized b ℏ s)
def timedTree (b ℏ φ : ℝ) (s : Schedule) : Tree Q Q 2 1 :=
 .node (realizedStep Q Q 2 (timedEvolution b ℏ s) (timedEvolution_normalized b ℏ s) (readout φ))
  (fun _ => .done)
def timedFamily (b ℏ φ : ℝ) (s : Schedule) (X : MatQ) (h : Hist) : MatJoint :=
 run Q Q 2 (timedTree b ℏ φ s) h (FiniteNontracialCoherentReadout.input X)
theorem timed_family_eq (b ℏ φ : ℝ) (s : Schedule) (X : MatQ) :
 timedFamily b ℏ φ s X=family (totalPhase b ℏ s) φ s X := by
 funext h; rcases h with ⟨a,⟨⟩⟩
 change ((readout φ).lift Q).branch a (krausMap (timedEvolution b ℏ s)
  (FiniteNontracialCoherentReadout.input X))=_
 rw [timedEvolution,krausMap_composeKraus]
 change ((readout φ).lift Q).branch a
  (swapJoint (timedLiftState b ℏ s (FiniteNontracialCoherentReadout.input X)))=_
 rw [FiniteNontracialCoherentReadout.input,timed_lift_product,swap_tensor,lift_branch_tensor,
  timed_free_correspondence]
 exact (observed_branch _ s (readout φ) a X).symm
theorem timed_empty (b ℏ φ : ℝ) (X : MatQ) :
 timedFamily b ℏ φ [] X=family 0 φ [] X := by
 rw [timed_family_eq]
 simp only [totalPhase,elapsed,mul_zero]
theorem free_zero_dose (θ φ : ℝ) (s : Schedule) (hG : G s=0) (hD : D s=0) (X : MatQ) :
 family θ φ s X=family θ φ [] X := by
 funext h; rcases h with ⟨a,⟨⟩⟩
 change run Q Q 2 (observedTree θ s (readout φ)) (a,()) _=
  run Q Q 2 (observedTree θ [] (readout φ)) (a,()) _
 rw [observed_branch,observed_branch,free_state,free_state,
  (FiniteNontracialSchedule.zero_dose_actions s hG hD X).1,FiniteNontracialSchedule.state_nil]
theorem timed_zero_duration (b ℏ φ : ℝ) (s : Schedule) (hz : ∀ h∈s,h.duration=0) (X : MatQ) :
 timedFamily b ℏ φ s X=family 0 φ [] X := by
 rw [timed_family_eq,all_zero_phase b ℏ s hz]
 exact free_zero_dose _ _ s (FiniteNontracialSchedule.zero_duration_doses s hz).1
  (FiniteNontracialSchedule.zero_duration_doses s hz).2 X
theorem timed_zero_rate (b ℏ φ : ℝ) (s : Schedule) (hz : ∀ h∈s,h.gamma=0 ∧ h.eta=0) (X : MatQ) :
 timedFamily b ℏ φ s X=family (totalPhase b ℏ s) φ [] X := by
 rw [timed_family_eq]
 exact free_zero_dose _ _ s (FiniteNontracialSchedule.zero_rate_doses s hz).1
  (FiniteNontracialSchedule.zero_rate_doses s hz).2 X
theorem positive_finite_retention (s : Schedule) :
 0<alpha s ∧ 0<beta s ∧ beta s≤alpha s ∧ alpha s≤1 :=
 ⟨lt_of_lt_of_le (FiniteNontracialSchedule.coefficients s).1
  (FiniteNontracialSchedule.coefficients s).2.1,FiniteNontracialSchedule.coefficients s⟩
theorem zero_dephasing_phase_actions (θ : ℝ) (s : Schedule) (hD : D s=0) (X : MatQ) :
 freeState θ s X=C θ (NontracialPauliReflection.Phi (alpha s) X) ∧
 freeObservable θ s X=NontracialPauliReflection.Psi (alpha s) (C (-θ) X) := by
 rw [free_state,free_observable,
  (FiniteNontracialMemoryScheduleControls.zero_dephasing_actions s hD X).1,
  (FiniteNontracialMemoryScheduleControls.zero_dephasing_actions s hD (C (-θ) X)).2]
 exact ⟨rfl,rfl⟩
def resetEvolution (θ : ℝ) (s : Schedule) := composeKraus (evolution θ s)
 (FiniteNontracialEnvironmentLift.liftKraus FiniteNontracialEnvironmentLift.gibbsResetKraus)
theorem resetEvolution_normalized (θ : ℝ) (s : Schedule) : IsKrausChannel (resetEvolution θ s) :=
 isKrausChannel_composeKraus (evolution_normalized θ s) FiniteNontracialEnvironmentLift.gibbsReset_normalized
def resetTree (θ φ : ℝ) (s : Schedule) : Tree Q Q 2 1 :=
 .node (realizedStep Q Q 2 (resetEvolution θ s) (resetEvolution_normalized θ s) (readout φ))
  (fun _ => .done)
def resetFamily (θ φ : ℝ) (s : Schedule) (X : MatQ) (h : Hist) : MatJoint :=
 run Q Q 2 (resetTree θ φ s) h (FiniteNontracialCoherentReadout.input X)
theorem reset_family_eq (θ φ : ℝ) (s : Schedule) {X : MatQ} (hX : IsDensityOperator X) :
 resetFamily θ φ s X=family θ φ s rhoN := by
 funext h; rcases h with ⟨a,⟨⟩⟩
 change ((readout φ).lift Q).branch a (krausMap (resetEvolution θ s)
  (FiniteNontracialCoherentReadout.input X))=_
 rw [resetEvolution,krausMap_composeKraus]
 change ((readout φ).lift Q).branch a (krausMap (evolution θ s)
  (FiniteNontracialEnvironmentLift.gibbsReset (FiniteNontracialCoherentReadout.input X)))=_
 rw [FiniteNontracialCoherentReadout.gibbs_reset_preparation hX]
 rfl
theorem reset_equal (θ φ : ℝ) (s : Schedule) :
 resetFamily θ φ s qubitX=resetFamily θ φ s qubitY := by
 rw [reset_family_eq θ φ s qubitX_density,reset_family_eq θ φ s qubitY_density]
def systemEvolution (θ : ℝ) (s : Schedule) :=
 composeKraus (evolution θ s) (tensorKraus resetKraus)
theorem systemEvolution_normalized (θ : ℝ) (s : Schedule) : IsKrausChannel (systemEvolution θ s) :=
 isKrausChannel_composeKraus (evolution_normalized θ s) resetSystem_normalized
def systemTree (θ φ : ℝ) (s : Schedule) : Tree Q Q 2 1 :=
 .node (realizedStep Q Q 2 (systemEvolution θ s) (systemEvolution_normalized θ s) (readout φ))
  (fun _ => .done)
def systemFamily (θ φ : ℝ) (s : Schedule) (X : MatQ) (h : Hist) : MatJoint :=
 run Q Q 2 (systemTree θ φ s) h (FiniteNontracialCoherentReadout.input X)
theorem system_family_eq (θ φ : ℝ) (s : Schedule) (X : MatQ) :
 systemFamily θ φ s X=family θ φ s X := by
 funext h; rcases h with ⟨a,⟨⟩⟩
 change ((readout φ).lift Q).branch a (krausMap (systemEvolution θ s)
  (FiniteNontracialCoherentReadout.input X))=_
 rw [systemEvolution,krausMap_composeKraus]
 change ((readout φ).lift Q).branch a (krausMap (evolution θ s)
  (resetSystem (FiniteNontracialCoherentReadout.input X)))=_
 rw [FiniteNontracialCoherentReadout.system_prepare_input]
 rfl
theorem stationary_same_tree (θ φ : ℝ) (s : Schedule) (E : Hist → MatJoint) :
 readoutError (family θ φ s rhoN) (family θ φ s rhoN) E=1/2 :=
 FiniteNontracialCoherentReadout.readoutError_same (family_valid _ _ _ rhoN_density) E


abbrev DiagonalHistory := History 2 2
def keepStep (θ : ℝ) (s : Schedule) : Step Q Q 2 :=
 realizedStep Q Q 2 (freeLiftKraus θ s) (free_lift_normalized θ s) (FiniteInstrument.prepare 0)
def flipKraus (θ : ℝ) (s : Schedule) := composeKraus (freeLiftKraus θ s) environmentXKraus
theorem flip_normalized (θ : ℝ) (s : Schedule) : IsKrausChannel (flipKraus θ s) :=
 isKrausChannel_composeKraus (free_lift_normalized θ s) environmentX_normalized
def flipStep (θ : ℝ) (s : Schedule) : Step Q Q 2 :=
 realizedStep Q Q 2 (flipKraus θ s) (flip_normalized θ s) (FiniteInstrument.prepare 0)
def keepTree (θ : ℝ) (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (keepStep θ s) (fun _ => .done))
def flipTree (θ : ℝ) (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (flipStep θ s) (fun _ => .done))
def keepFamily (θ : ℝ) (s : Schedule) (h : DiagonalHistory) : MatJoint :=
 run Q Q 2 (keepTree θ s) h correlatedInput
def flipFamily (θ : ℝ) (s : Schedule) (h : DiagonalHistory) : MatJoint :=
 run Q Q 2 (flipTree θ s) h correlatedInput
theorem C_basis (θ : ℝ) (i : Q) : C θ (basisState i)=basisState i := by
 ext a b
 fin_cases i <;> fin_cases a <;> fin_cases b <;> norm_num [C_entry,basisState]
theorem phase_diagonal_schedule (θ : ℝ) (s : Schedule) (i : Q) :
 freeState θ s (basisState i)=FiniteNontracialSchedule.state s (basisState i) := by
 rw [free_state,FiniteNontracialMemoryReadout.basis_state,C_add,C_smul,C_smul,C_rho,C_basis]
theorem keepStep_tensor (θ : ℝ) (s : Schedule) (a c : Q) (B : MatQ) :
 (keepStep θ s).branch Q Q 2 a (basisState c ⊗ₖ B)=
 if a=0 then basisState 0 ⊗ₖ freeState θ s B else 0 := by
 change ((FiniteInstrument.prepare 0).lift Q).branch a
  (krausMap (freeLiftKraus θ s) (basisState c ⊗ₖ B))=_
 rw [free_lift_product,lift_branch_tensor,prepare_basis]
 split_ifs <;> simp_all
theorem flipStep_basis (θ : ℝ) (s : Schedule) (a c e : Q) :
 (flipStep θ s).branch Q Q 2 a (basisState c ⊗ₖ basisState e)=
 if a=0 then basisState 0 ⊗ₖ freeState θ s (basisState (1-e)) else 0 := by
 change ((FiniteInstrument.prepare 0).lift Q).branch a (krausMap (flipKraus θ s) _)=_
 rw [flipKraus,krausMap_composeKraus,environmentX_basis]
 exact keepStep_tensor θ s a c _
theorem diagonal_families_preserved (θ : ℝ) (s : Schedule) :
 keepFamily θ s=FiniteNontracialMemoryReadout.keepFamily s ∧
 flipFamily θ s=FiniteNontracialMemoryReadout.flipFamily s := by
 constructor
 · funext h; rcases h with ⟨i,j,⟨⟩⟩
   change (keepStep θ s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput)=_
   rw [readStep_correlated,Step.branch_smul,keepStep_tensor,phase_diagonal_schedule,
    FiniteNontracialMemoryReadout.keep_run]
   split_ifs <;> simp
 · funext h; rcases h with ⟨i,j,⟨⟩⟩
   change (flipStep θ s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput)=_
   rw [readStep_correlated,Step.branch_smul,flipStep_basis,phase_diagonal_schedule,
    FiniteNontracialMemoryReadout.flip_run]
   split_ifs <;> simp
theorem diagonal_branches (θ : ℝ) (s : Schedule) (i j : Q) :
 keepFamily θ s (i,j,())=(if j=0 then (1/2:ℂ) •
  (basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState i)) else 0) ∧
 flipFamily θ s (i,j,())=(if j=0 then (1/2:ℂ) •
  (basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState (1-i))) else 0) := by
 rw [(diagonal_families_preserved θ s).1,(diagonal_families_preserved θ s).2,
  FiniteNontracialMemoryReadout.keep_run,FiniteNontracialMemoryReadout.flip_run]
 exact ⟨rfl,rfl⟩
theorem diagonal_physical_tables (θ : ℝ) (s : Schedule) (i j b : Q) :
 readoutTable correlationReadout (keepFamily θ s) (i,j,()) b=
 (if j=0 then (if b=0 then (alpha s+(1-alpha s)*NontracialPauliReflection.weights i)/2
  else (1-alpha s)*NontracialPauliReflection.weights (1-i)/2) else 0) ∧
 readoutTable correlationReadout (flipFamily θ s) (i,j,()) b=
 (if j=0 then (if b=0 then (1-alpha s)*NontracialPauliReflection.weights i/2
  else (alpha s+(1-alpha s)*NontracialPauliReflection.weights (1-i))/2) else 0) := by
 rw [(diagonal_families_preserved θ s).1,(diagonal_families_preserved θ s).2]
 exact FiniteNontracialMemoryReadout.physical_table s i j b
theorem diagonal_valid (θ : ℝ) (s : Schedule) :
 IsBranchFamily (keepFamily θ s) ∧ IsBranchFamily (flipFamily θ s) :=
 ⟨run_family _ correlatedInput_density,run_family _ correlatedInput_density⟩
theorem diagonal_laws (θ : ℝ) (s : Schedule) :
 (∀ h a,0≤readoutTable correlationReadout (keepFamily θ s) h a) ∧
 (∑ h,∑ a,readoutTable correlationReadout (keepFamily θ s) h a)=1 ∧
 (∀ h a,0≤readoutTable correlationReadout (flipFamily θ s) h a) ∧
 (∑ h,∑ a,readoutTable correlationReadout (flipFamily θ s) h a)=1 :=
 ⟨readoutTable_nonneg _ (diagonal_valid θ s).1,readoutTable_total _ (diagonal_valid θ s).1,
 readoutTable_nonneg _ (diagonal_valid θ s).2,readoutTable_total _ (diagonal_valid θ s).2⟩

theorem diagonal_distance (θ : ℝ) (s : Schedule) :
 branchDistance (keepFamily θ s) (flipFamily θ s)=alpha s := by
 rw [(diagonal_families_preserved θ s).1,(diagonal_families_preserved θ s).2]
 exact FiniteNontracialMemoryReadout.branch_distance s
theorem diagonal_attainment (θ : ℝ) (s : Schedule) :
 (∀ h,IsBinaryPOVM (correlationEffect h)) ∧
 readoutError (keepFamily θ s) (flipFamily θ s) correlationEffect=(1-alpha s)/2 ∧
 instrumentError (keepFamily θ s) (flipFamily θ s) correlationReadout=(1-alpha s)/2 := by
 rw [(diagonal_families_preserved θ s).1,(diagonal_families_preserved θ s).2]
 exact FiniteNontracialMemoryReadout.physical_attainment s
theorem diagonal_all_effect_isLeast (θ : ℝ) (s : Schedule) :
 IsLeast {x : ℝ | ∃ E : DiagonalHistory → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
 readoutError (keepFamily θ s) (flipFamily θ s) E=x} ((1-alpha s)/2) := by
 rw [(diagonal_families_preserved θ s).1,(diagonal_families_preserved θ s).2]
 exact FiniteNontracialMemoryReadout.all_effect_isLeast s
theorem diagonal_history_isLeast (θ : ℝ) (s : Schedule) :
 IsLeast {x : ℝ | ∃ a : DiagonalHistory → ℝ,(∀ h,0≤a h ∧ a h≤1) ∧
 historyError (keepFamily θ s) (flipFamily θ s) a=x} (1/2) := by
 rw [(diagonal_families_preserved θ s).1,(diagonal_families_preserved θ s).2]
 exact FiniteNontracialMemoryReadout.history_isLeast s
theorem pure_dephasing_controls (θ φ : ℝ) (s : Schedule) (hG : G s=0) (hD : 0<D s) :
 alpha s=1 ∧ beta s<1 ∧
 branchDistance (keepFamily θ s) (flipFamily θ s)=1 ∧
 instrumentError (keepFamily θ s) (flipFamily θ s) correlationReadout=0 ∧
 branchDistance (family θ φ s qubitX) (family θ φ s qubitY)=
 beta s*invSqrtTwo*|Real.cos (θ-φ)| := by
 have hc := FiniteNontracialMemoryScheduleControls.pure_dephasing_pair s hG hD
 refine ⟨hc.1,hc.2.1,?_,?_,observed_distance θ φ s⟩
 · rw [diagonal_distance,hc.1]
 · rw [(diagonal_attainment θ s).2.2,hc.1];norm_num

def fixtureSchedule (dephase : Bool) : Schedule :=
 if dephase then [FiniteNontracialCoherentReadout.dephasingLogTwoSlice]
 else [FiniteNontracialSchedule.logTwoSlice]
def fixtureSeparation (dephase : Bool) : ℝ := if dephase then invSqrtTwo/2 else invSqrtTwo/4
def fixtureAngle (n : Fin 3) : ℝ := if n=0 then 0 else if n=1 then Real.pi/2 else Real.pi
def fixtureMeasurement (n : Fin 3) (covariant : Bool) : ℝ :=
 if covariant then fixtureAngle n else 0
def fixtureMassA (d : ℝ) (n : Fin 3) (covariant : Bool) (i : Q) : ℝ :=
 if covariant then (if i=0 then (1+d)/2 else (1-d)/2)
 else if n=2 then (if i=0 then (1-d)/2 else (1+d)/2)
 else (if i=0 then (1+d)/2 else (1-d)/2)
def fixtureMassB (d : ℝ) (n : Fin 3) (covariant : Bool) (i : Q) : ℝ :=
 if covariant then (if i=0 then (1-d)/2 else (1+d)/2)
 else if n=0 then (if i=0 then (1-d)/2 else (1+d)/2)
 else (if i=0 then (1+d)/2 else (1-d)/2)
theorem fixture_coefficients (dephase : Bool) :
 alpha (fixtureSchedule dephase)=(if dephase then 1 else 1/2) ∧
 beta (fixtureSchedule dephase)*invSqrtTwo=fixtureSeparation dephase := by
 cases dephase <;>
 norm_num [fixtureSchedule,fixtureSeparation,FiniteNontracialSchedule.logTwo_coefficients,
  FiniteNontracialCoherentReadout.dephasingLogTwo_coefficients] <;> ring
theorem fixture_probabilities (dephase covariant : Bool) (n : Fin 3) (i : Q) :
 probabilityA (fixtureAngle n-fixtureMeasurement n covariant) (fixtureSchedule dephase) i=
 fixtureMassA (fixtureSeparation dephase) n covariant i ∧
 probabilityB (fixtureAngle n-fixtureMeasurement n covariant) (fixtureSchedule dephase) i=
 fixtureMassB (fixtureSeparation dephase) n covariant i := by
 cases covariant <;> fin_cases n <;> fin_cases i <;>
 norm_num [fixtureAngle,fixtureMeasurement,fixtureMassA,fixtureMassB,probabilityA,probabilityB,
  (fixture_coefficients dephase).2,Fin.ext_iff] <;> ring
theorem fixture_full_tables (dephase covariant rev : Bool) (n : Fin 3) (h : Hist) (a : Q) :
 readoutTable (decisionReadout rev)
 (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitX) h a=
 (if a=decisionLabel rev h then fixtureMassA (fixtureSeparation dephase) n covariant h.1 else 0) ∧
 readoutTable (decisionReadout rev)
 (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitY) h a=
 (if a=decisionLabel rev h then fixtureMassB (fixtureSeparation dephase) n covariant h.1 else 0) := by
 rw [readoutTableA,readoutTableB,(fixture_probabilities dephase covariant n h.1).1,
 (fixture_probabilities dephase covariant n h.1).2]
 exact ⟨rfl,rfl⟩
def fixtureCosine (n : Fin 3) (covariant : Bool) : ℝ := if covariant then 1 else if n=0 then 1 else if n=1 then 0 else -1
theorem fixture_cosine (n : Fin 3) (covariant : Bool) :
 Real.cos (fixtureAngle n-fixtureMeasurement n covariant)=fixtureCosine n covariant := by
 cases covariant <;> fin_cases n <;> norm_num [fixtureAngle,fixtureMeasurement,fixtureCosine]
theorem fixture_named_rules (dephase covariant rev : Bool) (n : Fin 3) :
 instrumentError (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitX)
 (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitY)
 (decisionReadout rev)=
 (if rev then (1+fixtureSeparation dephase*fixtureCosine n covariant)/2
 else (1-fixtureSeparation dephase*fixtureCosine n covariant)/2) := by
 rw [decision_attains,fixture_cosine,(fixture_coefficients dephase).2]
theorem fixture_all_effect_optimum (dephase covariant : Bool) (n : Fin 3) :
 IsLeast {x : ℝ | ∃ E : Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
 readoutError (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitX)
 (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitY) E=x}
 ((1-fixtureSeparation dephase*|fixtureCosine n covariant|)/2) := by
 simpa only [fixture_cosine,(fixture_coefficients dephase).2] using
 all_effect_isLeast (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase)
theorem fixture_history_optimum (dephase covariant : Bool) (n : Fin 3) :
 IsLeast {x : ℝ | ∃ a : Hist → ℝ,(∀ h,a h∈Set.Icc (0:ℝ) 1) ∧
 historyError (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitX)
 (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitY) a=x}
 ((1-fixtureSeparation dephase*|fixtureCosine n covariant|)/2) := by
 simpa only [fixture_cosine,(fixture_coefficients dephase).2] using
 randomized_isLeast (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase)

def witnessTime : ℝ := Real.pi/(2*delta)
def witnessRate : ℝ := 2*delta*Real.log 2/Real.pi
theorem witness_positive : 0<delta ∧ 0<Real.pi ∧ 0<Real.log 2 ∧ 0<witnessTime ∧ 0<witnessRate := by
 have hd := delta_pos
 have hp := Real.pi_pos
 have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
 exact ⟨hd,hp,hl,div_pos hp (mul_pos (by norm_num) hd),
 div_pos (mul_pos (mul_pos (by norm_num) hd) hl) hp⟩
def witnessSlice : Slice := ⟨witnessRate,witnessRate,witnessTime,
 witness_positive.2.2.2.2.le,witness_positive.2.2.2.2.le,witness_positive.2.2.2.1.le⟩
theorem witness_dose : witnessRate*witnessTime=Real.log 2 := by
 unfold witnessRate witnessTime
 field_simp [ne_of_gt delta_pos,ne_of_gt Real.pi_pos]
theorem witness_parameters :
 phase 1 1 witnessTime=Real.pi/2 ∧ totalPhase 1 1 [witnessSlice]=Real.pi/2 ∧
 G [witnessSlice]=Real.log 2 ∧ D [witnessSlice]=Real.log 2 ∧
 alpha [witnessSlice]=1/2 ∧ beta [witnessSlice]=1/4 := by
 have ht : phase 1 1 witnessTime=Real.pi/2 := by
  unfold phase frequency gap witnessTime
  field_simp [ne_of_gt delta_pos]
 have hG : G [witnessSlice]=Real.log 2 := by
  simpa only [FiniteNontracialSchedule.G,witnessSlice,add_zero] using witness_dose
 have hD : D [witnessSlice]=Real.log 2 := by
  simpa only [FiniteNontracialSchedule.D,witnessSlice,add_zero] using witness_dose
 refine ⟨ht,?_,hG,hD,?_,?_⟩
 · simpa only [totalPhase,elapsed,witnessSlice,add_zero,phase] using ht
 · norm_num [FiniteNontracialSchedule.alpha,hG,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
 · rw [FiniteNontracialSchedule.beta,hG,hD,neg_add,Real.exp_add]
   norm_num [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
theorem witness_primitive_normalized :
 IsKrausChannel (thermalKraus 1 1 witnessRate witnessRate witnessTime) :=
 normalized 1 1 _ _ _ witness_positive.2.2.2.2.le witness_positive.2.2.2.2.le witness_positive.2.2.2.1.le
theorem witness_nonzero_H : scaledH 1 1≠0 := scaledH_nonzero (by norm_num) (by norm_num)
theorem witness_actual_GKSL (X : MatQ) :
 timedState 1 1 [witnessSlice] X=
 OpenSystems.lindbladPropagatorAction (scaledH 1 1) (jumps witnessRate witnessRate) witnessTime X := by
 rw [timed_cons,timed_nil]
 exact state_eq_propagator 1 1 _ _ _ witness_positive.2.2.2.2.le
  witness_positive.2.2.2.2.le witness_positive.2.2.2.1.le X
theorem witness_noise_action (X : MatQ) :
 FiniteNontracialSchedule.state [witnessSlice] X=
 FiniteNontracialSchedule.state [FiniteNontracialSchedule.logTwoSlice] X := by
 rw [FiniteNontracialSchedule.state_formula,FiniteNontracialSchedule.state_formula]
 simp only [FiniteNontracialSchedule.stateForm,witness_parameters.2.2.2.2.1,
 witness_parameters.2.2.2.2.2,FiniteNontracialSchedule.logTwo_coefficients.1,
 FiniteNontracialSchedule.logTwo_coefficients.2]
theorem witness_actual_families (φ : ℝ) (X : MatQ) :
 timedFamily 1 1 φ [witnessSlice] X=
 family (Real.pi/2) φ [FiniteNontracialSchedule.logTwoSlice] X := by
 rw [timed_family_eq,witness_parameters.2.1]
 funext h;rcases h with ⟨a,⟨⟩⟩
 unfold family
 rw [observed_branch,observed_branch,free_state,free_state,witness_noise_action]
theorem witness_complete_tables (covariant rev : Bool) (h : Hist) (a : Q) :
 readoutTable (decisionReadout rev)
 (timedFamily 1 1 (fixtureMeasurement 1 covariant) [witnessSlice] qubitX) h a=
 (if a=decisionLabel rev h then fixtureMassA (invSqrtTwo/4) 1 covariant h.1 else 0) ∧
 readoutTable (decisionReadout rev)
 (timedFamily 1 1 (fixtureMeasurement 1 covariant) [witnessSlice] qubitY) h a=
 (if a=decisionLabel rev h then fixtureMassB (invSqrtTwo/4) 1 covariant h.1 else 0) := by
 rw [witness_actual_families,witness_actual_families]
 simpa only [fixtureSchedule,fixtureSeparation,fixtureAngle,Bool.false_eq_true,if_false,if_true,show (1:Fin 3)≠0 by decide]
 using fixture_full_tables false covariant rev 1 h a
theorem witness_named_rules (covariant rev : Bool) :
 instrumentError (timedFamily 1 1 (fixtureMeasurement 1 covariant) [witnessSlice] qubitX)
 (timedFamily 1 1 (fixtureMeasurement 1 covariant) [witnessSlice] qubitY) (decisionReadout rev)=
 (if covariant then (if rev then (1+invSqrtTwo/4)/2 else (1-invSqrtTwo/4)/2) else 1/2) := by
 rw [witness_actual_families,witness_actual_families]
 have h := fixture_named_rules false covariant rev 1
 cases covariant <;> cases rev <;> simpa [fixtureSchedule,fixtureSeparation,fixtureAngle,fixtureMeasurement,fixtureCosine] using h
theorem witness_effect_optimum (covariant : Bool) :
 IsLeast {x : ℝ | ∃ E : Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
 readoutError (timedFamily 1 1 (fixtureMeasurement 1 covariant) [witnessSlice] qubitX)
 (timedFamily 1 1 (fixtureMeasurement 1 covariant) [witnessSlice] qubitY) E=x}
 (if covariant then (1-invSqrtTwo/4)/2 else 1/2) := by
 rw [witness_actual_families,witness_actual_families]
 have h := fixture_all_effect_optimum false covariant 1
 cases covariant <;> simpa [fixtureSchedule,fixtureSeparation,fixtureAngle,fixtureMeasurement,fixtureCosine] using h
theorem witness_history_optimum (covariant : Bool) :
 IsLeast {x : ℝ | ∃ a : Hist → ℝ,(∀ h,a h∈Set.Icc (0:ℝ) 1) ∧
 historyError (timedFamily 1 1 (fixtureMeasurement 1 covariant) [witnessSlice] qubitX)
 (timedFamily 1 1 (fixtureMeasurement 1 covariant) [witnessSlice] qubitY) a=x}
 (if covariant then (1-invSqrtTwo/4)/2 else 1/2) := by
 rw [witness_actual_families,witness_actual_families]
 have h := fixture_history_optimum false covariant 1
 cases covariant <;> simpa [fixtureSchedule,fixtureSeparation,fixtureAngle,fixtureMeasurement,fixtureCosine] using h

def diagonalResetKeepKraus (θ : ℝ) (s : Schedule) :=
 composeKraus (FiniteNontracialEnvironmentLift.liftKraus FiniteNontracialEnvironmentLift.gibbsResetKraus)
  (freeLiftKraus θ s)
def diagonalResetFlipKraus (θ : ℝ) (s : Schedule) :=
 composeKraus (FiniteNontracialEnvironmentLift.liftKraus FiniteNontracialEnvironmentLift.gibbsResetKraus)
  (flipKraus θ s)
theorem diagonalResetKeep_normalized (θ : ℝ) (s : Schedule) : IsKrausChannel (diagonalResetKeepKraus θ s) :=
 isKrausChannel_composeKraus FiniteNontracialEnvironmentLift.gibbsReset_normalized (free_lift_normalized θ s)
theorem diagonalResetFlip_normalized (θ : ℝ) (s : Schedule) : IsKrausChannel (diagonalResetFlipKraus θ s) :=
 isKrausChannel_composeKraus FiniteNontracialEnvironmentLift.gibbsReset_normalized (flip_normalized θ s)
def diagonalResetKeepStep (θ : ℝ) (s : Schedule) : Step Q Q 2 :=
 realizedStep Q Q 2 (diagonalResetKeepKraus θ s) (diagonalResetKeep_normalized θ s) (FiniteInstrument.prepare 0)
def diagonalResetFlipStep (θ : ℝ) (s : Schedule) : Step Q Q 2 :=
 realizedStep Q Q 2 (diagonalResetFlipKraus θ s) (diagonalResetFlip_normalized θ s) (FiniteInstrument.prepare 0)
def diagonalResetKeepTree (θ : ℝ) (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (diagonalResetKeepStep θ s) (fun _ => .done))
def diagonalResetFlipTree (θ : ℝ) (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (diagonalResetFlipStep θ s) (fun _ => .done))
def diagonalResetKeepFamily (θ : ℝ) (s : Schedule) (h : DiagonalHistory) :=
 run Q Q 2 (diagonalResetKeepTree θ s) h correlatedInput
def diagonalResetFlipFamily (θ : ℝ) (s : Schedule) (h : DiagonalHistory) :=
 run Q Q 2 (diagonalResetFlipTree θ s) h correlatedInput
theorem reset_after_phase_tensor (θ : ℝ) (s : Schedule) (i e : Q) :
 krausMap (diagonalResetKeepKraus θ s) (basisState i ⊗ₖ basisState e)=basisState i ⊗ₖ rhoN := by
 rw [diagonalResetKeepKraus,krausMap_composeKraus,free_lift_product]
 change FiniteNontracialEnvironmentLift.gibbsReset (basisState i ⊗ₖ freeState θ s (basisState e))=_
 rw [FiniteNontracialEnvironmentLift.gibbsReset_eq,
 FiniteNontracialEnvironmentLift.ptrace2_kronecker,free_state,C_trace,FiniteNontracialSchedule.state_trace,(basisState_density e).2,one_smul]
theorem diagonalResetKeep_tensor (θ : ℝ) (s : Schedule) (i j : Q) :
 (diagonalResetKeepStep θ s).branch Q Q 2 j (basisState i ⊗ₖ basisState i)=
 if j=0 then basisState 0 ⊗ₖ rhoN else 0 := by
 change ((FiniteInstrument.prepare 0).lift Q).branch j
  (krausMap (diagonalResetKeepKraus θ s) _)=_
 rw [reset_after_phase_tensor,lift_branch_tensor,prepare_basis]
 split_ifs <;> simp_all
theorem diagonalResetFlip_tensor (θ : ℝ) (s : Schedule) (i j : Q) :
 (diagonalResetFlipStep θ s).branch Q Q 2 j (basisState i ⊗ₖ basisState i)=
 if j=0 then basisState 0 ⊗ₖ rhoN else 0 := by
 change ((FiniteInstrument.prepare 0).lift Q).branch j
  (krausMap (diagonalResetFlipKraus θ s) _)=_
 rw [diagonalResetFlipKraus,krausMap_composeKraus,flipKraus,krausMap_composeKraus,environmentX_basis]
 have hm := reset_after_phase_tensor θ s i (1-i)
 rw [diagonalResetKeepKraus,krausMap_composeKraus] at hm
 rw [hm,lift_branch_tensor,prepare_basis]
 split_ifs <;> simp_all
theorem diagonal_reset_families (θ : ℝ) (s : Schedule) :
 diagonalResetKeepFamily θ s=FiniteNontracialMemoryScheduleControls.resetKeepFamily s ∧
 diagonalResetFlipFamily θ s=FiniteNontracialMemoryScheduleControls.resetFlipFamily s := by
 constructor <;> funext h <;> rcases h with ⟨i,j,⟨⟩⟩
 · change (diagonalResetKeepStep θ s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput)=_
   rw [readStep_correlated,Step.branch_smul,diagonalResetKeep_tensor,
   (FiniteNontracialMemoryScheduleControls.reset_branches s i j).1]
   split_ifs <;> simp
 · change (diagonalResetFlipStep θ s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput)=_
   rw [readStep_correlated,Step.branch_smul,diagonalResetFlip_tensor,
   (FiniteNontracialMemoryScheduleControls.reset_branches s i j).2]
   split_ifs <;> simp
theorem diagonal_reset_erases (θ : ℝ) (s : Schedule) :
 diagonalResetKeepFamily θ s=diagonalResetFlipFamily θ s := by
 rw [(diagonal_reset_families θ s).1,(diagonal_reset_families θ s).2]
 exact FiniteNontracialMemoryScheduleControls.reset_families_equal s
theorem diagonal_reset_full_tables (θ : ℝ) (s : Schedule) (i j b : Q) :
 readoutTable correlationReadout (diagonalResetKeepFamily θ s) (i,j,()) b=
 (if j=0 then (if b=0 then NontracialPauliReflection.weights i/2 else NontracialPauliReflection.weights (1-i)/2) else 0) ∧
 readoutTable correlationReadout (diagonalResetFlipFamily θ s) (i,j,()) b=
 (if j=0 then (if b=0 then NontracialPauliReflection.weights i/2 else NontracialPauliReflection.weights (1-i)/2) else 0) := by
 rw [(diagonal_reset_families θ s).1,(diagonal_reset_families θ s).2]
 exact FiniteNontracialMemoryScheduleControls.reset_tables s i j b
def diagonalSystemKeepKraus (θ : ℝ) (s : Schedule) := composeKraus (freeLiftKraus θ s) (tensorKraus resetKraus)
def diagonalSystemFlipKraus (θ : ℝ) (s : Schedule) := composeKraus (flipKraus θ s) (tensorKraus resetKraus)
theorem diagonalSystemKeep_normalized (θ : ℝ) (s : Schedule) : IsKrausChannel (diagonalSystemKeepKraus θ s) :=
 isKrausChannel_composeKraus (free_lift_normalized θ s) resetSystem_normalized
theorem diagonalSystemFlip_normalized (θ : ℝ) (s : Schedule) : IsKrausChannel (diagonalSystemFlipKraus θ s) :=
 isKrausChannel_composeKraus (flip_normalized θ s) resetSystem_normalized
def diagonalSystemKeepStep (θ : ℝ) (s : Schedule) : Step Q Q 2 :=
 realizedStep Q Q 2 (diagonalSystemKeepKraus θ s) (diagonalSystemKeep_normalized θ s) (FiniteInstrument.prepare 0)
def diagonalSystemFlipStep (θ : ℝ) (s : Schedule) : Step Q Q 2 :=
 realizedStep Q Q 2 (diagonalSystemFlipKraus θ s) (diagonalSystemFlip_normalized θ s) (FiniteInstrument.prepare 0)
def diagonalSystemKeepTree (θ : ℝ) (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (diagonalSystemKeepStep θ s) (fun _ => .done))
def diagonalSystemFlipTree (θ : ℝ) (s : Schedule) : Tree Q Q 2 2 :=
 .node readStep (fun _ => .node (diagonalSystemFlipStep θ s) (fun _ => .done))
def diagonalSystemKeepFamily (θ : ℝ) (s : Schedule) (h : DiagonalHistory) :=
 run Q Q 2 (diagonalSystemKeepTree θ s) h correlatedInput
def diagonalSystemFlipFamily (θ : ℝ) (s : Schedule) (h : DiagonalHistory) :=
 run Q Q 2 (diagonalSystemFlipTree θ s) h correlatedInput
theorem diagonalSystemKeep_tensor (θ : ℝ) (s : Schedule) (i j : Q) :
 (diagonalSystemKeepStep θ s).branch Q Q 2 j (basisState i ⊗ₖ basisState i)=
 if j=0 then basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState i) else 0 := by
 change ((FiniteInstrument.prepare 0).lift Q).branch j (krausMap (diagonalSystemKeepKraus θ s) _)=_
 rw [diagonalSystemKeepKraus,krausMap_composeKraus]
 change (keepStep θ s).branch Q Q 2 j (resetSystem (basisState i ⊗ₖ basisState i))=_
 rw [resetSystem_basis,keepStep_tensor,phase_diagonal_schedule]
theorem diagonalSystemFlip_tensor (θ : ℝ) (s : Schedule) (i j : Q) :
 (diagonalSystemFlipStep θ s).branch Q Q 2 j (basisState i ⊗ₖ basisState i)=
 if j=0 then basisState 0 ⊗ₖ FiniteNontracialSchedule.state s (basisState (1-i)) else 0 := by
 change ((FiniteInstrument.prepare 0).lift Q).branch j (krausMap (diagonalSystemFlipKraus θ s) _)=_
 rw [diagonalSystemFlipKraus,krausMap_composeKraus]
 change (flipStep θ s).branch Q Q 2 j (resetSystem (basisState i ⊗ₖ basisState i))=_
 rw [resetSystem_basis,flipStep_basis,phase_diagonal_schedule]
theorem diagonal_system_families (θ : ℝ) (s : Schedule) :
 diagonalSystemKeepFamily θ s=keepFamily θ s ∧ diagonalSystemFlipFamily θ s=flipFamily θ s := by
 constructor <;> funext h <;> rcases h with ⟨i,j,⟨⟩⟩
 · change (diagonalSystemKeepStep θ s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput)=_
   rw [readStep_correlated,Step.branch_smul,diagonalSystemKeep_tensor,(diagonal_branches θ s i j).1]
   split_ifs <;> simp
 · change (diagonalSystemFlipStep θ s).branch Q Q 2 j (readStep.branch Q Q 2 i correlatedInput)=_
   rw [readStep_correlated,Step.branch_smul,diagonalSystemFlip_tensor,(diagonal_branches θ s i j).2]
   split_ifs <;> simp

theorem computational_laws_equal (θ : ℝ) (s : Schedule) (I : Hist → FiniteInstrument (Q×Q) 2) :
 readoutTable I (erasureFamily θ s qubitX)=readoutTable I (erasureFamily θ s qubitY) := by
 rw [computational_erasure]
theorem quarter_optima (s : Schedule) :
 IsLeast {x : ℝ | ∃ E : Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
 readoutError (family (Real.pi/2) 0 s qubitX) (family (Real.pi/2) 0 s qubitY) E=x} (1/2) ∧
 IsLeast {x : ℝ | ∃ a : Hist → ℝ,(∀ h,a h∈Set.Icc (0:ℝ) 1) ∧
 historyError (family (Real.pi/2) 0 s qubitX) (family (Real.pi/2) 0 s qubitY) a=x} (1/2) := by
 constructor
 · simpa using all_effect_isLeast (Real.pi/2) 0 s
 · simpa using randomized_isLeast (Real.pi/2) 0 s
theorem covariant_optima (θ : ℝ) (s : Schedule) :
 IsLeast {x : ℝ | ∃ E : Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
 readoutError (family θ θ s qubitX) (family θ θ s qubitY) E=x} ((1-beta s*invSqrtTwo)/2) ∧
 IsLeast {x : ℝ | ∃ a : Hist → ℝ,(∀ h,a h∈Set.Icc (0:ℝ) 1) ∧
 historyError (family θ θ s qubitX) (family θ θ s qubitY) a=x} ((1-beta s*invSqrtTwo)/2) := by
 constructor
 · simpa using all_effect_isLeast θ θ s
 · simpa using randomized_isLeast θ θ s
theorem reset_valid (θ φ : ℝ) (s : Schedule) {X : MatQ} (hX : IsDensityOperator X) :
 IsBranchFamily (resetFamily θ φ s X) := by
 rw [reset_family_eq θ φ s hX];exact family_valid _ _ _ rhoN_density
theorem reset_every_effect (θ φ : ℝ) (s : Schedule) (E : Hist → MatJoint) :
 readoutError (resetFamily θ φ s qubitX) (resetFamily θ φ s qubitY) E=1/2 := by
 rw [reset_equal]
 exact FiniteNontracialCoherentReadout.readoutError_same (reset_valid _ _ _ qubitY_density) E
theorem reset_every_instrument (θ φ : ℝ) (s : Schedule) (I : Hist → FiniteInstrument (Q×Q) 2) :
 instrumentError (resetFamily θ φ s qubitX) (resetFamily θ φ s qubitY) I=1/2 := by
 rw [reset_equal]
 exact FiniteNontracialCoherentReadout.instrumentError_same (reset_valid _ _ _ qubitY_density) I
theorem reset_every_history (θ φ : ℝ) (s : Schedule) (a : Hist → ℝ) :
 historyError (resetFamily θ φ s qubitX) (resetFamily θ φ s qubitY) a=1/2 := by
 rw [←historyError_scalar_effect,reset_every_effect]
theorem reset_effect_optimum (θ φ : ℝ) (s : Schedule) :
 IsLeast {x : ℝ | ∃ E : Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
 readoutError (resetFamily θ φ s qubitX) (resetFamily θ φ s qubitY) E=x} (1/2) := by
 constructor
 · exact ⟨decisionProjection false,decisionProjection_admissible false,reset_every_effect θ φ s _⟩
 · rintro x ⟨E,_,rfl⟩;rw [reset_every_effect]
theorem reset_history_optimum (θ φ : ℝ) (s : Schedule) :
 IsLeast {x : ℝ | ∃ a : Hist → ℝ,(∀ h,a h∈Set.Icc (0:ℝ) 1) ∧
 historyError (resetFamily θ φ s qubitX) (resetFamily θ φ s qubitY) a=x} (1/2) := by
 constructor
 · exact ⟨decisionScore false,decisionScore_admissible false,reset_every_history θ φ s _⟩
 · rintro x ⟨a,_,rfl⟩;rw [reset_every_history]
theorem reset_physical_laws (θ φ : ℝ) (s : Schedule) (I : Hist → FiniteInstrument (Q×Q) 2) :
 (∀ h a,0≤readoutTable I (resetFamily θ φ s qubitX) h a) ∧
 (∑ h,∑ a,readoutTable I (resetFamily θ φ s qubitX) h a)=1 ∧
 (∀ h a,0≤readoutTable I (resetFamily θ φ s qubitY) h a) ∧
 (∑ h,∑ a,readoutTable I (resetFamily θ φ s qubitY) h a)=1 :=
 ⟨readoutTable_nonneg I (reset_valid _ _ _ qubitX_density),readoutTable_total I (reset_valid _ _ _ qubitX_density),
 readoutTable_nonneg I (reset_valid _ _ _ qubitY_density),readoutTable_total I (reset_valid _ _ _ qubitY_density)⟩
theorem diagonal_reset_laws (θ : ℝ) (s : Schedule) :
 (∀ h a,0≤readoutTable correlationReadout (diagonalResetKeepFamily θ s) h a) ∧
 (∑ h,∑ a,readoutTable correlationReadout (diagonalResetKeepFamily θ s) h a)=1 ∧
 (∀ h a,0≤readoutTable correlationReadout (diagonalResetFlipFamily θ s) h a) ∧
 (∑ h,∑ a,readoutTable correlationReadout (diagonalResetFlipFamily θ s) h a)=1 := by
 rw [(diagonal_reset_families θ s).1,(diagonal_reset_families θ s).2]
 exact FiniteNontracialMemoryScheduleControls.reset_laws s
theorem diagonal_reset_optimum (θ : ℝ) (s : Schedule) :
 IsLeast {x : ℝ | ∃ E : DiagonalHistory → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
 readoutError (diagonalResetKeepFamily θ s) (diagonalResetFlipFamily θ s) E=x} (1/2) := by
 rw [(diagonal_reset_families θ s).1,(diagonal_reset_families θ s).2]
 exact FiniteNontracialMemoryScheduleControls.reset_all_effect_isLeast s
theorem diagonal_reset_every_history (θ : ℝ) (s : Schedule) (a : DiagonalHistory → ℝ) :
 historyError (diagonalResetKeepFamily θ s) (diagonalResetFlipFamily θ s) a=1/2 := by
 rw [(diagonal_reset_families θ s).1,(diagonal_reset_families θ s).2]
 exact FiniteNontracialMemoryScheduleControls.reset_every_history s a
theorem diagonal_system_tables (θ : ℝ) (s : Schedule) :
 readoutTable correlationReadout (diagonalSystemKeepFamily θ s)=readoutTable correlationReadout (keepFamily θ s) ∧
 readoutTable correlationReadout (diagonalSystemFlipFamily θ s)=readoutTable correlationReadout (flipFamily θ s) := by
 rw [(diagonal_system_families θ s).1,(diagonal_system_families θ s).2];exact ⟨rfl,rfl⟩
theorem diagonal_finite_not_reset (θ : ℝ) (s : Schedule) : keepFamily θ s≠flipFamily θ s := by
 intro h
 have hd := diagonal_distance θ s
 rw [h,branchDistance_self] at hd
 have ha : 0<alpha s := Real.exp_pos _
 linarith
theorem diagonal_numeric_tables (θ : ℝ) (i j b : Q) :
 readoutTable correlationReadout (keepFamily θ [FiniteNontracialSchedule.logTwoSlice]) (i,j,()) b=
 (if j=0 then FiniteNontracialMemoryScheduleControls.logTwoKeep i b else 0) ∧
 readoutTable correlationReadout (flipFamily θ [FiniteNontracialSchedule.logTwoSlice]) (i,j,()) b=
 (if j=0 then FiniteNontracialMemoryScheduleControls.logTwoFlip i b else 0) := by
 rw [(diagonal_families_preserved θ _).1,(diagonal_families_preserved θ _).2]
 exact FiniteNontracialMemoryScheduleControls.logTwo_diagonal_tables i j b
theorem diagonal_dephasing_tables (θ : ℝ) (i j b : Q) :
 readoutTable correlationReadout (keepFamily θ [FiniteNontracialCoherentReadout.dephasingLogTwoSlice]) (i,j,()) b=
 (if j=0 ∧ b=0 then 1/2 else 0) ∧
 readoutTable correlationReadout (flipFamily θ [FiniteNontracialCoherentReadout.dephasingLogTwoSlice]) (i,j,()) b=
 (if j=0 ∧ b=1 then 1/2 else 0) := by
 rw [(diagonal_families_preserved θ _).1,(diagonal_families_preserved θ _).2]
 exact FiniteNontracialMemoryScheduleControls.dephasingLogTwo_diagonal_tables i j b
theorem stationary_physical_error (θ φ : ℝ) (s : Schedule) (I : Hist → FiniteInstrument (Q×Q) 2) :
 instrumentError (family θ φ s rhoN) (family θ φ s rhoN) I=1/2 :=
 FiniteNontracialCoherentReadout.instrumentError_same (family_valid _ _ _ rhoN_density) I
theorem stationary_history_error (θ φ : ℝ) (s : Schedule) (a : Hist → ℝ) :
 historyError (family θ φ s rhoN) (family θ φ s rhoN) a=1/2 := by
 rw [←historyError_scalar_effect,stationary_same_tree]
theorem imaginary_free_state (θ : ℝ) (s : Schedule) :
 freeState θ s (Complex.I • FiniteGibbsClock.E01)=
 ((beta s:ℂ)*Complex.exp (Complex.I*θ)) • (Complex.I • FiniteGibbsClock.E01) := by
 rw [free_state,iE01_eq_imaginary,FiniteNontracialMemoryScheduleControls.imaginary_state,
 ←iE01_eq_imaginary,C_smul,C_smul,C_E01]
 module
theorem imaginary_free_observable (θ : ℝ) (s : Schedule) :
 freeObservable θ s (Complex.I • FiniteGibbsClock.E01)=
 ((beta s:ℂ)*Complex.exp (-Complex.I*θ)) • (Complex.I • FiniteGibbsClock.E01) := by
 rw [free_observable,C_smul,C_E01]
 have hs (z : ℂ) (A : MatQ) : FiniteNontracialSchedule.observable s (z • A)=
 z • FiniteNontracialSchedule.observable s A := by
  simp [FiniteNontracialSchedule.observable,Channel.heisenberg,Finset.smul_sum]
 have he := FiniteNontracialMemoryScheduleControls.imaginary_observable s
 rw [←iE01_eq_imaginary,hs] at he
 rw [hs,hs]
 rw [smul_comm,he]
 simp only [Complex.ofReal_neg,mul_neg,neg_mul,smul_smul]
 ring_nf
theorem imaginary_guard :
 ¬(Complex.I • FiniteGibbsClock.E01).IsHermitian ∧
 ¬(Complex.I • FiniteGibbsClock.E01).PosSemidef ∧
 ¬IsDensityOperator (Complex.I • FiniteGibbsClock.E01) :=
 ⟨iE01_not_hermitian,iE01_not_posSemidef,iE01_not_density⟩
theorem imaginary_full_effect_duality (θ : ℝ) (s : Schedule) (A : MatQ) :
 (A*freeState θ s (Complex.I • FiniteGibbsClock.E01)).trace=
 (freeObservable θ s A*(Complex.I • FiniteGibbsClock.E01)).trace := by
 rw [freeState,freeObservable,Matrix.trace_mul_comm,←Channel.trace_duality,Matrix.trace_mul_comm]
theorem imaginary_GKSL_control (b ℏ γ η t : ℝ) (hγ : 0≤γ) (hη : 0≤η) (ht : 0≤t) :
 state b ℏ γ η t (Complex.I • FiniteGibbsClock.E01)=
 OpenSystems.lindbladPropagatorAction (scaledH b ℏ) (jumps γ η) t (Complex.I • FiniteGibbsClock.E01) ∧
 state b ℏ γ η t (Complex.I • FiniteGibbsClock.E01)=
 ((Real.exp (-(γ+η)*t):ℂ)*Complex.exp (Complex.I*phase b ℏ t)) • (Complex.I • FiniteGibbsClock.E01) ∧
 observable b ℏ γ η t (Complex.I • FiniteGibbsClock.E01)=
 ((Real.exp (-(γ+η)*t):ℂ)*Complex.exp (-Complex.I*phase b ℏ t)) • (Complex.I • FiniteGibbsClock.E01) :=
 ⟨state_eq_propagator b ℏ γ η t hγ hη ht _,state_iE01 b ℏ γ η t hγ hη ht,
 observable_iE01 b ℏ γ η t hγ hη ht⟩
theorem reflection_zero_controls (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (a : Fin 3) :
 SKEFTHawking.FinitePositiveKernel.mk
 (NontracialPauliReflection.kernel 0 r (by norm_num) (by norm_num) hr hr1)
 (NontracialPauliReflection.kernel_posSemidef 0 r (by norm_num) (by norm_num) hr hr1)
 (NontracialPauliReflection.innerMode a)=0 :=
 NontracialPauliReflection.reset_modes_null r hr hr1 a
def sideNullScore (u : NontracialPauliReflection.HalfHistory) : ℂ :=
 (if u=(0,0) then 1 else 0)-(if u=(0,1) then 1 else 0)
theorem side_null_halfEffect :
 NontracialPauliReflection.halfEffect 0 (0,0)=NontracialPauliReflection.halfEffect 0 (0,1) := by
 rw [NontracialPauliReflection.side_reset_halfEffect,NontracialPauliReflection.side_reset_halfEffect]
 ext i j;fin_cases i <;> fin_cases j <;>
 norm_num [PauliInstrumentReconstruction.effect,PauliInstrumentReconstruction.projector,
 PauliInstrumentReconstruction.sign,PauliInstrumentReconstruction.outcomeEquiv,finProdFinEquiv,
 Fin.divNat,Fin.modNat,PauliInstrumentReconstruction.sigma,pauliX,rhoN,Matrix.trace,
 Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.one_apply]
theorem side_null_synthesis (p : ℝ) : NontracialPauliReflection.synthesis p 0 sideNullScore=0 := by
 simp only [NontracialPauliReflection.synthesis,sideNullScore,sub_smul,Finset.sum_sub_distrib]
 simp only [ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
 rw [NontracialPauliReflection.midpoint,NontracialPauliReflection.midpoint,side_null_halfEffect,sub_self]
theorem side_null_quotient (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
 SKEFTHawking.FinitePositiveKernel.mk
 (NontracialPauliReflection.kernel p 0 hp hp1 (by norm_num) (by norm_num))
 (NontracialPauliReflection.kernel_posSemidef p 0 hp hp1 (by norm_num) (by norm_num)) sideNullScore=0 :=
 (NontracialPauliReflection.null_iff p 0 hp hp1 (by norm_num) (by norm_num) sideNullScore).2 (side_null_synthesis p)

theorem stationary_projection_trace (φ : ℝ) (a : Q) :
 (readProjection φ a*rhoN).trace=(1/2:ℂ) := by
 rw [readProjection,←C_rho φ,←C_mul,C_trace]
 fin_cases a <;>
 norm_num [FiniteNontracialCoherentReadout.readProjection,qubitProjector,qubitDirection,
 rhoN,pauliX,pauliY,Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,
 Matrix.one_apply]
theorem stationary_coherent_branches (θ φ : ℝ) (s : Schedule) (a : Q) :
 family θ φ s rhoN (a,())=(1/2:ℂ) • (readProjection φ a ⊗ₖ basisState 0) := by
 rw [family,observed_branch,free_state,FiniteNontracialSchedule.state_stationary,C_rho,
 readout_branch,stationary_projection_trace,Matrix.smul_kronecker]
theorem reset_complete_branches (θ φ : ℝ) (s : Schedule) (a : Q) :
 resetFamily θ φ s qubitX (a,())=(1/2:ℂ) • (readProjection φ a ⊗ₖ basisState 0) ∧
 resetFamily θ φ s qubitY (a,())=(1/2:ℂ) • (readProjection φ a ⊗ₖ basisState 0) := by
 rw [reset_family_eq θ φ s qubitX_density,reset_family_eq θ φ s qubitY_density,
 stationary_coherent_branches];exact ⟨rfl,rfl⟩
theorem reset_complete_tables (θ φ : ℝ) (s : Schedule) (rev : Bool) (h : Hist) (a : Q) :
 readoutTable (decisionReadout rev) (resetFamily θ φ s qubitX) h a=
 (if a=decisionLabel rev h then 1/2 else 0) ∧
 readoutTable (decisionReadout rev) (resetFamily θ φ s qubitY) h a=
 (if a=decisionLabel rev h then 1/2 else 0) := by
 rcases h with ⟨i,⟨⟩⟩
 simp only [readoutTable,decisionReadout_weight,(reset_complete_branches θ φ s i).1,
 (reset_complete_branches θ φ s i).2,Matrix.trace_smul,(support_density φ i).2]
 norm_num
def diagonalStationaryFamily (θ : ℝ) (s : Schedule) (h : DiagonalHistory) : MatJoint :=
 run Q Q 2 (keepTree θ s) h FiniteNontracialMemoryScheduleControls.stationaryInput
theorem diagonal_stationary_family (θ : ℝ) (s : Schedule) :
 diagonalStationaryFamily θ s=FiniteNontracialMemoryScheduleControls.stationaryFamily s := by
 funext h;rcases h with ⟨i,j,⟨⟩⟩
 change (keepStep θ s).branch Q Q 2 j (readStep.branch Q Q 2 i FiniteNontracialMemoryScheduleControls.stationaryInput)=_
 rw [readStep,localStep_branch]
 unfold FiniteNontracialMemoryScheduleControls.stationaryInput
 rw [lift_branch_tensor,computational_basis,FiniteNontracialMemoryScheduleControls.stationary_branch]
 fin_cases i <;> fin_cases j <;>
 simp [keepStep_tensor,free_state,FiniteNontracialSchedule.state_stationary,C_rho,Step.branch_zero,
 FiniteNontracialMemoryScheduleControls.stationaryInput]
theorem diagonal_stationary_tables (θ : ℝ) (s : Schedule) (i j b : Q) :
 readoutTable correlationReadout (diagonalStationaryFamily θ s) (i,j,()) b=
 (if i=0 ∧ j=0 then NontracialPauliReflection.weights b else 0) := by
 rw [diagonal_stationary_family]
 exact FiniteNontracialMemoryScheduleControls.stationary_tables s i j b
theorem diagonal_stationary_same_tree (θ : ℝ) (s : Schedule) (E : DiagonalHistory → MatJoint) :
 readoutError (diagonalStationaryFamily θ s) (diagonalStationaryFamily θ s) E=1/2 := by
 rw [diagonal_stationary_family]
 exact FiniteNontracialMemoryScheduleControls.stationary_every_effect s E
theorem side_null_score_nonzero : sideNullScore≠0 := by
 intro h
 have hi:=congrFun h (0,0)
 norm_num [sideNullScore,Fin.ext_iff] at hi
theorem covariant_named_history_attainment (θ : ℝ) (s : Schedule) :
 historyError (family θ θ s qubitX) (family θ θ s qubitY) (decisionScore false)=
 (1-beta s*invSqrtTwo)/2 := by simp [decisionScore_attains]
theorem fixture_distances (dephase covariant : Bool) (n : Fin 3) :
 branchDistance (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitX)
 (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitY)=
 fixtureSeparation dephase*|fixtureCosine n covariant| ∧
 familyHistoryVariation (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitX)
 (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitY)=
 fixtureSeparation dephase*|fixtureCosine n covariant| := by
 rw [observed_distance,observed_variation,fixture_cosine,(fixture_coefficients dephase).2]
 exact ⟨rfl,rfl⟩
theorem fixture_named_history_rules (dephase covariant rev : Bool) (n : Fin 3) :
 historyError (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitX)
 (family (fixtureAngle n) (fixtureMeasurement n covariant) (fixtureSchedule dephase) qubitY)
 (decisionScore rev)=
 (if rev then (1+fixtureSeparation dephase*fixtureCosine n covariant)/2
 else (1-fixtureSeparation dephase*fixtureCosine n covariant)/2) := by
 rw [decisionScore_attains,fixture_cosine,(fixture_coefficients dephase).2]
theorem witness_named_history_rules (covariant rev : Bool) :
 historyError (timedFamily 1 1 (fixtureMeasurement 1 covariant) [witnessSlice] qubitX)
 (timedFamily 1 1 (fixtureMeasurement 1 covariant) [witnessSlice] qubitY) (decisionScore rev)=
 (if covariant then (if rev then (1+invSqrtTwo/4)/2 else (1-invSqrtTwo/4)/2) else 1/2) := by
 rw [witness_actual_families,witness_actual_families]
 have h := fixture_named_history_rules false covariant rev 1
 cases covariant <;> cases rev <;> simpa [fixtureSchedule,fixtureSeparation,fixtureAngle,fixtureMeasurement,fixtureCosine] using h

theorem pre_evolution_distance (θ : ℝ) (s : Schedule) :
 traceDist (krausMap (evolution θ s) (FiniteNontracialCoherentReadout.input qubitX))
 (krausMap (evolution θ s) (FiniteNontracialCoherentReadout.input qubitY))=beta s*invSqrtTwo := by
 rw [evolution,krausMap_composeKraus,krausMap_composeKraus]
 change traceDist (swapJoint (krausMap (freeLiftKraus θ s) (FiniteNontracialCoherentReadout.input qubitX)))
  (swapJoint (krausMap (freeLiftKraus θ s) (FiniteNontracialCoherentReadout.input qubitY)))=_
 rw [FiniteNontracialCoherentReadout.input,FiniteNontracialCoherentReadout.input,
 free_lift_product,free_lift_product,swap_tensor,swap_tensor,
 FiniteAdaptiveProcessRobustness.traceDist_tensor_right (basisState_density 0),pre_qubit_distance]
theorem computational_physical_laws (θ : ℝ) (s : Schedule) (I : Hist → FiniteInstrument (Q×Q) 2) :
 (∀ h a,0≤readoutTable I (erasureFamily θ s qubitX) h a) ∧
 (∑ h,∑ a,readoutTable I (erasureFamily θ s qubitX) h a)=1 ∧
 (∀ h a,0≤readoutTable I (erasureFamily θ s qubitY) h a) ∧
 (∑ h,∑ a,readoutTable I (erasureFamily θ s qubitY) h a)=1 := by
 have hX : IsBranchFamily (erasureFamily θ s qubitX) := run_family _ (FiniteNontracialCoherentReadout.input_density qubitX_density)
 have hY : IsBranchFamily (erasureFamily θ s qubitY) := run_family _ (FiniteNontracialCoherentReadout.input_density qubitY_density)
 exact ⟨readoutTable_nonneg I hX,readoutTable_total I hX,readoutTable_nonneg I hY,readoutTable_total I hY⟩

end SKEFTHawking.QuantumNetwork.FiniteNontracialPhaseReadout
