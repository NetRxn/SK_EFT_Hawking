import SKEFTHawking.QuantumNetwork.FiniteNontracialEnvironmentLift
import SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness

/-! Actual complex retained-memory readout: E relaxation, SWAP, local S projection.
All histories and decision outcomes are retained without conditioning on branch mass.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteNontracialCoherentReadout
open Matrix FiniteMemoryProcess FiniteMemoryCoarseGraining FiniteInterventionProcess
open FiniteAdaptiveMapPerturbation FiniteAdaptiveReadoutDiscrimination FiniteAdaptiveReadoutRobustness
open FiniteNontracialSchedule (Schedule Slice alpha beta G D)
open NontracialPauliReflection (rhoN rhoN_trace rhoN_density)
open scoped BigOperators Kronecker ComplexOrder
abbrev Q := Fin 2
abbrev MatQ := Matrix Q Q ℂ
abbrev MatJoint := Matrix (Q × Q) (Q × Q) ℂ
abbrev Hist := History 2 1

def input (X : MatQ) : MatJoint := basisState 0 ⊗ₖ X
theorem input_density {X : MatQ} (hX : IsDensityOperator X) : IsDensityOperator (input X) :=
  ⟨(basisState_density 0).1.kronecker hX.1,
    by rw [input,Matrix.trace_kronecker,(basisState_density 0).2,hX.2,one_mul]⟩

def projection (z : ℂ) : MatQ := (1/2:ℂ) • (1 + z • (pauliX-pauliY))
def readProjection (a : Q) : MatQ := if a=0 then qubitProjector else 1-qubitProjector

/-- An all-complex rank-one compression, with the projector coefficient fixed algebraically. -/
theorem projection_compression (z : ℂ) (hz : z^2=1/2) (X : MatQ) :
    projection z * X * projection z = (projection z * X).trace • projection z := by
  have hz3 : z^3=z/2 := by rw [pow_succ,hz]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection,pauliX,pauliY,Matrix.mul_apply,Matrix.vecMul,dotProduct,
      Matrix.trace,Fin.sum_univ_two,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul] <;>
    ring_nf <;> norm_num [hz,hz3,Complex.I_sq] <;> ring

theorem projection_complement (z : ℂ) : 1-projection z = projection (-z) := by
  unfold projection
  module

theorem readProjection_compression (a : Q) (X : MatQ) :
    readProjection a * X * readProjection a = (readProjection a * X).trace • readProjection a := by
  fin_cases a
  · exact projection_compression (invSqrtTwo:ℂ) invSqrtTwo_complex_sq X
  · change (1-projection (invSqrtTwo:ℂ)) * X * (1-projection (invSqrtTwo:ℂ)) =
      ((1-projection (invSqrtTwo:ℂ))*X).trace • (1-projection (invSqrtTwo:ℂ))
    rw [projection_complement]
    exact projection_compression (-(invSqrtTwo:ℂ)) (by simpa using invSqrtTwo_complex_sq) X

theorem readProjection_trace (a : Q) : (readProjection a).trace=1 := by
  fin_cases a <;> norm_num [readProjection,qubitProjector,qubitDirection,Matrix.trace,
    Fin.sum_univ_two,pauliX,pauliY,Matrix.one_apply]
theorem projection_rho_trace (a : Q) : (readProjection a*rhoN).trace=1/2 := by
  fin_cases a <;> norm_num [readProjection,qubitProjector,qubitDirection,rhoN,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,
    pauliX,pauliY,Matrix.one_apply]

theorem readout_branch (a : Q) (X : MatQ) :
    qubitReadout.branch a X = (readProjection a*X).trace • readProjection a := by
  fin_cases a
  · change qubitReadout.branch 0 X = (readProjection 0*X).trace • readProjection 0
    rw [qubitReadout,projectiveReadout_branch_zero]
    exact readProjection_compression 0 X
  · change qubitReadout.branch 1 X = (readProjection 1*X).trace • readProjection 1
    rw [qubitReadout,projectiveReadout_branch_one]
    exact readProjection_compression 1 X

def probabilityA (s : Schedule) (a : Q) : ℝ :=
  if a=0 then (1+beta s*invSqrtTwo)/2 else (1-beta s*invSqrtTwo)/2
def probabilityB (s : Schedule) (a : Q) : ℝ :=
  if a=0 then (1-beta s*invSqrtTwo)/2 else (1+beta s*invSqrtTwo)/2

theorem qubit_diagonal (X : MatQ) (hX : X=qubitX ∨ X=qubitY) :
    NontracialReflectionDynamics.diagonalPart X = (1/2:ℂ) • 1 := by
  rcases hX with rfl|rfl <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [NontracialReflectionDynamics.diagonalPart,qubitX,qubitY,pauliX,pauliY,Matrix.one_apply]

theorem schedule_qubitX (s : Schedule) :
    FiniteNontracialSchedule.state s qubitX =
      (1-(alpha s:ℂ)) • rhoN + (alpha s:ℂ) • ((1/2:ℂ) • 1) +
      (beta s:ℂ) • ((1/2:ℂ) • pauliX) := by
  rw [FiniteNontracialSchedule.state_formula]
  unfold FiniteNontracialSchedule.stateForm
  rw [qubitX_density.2,qubit_diagonal _ (Or.inl rfl)]
  simp only [one_smul]
  unfold qubitX
  module
theorem schedule_qubitY (s : Schedule) :
    FiniteNontracialSchedule.state s qubitY =
      (1-(alpha s:ℂ)) • rhoN + (alpha s:ℂ) • ((1/2:ℂ) • 1) +
      (beta s:ℂ) • ((1/2:ℂ) • pauliY) := by
  rw [FiniteNontracialSchedule.state_formula]
  unfold FiniteNontracialSchedule.stateForm
  rw [qubitY_density.2,qubit_diagonal _ (Or.inr rfl)]
  simp only [one_smul]
  unfold qubitY
  module

theorem schedule_pair_difference (s : Schedule) :
    FiniteNontracialSchedule.state s qubitX-FiniteNontracialSchedule.state s qubitY =
      (beta s:ℂ) • (qubitX-qubitY) := by
  rw [schedule_qubitX,schedule_qubitY]
  unfold qubitX qubitY
  module

theorem trace_probabilityA (s : Schedule) (a : Q) :
    (readProjection a*FiniteNontracialSchedule.state s qubitX).trace = (probabilityA s a:ℂ) := by
  rw [schedule_qubitX]
  fin_cases a <;>
    norm_num [readProjection,probabilityA,qubitProjector,qubitDirection,rhoN,pauliX,pauliY,
      Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.one_apply,
      Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div] <;> ring
theorem trace_probabilityB (s : Schedule) (a : Q) :
    (readProjection a*FiniteNontracialSchedule.state s qubitY).trace = (probabilityB s a:ℂ) := by
  rw [schedule_qubitY]
  fin_cases a <;>
    norm_num [readProjection,probabilityB,qubitProjector,qubitDirection,rhoN,pauliX,pauliY,
      Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.one_apply,
      Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div] <;>
    ring_nf <;> norm_num [Complex.I_sq]

def evolution (s : Schedule) :=
  composeKraus swapKraus (FiniteNontracialEnvironmentLift.scheduleKraus s)
theorem evolution_normalized (s : Schedule) : IsKrausChannel (evolution s) :=
  isKrausChannel_composeKraus swapKraus_normalized
    (FiniteNontracialEnvironmentLift.schedule_normalized s)
def observedStep (s : Schedule) (I : FiniteInstrument Q 2) : Step Q Q 2 :=
  realizedStep Q Q 2 (evolution s) (evolution_normalized s) I
def observedTree (s : Schedule) (I : FiniteInstrument Q 2) : Tree Q Q 2 1 :=
  .node (observedStep s I) (fun _ => .done)
def tree (s : Schedule) : Tree Q Q 2 1 := observedTree s qubitReadout
def family (s : Schedule) (X : MatQ) (h : Hist) : MatJoint :=
  run Q Q 2 (tree s) h (input X)

theorem observed_branch (s : Schedule) (I : FiniteInstrument Q 2) (a : Q) (X : MatQ) :
    run Q Q 2 (observedTree s I) (a,()) (input X) =
      I.branch a (FiniteNontracialSchedule.state s X) ⊗ₖ basisState 0 := by
  change (I.lift Q).branch a (krausMap (evolution s) (input X)) = _
  rw [evolution,krausMap_composeKraus]
  change (I.lift Q).branch a
    (swapJoint (FiniteNontracialEnvironmentLift.scheduleState s (input X))) = _
  rw [input,FiniteNontracialEnvironmentLift.schedule_product,swap_tensor,lift_branch_tensor]

theorem familyA_branch (s : Schedule) (h : Hist) :
    family s qubitX h = (probabilityA s h.1:ℂ) • (readProjection h.1 ⊗ₖ basisState 0) := by
  rcases h with ⟨a,⟨⟩⟩
  change run Q Q 2 (observedTree s qubitReadout) (a,()) (input qubitX)=_
  rw [observed_branch,readout_branch,trace_probabilityA,Matrix.smul_kronecker]
theorem familyB_branch (s : Schedule) (h : Hist) :
    family s qubitY h = (probabilityB s h.1:ℂ) • (readProjection h.1 ⊗ₖ basisState 0) := by
  rcases h with ⟨a,⟨⟩⟩
  change run Q Q 2 (observedTree s qubitReadout) (a,()) (input qubitY)=_
  rw [observed_branch,readout_branch,trace_probabilityB,Matrix.smul_kronecker]

theorem invSqrtTwo_lt_one : invSqrtTwo<1 := by
  nlinarith [invSqrtTwo_sq,invSqrtTwo_pos]
theorem separation_bounds (s : Schedule) : 0<beta s*invSqrtTwo ∧ beta s*invSqrtTwo<1 := by
  have hb := FiniteNontracialSchedule.coefficients s
  refine ⟨mul_pos hb.1 invSqrtTwo_pos,?_⟩
  have hle : beta s*invSqrtTwo ≤ invSqrtTwo := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb.2.1.trans hb.2.2) invSqrtTwo_pos.le
  exact hle.trans_lt invSqrtTwo_lt_one

theorem probabilityA_positive (s : Schedule) (a : Q) : 0<probabilityA s a := by
  have h := separation_bounds s
  fin_cases a
  · change 0<(1+beta s*invSqrtTwo)/2; linarith
  · change 0<(1-beta s*invSqrtTwo)/2; linarith
theorem probabilityB_positive (s : Schedule) (a : Q) : 0<probabilityB s a := by
  have h := separation_bounds s
  fin_cases a
  · change 0<(1-beta s*invSqrtTwo)/2; linarith
  · change 0<(1+beta s*invSqrtTwo)/2; linarith

theorem familyA_trace (s : Schedule) (h : Hist) : (family s qubitX h).trace=(probabilityA s h.1:ℂ) := by
  rw [familyA_branch,Matrix.trace_smul,Matrix.trace_kronecker,readProjection_trace,(basisState_density 0).2]
  simp
theorem familyB_trace (s : Schedule) (h : Hist) : (family s qubitY h).trace=(probabilityB s h.1:ℂ) := by
  rw [familyB_branch,Matrix.trace_smul,Matrix.trace_kronecker,readProjection_trace,(basisState_density 0).2]
  simp
theorem family_valid (s : Schedule) {X : MatQ} (hX : IsDensityOperator X) : IsBranchFamily (family s X) :=
  run_family (tree s) (input_density hX)
theorem familyA_valid (s : Schedule) : IsBranchFamily (family s qubitX) := family_valid s qubitX_density
theorem familyB_valid (s : Schedule) : IsBranchFamily (family s qubitY) := family_valid s qubitY_density

theorem full_laws (s : Schedule) :
    (∀ h,0<(family s qubitX h).trace.re) ∧ (∑ h,(family s qubitX h).trace.re)=1 ∧
    (∀ h,0<(family s qubitY h).trace.re) ∧ (∑ h,(family s qubitY h).trace.re)=1 := by
  refine ⟨?_,(familyA_valid s).2,?_,(familyB_valid s).2⟩
  · intro h; rw [familyA_trace,Complex.ofReal_re]; exact probabilityA_positive s _
  · intro h; rw [familyB_trace,Complex.ofReal_re]; exact probabilityB_positive s _

theorem pre_qubit_distance (s : Schedule) :
    traceDist (FiniteNontracialSchedule.state s qubitX) (FiniteNontracialSchedule.state s qubitY)=
      beta s*invSqrtTwo := by
  unfold traceDist
  rw [schedule_pair_difference,traceNorm_smul_nonneg (FiniteNontracialSchedule.coefficients s).1.le]
  have h := qubit_distance
  unfold traceDist at h
  calc
    1/2*(beta s*traceNorm (qubitX-qubitY)) = beta s*(1/2*traceNorm (qubitX-qubitY)) := by ring
    _ = beta s*invSqrtTwo := congrArg (beta s*·) h
theorem pre_joint_distance (s : Schedule) :
    traceDist (FiniteNontracialEnvironmentLift.scheduleState s (input qubitX))
      (FiniteNontracialEnvironmentLift.scheduleState s (input qubitY))=beta s*invSqrtTwo := by
  rw [input,input,FiniteNontracialEnvironmentLift.schedule_product,
    FiniteNontracialEnvironmentLift.schedule_product,
    FiniteAdaptiveProcessRobustness.traceDist_tensor_left (basisState_density 0),pre_qubit_distance]

/-- A separately normalized SWAP/measurement continuation supplies the upper bound. -/
def postTree : Tree Q Q 2 1 :=
  .node (realizedStep Q Q 2 swapKraus swapKraus_normalized qubitReadout) (fun _ => .done)
theorem family_factor (s : Schedule) (X : MatQ) (h : Hist) :
    family s X h = run Q Q 2 postTree h
      (FiniteNontracialEnvironmentLift.scheduleState s (input X)) := by
  rcases h with ⟨a,⟨⟩⟩
  change (qubitReadout.lift Q).branch a (krausMap (evolution s) (input X)) =
    (qubitReadout.lift Q).branch a (krausMap swapKraus
      (FiniteNontracialEnvironmentLift.scheduleState s (input X)))
  rw [evolution,krausMap_composeKraus]
  rfl

theorem observed_distance_upper (s : Schedule) :
    branchDistance (family s qubitX) (family s qubitY) ≤ beta s*invSqrtTwo := by
  have hA : family s qubitX = fun h => run Q Q 2 postTree h
      (FiniteNontracialEnvironmentLift.scheduleState s (input qubitX)) := funext (family_factor s qubitX)
  have hB : family s qubitY = fun h => run Q Q 2 postTree h
      (FiniteNontracialEnvironmentLift.scheduleState s (input qubitY)) := funext (family_factor s qubitY)
  rw [hA,hB,tree_branchDistance]
  have hu := outputDistance_common Q Q 2 postTree
    (FiniteNontracialEnvironmentLift.schedule_density s (input_density qubitX_density)).1.isHermitian
    (FiniteNontracialEnvironmentLift.schedule_density s (input_density qubitY_density)).1.isHermitian
  rw [pre_joint_distance] at hu
  exact hu

/-- Signed separation of the actual first event, not an assumption about measurement. -/
theorem first_event_separation (s : Schedule) :
    (family s qubitX (0,())).trace.re-(family s qubitY (0,())).trace.re=beta s*invSqrtTwo := by
  rw [familyA_trace,familyB_trace]
  simp only [Complex.ofReal_re,probabilityA,probabilityB,if_true]
  ring

theorem observed_variation (s : Schedule) :
    familyHistoryVariation (family s qubitX) (family s qubitY)=beta s*invSqrtTwo := by
  have h0 : probabilityA s 0-probabilityB s 0=beta s*invSqrtTwo := by simp [probabilityA,probabilityB]; ring
  have h1 : probabilityA s 1-probabilityB s 1= -(beta s*invSqrtTwo) := by simp [probabilityA,probabilityB]; ring
  unfold familyHistoryVariation
  simp only [familyA_trace,familyB_trace,Complex.ofReal_re]
  change (∑ h : Q × Unit, |probabilityA s h.1-probabilityB s h.1|)/2=_
  simp only [Fintype.sum_prod_type,Fintype.sum_unique,Fin.sum_univ_two,h0,h1,abs_neg,
    abs_of_pos (separation_bounds s).1]
  ring
theorem observed_distance_lower (s : Schedule) :
    beta s*invSqrtTwo ≤ branchDistance (family s qubitX) (family s qubitY) := by
  rw [← observed_variation]
  exact familyHistoryVariation_le_branchDistance (familyA_valid s) (familyB_valid s)
theorem observed_distance (s : Schedule) :
    branchDistance (family s qubitX) (family s qubitY)=beta s*invSqrtTwo :=
  le_antisymm (observed_distance_upper s) (observed_distance_lower s)
theorem tree_output_distance (s : Schedule) :
    outputDistance Q Q 2 (tree s) (tree s) (input qubitX) (input qubitY)=beta s*invSqrtTwo := by
  rw [← tree_branchDistance]
  exact observed_distance s
theorem tree_history_variation (s : Schedule) :
    historyVariation Q Q 2 (tree s) (tree s) (input qubitX) (input qubitY)=beta s*invSqrtTwo := by
  rw [← tree_familyHistoryVariation]
  exact observed_variation s

def decisionScore (h : Hist) : ℝ := if h.1=0 then 1 else 0
def decisionProjection (h : Hist) : MatJoint := if h.1=0 then 1 else 0
theorem decisionProjection_hermitian (h : Hist) : (decisionProjection h).IsHermitian := by
  unfold decisionProjection; split_ifs <;> simp
theorem decisionProjection_idem (h : Hist) : decisionProjection h*decisionProjection h=decisionProjection h := by
  unfold decisionProjection; split_ifs <;> simp
def decisionReadout (h : Hist) : FiniteInstrument (Q × Q) 2 :=
  projectiveReadout (decisionProjection h) (decisionProjection_hermitian h) (decisionProjection_idem h)

theorem decisionReadout_weight (h : Hist) (a : Q) (Z : MatJoint) :
    (decisionReadout h).weight a Z = if a=h.1 then Z.trace.re else 0 := by
  rcases h with ⟨h,⟨⟩⟩
  fin_cases h <;> fin_cases a <;>
    norm_num [decisionReadout,decisionProjection,projectiveReadout_weight_zero,projectiveReadout_weight_one]

theorem readoutTableA (s : Schedule) (h : Hist) (a : Q) :
    readoutTable decisionReadout (family s qubitX) h a = if a=h.1 then probabilityA s h.1 else 0 := by
  rw [readoutTable,decisionReadout_weight,familyA_trace,Complex.ofReal_re]
theorem readoutTableB (s : Schedule) (h : Hist) (a : Q) :
    readoutTable decisionReadout (family s qubitY) h a = if a=h.1 then probabilityB s h.1 else 0 := by
  rw [readoutTable,decisionReadout_weight,familyB_trace,Complex.ofReal_re]
theorem decision_laws (s : Schedule) :
    (∀ h a,0≤readoutTable decisionReadout (family s qubitX) h a) ∧
    (∑ h,∑ a,readoutTable decisionReadout (family s qubitX) h a)=1 ∧
    (∀ h a,0≤readoutTable decisionReadout (family s qubitY) h a) ∧
    (∑ h,∑ a,readoutTable decisionReadout (family s qubitY) h a)=1 :=
  ⟨readoutTable_nonneg _ (familyA_valid s),readoutTable_total _ (familyA_valid s),
    readoutTable_nonneg _ (familyB_valid s),readoutTable_total _ (familyB_valid s)⟩
theorem decision_attains (s : Schedule) :
    instrumentError (family s qubitX) (family s qubitY) decisionReadout=(1-beta s*invSqrtTwo)/2 := by
  unfold instrumentError
  simp only [readoutTableA,readoutTableB]
  change ((∑ h : Q × Unit,if (0:Q)=h.1 then probabilityB s h.1 else 0)+
    (∑ h : Q × Unit,if (1:Q)=h.1 then probabilityA s h.1 else 0))/2=_
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_two,probabilityA,probabilityB]

theorem decision_effect_realizes (s : Schedule) :
    readoutError (family s qubitX) (family s qubitY) decisionProjection=
      instrumentError (family s qubitX) (family s qubitY) decisionReadout := by
  simp only [readoutError,instrumentError,readoutTable,decisionReadout,
    projectiveReadout_weight_zero,projectiveReadout_weight_one]
theorem all_effect_isLeast (s : Schedule) :
    IsLeast {x : ℝ | ∃ E : Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
      readoutError (family s qubitX) (family s qubitY) E=x} ((1-beta s*invSqrtTwo)/2) := by
  simpa only [observed_distance] using readoutError_isLeast (familyA_valid s) (familyB_valid s)
theorem every_randomized_isLeast (s : Schedule) :
    IsLeast {x : ℝ | ∃ a : Hist → ℝ,(∀ h,a h∈Set.Icc (0:ℝ) 1) ∧
      historyError (family s qubitX) (family s qubitY) a=x} ((1-beta s*invSqrtTwo)/2) := by
  simpa only [observed_variation] using historyError_isLeast (familyA_valid s) (familyB_valid s)
theorem decisionScore_admissible : ∀ h,decisionScore h∈Set.Icc (0:ℝ) 1 := by
  intro h; unfold decisionScore; split_ifs <;> norm_num
theorem decisionScore_attains (s : Schedule) :
    historyError (family s qubitX) (family s qubitY) decisionScore=(1-beta s*invSqrtTwo)/2 := by
  rw [← historyError_scalar_effect]
  have he : (fun h => (decisionScore h:ℂ) • (1:MatJoint))=decisionProjection := by
    funext h; unfold decisionScore decisionProjection; split_ifs <;> simp
  rw [he,decision_effect_realizes,decision_attains]

/-- The actual computational instrument compresses every complex matrix to its diagonal entry. -/
theorem computational_compression (a : Q) (X : MatQ) :
    FiniteInstrument.computational.branch a X = X a a • basisState a := by
  simp only [FiniteInstrument.branch,FiniteInstrument.computational]
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [FiniteInstrument.branch,FiniteInstrument.computational,krausMap,basisState,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]

def erasureProbability (s : Schedule) (a : Q) : ℝ :=
  alpha s/2+(1-alpha s)*(rhoN a a).re
def erasureTree (s : Schedule) : Tree Q Q 2 1 := observedTree s FiniteInstrument.computational
def erasureFamily (s : Schedule) (X : MatQ) (h : Hist) : MatJoint :=
  run Q Q 2 (erasureTree s) h (input X)

theorem erasure_branch (s : Schedule) (X : MatQ) (hX : X=qubitX ∨ X=qubitY) (h : Hist) :
    erasureFamily s X h = (erasureProbability s h.1:ℂ) • (basisState h.1 ⊗ₖ basisState 0) := by
  rcases h with ⟨a,⟨⟩⟩
  change run Q Q 2 (observedTree s FiniteInstrument.computational) (a,()) (input X)=_
  rw [observed_branch,computational_compression,Matrix.smul_kronecker]
  congr 1
  rcases hX with rfl|rfl
  · rw [schedule_qubitX]
    fin_cases a <;> norm_num [erasureProbability,rhoN,pauliX,Matrix.one_apply,
      Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div] <;> ring
  · rw [schedule_qubitY]
    fin_cases a <;> norm_num [erasureProbability,rhoN,pauliY,Matrix.one_apply,
      Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div] <;> ring

theorem erasure_family_equal (s : Schedule) : erasureFamily s qubitX=erasureFamily s qubitY := by
  funext h; rw [erasure_branch s qubitX (Or.inl rfl),erasure_branch s qubitY (Or.inr rfl)]
theorem erasure_histories_equal (s : Schedule) (h : Hist) :
    weight Q Q 2 (erasureTree s) h (input qubitX)=weight Q Q 2 (erasureTree s) h (input qubitY) :=
  congrArg (fun Z : MatJoint => Z.trace.re) (congrFun (erasure_family_equal s) h)
theorem erasure_terminal_equal (s : Schedule) :
    terminalState Q Q 2 (erasureTree s) (input qubitX)=terminalState Q Q 2 (erasureTree s) (input qubitY) :=
  congrArg (fun A : Hist → MatJoint => ∑ h,A h) (erasure_family_equal s)
theorem erasure_valid (s : Schedule) : IsBranchFamily (erasureFamily s qubitX) :=
  run_family (erasureTree s) (input_density qubitX_density)

theorem branchDistance_same (A : Hist → MatJoint) : branchDistance A A=0 := by
  simp [branchDistance,traceDist_self]
theorem variation_same (A : Hist → MatJoint) : familyHistoryVariation A A=0 := by
  simp [familyHistoryVariation]
theorem readoutError_same {A : Hist → MatJoint} (hA : IsBranchFamily A) (E : Hist → MatJoint) :
    readoutError A A E=1/2 := by rw [readoutError_eq _ _ _ hA.2]; simp
theorem instrumentError_same {A : Hist → MatJoint} (hA : IsBranchFamily A)
    (I : Hist → FiniteInstrument (Q×Q) 2) : instrumentError A A I=1/2 := by
  have ht := readoutTable_total I hA
  simp only [Fin.sum_univ_two] at ht
  unfold instrumentError
  rw [← Finset.sum_add_distrib,ht]

theorem erasure_distance (s : Schedule) :
    branchDistance (erasureFamily s qubitX) (erasureFamily s qubitY)=0 := by
  rw [← erasure_family_equal]; exact branchDistance_same _
theorem erasure_variation (s : Schedule) :
    familyHistoryVariation (erasureFamily s qubitX) (erasureFamily s qubitY)=0 := by
  rw [← erasure_family_equal]; exact variation_same _
theorem erasure_output_distance (s : Schedule) :
    outputDistance Q Q 2 (erasureTree s) (erasureTree s) (input qubitX) (input qubitY)=0 := by
  rw [← tree_branchDistance]; exact erasure_distance s
theorem erasure_history_variation (s : Schedule) :
    historyVariation Q Q 2 (erasureTree s) (erasureTree s) (input qubitX) (input qubitY)=0 := by
  rw [← tree_familyHistoryVariation]; exact erasure_variation s
theorem erasure_every_effect (s : Schedule) (E : Hist → MatJoint) :
    readoutError (erasureFamily s qubitX) (erasureFamily s qubitY) E=1/2 := by
  rw [← erasure_family_equal]; exact readoutError_same (erasure_valid s) E
theorem erasure_every_readout (s : Schedule) (I : Hist → FiniteInstrument (Q×Q) 2) :
    instrumentError (erasureFamily s qubitX) (erasureFamily s qubitY) I=1/2 := by
  rw [← erasure_family_equal]; exact instrumentError_same (erasure_valid s) I
theorem erasure_every_history (s : Schedule) (a : Hist → ℝ) :
    historyError (erasureFamily s qubitX) (erasureFamily s qubitY) a=1/2 := by
  exact historyError_same_law (erasure_valid s) (fun h =>
    congrArg (fun Z : MatJoint => Z.trace.re) (congrFun (erasure_family_equal s) h)) a
theorem erasure_all_effect_isLeast (s : Schedule) :
    IsLeast {x : ℝ | ∃ E : Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
      readoutError (erasureFamily s qubitX) (erasureFamily s qubitY) E=x} (1/2) := by
  have hB : IsBranchFamily (erasureFamily s qubitY) := by rw [← erasure_family_equal]; exact erasure_valid s
  simpa only [erasure_distance,sub_zero] using readoutError_isLeast (erasure_valid s) hB
theorem erasure_randomized_isLeast (s : Schedule) :
    IsLeast {x : ℝ | ∃ a : Hist → ℝ,(∀ h,a h∈Set.Icc (0:ℝ) 1) ∧
      historyError (erasureFamily s qubitX) (erasureFamily s qubitY) a=x} (1/2) := by
  have hB : IsBranchFamily (erasureFamily s qubitY) := by rw [← erasure_family_equal]; exact erasure_valid s
  simpa only [erasure_variation,sub_zero] using historyError_isLeast (erasure_valid s) hB

/-- Endpoint identities concern the actions of the actual composed family. -/
theorem zero_dose_evolution (s : Schedule) (hG : G s=0) (hD : D s=0) (Z : MatJoint) :
    krausMap (evolution s) Z=swapJoint Z := by
  rw [evolution,krausMap_composeKraus]
  change swapJoint (FiniteNontracialEnvironmentLift.scheduleState s Z)=_
  rw [(FiniteNontracialEnvironmentLift.schedule_zero_dose s hG hD Z).1]
theorem zero_dose_family (s : Schedule) (hG : G s=0) (hD : D s=0) (X : MatQ) :
    family s X=family [] X := by
  funext h; rcases h with ⟨a,⟨⟩⟩
  change run Q Q 2 (observedTree s qubitReadout) (a,()) (input X)=
    run Q Q 2 (observedTree [] qubitReadout) (a,()) (input X)
  rw [observed_branch,observed_branch,(FiniteNontracialSchedule.zero_dose_actions s hG hD X).1,
    FiniteNontracialSchedule.state_nil]
theorem zero_dose_beta (s : Schedule) (hG : G s=0) (hD : D s=0) : beta s=1 := by
  simp [beta,hG,hD]

theorem empty_controls :
    (∀ Z,krausMap (evolution []) Z=swapJoint Z) ∧
    outputDistance Q Q 2 (tree []) (tree []) (input qubitX) (input qubitY)=invSqrtTwo ∧
    instrumentError (family [] qubitX) (family [] qubitY) decisionReadout=(1-invSqrtTwo)/2 := by
  refine ⟨zero_dose_evolution [] rfl rfl,?_,?_⟩
  · simpa using tree_output_distance []
  · simpa using decision_attains []
theorem zero_duration_controls (s : Schedule) (hz : ∀ h∈s,h.duration=0) :
    (∀ Z,krausMap (evolution s) Z=swapJoint Z) ∧
    (∀ X,family s X=family [] X) ∧
    outputDistance Q Q 2 (tree s) (tree s) (input qubitX) (input qubitY)=invSqrtTwo ∧
    instrumentError (family s qubitX) (family s qubitY) decisionReadout=(1-invSqrtTwo)/2 := by
  have hd := FiniteNontracialSchedule.zero_duration_doses s hz
  refine ⟨zero_dose_evolution s hd.1 hd.2,zero_dose_family s hd.1 hd.2,?_,?_⟩
  · rw [tree_output_distance,zero_dose_beta s hd.1 hd.2,one_mul]
  · rw [decision_attains,zero_dose_beta s hd.1 hd.2,one_mul]
theorem zero_rates_controls (s : Schedule) (hz : ∀ h∈s,h.gamma=0 ∧ h.eta=0) :
    (∀ Z,krausMap (evolution s) Z=swapJoint Z) ∧
    (∀ X,family s X=family [] X) ∧
    outputDistance Q Q 2 (tree s) (tree s) (input qubitX) (input qubitY)=invSqrtTwo ∧
    instrumentError (family s qubitX) (family s qubitY) decisionReadout=(1-invSqrtTwo)/2 := by
  have hd := FiniteNontracialSchedule.zero_rate_doses s hz
  refine ⟨zero_dose_evolution s hd.1 hd.2,zero_dose_family s hd.1 hd.2,?_,?_⟩
  · rw [tree_output_distance,zero_dose_beta s hd.1 hd.2,one_mul]
  · rw [decision_attains,zero_dose_beta s hd.1 hd.2,one_mul]

theorem pure_dephasing_controls (s : Schedule) (hG : G s=0) (hD : 0<D s) :
    alpha s=1 ∧ beta s<1 ∧
    outputDistance Q Q 2 (tree s) (tree s) (input qubitX) (input qubitY)< invSqrtTwo ∧
    (1-invSqrtTwo)/2< instrumentError (family s qubitX) (family s qubitY) decisionReadout := by
  have hb : beta s<1 := by rw [beta,hG,zero_add,Real.exp_lt_one_iff]; linarith
  have hbc : beta s*invSqrtTwo< invSqrtTwo := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hb invSqrtTwo_pos
  refine ⟨by simp [alpha,hG],hb,?_,?_⟩
  · rw [tree_output_distance]; exact hbc
  · rw [decision_attains]; linarith

/-- Both numeric guards retain every actual history/decision table entry, including zeros. -/
theorem logTwo_tables (h : Hist) (a : Q) :
    readoutTable decisionReadout (family [FiniteNontracialSchedule.logTwoSlice] qubitX) h a =
      (if a=h.1 then (if h.1=0 then (1+invSqrtTwo/4)/2 else (1-invSqrtTwo/4)/2) else 0) ∧
    readoutTable decisionReadout (family [FiniteNontracialSchedule.logTwoSlice] qubitY) h a =
      if a=h.1 then (if h.1=0 then (1-invSqrtTwo/4)/2 else (1+invSqrtTwo/4)/2) else 0 := by
  rw [readoutTableA,readoutTableB]
  simp only [probabilityA,probabilityB,FiniteNontracialSchedule.logTwo_coefficients.2]
  constructor <;> split_ifs <;> ring

theorem logTwo_controls :
    0≤FiniteNontracialSchedule.logTwoSlice.duration ∧
    alpha [FiniteNontracialSchedule.logTwoSlice]=1/2 ∧ beta [FiniteNontracialSchedule.logTwoSlice]=1/4 ∧
    outputDistance Q Q 2 (tree [FiniteNontracialSchedule.logTwoSlice])
      (tree [FiniteNontracialSchedule.logTwoSlice]) (input qubitX) (input qubitY)=invSqrtTwo/4 ∧
    instrumentError (family [FiniteNontracialSchedule.logTwoSlice] qubitX)
      (family [FiniteNontracialSchedule.logTwoSlice] qubitY) decisionReadout=(1-invSqrtTwo/4)/2 := by
  refine ⟨FiniteNontracialSchedule.logTwoSlice.duration_nonneg,
    FiniteNontracialSchedule.logTwo_coefficients.1,FiniteNontracialSchedule.logTwo_coefficients.2,?_,?_⟩
  · rw [tree_output_distance,FiniteNontracialSchedule.logTwo_coefficients.2]; ring
  · rw [decision_attains,FiniteNontracialSchedule.logTwo_coefficients.2]; ring

def dephasingLogTwoSlice : Slice :=
  ⟨0,1,Real.log 2,le_refl 0,zero_le_one,Real.log_nonneg (by norm_num)⟩
theorem dephasingLogTwo_coefficients : alpha [dephasingLogTwoSlice]=1 ∧ beta [dephasingLogTwoSlice]=1/2 := by
  have hl : Real.exp (-Real.log 2)=(1:ℝ)/2 := by
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]; norm_num
  constructor
  · simp [alpha,G,dephasingLogTwoSlice]
  · simpa [beta,G,D,dephasingLogTwoSlice] using hl
theorem dephasingLogTwo_tables (h : Hist) (a : Q) :
    readoutTable decisionReadout (family [dephasingLogTwoSlice] qubitX) h a =
      (if a=h.1 then (if h.1=0 then (1+invSqrtTwo/2)/2 else (1-invSqrtTwo/2)/2) else 0) ∧
    readoutTable decisionReadout (family [dephasingLogTwoSlice] qubitY) h a =
      if a=h.1 then (if h.1=0 then (1-invSqrtTwo/2)/2 else (1+invSqrtTwo/2)/2) else 0 := by
  rw [readoutTableA,readoutTableB]
  simp only [probabilityA,probabilityB,dephasingLogTwo_coefficients.2]
  constructor <;> split_ifs <;> ring

theorem dephasingLogTwo_controls :
    0≤dephasingLogTwoSlice.duration ∧ alpha [dephasingLogTwoSlice]=1 ∧ beta [dephasingLogTwoSlice]=1/2 ∧
    outputDistance Q Q 2 (tree [dephasingLogTwoSlice]) (tree [dephasingLogTwoSlice])
      (input qubitX) (input qubitY)=invSqrtTwo/2 ∧
    instrumentError (family [dephasingLogTwoSlice] qubitX) (family [dephasingLogTwoSlice] qubitY)
      decisionReadout=(1-invSqrtTwo/2)/2 := by
  refine ⟨dephasingLogTwoSlice.duration_nonneg,dephasingLogTwo_coefficients.1,
    dephasingLogTwo_coefficients.2,?_,?_⟩
  · rw [tree_output_distance,dephasingLogTwo_coefficients.2]; ring
  · rw [decision_attains,dephasingLogTwo_coefficients.2]; ring

/-- A complete E Gibbs reset is a separate normalized physical preparation, before the schedule. -/
def resetEvolution (s : Schedule) := composeKraus (evolution s)
  (FiniteNontracialEnvironmentLift.liftKraus FiniteNontracialEnvironmentLift.gibbsResetKraus)
theorem resetEvolution_normalized (s : Schedule) : IsKrausChannel (resetEvolution s) :=
  isKrausChannel_composeKraus (evolution_normalized s) FiniteNontracialEnvironmentLift.gibbsReset_normalized
def resetTree (s : Schedule) : Tree Q Q 2 1 :=
  .node (realizedStep Q Q 2 (resetEvolution s) (resetEvolution_normalized s) qubitReadout) (fun _ => .done)
def resetFamily (s : Schedule) (X : MatQ) (h : Hist) : MatJoint :=
  run Q Q 2 (resetTree s) h (input X)

theorem gibbs_reset_preparation {X : MatQ} (hX : IsDensityOperator X) :
    FiniteNontracialEnvironmentLift.gibbsReset (input X)=input rhoN := by
  rw [FiniteNontracialEnvironmentLift.gibbsReset_eq,input,
    FiniteNontracialEnvironmentLift.ptrace2_kronecker,hX.2,one_smul]
  rfl
theorem resetFamily_eq (s : Schedule) {X : MatQ} (hX : IsDensityOperator X) :
    resetFamily s X=family s rhoN := by
  funext h; rcases h with ⟨a,⟨⟩⟩
  change (qubitReadout.lift Q).branch a (krausMap (resetEvolution s) (input X))=_
  rw [resetEvolution,krausMap_composeKraus]
  change (qubitReadout.lift Q).branch a
    (krausMap (evolution s) (FiniteNontracialEnvironmentLift.gibbsReset (input X)))=_
  rw [gibbs_reset_preparation hX]
  rfl
theorem reset_branch (s : Schedule) {X : MatQ} (hX : IsDensityOperator X) (h : Hist) :
    resetFamily s X h=(1/2:ℂ) • (readProjection h.1 ⊗ₖ basisState 0) := by
  rw [resetFamily_eq s hX]
  rcases h with ⟨a,⟨⟩⟩
  change run Q Q 2 (observedTree s qubitReadout) (a,()) (input rhoN)=_
  rw [observed_branch,FiniteNontracialSchedule.state_stationary,readout_branch,
    projection_rho_trace,Matrix.smul_kronecker]
theorem reset_inputs_equal :
    FiniteNontracialEnvironmentLift.gibbsReset (input qubitX)=
      FiniteNontracialEnvironmentLift.gibbsReset (input qubitY) := by
  rw [gibbs_reset_preparation qubitX_density,gibbs_reset_preparation qubitY_density]
theorem reset_families_equal (s : Schedule) : resetFamily s qubitX=resetFamily s qubitY := by
  rw [resetFamily_eq s qubitX_density,resetFamily_eq s qubitY_density]
theorem reset_valid (s : Schedule) : IsBranchFamily (resetFamily s qubitX) :=
  run_family (resetTree s) (input_density qubitX_density)
theorem reset_tables (s : Schedule) (h : Hist) (a : Q) :
    readoutTable decisionReadout (resetFamily s qubitX) h a=(if a=h.1 then 1/2 else 0) ∧
    readoutTable decisionReadout (resetFamily s qubitY) h a=(if a=h.1 then 1/2 else 0) := by
  simp only [readoutTable,decisionReadout_weight,reset_branch s qubitX_density,
    reset_branch s qubitY_density,Matrix.trace_smul,Matrix.trace_kronecker,readProjection_trace,
    (basisState_density 0).2]
  norm_num

theorem reset_distance (s : Schedule) :
    branchDistance (resetFamily s qubitX) (resetFamily s qubitY)=0 := by
  rw [← reset_families_equal]; exact branchDistance_same _
theorem reset_variation (s : Schedule) :
    familyHistoryVariation (resetFamily s qubitX) (resetFamily s qubitY)=0 := by
  rw [← reset_families_equal]; exact variation_same _
theorem reset_output_distance (s : Schedule) :
    outputDistance Q Q 2 (resetTree s) (resetTree s) (input qubitX) (input qubitY)=0 := by
  rw [← tree_branchDistance]; exact reset_distance s
theorem reset_every_effect (s : Schedule) (E : Hist → MatJoint) :
    readoutError (resetFamily s qubitX) (resetFamily s qubitY) E=1/2 := by
  rw [← reset_families_equal]; exact readoutError_same (reset_valid s) E
theorem reset_every_readout (s : Schedule) (I : Hist → FiniteInstrument (Q×Q) 2) :
    instrumentError (resetFamily s qubitX) (resetFamily s qubitY) I=1/2 := by
  rw [← reset_families_equal]; exact instrumentError_same (reset_valid s) I
theorem reset_every_history (s : Schedule) (a : Hist → ℝ) :
    historyError (resetFamily s qubitX) (resetFamily s qubitY) a=1/2 := by
  exact historyError_same_law (reset_valid s) (fun h =>
    congrArg (fun Z : MatJoint => Z.trace.re) (congrFun (reset_families_equal s) h)) a
theorem reset_all_effect_isLeast (s : Schedule) :
    IsLeast {x : ℝ | ∃ E : Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
      readoutError (resetFamily s qubitX) (resetFamily s qubitY) E=x} (1/2) := by
  have hB : IsBranchFamily (resetFamily s qubitY) := by rw [← reset_families_equal]; exact reset_valid s
  simpa only [reset_distance,sub_zero] using readoutError_isLeast (reset_valid s) hB
theorem reset_randomized_isLeast (s : Schedule) :
    IsLeast {x : ℝ | ∃ a : Hist → ℝ,(∀ h,a h∈Set.Icc (0:ℝ) 1) ∧
      historyError (resetFamily s qubitX) (resetFamily s qubitY) a=x} (1/2) := by
  have hB : IsBranchFamily (resetFamily s qubitY) := by rw [← reset_families_equal]; exact reset_valid s
  simpa only [reset_variation,sub_zero] using historyError_isLeast (reset_valid s) hB

/-- System-only discard-and-prepare precedes E relaxation and SWAP, so E remains observable. -/
def systemPrepareEvolution (s : Schedule) := composeKraus (evolution s) (tensorKraus resetKraus)
theorem systemPrepareEvolution_normalized (s : Schedule) : IsKrausChannel (systemPrepareEvolution s) :=
  isKrausChannel_composeKraus (evolution_normalized s) resetSystem_normalized
def systemPrepareTree (s : Schedule) : Tree Q Q 2 1 :=
  .node (realizedStep Q Q 2 (systemPrepareEvolution s) (systemPrepareEvolution_normalized s) qubitReadout)
    (fun _ => .done)
def systemPrepareFamily (s : Schedule) (X : MatQ) (h : Hist) : MatJoint :=
  run Q Q 2 (systemPrepareTree s) h (input X)
theorem system_prepare_input (X : MatQ) : resetSystem (input X)=input X := by
  rw [resetSystem_eq]
  unfold input
  congr 1
  ext i j
  norm_num [ptrace1,basisState,Fin.sum_univ_two]
theorem systemPrepareFamily_eq (s : Schedule) (X : MatQ) : systemPrepareFamily s X=family s X := by
  funext h; rcases h with ⟨a,⟨⟩⟩
  change (qubitReadout.lift Q).branch a (krausMap (systemPrepareEvolution s) (input X))=_
  rw [systemPrepareEvolution,krausMap_composeKraus]
  change (qubitReadout.lift Q).branch a (krausMap (evolution s) (resetSystem (input X)))=_
  rw [system_prepare_input]
  rfl
theorem system_prepare_tables (s : Schedule) (h : Hist) (a : Q) :
    readoutTable decisionReadout (systemPrepareFamily s qubitX) h a=
      (if a=h.1 then probabilityA s h.1 else 0) ∧
    readoutTable decisionReadout (systemPrepareFamily s qubitY) h a=
      (if a=h.1 then probabilityB s h.1 else 0) := by
  rw [systemPrepareFamily_eq,systemPrepareFamily_eq,readoutTableA,readoutTableB]; exact ⟨rfl,rfl⟩
theorem system_prepare_controls (s : Schedule) :
    outputDistance Q Q 2 (systemPrepareTree s) (systemPrepareTree s) (input qubitX) (input qubitY)=
      beta s*invSqrtTwo ∧
    instrumentError (systemPrepareFamily s qubitX) (systemPrepareFamily s qubitY) decisionReadout=
      (1-beta s*invSqrtTwo)/2 := by
  constructor
  · rw [← tree_branchDistance]
    change branchDistance (systemPrepareFamily s qubitX) (systemPrepareFamily s qubitY)=_
    rw [systemPrepareFamily_eq,systemPrepareFamily_eq,observed_distance]
  · rw [systemPrepareFamily_eq,systemPrepareFamily_eq,decision_attains]
theorem system_prepare_all_effect_isLeast (s : Schedule) :
    IsLeast {x : ℝ | ∃ E : Hist → MatJoint,(∀ h,IsBinaryPOVM (E h)) ∧
      readoutError (systemPrepareFamily s qubitX) (systemPrepareFamily s qubitY) E=x}
      ((1-beta s*invSqrtTwo)/2) := by
  rw [systemPrepareFamily_eq,systemPrepareFamily_eq]; exact all_effect_isLeast s
theorem system_prepare_randomized_isLeast (s : Schedule) :
    IsLeast {x : ℝ | ∃ a : Hist → ℝ,(∀ h,a h∈Set.Icc (0:ℝ) 1) ∧
      historyError (systemPrepareFamily s qubitX) (systemPrepareFamily s qubitY) a=x}
      ((1-beta s*invSqrtTwo)/2) := by
  rw [systemPrepareFamily_eq,systemPrepareFamily_eq]; exact every_randomized_isLeast s

theorem identical_controls (s : Schedule) {X : MatQ} (hX : IsDensityOperator X) :
    outputDistance Q Q 2 (tree s) (tree s) (input X) (input X)=0 ∧
    historyVariation Q Q 2 (tree s) (tree s) (input X) (input X)=0 ∧
    (∀ E : Hist → MatJoint,readoutError (family s X) (family s X) E=1/2) ∧
    (∀ I : Hist → FiniteInstrument (Q×Q) 2,instrumentError (family s X) (family s X) I=1/2) ∧
    (∀ a : Hist → ℝ,historyError (family s X) (family s X) a=1/2) := by
  refine ⟨?_,?_,readoutError_same (family_valid s hX),instrumentError_same (family_valid s hX),?_⟩
  · rw [← tree_branchDistance]; exact branchDistance_same _
  · rw [← tree_familyHistoryVariation]; exact variation_same _
  · intro a; exact historyError_same_law (family_valid s hX) (fun _ => rfl) a

/-- The named attaining decision is a normalized physical binary instrument and admissible effect. -/
theorem decisionReadout_normalized (h : Hist) :
    (∑ a,∑ k,((decisionReadout h).operators a k)ᴴ*(decisionReadout h).operators a k)=1 :=
  (decisionReadout h).normalized
theorem decision_effect_admissible (h : Hist) : IsBinaryPOVM (decisionProjection h) := by
  have he : (decisionScore h:ℂ) • (1:MatJoint)=decisionProjection h := by
    unfold decisionScore decisionProjection; split_ifs <;> simp
  rw [← he]
  exact scalar_effect_admissible decisionScore decisionScore_admissible h

theorem erasure_probability_positive (s : Schedule) (a : Q) : 0<erasureProbability s a := by
  have hc := FiniteNontracialSchedule.coefficients s
  have ha : 0<alpha s := hc.1.trans_le hc.2.1
  fin_cases a <;> norm_num [erasureProbability,rhoN] <;> nlinarith [hc.2.2]
theorem erasure_trace (s : Schedule) (X : MatQ) (hX : X=qubitX ∨ X=qubitY) (h : Hist) :
    (erasureFamily s X h).trace=(erasureProbability s h.1:ℂ) := by
  rw [erasure_branch s X hX,Matrix.trace_smul,Matrix.trace_kronecker,
    (basisState_density h.1).2,(basisState_density 0).2]
  simp
theorem erasure_laws (s : Schedule) :
    (∀ h,0<(erasureFamily s qubitX h).trace.re) ∧ (∑ h,(erasureFamily s qubitX h).trace.re)=1 ∧
    (∀ h,0<(erasureFamily s qubitY h).trace.re) ∧ (∑ h,(erasureFamily s qubitY h).trace.re)=1 := by
  refine ⟨?_,(erasure_valid s).2,?_,?_⟩
  · intro h; rw [erasure_trace s qubitX (Or.inl rfl),Complex.ofReal_re]; exact erasure_probability_positive s _
  · intro h; rw [erasure_trace s qubitY (Or.inr rfl),Complex.ofReal_re]; exact erasure_probability_positive s _
  · rw [← erasure_family_equal]; exact (erasure_valid s).2
theorem erasure_tables (s : Schedule) (h : Hist) (a : Q) :
    readoutTable decisionReadout (erasureFamily s qubitX) h a=
      (if a=h.1 then erasureProbability s h.1 else 0) ∧
    readoutTable decisionReadout (erasureFamily s qubitY) h a=
      (if a=h.1 then erasureProbability s h.1 else 0) := by
  simp only [readoutTable,decisionReadout_weight,erasure_trace s qubitX (Or.inl rfl),
    erasure_trace s qubitY (Or.inr rfl),Complex.ofReal_re]
  trivial

theorem reset_laws (s : Schedule) :
    (∀ h a,0≤readoutTable decisionReadout (resetFamily s qubitX) h a) ∧
    (∑ h,∑ a,readoutTable decisionReadout (resetFamily s qubitX) h a)=1 ∧
    (∀ h a,0≤readoutTable decisionReadout (resetFamily s qubitY) h a) ∧
    (∑ h,∑ a,readoutTable decisionReadout (resetFamily s qubitY) h a)=1 := by
  have hB : IsBranchFamily (resetFamily s qubitY) := by rw [← reset_families_equal]; exact reset_valid s
  exact ⟨readoutTable_nonneg _ (reset_valid s),readoutTable_total _ (reset_valid s),
    readoutTable_nonneg _ hB,readoutTable_total _ hB⟩

end SKEFTHawking.QuantumNetwork.FiniteNontracialCoherentReadout
