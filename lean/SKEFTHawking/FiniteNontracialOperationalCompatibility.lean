import SKEFTHawking.FiniteNontracialScheduleTransfer
import SKEFTHawking.QuantumNetwork.FiniteNontracialMemoryReadout
import SKEFTHawking.QuantumNetwork.FiniteNontracialCoherentReadout

/-! Compatibility of independent operational readouts and weighted history transfer.
Physical values below are actual tree distances and readout errors. The reflection
quotient metric, its six-outcome carrier, and the two-qubit carrier remain distinct.
Schedules supply finite doses; no measured clock or switching derivative is defined.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.NontracialOperationalCompatibility
open Matrix NontracialHistoryConsistency NontracialPauliReflection NontracialScheduleTransfer
open FiniteInterventionProcess FiniteAdaptiveMapPerturbation FiniteAdaptiveReadoutDiscrimination
open FiniteAdaptiveReadoutRobustness
open FiniteNontracialSchedule (Schedule Slice alpha beta G D)
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

abbrev ReflectionCarrier := (Fin 2) × Unit
abbrev PhysicalCarrier := (Fin 2) × (Fin 2)
abbrev RecursiveCarrier := (Fin 3) × Unit

/-- These definitions retain the physical constructors; no scalar law is supplied. -/
def diagonalDistance (s : Schedule) : ℝ := outputDistance (Fin 2) (Fin 2) 2
  (FiniteNontracialMemoryReadout.keepTree s) (FiniteNontracialMemoryReadout.flipTree s)
  correlatedInput correlatedInput
def coherentDistance (s : Schedule) : ℝ := outputDistance (Fin 2) (Fin 2) 2
  (FiniteNontracialCoherentReadout.tree s) (FiniteNontracialCoherentReadout.tree s)
  (FiniteNontracialCoherentReadout.input qubitX) (FiniteNontracialCoherentReadout.input qubitY)
def diagonalError (s : Schedule) : ℝ := instrumentError
  (FiniteNontracialMemoryReadout.keepFamily s) (FiniteNontracialMemoryReadout.flipFamily s) correlationReadout
def coherentError (s : Schedule) : ℝ := instrumentError
  (FiniteNontracialCoherentReadout.family s qubitX) (FiniteNontracialCoherentReadout.family s qubitY)
  FiniteNontracialCoherentReadout.decisionReadout

theorem diagonal_value (s : Schedule) : diagonalDistance s=alpha s :=
  FiniteNontracialMemoryReadout.output_distance s
theorem coherent_value (s : Schedule) : coherentDistance s=beta s*invSqrtTwo :=
  FiniteNontracialCoherentReadout.tree_output_distance s
theorem diagonal_error_value (s : Schedule) : diagonalError s=(1-alpha s)/2 :=
  FiniteNontracialMemoryReadout.instrument_error s
theorem coherent_error_value (s : Schedule) : coherentError s=(1-beta s*invSqrtTwo)/2 :=
  FiniteNontracialCoherentReadout.decision_attains s

/-- Both operational values retain their independent physical upper and lower proofs. -/
theorem diagonal_independent_bounds (s : Schedule) :
    alpha s ≤ branchDistance (FiniteNontracialMemoryReadout.keepFamily s) (FiniteNontracialMemoryReadout.flipFamily s) ∧
    branchDistance (FiniteNontracialMemoryReadout.keepFamily s) (FiniteNontracialMemoryReadout.flipFamily s) ≤ alpha s :=
  ⟨FiniteNontracialMemoryReadout.distance_lower s,FiniteNontracialMemoryReadout.distance_upper s⟩
theorem coherent_independent_bounds (s : Schedule) :
    beta s*invSqrtTwo ≤ branchDistance (FiniteNontracialCoherentReadout.family s qubitX)
      (FiniteNontracialCoherentReadout.family s qubitY) ∧
    branchDistance (FiniteNontracialCoherentReadout.family s qubitX)
      (FiniteNontracialCoherentReadout.family s qubitY) ≤ beta s*invSqrtTwo :=
  ⟨FiniteNontracialCoherentReadout.observed_distance_lower s,
    FiniteNontracialCoherentReadout.observed_distance_upper s⟩

/-- Equality of proved real values; the operator and physical carriers remain separate. -/
theorem centered_norm_diagonal_compatibility (p : Gap) (rs : List Gap) (s : Schedule) (hp : 0<p.value) :
    ‖scheduleTransfer p rs s-historyScalarProjection p rs‖=diagonalDistance s := by
  rw [centered_opNorm p rs s hp,diagonal_value]
theorem coherent_trace_variation_compatibility (s : Schedule) :
    historyVariation (Fin 2) (Fin 2) 2 (FiniteNontracialCoherentReadout.tree s)
      (FiniteNontracialCoherentReadout.tree s) (FiniteNontracialCoherentReadout.input qubitX)
      (FiniteNontracialCoherentReadout.input qubitY)=coherentDistance s := by
  rw [coherent_value]; exact FiniteNontracialCoherentReadout.tree_history_variation s

/-- Actual quotient eigenvectors retain the two distinct physical decay factors. -/
theorem mode_actions (p : Gap) (rs : List Gap) (s : Schedule) :
    scheduleTransfer p rs s (historyCenteredVector p rs 2)=
      (diagonalDistance s:ℂ) • historyCenteredVector p rs 2 ∧
    scheduleTransfer p rs s (historyCenteredVector p rs 0)=
      (beta s:ℂ) • historyCenteredVector p rs 0 ∧
    scheduleTransfer p rs s (historyCenteredVector p rs 1)=
      (beta s:ℂ) • historyCenteredVector p rs 1 ∧
    scheduleTransfer p rs s (historyComplexVector p rs)=
      (beta s:ℂ) • historyComplexVector p rs := by
  rw [scheduleTransfer_effective,diagonal_value]
  simp only [historyTransfer_centered,historyTransfer_complex,
    show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide,if_true,if_false,mul_one,alpha,beta]
  trivial

/-- Full-time weighted mode norms, derived from the scheduled quotient action. -/
theorem weighted_mode_norms (p : Gap) (rs : List Gap) (s : Schedule) :
    ‖scheduleTransfer p rs s (historyCenteredVector p rs 2)‖^2=576*p.value^2*alpha s^2/625 ∧
    ‖scheduleTransfer p rs s (historyCenteredVector p rs 0)‖^2=24*p.value^2*beta s^2/25 ∧
    ‖scheduleTransfer p rs s (historyCenteredVector p rs 1)‖^2=24*p.value^2*beta s^2/25 ∧
    ‖scheduleTransfer p rs s (historyComplexVector p rs)‖^2=48*p.value^2*beta s^2/25 := by
  rcases full_mode_norms p rs s with ⟨hX,hY,hZ,hC⟩
  rw [hX,hY,hZ,hC]
  constructor; ring
  constructor; ring
  constructor <;> ring

/-- Typed scalar compatibility has explicit weighted coefficients, not norm identification. -/
theorem weighted_physical_values (p : Gap) (rs : List Gap) (s : Schedule) :
    ‖scheduleTransfer p rs s (historyCenteredVector p rs 2)‖^2=
      (576*p.value^2/625)*diagonalDistance s^2 ∧
    ‖scheduleTransfer p rs s (historyCenteredVector p rs 0)‖^2=
      (48*p.value^2/25)*coherentDistance s^2 ∧
    ‖scheduleTransfer p rs s (historyCenteredVector p rs 1)‖^2=
      (48*p.value^2/25)*coherentDistance s^2 ∧
    ‖scheduleTransfer p rs s (historyComplexVector p rs)‖^2=
      (96*p.value^2/25)*coherentDistance s^2 := by
  rcases full_mode_norms p rs s with ⟨hX,hY,hZ,hC⟩
  rw [hX,hY,hZ,hC,diagonal_value,coherent_value,mul_pow,invSqrtTwo_sq]
  constructor; rfl
  constructor; ring
  constructor <;> ring

/-- The negative quotient H is dual to the literal actual jump generator on all complex matrices. -/
theorem primitive_negative_generator (p : Gap) (rs : List Gap) (h : Slice)
    (z : HistorySpace p rs) (X : Mat2) :
    (historyCoordinates p rs z * OpenSystems.lindbladGenerator 0
      (SKEFTHawking.FinitePositiveKernel.GibbsBlockRelaxation.jumps NontracialReflectionDynamics.signature weights h.gamma h.eta) X).trace=
      (historyCoordinates p rs (-historyGenerator p rs h.gamma h.eta z)*X).trace :=
  primitive_generator_duality p rs h z X

theorem primitive_actual_propagator (h : Slice) (X : Mat2) :
    FiniteNontracialSchedule.state [h] X=OpenSystems.lindbladPropagatorAction 0
      (SKEFTHawking.FinitePositiveKernel.GibbsBlockRelaxation.jumps NontracialReflectionDynamics.signature weights h.gamma h.eta) h.duration X :=
  FiniteNontracialSchedule.singleton_propagator h X

/-- This is a primitive quotient orbit derivative, not a schedule switching-time derivative. -/
theorem primitive_negative_orbit (p : Gap) (rs : List Gap) (h : Slice) (u : ℝ) (z : HistorySpace p rs) :
    HasDerivAt (fun t : ℝ => historyTransfer p rs h.gamma h.eta t z)
      (-historyGenerator p rs h.gamma h.eta (historyTransfer p rs h.gamma h.eta u z)) u :=
  primitive_orbit_derivative p rs h u z

/-- Durations are literally halved in the same certified slice list. -/
theorem actual_half_factors (s : Schedule) :
    alpha (halfSchedule s)=√(diagonalDistance s) ∧ beta (halfSchedule s)=√(beta s) ∧
    coherentDistance (halfSchedule s)=√(beta s)*invSqrtTwo := by
  rw [diagonal_value,coherent_value,alpha_half,beta_half]
  exact ⟨rfl,rfl,rfl⟩
theorem actual_half_inserted_norm (p : Gap) (rs : List Gap) (s : Schedule) (z : HistorySpace p rs) :
    ‖toInserted p rs s z‖=‖scheduleTransfer p rs (halfSchedule s) z‖ :=
  inserted_norm_halfTransfer p rs s z

/-- The inserted metric has one damping factor, while the transferred metric has its square. -/
theorem inserted_mode_physical_values (p : Gap) (rs : List Gap) (s : Schedule) :
    ‖toInserted p rs s (historyCenteredVector p rs 2)‖^2=
      (576*p.value^2/625)*diagonalDistance s ∧
    ‖toInserted p rs s (historyCenteredVector p rs 0)‖^2=(24*p.value^2/25)*beta s ∧
    ‖toInserted p rs s (historyCenteredVector p rs 1)‖^2=(24*p.value^2/25)*beta s ∧
    ‖toInserted p rs s (historyComplexVector p rs)‖^2=(48*p.value^2/25)*beta s := by
  rcases inserted_mode_norms p rs s with ⟨hX,hY,hZ,hC⟩
  rw [hX,hY,hZ,hC,diagonal_value]
  exact ⟨rfl,rfl,rfl,rfl⟩

def ordinaryEffect (p : Gap) (rs : List Gap) (u : Labels rs) : Matrix ReflectionCarrier ReflectionCarrier ℂ :=
  FiniteAdaptiveProcessRobustness.effect (historyPositiveTree p rs) (PauliHistoryConsistency.indicatorScore u)
def scheduledEffect (p : Gap) (rs : List Gap) (s : Schedule) (u : Labels rs) : Matrix ReflectionCarrier ReflectionCarrier ℂ :=
  FiniteAdaptiveProcessRobustness.effect (positiveTree p s rs) (PauliHistoryConsistency.indicatorScore u)
def halfEffect (p : Gap) (rs : List Gap) (s : Schedule) (u : Labels rs) : Matrix ReflectionCarrier ReflectionCarrier ℂ :=
  FiniteAdaptiveProcessRobustness.effect (halfPositiveTree p s rs) (PauliHistoryConsistency.indicatorScore u)

/-- Three separately realized trees give three separately typed observable formulas. -/
theorem three_actual_effects (p : Gap) (rs : List Gap) (s : Schedule) (u : Labels rs) :
    ordinaryEffect p rs u=GibbsMultilevelReflection.joint (Psi p.value (historyEffect rs u)) ∧
    scheduledEffect p rs s u=GibbsMultilevelReflection.joint
      (Psi (p.value*p.value) (FiniteNontracialSchedule.observable s (historyEffect rs u))) ∧
    halfEffect p rs s u=GibbsMultilevelReflection.joint
      (FiniteNontracialSchedule.observable (halfSchedule s) (Psi p.value (historyEffect rs u))) :=
  ⟨ordinary_split_effect p rs u,unsplit_effect p rs s u,half_split_effect p rs s u⟩

/-- Every effect is bound to actual branch traces, including non-Hermitian inputs. -/
theorem three_all_complex_traces (p : Gap) (rs : List Gap) (s : Schedule) (u : Labels rs) (X : Mat2) :
    (run (Fin 2) Unit 6 (historyPositiveTree p rs) u (GibbsMultilevelReflection.joint X)).trace=
      (Psi p.value (historyEffect rs u)*X).trace ∧
    (run (Fin 2) Unit 6 (positiveTree p s rs) u (GibbsMultilevelReflection.joint X)).trace=
      (Psi (p.value*p.value) (FiniteNontracialSchedule.observable s (historyEffect rs u))*X).trace ∧
    (run (Fin 2) Unit 6 (halfPositiveTree p s rs) u (GibbsMultilevelReflection.joint X)).trace=
      (FiniteNontracialSchedule.observable (halfSchedule s) (Psi p.value (historyEffect rs u))*X).trace :=
  ⟨history_positive_trace p rs u X,positive_trace p rs s u X,half_positive_trace p rs s u X⟩

theorem full_half_metric_strict (p : Gap) (rs : List Gap) (s : Schedule)
    (hp : 0<p.value) (hdose : 0<G s+D s) :
    ‖scheduleTransfer p rs s (historyCenteredVector p rs 0)‖^2 <
      ‖toInserted p rs s (historyCenteredVector p rs 0)‖^2 ∧
    ‖toInserted p rs s (historyCenteredVector p rs 0)‖^2 < ‖historyCenteredVector p rs 0‖^2 :=
  ⟨full_x_lt_inserted p rs s hp hdose,inserted_x_lt_original p rs s hp hdose⟩

def zeroGap : Gap := ⟨0,le_refl 0,zero_le_one⟩

/-- The carriers have different finite cardinalities; arity six belongs to reflection trees. -/
theorem carrier_cardinalities :
    Fintype.card ReflectionCarrier=2 ∧ Fintype.card PhysicalCarrier=4 ∧ Fintype.card RecursiveCarrier=3 := by
  norm_num [ReflectionCarrier,PhysicalCarrier,RecursiveCarrier]
theorem reflection_physical_no_equiv : ¬Nonempty (ReflectionCarrier ≃ PhysicalCarrier) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  norm_num [ReflectionCarrier,PhysicalCarrier] at h
theorem reflection_recursive_no_equiv : ¬Nonempty (ReflectionCarrier ≃ RecursiveCarrier) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  norm_num [ReflectionCarrier,RecursiveCarrier] at h

/-- Independent reflection reset kills H and centered classes for every operational schedule. -/
theorem reflection_reset (p : Gap) (rs : List Gap) (s : Schedule) (hp : p.value=0) :
    historyScalarProjection p rs=1 ∧ historyDiagonalProjection p rs=1 ∧ scheduleTransfer p rs s=1 ∧
    historyGenerator p rs (G s) (D s)=0 ∧
    ‖scheduleTransfer p rs s-historyScalarProjection p rs‖=0 ∧
    (∀ a,historyCenteredVector p rs a=0) ∧ historyComplexVector p rs=0 :=
  ⟨historyScalarProjection_reset p rs hp,historyDiagonalProjection_reset p rs hp,
    reset_transfer p rs s hp,historyGenerator_reset p rs hp (G s) (D s),
    reset_centered_opNorm p rs s hp,(reset_centered_classes p rs hp).1,
    (reset_centered_classes p rs hp).2⟩

/-- Positive physical doses coexist with identity reflection transfer at p=0. -/
theorem reset_physical_positive_dose (p : Gap) (rs : List Gap) (s : Schedule)
    (hp : p.value=0) (hG : 0<G s) (hdose : 0<G s+D s) :
    ‖scheduleTransfer p rs s-historyScalarProjection p rs‖=0 ∧
    (0<diagonalDistance s ∧ diagonalDistance s<1) ∧
    (0<coherentDistance s ∧ coherentDistance s< invSqrtTwo) ∧
    (0<diagonalError s ∧ diagonalError s<1/2) := by
  have hc := FiniteNontracialSchedule.coefficients s
  have ha : 0<alpha s := hc.1.trans_le hc.2.1
  have ha1 : alpha s<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hG)
  have hb1 : beta s<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hdose)
  refine ⟨reset_centered_opNorm p rs s hp,?_,?_,?_⟩
  · rw [diagonal_value]; exact ⟨ha,ha1⟩
  · rw [coherent_value]
    refine ⟨mul_pos hc.1 invSqrtTwo_pos,?_⟩
    simpa only [one_mul] using mul_lt_mul_of_pos_right hb1 invSqrtTwo_pos
  · rw [diagonal_error_value]; constructor <;> linarith

/-- Concrete positive log-two doses give a nonzero two-qubit readout at reflection reset. -/
theorem reset_logTwo_witness (rs : List Gap) :
    0<G [FiniteNontracialSchedule.logTwoSlice] ∧ 0<D [FiniteNontracialSchedule.logTwoSlice] ∧
    scheduleTransfer zeroGap rs [FiniteNontracialSchedule.logTwoSlice]=1 ∧
    ‖scheduleTransfer zeroGap rs [FiniteNontracialSchedule.logTwoSlice]-historyScalarProjection zeroGap rs‖=0 ∧
    diagonalDistance [FiniteNontracialSchedule.logTwoSlice]=1/2 ∧
    coherentDistance [FiniteNontracialSchedule.logTwoSlice]=invSqrtTwo/4 ∧
    diagonalError [FiniteNontracialSchedule.logTwoSlice]=1/4 ∧
    coherentError [FiniteNontracialSchedule.logTwoSlice]=(1-invSqrtTwo/4)/2 := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨?_,?_,reset_transfer zeroGap rs _ rfl,reset_centered_opNorm zeroGap rs _ rfl,?_,?_,?_,?_⟩
  · simpa [G,FiniteNontracialSchedule.logTwoSlice] using hl
  · simpa [D,FiniteNontracialSchedule.logTwoSlice] using hl
  · rw [diagonal_value]; exact FiniteNontracialSchedule.logTwo_coefficients.1
  · rw [coherent_value,FiniteNontracialSchedule.logTwo_coefficients.2]; ring
  · rw [diagonal_error_value,FiniteNontracialSchedule.logTwo_coefficients.1]; norm_num
  · rw [coherent_error_value,FiniteNontracialSchedule.logTwo_coefficients.2]; ring

/-- A zero side gap retains positive inner witnesses whenever central retention is positive. -/
theorem zero_side_positive_witnesses (p : Gap) (hp : 0<p.value) :
    0<‖historyCenteredVector p [zeroGap] 0‖^2 ∧
    0<‖historyCenteredVector p [zeroGap] 2‖^2 ∧
    0<‖historyComplexVector p [zeroGap]‖^2 := by
  rw [(historyProjection_mode_norms p [zeroGap]).2.1,
    (historyProjection_mode_norms p [zeroGap]).2.2.2.1,
    (historyProjection_mode_norms p [zeroGap]).2.2.2.2]
  constructor; positivity
  constructor <;> positivity
theorem zero_side_centered_compatibility (p : Gap) (hp : 0<p.value) (s : Schedule) :
    ‖scheduleTransfer p [zeroGap] s-historyScalarProjection p [zeroGap]‖=diagonalDistance s :=
  centered_norm_diagonal_compatibility p [zeroGap] s hp

/-- Observable constant coordinates remain fixed; state coordinates change under reset dose. -/
theorem constant_observable_coordinates (p : Gap) (rs : List Gap) (s : Schedule) :
    historyCoordinates p rs (scheduleTransfer p rs s (historyConstantVector p rs))=1 ∧
    FiniteNontracialSchedule.observable s (1:Mat2)=1 := by
  have hc : historyCoordinates p rs (scheduleTransfer p rs s (historyConstantVector p rs))=1 := by
    rw [constant_fixed,historyConstantVector_coordinates]
  refine ⟨hc,?_⟩
  rw [scheduleTransfer_coordinates,historyConstantVector_coordinates] at hc
  exact hc

theorem constant_state_coordinates (s : Schedule) :
    FiniteNontracialSchedule.state s (1:Mat2)=
      (1-(alpha s:ℂ)) • ((2:ℂ) • rhoN)+(alpha s:ℂ) • (1:Mat2) := by
  rw [FiniteNontracialSchedule.state_formula]
  unfold FiniteNontracialSchedule.stateForm
  have ht : (1:Mat2).trace=2 := by norm_num [Matrix.trace,Fin.sum_univ_two,Matrix.one_apply]
  have hd : NontracialReflectionDynamics.diagonalPart (1:Mat2)=1 := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [NontracialReflectionDynamics.diagonalPart,Matrix.one_apply]
  rw [ht,hd,sub_self,smul_zero,add_zero]
  module

theorem state_observable_constant_distinct (p : Gap) (rs : List Gap) (s : Schedule) (hG : 0<G s) :
    FiniteNontracialSchedule.state s (1:Mat2)≠FiniteNontracialSchedule.observable s (1:Mat2) := by
  have h := constant_state_observable_guard p rs s hG
  rw [scheduleTransfer_coordinates,historyConstantVector_coordinates] at h
  exact h

/-- The actual weighted chronological metric differs from the one-sided state metric. -/
theorem weighted_state_metric_distinct (p : Gap) (rs : List Gap) (hp : p.value=1) :
    ‖historyCenteredVector p rs 0‖^2<(pauliX*rhoN*pauliXᴴ).trace.re :=
  metric_mismatch_guard p hp rs

/-- Even at the empty physical schedule, weighted mode norms are not the physical distances. -/
theorem weighted_physical_metric_distinct (p : Gap) (rs : List Gap) (hp : p.value=1) :
    ‖historyCenteredVector p rs 0‖^2≠coherentDistance [] ^ 2 ∧
    ‖historyCenteredVector p rs 2‖^2≠diagonalDistance [] ^ 2 := by
  rw [(historyProjection_mode_norms p rs).2.1,(historyProjection_mode_norms p rs).2.2.2.1,
    coherent_value,diagonal_value,hp,FiniteNontracialSchedule.beta_nil,FiniteNontracialSchedule.alpha_nil]
  norm_num [invSqrtTwo_sq]

/-- Both physical errors are attained by their actual instruments, with distinct decay rules. -/
theorem physical_attained_errors (s : Schedule) :
    diagonalError s=(1-diagonalDistance s)/2 ∧ coherentError s=(1-coherentDistance s)/2 := by
  rw [diagonal_error_value,coherent_error_value,diagonal_value,coherent_value]
  exact ⟨rfl,rfl⟩

/-- The bridge's inserted space remains tied to the actual chronological operational kernel. -/
theorem actual_kernel_pairing (p : Gap) (rs : List Gap) (s : Schedule) (F H : Labels rs → ℂ) :
    SKEFTHawking.FinitePositiveKernel.pairing (kernel p rs s) F H=
      ⟪SKEFTHawking.FinitePositiveKernel.mk _ (history_posSemidef p rs) F,
        scheduleTransfer p rs s (SKEFTHawking.FinitePositiveKernel.mk _ (history_posSemidef p rs) H)⟫_ℂ :=
  kernel_pairing p rs s F H

theorem actual_central_half_branches (p : Gap) (s : Schedule) (i : Fin 6) (X : Mat2) :
    (centralStep p s).branch (Fin 2) Unit 6 i (GibbsMultilevelReflection.joint X)=
      GibbsMultilevelReflection.joint (instrument.branch i (FiniteNontracialSchedule.state s (Phi (p.value*p.value) X))) ∧
    (splitStep p s).branch (Fin 2) Unit 6 i (GibbsMultilevelReflection.joint X)=
      GibbsMultilevelReflection.joint (instrument.branch i (FiniteNontracialSchedule.state (halfSchedule s) (Phi p.value X))) :=
  ⟨centralStep_branch p s i X,splitStep_branch p s i X⟩

/-- Off-diagonal observable action follows the actual composed channel formula. -/
theorem observable_offDiagonal (s : Schedule) (A : Mat2) :
    FiniteNontracialSchedule.observable s A 0 1=(beta s:ℂ)*A 0 1 := by
  rw [FiniteNontracialSchedule.observable_formula]
  simp [FiniteNontracialSchedule.observableForm,NontracialReflectionDynamics.diagonalPart]

theorem x_event_effect : historyEffect [] (0,())=(1/6:ℂ) • (1+pauliX) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [historyEffect,PauliInstrumentReconstruction.effect,PauliInstrumentReconstruction.projector,
      PauliInstrumentReconstruction.sign,PauliInstrumentReconstruction.outcomeEquiv,finProdFinEquiv,
      Fin.divNat,Fin.modNat,PauliInstrumentReconstruction.sigma,pauliX,Matrix.one_apply]

/-- Concrete literal entries distinguish all three actual effects at positive dose. -/
theorem three_effect_entries :
    ordinaryEffect PauliHistoryConsistency.identityGap [] (0,()) (0,()) (1,())=1/6 ∧
    scheduledEffect PauliHistoryConsistency.identityGap [] [FiniteNontracialSchedule.logTwoSlice]
      (0,()) (0,()) (1,())=1/24 ∧
    halfEffect PauliHistoryConsistency.identityGap [] [FiniteNontracialSchedule.logTwoSlice]
      (0,()) (0,()) (1,())=1/12 := by
  have ho := (three_actual_effects PauliHistoryConsistency.identityGap [] [FiniteNontracialSchedule.logTwoSlice] (0,())).1
  have hu := (three_actual_effects PauliHistoryConsistency.identityGap [] [FiniteNontracialSchedule.logTwoSlice] (0,())).2.1
  have hh := (three_actual_effects PauliHistoryConsistency.identityGap [] [FiniteNontracialSchedule.logTwoSlice] (0,())).2.2
  have hb : beta (halfSchedule [FiniteNontracialSchedule.logTwoSlice])=1/2 := by
    rw [beta_half,FiniteNontracialSchedule.logTwo_coefficients.2]; norm_num
  rw [ho,hu,hh]
  norm_num only [PauliHistoryConsistency.identityGap,mul_one,Psi_one,
    GibbsMultilevelReflection.joint,Matrix.kronecker_apply,Matrix.one_apply,if_true,mul_one]
  rw [observable_offDiagonal,observable_offDiagonal,x_event_effect]
  norm_num [FiniteNontracialSchedule.logTwo_coefficients.2,hb,pauliX,Matrix.one_apply]

theorem three_effects_distinct :
    ordinaryEffect PauliHistoryConsistency.identityGap [] (0,())≠
      scheduledEffect PauliHistoryConsistency.identityGap [] [FiniteNontracialSchedule.logTwoSlice] (0,()) ∧
    ordinaryEffect PauliHistoryConsistency.identityGap [] (0,())≠
      halfEffect PauliHistoryConsistency.identityGap [] [FiniteNontracialSchedule.logTwoSlice] (0,()) ∧
    scheduledEffect PauliHistoryConsistency.identityGap [] [FiniteNontracialSchedule.logTwoSlice] (0,())≠
      halfEffect PauliHistoryConsistency.identityGap [] [FiniteNontracialSchedule.logTwoSlice] (0,()) := by
  rcases three_effect_entries with ⟨ho,hu,hh⟩
  refine ⟨?_,?_,?_⟩
  · intro h; have he := congrArg (fun M : Matrix ReflectionCarrier ReflectionCarrier ℂ => M (0,()) (1,())) h
    rw [ho,hu] at he; norm_num at he
  · intro h; have he := congrArg (fun M : Matrix ReflectionCarrier ReflectionCarrier ℂ => M (0,()) (1,())) h
    rw [ho,hh] at he; norm_num at he
  · intro h; have he := congrArg (fun M : Matrix ReflectionCarrier ReflectionCarrier ℂ => M (0,()) (1,())) h
    rw [hu,hh] at he; norm_num at he

/-- Strict distinction guards are compatible with actual coincident zero-dose actions. -/
theorem zero_dose_consistency (p : Gap) (rs : List Gap) (s : Schedule) (hG : G s=0) (hD : D s=0) :
    (∀ X,FiniteNontracialSchedule.state s X=X ∧ FiniteNontracialSchedule.observable s X=X) ∧
    scheduleTransfer p rs s=1 ∧ diagonalDistance s=1 ∧ coherentDistance s=invSqrtTwo := by
  refine ⟨FiniteNontracialSchedule.zero_dose_actions s hG hD,?_,?_,?_⟩
  · rw [scheduleTransfer_effective,hG,hD,historyTransfer_rates_zero]
  · rw [diagonal_value]; simp [alpha,hG]
  · rw [coherent_value]; simp [beta,hG,hD]

end SKEFTHawking.QuantumNetwork.NontracialOperationalCompatibility
