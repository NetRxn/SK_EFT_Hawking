import SKEFTHawking.QuantumNetwork.FiniteNontracialThermalPhase
import SKEFTHawking.FiniteNontracialScheduleTransfer

/-! Phase transport on the original weighted history quotient. The representative
map uses raw synthesis and Pauli coefficients without dividing any retention.
The forward state phase and the observable phase have opposite signs. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.NontracialPhaseHistoryTransfer
open Matrix NontracialHistoryConsistency NontracialPauliReflection FinitePositiveKernel
open FiniteNontracialThermalPhase
open scoped BigOperators ComplexOrder InnerProductSpace

def rotationLinear (θ : ℝ) : Mat2 →ₗ[ℂ] Mat2 where
  toFun := C (-θ)
  map_add' := C_add (-θ)
  map_smul' := C_smul (-θ)

theorem C_Psi (θ q : ℝ) (A : Mat2) : C θ (Psi q A) = Psi q (C θ A) := by
  simp only [Psi, C_add, C_smul, C_one, C_weighted_trace]

theorem C_form (θ : ℝ) (A B : Mat2) : form (C θ A) (C θ B) = form A B := by
  unfold form
  rw [← C_adjoint, ← C_R θ, ← C_mul, ← C_mul, ← C_mul, C_trace]
  rw [C_R]

def rawPhase (rs : List Gap) (θ : ℝ) : (Labels rs → ℂ) →ₗ[ℂ] (Labels rs → ℂ) :=
  (historyInnerPullLinear rs).comp (NontracialReflectionDynamics.pauliCoefficients.comp
    ((rotationLinear θ).comp (historyRawSynthesisLinear rs)))

theorem rawPhase_synthesis (p : Gap) (rs : List Gap) (θ : ℝ) (F : Labels rs → ℂ) :
    historySynthesis p rs (rawPhase rs θ F) = C (-θ) (historySynthesis p rs F) := by
  change historySynthesis p rs (fun u => PauliInstrumentReconstruction.coefficients
    (C (-θ) (historyRawSynthesis rs F)) u.1) = _
  rw [historySynthesis_inner, PauliInstrumentReconstruction.synthesis_coefficients,
    ← C_Psi, history_synthesis_raw]

theorem rawPhase_pairing (p : Gap) (rs : List Gap) (θ : ℝ) (F H : Labels rs → ℂ) :
    pairing (historyKernel p rs) (rawPhase rs θ F) (rawPhase rs θ H) =
      pairing (historyKernel p rs) F H := by
  rw [history_pairing, history_pairing, rawPhase_synthesis, rawPhase_synthesis, C_form]

theorem rawPhase_inverse_null (p : Gap) (rs : List Gap) (θ : ℝ) (F : Labels rs → ℂ) :
    rawPhase rs θ (rawPhase rs (-θ) F) - F ∈
      nullSpace (historyKernel p rs) (history_posSemidef p rs) := by
  apply (mem_nullSpace_iff _ _ _).mpr
  rw [history_pairing, form_self_zero_iff]
  change historySynthesisLinear p rs (_ - F) = 0
  rw [map_sub]
  change historySynthesis p rs (rawPhase rs θ (rawPhase rs (-θ) F)) -
    historySynthesis p rs F = 0
  rw [rawPhase_synthesis, rawPhase_synthesis, neg_neg, C_inverse, sub_self]

/-- A genuine isometric equivalence of the old positive quotient, including reset. -/
def phaseIsometry (p : Gap) (rs : List Gap) (θ : ℝ) : HistorySpace p rs ≃ₗᵢ[ℂ] HistorySpace p rs :=
  descendUnitary (history_posSemidef p rs) (rawPhase rs θ) (rawPhase rs (-θ))
    (rawPhase_pairing p rs θ) (rawPhase_inverse_null p rs θ)

theorem phaseIsometry_mk (p : Gap) (rs : List Gap) (θ : ℝ) (F : Labels rs → ℂ) :
    phaseIsometry p rs θ (mk _ (history_posSemidef p rs) F) =
      mk _ (history_posSemidef p rs) (rawPhase rs θ F) :=
  descendUnitary_mk _ _ _ _ _ F

theorem phase_coordinates (p : Gap) (rs : List Gap) (θ : ℝ) (z : HistorySpace p rs) :
    historyCoordinates p rs (phaseIsometry p rs θ z) = C (-θ) (historyCoordinates p rs z) := by
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  rw [phaseIsometry_mk, historyCoordinates_mk, historyCoordinates_mk, rawPhase_synthesis]

theorem phase_inner (p : Gap) (rs : List Gap) (θ : ℝ) (z w : HistorySpace p rs) :
    ⟪phaseIsometry p rs θ z,phaseIsometry p rs θ w⟫_ℂ = ⟪z,w⟫_ℂ := by
  rw [history_coordinates_inner, history_coordinates_inner, phase_coordinates, phase_coordinates, C_form]

theorem phase_norm (p : Gap) (rs : List Gap) (θ : ℝ) (z : HistorySpace p rs) :
    ‖phaseIsometry p rs θ z‖ = ‖z‖ := (phaseIsometry p rs θ).norm_map z

theorem phase_continuous (p : Gap) (rs : List Gap) (θ : ℝ) : Continuous (phaseIsometry p rs θ) :=
  (phaseIsometry p rs θ).continuous

theorem phase_group (p : Gap) (rs : List Gap) (θ φ : ℝ) (z : HistorySpace p rs) :
    phaseIsometry p rs θ (phaseIsometry p rs φ z) = phaseIsometry p rs (θ+φ) z := by
  apply historyCoordinates_injective p rs
  simp only [phase_coordinates, neg_add, C_group]

theorem phase_zero (p : Gap) (rs : List Gap) (z : HistorySpace p rs) : phaseIsometry p rs 0 z = z := by
  apply historyCoordinates_injective p rs
  rw [phase_coordinates, neg_zero, C_zero]

theorem phase_inverse (p : Gap) (rs : List Gap) (θ : ℝ) (z : HistorySpace p rs) :
    phaseIsometry p rs (-θ) (phaseIsometry p rs θ z) = z := by
  rw [phase_group, neg_add_cancel, phase_zero]

theorem phase_reset (p : Gap) (rs : List Gap) (θ : ℝ) (hp : p.value=0) (z : HistorySpace p rs) :
    phaseIsometry p rs θ z = z := by
  apply historyCoordinates_injective p rs
  rw [phase_coordinates, history_coordinates_reset p hp, C_smul, C_one]

theorem phase_adjoint_inner (p : Gap) (rs : List Gap) (θ : ℝ) (z w : HistorySpace p rs) :
    ⟪phaseIsometry p rs θ z,w⟫_ℂ = ⟪z,phaseIsometry p rs (-θ) w⟫_ℂ := by
  have h := phase_inner p rs θ z (phaseIsometry p rs (-θ) w)
  rw [phase_group, add_neg_cancel, phase_zero] at h
  exact h

open NontracialScheduleTransfer

def phaseOperator (p : Gap) (rs : List Gap) (θ : ℝ) : HistorySpace p rs →L[ℂ] HistorySpace p rs :=
  (phaseIsometry p rs θ).toLinearIsometry.toContinuousLinearMap

def phaseTransfer (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    HistorySpace p rs →L[ℂ] HistorySpace p rs :=
  (phaseOperator p rs θ).comp (scheduleTransfer p rs s)

theorem schedule_observable_C (s : Schedule.Data) (θ : ℝ) (A : Mat2) :
    FiniteNontracialSchedule.observable s (C θ A) = C θ (FiniteNontracialSchedule.observable s A) := by
  rw [FiniteNontracialSchedule.observable_effective, FiniteNontracialSchedule.observable_effective]
  exact observable_C _ _ _ _ (FiniteNontracialSchedule.G_nonneg s)
    (FiniteNontracialSchedule.D_nonneg s) zero_le_one A

theorem phase_commute (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (z : HistorySpace p rs) :
    phaseIsometry p rs θ (scheduleTransfer p rs s z) = scheduleTransfer p rs s (phaseIsometry p rs θ z) := by
  apply historyCoordinates_injective p rs
  rw [phase_coordinates, scheduleTransfer_coordinates, scheduleTransfer_coordinates, phase_coordinates,
    schedule_observable_C]

theorem transfer_coordinates (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (z : HistorySpace p rs) :
    historyCoordinates p rs (phaseTransfer p rs s θ z) = freeObservable θ s (historyCoordinates p rs z) := by
  change historyCoordinates p rs (phaseIsometry p rs θ (scheduleTransfer p rs s z)) = _
  rw [phase_coordinates, scheduleTransfer_coordinates, free_observable, schedule_observable_C]

theorem schedule_symmetric (p : Gap) (rs : List Gap) (s : Schedule.Data) (z w : HistorySpace p rs) :
    ⟪scheduleTransfer p rs s z,w⟫_ℂ = ⟪z,scheduleTransfer p rs s w⟫_ℂ := by
  rw [scheduleTransfer_effective]
  exact (historyTransfer_positive p rs _ _ _ (FiniteNontracialSchedule.G_nonneg s)
    (FiniteNontracialSchedule.D_nonneg s) zero_le_one).isSymmetric z w

theorem transfer_adjoint_inner (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (z w : HistorySpace p rs) :
    ⟪phaseTransfer p rs s θ z,w⟫_ℂ = ⟪z,phaseTransfer p rs s (-θ) w⟫_ℂ := by
  change ⟪phaseIsometry p rs θ (scheduleTransfer p rs s z),w⟫_ℂ =
    ⟪z,phaseIsometry p rs (-θ) (scheduleTransfer p rs s w)⟫_ℂ
  rw [phase_adjoint_inner, schedule_symmetric, phase_commute]

theorem transfer_composition (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ φ : ℝ) (z : HistorySpace p rs) :
    phaseTransfer p rs s θ (phaseTransfer p rs s φ z) =
      phaseIsometry p rs (θ+φ) (scheduleTransfer p rs s (scheduleTransfer p rs s z)) := by
  change phaseIsometry p rs θ (scheduleTransfer p rs s
    (phaseIsometry p rs φ (scheduleTransfer p rs s z))) = _
  rw [← phase_commute, phase_group]

theorem transfer_normal (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (z : HistorySpace p rs) :
    phaseTransfer p rs s (-θ) (phaseTransfer p rs s θ z) = scheduleTransfer p rs s (scheduleTransfer p rs s z) ∧
    phaseTransfer p rs s θ (phaseTransfer p rs s (-θ) z) = scheduleTransfer p rs s (scheduleTransfer p rs s z) := by
  constructor <;> rw [transfer_composition] <;> simp only [neg_add_cancel, add_neg_cancel, phase_zero]

theorem transfer_inner (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (z w : HistorySpace p rs) :
    ⟪phaseTransfer p rs s θ z,phaseTransfer p rs s θ w⟫_ℂ =
      ⟪scheduleTransfer p rs s z,scheduleTransfer p rs s w⟫_ℂ :=
  phase_inner p rs θ _ _

theorem transfer_norm (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (z : HistorySpace p rs) :
    ‖phaseTransfer p rs s θ z‖ = ‖scheduleTransfer p rs s z‖ := phase_norm p rs θ _

theorem phase_scalar (p : Gap) (rs : List Gap) (θ : ℝ) (z : HistorySpace p rs) :
    phaseIsometry p rs θ (historyScalarProjection p rs z) = historyScalarProjection p rs z := by
  apply historyCoordinates_injective p rs
  rw [phase_coordinates, historyScalarProjection_coordinates]
  simp only [NontracialReflectionDynamics.scalarPart, C_smul, C_one]

theorem centered_factor (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    phaseTransfer p rs s θ-historyScalarProjection p rs =
      (phaseOperator p rs θ).comp (scheduleTransfer p rs s-historyScalarProjection p rs) := by
  ext z
  change phaseIsometry p rs θ (scheduleTransfer p rs s z)-historyScalarProjection p rs z =
    phaseIsometry p rs θ (scheduleTransfer p rs s z-historyScalarProjection p rs z)
  rw [map_sub, phase_scalar]

theorem centered_norm (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (hp : 0<p.value) :
    ‖phaseTransfer p rs s θ-historyScalarProjection p rs‖ = FiniteNontracialSchedule.alpha s := by
  rw [centered_factor, phaseOperator, LinearIsometry.norm_toContinuousLinearMap_comp, centered_opNorm p rs s hp]

theorem reset_centered_norm (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (hp : p.value=0) :
    ‖phaseTransfer p rs s θ-historyScalarProjection p rs‖ = 0 := by
  rw [centered_factor, phaseOperator, LinearIsometry.norm_toContinuousLinearMap_comp, reset_centered_opNorm p rs s hp]

theorem transfer_zero (p : Gap) (rs : List Gap) (s : Schedule.Data) : phaseTransfer p rs s 0 = scheduleTransfer p rs s := by
  ext z
  exact phase_zero p rs (scheduleTransfer p rs s z)

theorem transfer_reset (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (hp : p.value=0) :
    phaseTransfer p rs s θ = 1 := by
  ext z
  change phaseIsometry p rs θ (scheduleTransfer p rs s z) = z
  rw [reset_transfer p rs s hp]
  exact phase_reset p rs θ hp z


theorem exp_pos_phase (θ : ℝ) : Complex.exp (Complex.I*θ) =
    (Real.cos θ : ℂ)+(Real.sin θ : ℂ)*Complex.I := by
  rw [mul_comm, Complex.exp_ofReal_mul_I]
theorem exp_neg_phase (θ : ℝ) : Complex.exp (-(Complex.I*θ)) =
    (Real.cos θ : ℂ)-(Real.sin θ : ℂ)*Complex.I := by
  have h := exp_pos_phase (-θ)
  simpa [sub_eq_add_neg] using h

theorem rotation_X (θ : ℝ) : C (-θ) pauliX =
    (Real.cos θ : ℂ) • pauliX+(Real.sin θ : ℂ) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C_entry, pauliX, pauliY, exp_pos_phase, exp_neg_phase, sub_eq_add_neg]

theorem rotation_Y (θ : ℝ) : C (-θ) pauliY =
    -(Real.sin θ : ℂ) • pauliX+(Real.cos θ : ℂ) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C_entry, pauliX, pauliY, exp_pos_phase, exp_neg_phase] <;>
    ring_nf <;> simp [Complex.I_sq, sub_eq_add_neg]

theorem rotation_Z (θ : ℝ) : C (-θ) centeredZ = centeredZ := by
  rw [centeredZ_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C_entry]

theorem phase_X (p : Gap) (rs : List Gap) (θ : ℝ) :
    phaseIsometry p rs θ (historyCenteredVector p rs 0) =
      (Real.cos θ : ℂ) • historyCenteredVector p rs 0+
      (Real.sin θ : ℂ) • historyCenteredVector p rs 1 := by
  apply historyCoordinates_injective p rs
  simp only [phase_coordinates, map_add, map_smul, historyCenteredVector_coordinates]
  change C (-θ) ((p.value : ℂ) • pauliX) = _
  rw [C_smul, rotation_X]
  change _ = (Real.cos θ : ℂ) • ((p.value : ℂ) • pauliX)+
    (Real.sin θ : ℂ) • ((p.value : ℂ) • pauliY)
  module

theorem phase_Y (p : Gap) (rs : List Gap) (θ : ℝ) :
    phaseIsometry p rs θ (historyCenteredVector p rs 1) =
      -(Real.sin θ : ℂ) • historyCenteredVector p rs 0+
      (Real.cos θ : ℂ) • historyCenteredVector p rs 1 := by
  apply historyCoordinates_injective p rs
  simp only [phase_coordinates, map_add, map_smul, historyCenteredVector_coordinates]
  change C (-θ) ((p.value : ℂ) • pauliY) = _
  rw [C_smul, rotation_Y]
  change _ = -(Real.sin θ : ℂ) • ((p.value : ℂ) • pauliX)+
    (Real.cos θ : ℂ) • ((p.value : ℂ) • pauliY)
  module

theorem phase_Z (p : Gap) (rs : List Gap) (θ : ℝ) :
    phaseIsometry p rs θ (historyCenteredVector p rs 2) = historyCenteredVector p rs 2 := by
  apply historyCoordinates_injective p rs
  rw [phase_coordinates, historyCenteredVector_coordinates]
  change C (-θ) ((p.value : ℂ) • centeredZ) = _
  rw [C_smul, rotation_Z]
  rfl

theorem phase_constant (p : Gap) (rs : List Gap) (θ : ℝ) :
    phaseIsometry p rs θ (historyConstantVector p rs) = historyConstantVector p rs := by
  apply historyCoordinates_injective p rs
  rw [phase_coordinates, historyConstantVector_coordinates, C_one]

theorem schedule_mode (p : Gap) (rs : List Gap) (s : Schedule.Data) (a : Fin 3) :
    scheduleTransfer p rs s (historyCenteredVector p rs a) =
      ((if a=2 then FiniteNontracialSchedule.alpha s else FiniteNontracialSchedule.beta s) : ℂ) •
        historyCenteredVector p rs a := by
  rw [scheduleTransfer_effective, historyTransfer_centered]
  split_ifs <;> simp_all [FiniteNontracialSchedule.alpha,FiniteNontracialSchedule.beta]

theorem transfer_X (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    phaseTransfer p rs s θ (historyCenteredVector p rs 0) =
      (FiniteNontracialSchedule.beta s : ℂ) •
        ((Real.cos θ : ℂ) • historyCenteredVector p rs 0+
          (Real.sin θ : ℂ) • historyCenteredVector p rs 1) := by
  change phaseIsometry p rs θ (scheduleTransfer p rs s _) = _
  rw [schedule_mode]
  simp only [show (0 : Fin 3) ≠ 2 by decide, if_false, map_smul, phase_X]

theorem transfer_Y (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    phaseTransfer p rs s θ (historyCenteredVector p rs 1) =
      (FiniteNontracialSchedule.beta s : ℂ) •
        (-(Real.sin θ : ℂ) • historyCenteredVector p rs 0+
          (Real.cos θ : ℂ) • historyCenteredVector p rs 1) := by
  change phaseIsometry p rs θ (scheduleTransfer p rs s _) = _
  rw [schedule_mode]
  simp only [show (1 : Fin 3) ≠ 2 by decide, if_false, map_smul, phase_Y]

theorem transfer_Z (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    phaseTransfer p rs s θ (historyCenteredVector p rs 2) =
      (FiniteNontracialSchedule.alpha s : ℂ) • historyCenteredVector p rs 2 := by
  change phaseIsometry p rs θ (scheduleTransfer p rs s _) = _
  rw [schedule_mode]
  simp only [if_true, map_smul, phase_Z]

def conjugateCircularVector (p : Gap) (rs : List Gap) : HistorySpace p rs :=
  historyCenteredVector p rs 0-Complex.I • historyCenteredVector p rs 1

theorem phase_circular (p : Gap) (rs : List Gap) (θ : ℝ) :
    phaseIsometry p rs θ (historyComplexVector p rs) =
      Complex.exp (-Complex.I*θ) • historyComplexVector p rs := by
  apply historyCoordinates_injective p rs
  rw [phase_coordinates, map_smul, historyComplexVector_coordinates, C_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C_entry, pauliX, pauliY]
  ring

theorem phase_conjugate_circular (p : Gap) (rs : List Gap) (θ : ℝ) :
    phaseIsometry p rs θ (conjugateCircularVector p rs) =
      Complex.exp (Complex.I*θ) • conjugateCircularVector p rs := by
  apply historyCoordinates_injective p rs
  rw [phase_coordinates, map_smul]
  simp only [conjugateCircularVector, map_sub, map_smul, historyCenteredVector_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C_entry, modeMatrix, pauliX, pauliY]
  ring_nf
  simp [Complex.I_sq]

theorem transfer_circular (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    phaseTransfer p rs s θ (historyComplexVector p rs) =
      ((FiniteNontracialSchedule.beta s : ℂ)*Complex.exp (-Complex.I*θ)) • historyComplexVector p rs := by
  change phaseIsometry p rs θ (scheduleTransfer p rs s _) = _
  have h : scheduleTransfer p rs s (historyComplexVector p rs) =
      (FiniteNontracialSchedule.beta s : ℂ) • historyComplexVector p rs := by
    rw [historyComplexVector_decomposition, map_add, map_smul, schedule_mode, schedule_mode]
    simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, if_false]
    module
  rw [h, map_smul, phase_circular, smul_smul]

theorem transfer_conjugate_circular (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    phaseTransfer p rs s θ (conjugateCircularVector p rs) =
      ((FiniteNontracialSchedule.beta s : ℂ)*Complex.exp (Complex.I*θ)) • conjugateCircularVector p rs := by
  change phaseIsometry p rs θ (scheduleTransfer p rs s _) = _
  have h : scheduleTransfer p rs s (conjugateCircularVector p rs) =
      (FiniteNontracialSchedule.beta s : ℂ) • conjugateCircularVector p rs := by
    rw [conjugateCircularVector, map_sub, map_smul, schedule_mode, schedule_mode]
    simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, if_false]
    module
  rw [h, map_smul, phase_conjugate_circular, smul_smul]



open FiniteInterventionProcess

/-- Only the central channel changes: reset, noise, forward phase, instrument. -/
def centralKraus (p : Gap) (s : Schedule.Data) (θ : ℝ) :=
  composeKraus (phaseKraus θ) (resetScheduleKraus (PauliHistoryConsistency.squaredGap p) s)

theorem central_normalized (p : Gap) (s : Schedule.Data) (θ : ℝ) :
    IsKrausChannel (centralKraus p s θ) :=
  isKrausChannel_composeKraus (phase_normalized θ)
    (isKrausChannel_composeKraus (FiniteNontracialSchedule.normalized s)
      (channel_normalized (PauliHistoryConsistency.squaredGap p).nonnegative
        (PauliHistoryConsistency.squaredGap p).bounded))

theorem central_action (p : Gap) (s : Schedule.Data) (θ : ℝ) (X : Mat2) :
    krausMap (centralKraus p s θ) X =
      C θ (FiniteNontracialSchedule.state s (Phi (p.value*p.value) X)) := by
  rw [centralKraus, krausMap_composeKraus, phase_action, resetScheduleKraus,
    krausMap_composeKraus, channel_state (PauliHistoryConsistency.squaredGap p).nonnegative
      (PauliHistoryConsistency.squaredGap p).bounded]
  rfl

def centralStep (p : Gap) (s : Schedule.Data) (θ : ℝ) : Step (Fin 2) Unit 6 where
  count := _
  evolution k := GibbsMultilevelReflection.joint (centralKraus p s θ k)
  normalized := GibbsMultilevelReflection.joint_normalized _ (central_normalized p s θ)
  instrument := instrument

theorem central_branch (p : Gap) (s : Schedule.Data) (θ : ℝ) (i : Fin 6) (X : Mat2) :
    (centralStep p s θ).branch (Fin 2) Unit 6 i (GibbsMultilevelReflection.joint X) =
      GibbsMultilevelReflection.joint (instrument.branch i
        (C θ (FiniteNontracialSchedule.state s (Phi (p.value*p.value) X)))) := by
  change (instrument.lift Unit).branch i
    (krausMap (fun k => GibbsMultilevelReflection.joint (centralKraus p s θ k))
      (GibbsMultilevelReflection.joint X)) = _
  rw [GibbsMultilevelReflection.joint_kraus, central_action]
  exact GibbsMultilevelReflection.joint_kraus _ _

def positiveTree (p : Gap) (s : Schedule.Data) (θ : ℝ) :
    (rs : List Gap) → Tree (Fin 2) Unit 6 (rs.length+1)
  | [] => .node (centralStep p s θ) (fun _ => .done)
  | r::rs => .node (centralStep p s θ) (fun _ => historyPositiveTree r rs)

def reflectedTree (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    Tree (Fin 2) Unit 6 ((rs.length+1)+(rs.length+1)) :=
  PauliHistoryConsistency.appendTree (historyNegativeTree rs) (positiveTree p s θ rs)

/-- The operational kernel is defined by actual run weights, before any pairing law. -/
def kernel (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (u v : Labels rs) : ℂ :=
  (weight (Fin 2) Unit 6 (reflectedTree p rs s θ)
    (PauliHistoryConsistency.reflectedHistory rs u v) (GibbsMultilevelReflection.joint rhoN) : ℂ)

theorem actual_probabilities (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    (∀ h,0≤weight (Fin 2) Unit 6 (reflectedTree p rs s θ) h (GibbsMultilevelReflection.joint rhoN)) ∧
      (∑ h,weight (Fin 2) Unit 6 (reflectedTree p rs s θ) h (GibbsMultilevelReflection.joint rhoN))=1 :=
  normalized_weights (Fin 2) Unit 6 _ joint_density

theorem positive_trace (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (u : Labels rs) (X : Mat2) :
    (run (Fin 2) Unit 6 (positiveTree p s θ rs) u (GibbsMultilevelReflection.joint X)).trace =
      (Psi (p.value*p.value) (FiniteNontracialSchedule.observable s (C (-θ) (historyEffect rs u)))*X).trace := by
  cases rs with
  | nil =>
    rcases u with ⟨o,⟨⟩⟩
    simp only [positiveTree, run, central_branch, GibbsMultilevelReflection.joint_trace, branch_trace]
    rw [C_dual, FiniteNontracialSchedule.trace_dual, Phi_Psi_duality]
    rfl
  | cons r rs =>
    change (run (Fin 2) Unit 6 (historyPositiveTree r rs) u.2
      ((centralStep p s θ).branch (Fin 2) Unit 6 u.1 (GibbsMultilevelReflection.joint X))).trace = _
    rw [central_branch, history_positive_trace, trace_duality, C_dual,
      FiniteNontracialSchedule.trace_dual, Phi_Psi_duality]
    rfl

theorem reflected_trace (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (u v : Labels rs) :
    (run (Fin 2) Unit 6 (reflectedTree p rs s θ) (PauliHistoryConsistency.reflectedHistory rs u v)
      (GibbsMultilevelReflection.joint rhoN)).trace =
      (historyEffect rs v*C θ (FiniteNontracialSchedule.state s
        (Phi (p.value*p.value) (Gamma (historyEffect rs u))))).trace := by
  rw [reflectedTree, PauliHistoryConsistency.reflectedHistory, PauliHistoryConsistency.run_append,
    history_negative_run, positive_trace, ← Phi_Psi_duality, ← FiniteNontracialSchedule.trace_dual, ← C_dual]

theorem kernel_trace (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (u v : Labels rs) :
    kernel p rs s θ u v = (historyEffect rs v*C θ (FiniteNontracialSchedule.state s
      (Phi (p.value*p.value) (Gamma (historyEffect rs u))))).trace := by
  unfold kernel weight
  rw [reflected_trace]
  apply hermitian_product_real _ _ (historyEffect_adjoint rs v)
  have hB : (Phi (p.value*p.value) (Gamma (historyEffect rs u))).IsHermitian := by
    change _ᴴ = _
    rw [Phi_Gamma, Gamma_adjoint, Psi_adjoint, historyEffect_adjoint]
  exact (C_hermitian θ (krausMap_isHermitian _ hB)).eq

theorem schedule_Psi (p : ℝ) (s : Schedule.Data) (A : Mat2) :
    FiniteNontracialSchedule.observable s (Psi p A) =
      Psi p (FiniteNontracialSchedule.observable s A) := by
  rw [FiniteNontracialSchedule.observable_effective, FiniteNontracialSchedule.observable_effective]
  exact NontracialReflectionDynamics.observable_Psi p _ _ _
    (FiniteNontracialSchedule.G_nonneg s) (FiniteNontracialSchedule.D_nonneg s) zero_le_one A

theorem kernel_form (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (u v : Labels rs) :
    kernel p rs s θ u v =
      form (historyMidpoint p rs u) (C (-θ) (FiniteNontracialSchedule.observable s (historyMidpoint p rs v))) := by
  rw [kernel_trace, C_dual, FiniteNontracialSchedule.trace_dual, central_split]
  rw [form, historyMidpoint_adjoint]
  simp only [historyMidpoint, Gamma, Matrix.mul_assoc]
  rw [← schedule_Psi, ← C_Psi, schedule_observable_C]

theorem kernel_pairing (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (F H : Labels rs → ℂ) :
    pairing (kernel p rs s θ) F H =
      ⟪mk _ (history_posSemidef p rs) F,phaseTransfer p rs s θ (mk _ (history_posSemidef p rs) H)⟫_ℂ := by
  rw [history_coordinates_inner, transfer_coordinates, free_observable,
    historyCoordinates_mk, historyCoordinates_mk, schedule_observable_C]
  let L : Mat2 →ₗ[ℂ] Mat2 := (rotationLinear θ).comp
    (NontracialReflectionDynamics.observableLinear (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1)
  have hL (A : Mat2) : L A = C (-θ) (FiniteNontracialSchedule.observable s A) := by
    change C (-θ) (NontracialReflectionDynamics.observable _ _ _ A) = _
    rw [FiniteNontracialSchedule.observable_effective]
  simp_rw [← hL]
  simp only [historySynthesis, map_sum, map_smul, NontracialReflectionDynamics.form_sum_left,
    NontracialReflectionDynamics.form_sum_right, form_smul]
  simp only [pairing, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, kernel_form, ← hL]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring


theorem centered_inner (p : Gap) (rs : List Gap) (a b : Fin 3) :
    ⟪historyCenteredVector p rs a,historyCenteredVector p rs b⟫_ℂ =
      if a=b then (modeNorm a*p.value^2 : ℝ) else 0 := by
  rw [history_coordinates_inner, historyCenteredVector_coordinates, historyCenteredVector_coordinates,
    form_smul, modeMatrix_form]
  split_ifs <;> simp
  ring

theorem transfer_quarter_X (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    phaseTransfer p rs s (Real.pi/2) (historyCenteredVector p rs 0) =
      (FiniteNontracialSchedule.beta s : ℂ) • historyCenteredVector p rs 1 := by
  simp [transfer_X]
theorem transfer_quarter_Y (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    phaseTransfer p rs s (Real.pi/2) (historyCenteredVector p rs 1) =
      -(FiniteNontracialSchedule.beta s : ℂ) • historyCenteredVector p rs 0 := by
  simp [transfer_Y]
theorem transfer_half_X (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    phaseTransfer p rs s Real.pi (historyCenteredVector p rs 0) =
      -(FiniteNontracialSchedule.beta s : ℂ) • historyCenteredVector p rs 0 := by
  simp [transfer_X]

theorem quarter_inner_witnesses (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    ⟪phaseTransfer p rs s (Real.pi/2) (historyCenteredVector p rs 0),historyCenteredVector p rs 1⟫_ℂ =
      (FiniteNontracialSchedule.beta s*(24*p.value^2/25) : ℝ) ∧
    ⟪historyCenteredVector p rs 0,phaseTransfer p rs s (Real.pi/2) (historyCenteredVector p rs 1)⟫_ℂ =
      (-FiniteNontracialSchedule.beta s*(24*p.value^2/25) : ℝ) := by
  constructor
  · rw [transfer_quarter_X, inner_smul_left, centered_inner]
    norm_num [modeNorm]
    ring_nf
    simp
  · rw [transfer_quarter_Y, inner_smul_right, centered_inner]
    norm_num [modeNorm]
    ring_nf
    simp

theorem quarter_not_symmetric (p : Gap) (rs : List Gap) (s : Schedule.Data) (hp : 0<p.value) :
    ¬ (phaseTransfer p rs s (Real.pi/2)).toLinearMap.IsSymmetric := by
  intro h
  have he := h (historyCenteredVector p rs 0) (historyCenteredVector p rs 1)
  change ⟪phaseTransfer p rs s (Real.pi/2) (historyCenteredVector p rs 0),historyCenteredVector p rs 1⟫_ℂ =
    ⟪historyCenteredVector p rs 0,phaseTransfer p rs s (Real.pi/2) (historyCenteredVector p rs 1)⟫_ℂ at he
  rw [(quarter_inner_witnesses p rs s).1, (quarter_inner_witnesses p rs s).2] at he
  have heR := congrArg Complex.re he
  simp only [Complex.ofReal_re] at heR
  have hk : 0<FiniteNontracialSchedule.beta s := Real.exp_pos _
  nlinarith [sq_pos_of_pos hp]

theorem half_quadratic (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    (⟪historyCenteredVector p rs 0,phaseTransfer p rs s Real.pi (historyCenteredVector p rs 0)⟫_ℂ).re =
      -FiniteNontracialSchedule.beta s*(24*p.value^2/25) := by
  rw [transfer_half_X, inner_smul_right, centered_inner]
  norm_num [modeNorm, ← Complex.ofReal_pow, Complex.mul_re]
  ring_nf
  simp

theorem half_quadratic_negative (p : Gap) (rs : List Gap) (s : Schedule.Data) (hp : 0<p.value) :
    (⟪historyCenteredVector p rs 0,phaseTransfer p rs s Real.pi (historyCenteredVector p rs 0)⟫_ℂ).re < 0 := by
  rw [half_quadratic]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _)) (by positivity)

theorem transfer_constant (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    phaseTransfer p rs s θ (historyConstantVector p rs) = historyConstantVector p rs := by
  change phaseIsometry p rs θ (scheduleTransfer p rs s _) = _
  rw [constant_fixed, phase_constant]

theorem full_mode_norms (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    ‖phaseTransfer p rs s θ (historyCenteredVector p rs 0)‖^2 =
      (24*p.value^2/25)*FiniteNontracialSchedule.beta s^2 ∧
    ‖phaseTransfer p rs s θ (historyCenteredVector p rs 1)‖^2 =
      (24*p.value^2/25)*FiniteNontracialSchedule.beta s^2 ∧
    ‖phaseTransfer p rs s θ (historyCenteredVector p rs 2)‖^2 =
      (576*p.value^2/625)*FiniteNontracialSchedule.alpha s^2 ∧
    ‖phaseTransfer p rs s θ (historyComplexVector p rs)‖^2 =
      (48*p.value^2/25)*FiniteNontracialSchedule.beta s^2 := by
  simp only [transfer_norm]
  exact NontracialScheduleTransfer.full_mode_norms p rs s

theorem conjugate_circular_norm (p : Gap) (rs : List Gap) :
    ‖conjugateCircularVector p rs‖^2 = 48*p.value^2/25 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [conjugateCircularVector, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, centered_inner]
  norm_num [modeNorm, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im]
  ring

theorem conjugate_circular_transfer_norm (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    ‖phaseTransfer p rs s θ (conjugateCircularVector p rs)‖^2 =
      (48*p.value^2/25)*FiniteNontracialSchedule.beta s^2 := by
  rw [transfer_norm]
  have h : scheduleTransfer p rs s (conjugateCircularVector p rs) =
      (FiniteNontracialSchedule.beta s : ℂ) • conjugateCircularVector p rs := by
    rw [conjugateCircularVector, map_sub, map_smul, schedule_mode, schedule_mode]
    simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, if_false]
    module
  rw [h, norm_smul, mul_pow, conjugate_circular_norm]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring


theorem kernel_entry (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (u v : Labels rs) :
    kernel p rs s θ u v = ⟪historySingletonVector p rs u,
      phaseTransfer p rs s θ (historySingletonVector p rs v)⟫_ℂ := by
  rw [kernel_form, history_coordinates_inner, transfer_coordinates, free_observable,
    historySingletonVector_coordinates, historySingletonVector_coordinates, schedule_observable_C]

theorem singleton_x (p : Gap) :
    historySingletonVector p [] (0,()) = (1/6 : ℂ) •
      (historyConstantVector p []+historyCenteredVector p [] 0) := by
  apply historyCoordinates_injective p []
  rw [historySingletonVector_coordinates, map_smul, map_add,
    historyConstantVector_coordinates, historyCenteredVector_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [historyMidpoint, historyEffect, Psi, rhoN, modeMatrix,
      PauliInstrumentReconstruction.effect, PauliInstrumentReconstruction.projector,
      PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv,
      finProdFinEquiv, Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma,
      pauliX, Matrix.mul_apply, Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem singleton_y (p : Gap) :
    historySingletonVector p [] (2,()) = (1/6 : ℂ) •
      (historyConstantVector p []+historyCenteredVector p [] 1) := by
  apply historyCoordinates_injective p []
  rw [historySingletonVector_coordinates, map_smul, map_add,
    historyConstantVector_coordinates, historyCenteredVector_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [historyMidpoint, historyEffect, Psi, rhoN, modeMatrix,
      PauliInstrumentReconstruction.effect, PauliInstrumentReconstruction.projector,
      PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv,
      finProdFinEquiv, Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma,
      pauliX, pauliY, Matrix.mul_apply, Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem constant_inner (p : Gap) (rs : List Gap) :
    ⟪historyConstantVector p rs,historyConstantVector p rs⟫_ℂ = 1 := by
  rw [history_coordinates_inner, historyConstantVector_coordinates]
  norm_num [form_entries]

theorem constant_centered_inner (p : Gap) (rs : List Gap) (a : Fin 3) :
    ⟪historyConstantVector p rs,historyCenteredVector p rs a⟫_ℂ = 0 ∧
      ⟪historyCenteredVector p rs a,historyConstantVector p rs⟫_ℂ = 0 := by
  rw [history_coordinates_inner, history_coordinates_inner,
    historyConstantVector_coordinates, historyCenteredVector_coordinates]
  fin_cases a <;> constructor <;>
    norm_num [form_entries, modeMatrix, centeredZ_entries, pauliX, pauliY, Complex.star_def] <;> ring

theorem singleton_quarter_xy (p : Gap) (s : Schedule.Data) :
    kernel p [] s (Real.pi/2) (0,()) (2,()) =
      (1-(24/25 : ℂ)*(p.value : ℂ)^2*FiniteNontracialSchedule.beta s)/36 := by
  rw [kernel_entry, singleton_x, singleton_y, map_smul, map_add, transfer_constant, transfer_quarter_Y]
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    constant_inner, (constant_centered_inner p [] 0).1, (constant_centered_inner p [] 0).2, centered_inner]
  norm_num [modeNorm, map_ofNat]
  ring

theorem singleton_quarter_yx (p : Gap) (s : Schedule.Data) :
    kernel p [] s (Real.pi/2) (2,()) (0,()) =
      (1+(24/25 : ℂ)*(p.value : ℂ)^2*FiniteNontracialSchedule.beta s)/36 := by
  rw [kernel_entry, singleton_y, singleton_x, map_smul, map_add, transfer_constant, transfer_quarter_X]
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    constant_inner, (constant_centered_inner p [] 1).1, (constant_centered_inner p [] 1).2, centered_inner]
  norm_num [modeNorm, map_ofNat]
  ring


theorem quarter_not_selfAdjoint (p : Gap) (rs : List Gap) (s : Schedule.Data) (hp : 0<p.value) :
    ¬ IsSelfAdjoint (phaseTransfer p rs s (Real.pi/2)) :=
  fun h => quarter_not_symmetric p rs s hp h.isSymmetric

theorem quarter_strict_orientation (p : Gap) (s : Schedule.Data) (hp : 0<p.value) :
    (kernel p [] s (Real.pi/2) (0,()) (2,())).re <
      (kernel p [] s (Real.pi/2) (2,()) (0,())).re := by
  rw [singleton_quarter_xy, singleton_quarter_yx]
  norm_num [Complex.mul_re, Complex.div_re, ← Complex.ofReal_pow]
  have hk : 0<FiniteNontracialSchedule.beta s := Real.exp_pos _
  nlinarith [mul_pos (sq_pos_of_pos hp) hk]

theorem quarter_kernel_not_hermitian (p : Gap) (s : Schedule.Data) (hp : 0<p.value) :
    ¬ Matrix.IsHermitian (kernel p [] s (Real.pi/2)) := by
  intro h
  have he := congrArg (fun A : Matrix (Labels []) (Labels []) ℂ => (A (0,()) (2,())).re) h.eq
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re] at he
  exact (ne_of_lt (quarter_strict_orientation p s hp)) he.symm

theorem quarter_kernel_not_posSemidef (p : Gap) (s : Schedule.Data) (hp : 0<p.value) :
    ¬ Matrix.PosSemidef (kernel p [] s (Real.pi/2)) :=
  fun h => quarter_kernel_not_hermitian p s hp h.isHermitian

theorem C_half_opposite (A : Mat2) : C (-Real.pi) A = C Real.pi A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C_entry, exp_pos_phase, exp_neg_phase]

theorem transfer_half_opposite (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    phaseTransfer p rs s (-Real.pi) = phaseTransfer p rs s Real.pi := by
  ext z
  apply historyCoordinates_injective p rs
  simp only [transfer_coordinates, free_observable, neg_neg, C_half_opposite]

theorem half_symmetric (p : Gap) (rs : List Gap) (s : Schedule.Data) (z w : HistorySpace p rs) :
    ⟪phaseTransfer p rs s Real.pi z,w⟫_ℂ = ⟪z,phaseTransfer p rs s Real.pi w⟫_ℂ := by
  rw [transfer_adjoint_inner, transfer_half_opposite]

theorem half_kernel_hermitian (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    Matrix.IsHermitian (kernel p rs s Real.pi) := by
  ext u v
  simp only [Matrix.conjTranspose_apply, kernel_entry]
  change (starRingEnd ℂ) ⟪historySingletonVector p rs v,phaseTransfer p rs s Real.pi (historySingletonVector p rs u)⟫_ℂ = _
  rw [inner_conj_symm]
  exact half_symmetric p rs s _ _

theorem half_coefficient_quadratic (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    (pairing (kernel p rs s Real.pi) (historyCenteredCoefficients rs 0)
      (historyCenteredCoefficients rs 0)).re = -FiniteNontracialSchedule.beta s*(24*p.value^2/25) := by
  rw [kernel_pairing]
  exact half_quadratic p rs s

theorem half_kernel_not_posSemidef (p : Gap) (rs : List Gap) (s : Schedule.Data) (hp : 0<p.value) :
    ¬ Matrix.PosSemidef (kernel p rs s Real.pi) := by
  intro h
  have hn := (h.dotProduct_mulVec_nonneg (historyCenteredCoefficients rs 0)).1
  change 0 ≤ (pairing (kernel p rs s Real.pi) _ _).re at hn
  rw [kernel_pairing] at hn
  exact (not_le_of_gt (half_quadratic_negative p rs s hp)) hn

theorem quarter_empty_exact (p : Gap) (hp : p.value=1) :
    kernel p [] [] (Real.pi/2) (0,()) (2,())=1/900 ∧
      kernel p [] [] (Real.pi/2) (2,()) (0,())=49/900 := by
  rw [singleton_quarter_xy, singleton_quarter_yx]
  norm_num [hp, FiniteNontracialSchedule.beta, FiniteNontracialSchedule.G, FiniteNontracialSchedule.D]

theorem quarter_logTwo_exact (p : Gap) (hp : p.value=1) :
    kernel p [] [FiniteNontracialSchedule.logTwoSlice] (Real.pi/2) (0,()) (2,())=19/900 ∧
      kernel p [] [FiniteNontracialSchedule.logTwoSlice] (Real.pi/2) (2,()) (0,())=31/900 := by
  rw [singleton_quarter_xy, singleton_quarter_yx, FiniteNontracialSchedule.logTwo_coefficients.2]
  norm_num [hp]

theorem positive_effect (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (u : Labels rs) :
    FiniteAdaptiveProcessRobustness.effect (positiveTree p s θ rs)
      (PauliHistoryConsistency.indicatorScore u) =
      GibbsMultilevelReflection.joint
        (Psi (p.value*p.value) (FiniteNontracialSchedule.observable s (C (-θ) (historyEffect rs u)))) := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  obtain ⟨Y,rfl⟩ := PauliHistoryConsistency.joint_surjective X
  rw [PauliHistoryConsistency.effect_complex_trace]
  simp only [PauliHistoryConsistency.indicatorScore,apply_ite,ite_mul,Complex.ofReal_one,
    Complex.ofReal_zero,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [positive_trace]
  rw [GibbsMultilevelReflection.joint,GibbsMultilevelReflection.joint,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.trace_kronecker]
  simp [Matrix.trace]

theorem transfer_zero_positive (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    (phaseTransfer p rs s 0).IsPositive := by
  rw [transfer_zero, scheduleTransfer_effective]
  exact historyTransfer_positive p rs _ _ _ (FiniteNontracialSchedule.G_nonneg s)
    (FiniteNontracialSchedule.D_nonneg s) zero_le_one

theorem transfer_zero_selfAdjoint (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    IsSelfAdjoint (phaseTransfer p rs s 0) := (transfer_zero_positive p rs s).isSelfAdjoint

theorem phase_period (p : Gap) (rs : List Gap) (θ : ℝ) (z : HistorySpace p rs) :
    phaseIsometry p rs (θ+2*Real.pi) z = phaseIsometry p rs θ z := by
  apply historyCoordinates_injective p rs
  rw [phase_coordinates, phase_coordinates]
  have h := C_periodic (-(θ+2*Real.pi)) (historyCoordinates p rs z)
  have he : -(θ+2*Real.pi)+2*Real.pi = -θ := by ring
  rw [he] at h
  exact h.symm

theorem transfer_period (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    phaseTransfer p rs s (θ+2*Real.pi) = phaseTransfer p rs s θ := by
  ext z
  exact phase_period p rs θ _

theorem transfer_empty (p : Gap) (rs : List Gap) (θ : ℝ) :
    phaseTransfer p rs [] θ = phaseOperator p rs θ := by
  ext z
  rfl

theorem zero_dose_transfer (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ)
    (hG : FiniteNontracialSchedule.G s=0) (hD : FiniteNontracialSchedule.D s=0) :
    phaseTransfer p rs s θ = phaseOperator p rs θ := by
  ext z
  apply historyCoordinates_injective p rs
  rw [transfer_coordinates, free_observable, (FiniteNontracialSchedule.zero_dose_actions s hG hD _).2]
  exact (phase_coordinates p rs θ z).symm

theorem zero_duration_transfer (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ)
    (hz : ∀ h∈s,h.duration=0) : phaseTransfer p rs s θ = phaseOperator p rs θ :=
  zero_dose_transfer p rs s θ (FiniteNontracialSchedule.zero_duration_doses s hz).1
    (FiniteNontracialSchedule.zero_duration_doses s hz).2

theorem zero_rate_transfer (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ)
    (hz : ∀ h∈s,h.gamma=0 ∧ h.eta=0) : phaseTransfer p rs s θ = phaseOperator p rs θ :=
  zero_dose_transfer p rs s θ (FiniteNontracialSchedule.zero_rate_doses s hz).1
    (FiniteNontracialSchedule.zero_rate_doses s hz).2

theorem reset_centered_null (p : Gap) (rs : List Gap) (hp : p.value=0) (a : Fin 3) :
    historyCenteredVector p rs a = 0 := by
  apply historyCoordinates_injective p rs
  rw [historyCenteredVector_coordinates, hp, Complex.ofReal_zero, zero_smul, map_zero]

theorem reset_circular_null (p : Gap) (rs : List Gap) (hp : p.value=0) :
    historyComplexVector p rs=0 ∧ conjugateCircularVector p rs=0 := by
  simp [historyComplexVector_decomposition, conjugateCircularVector, reset_centered_null p rs hp]

theorem constant_norm (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    ‖phaseTransfer p rs s θ (historyConstantVector p rs)‖=1 := by
  rw [transfer_constant, historyConstantVector_norm]

theorem metric_guard (p : Gap) (hp : p.value=1) (rs : List Gap) :
    ‖historyCenteredVector p rs 0‖^2 < (pauliX*rhoN*pauliXᴴ).trace.re :=
  NontracialScheduleTransfer.metric_mismatch_guard p hp rs

/-- This is algebra on arbitrary complex coordinates, not a density or effect. -/
theorem imaginary_coordinate_guard :
    ¬ (Complex.I • FiniteGibbsClock.E01).IsHermitian ∧
    ¬ (Complex.I • FiniteGibbsClock.E01).PosSemidef ∧
    ¬ IsDensityOperator (Complex.I • FiniteGibbsClock.E01) :=
  ⟨iE01_not_hermitian,iE01_not_posSemidef,iE01_not_density⟩


theorem phase_adjoint (p : Gap) (rs : List Gap) (θ : ℝ) :
    (phaseOperator p rs θ).adjoint = phaseOperator p rs (-θ) := by
  ext z
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact phase_adjoint_inner p rs θ w z

theorem transfer_adjoint (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    (phaseTransfer p rs s θ).adjoint = phaseTransfer p rs s (-θ) := by
  ext z
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, transfer_adjoint_inner]

theorem transfer_adjoint_mul (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    (phaseTransfer p rs s θ).adjoint * phaseTransfer p rs s θ =
      scheduleTransfer p rs s * scheduleTransfer p rs s ∧
    phaseTransfer p rs s θ * (phaseTransfer p rs s θ).adjoint =
      scheduleTransfer p rs s * scheduleTransfer p rs s := by
  rw [transfer_adjoint]
  constructor
  · ext z; exact (transfer_normal p rs s θ z).1
  · ext z; exact (transfer_normal p rs s θ z).2

theorem half_selfAdjoint (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    IsSelfAdjoint (phaseTransfer p rs s Real.pi) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro z w
  exact half_symmetric p rs s z w

theorem quarter_kernel_not_hermitian_all_depths (p : Gap) (rs : List Gap)
    (s : Schedule.Data) (hp : 0<p.value) :
    ¬ Matrix.IsHermitian (kernel p rs s (Real.pi/2)) := by
  intro h
  apply quarter_not_symmetric p rs s hp
  intro z w
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  obtain ⟨H,rfl⟩ := mk_surjective _ _ w
  change ⟪phaseTransfer p rs s (Real.pi/2) (mk _ (history_posSemidef p rs) F),
    mk _ (history_posSemidef p rs) H⟫_ℂ =
      ⟪mk _ (history_posSemidef p rs) F,phaseTransfer p rs s (Real.pi/2) (mk _ (history_posSemidef p rs) H)⟫_ℂ
  rw [← kernel_pairing]
  have hc : star (pairing (kernel p rs s (Real.pi/2)) H F) =
      pairing (kernel p rs s (Real.pi/2)) F H := by
    unfold pairing
    rw [← star_dotProduct, star_mulVec, h.eq, dotProduct_mulVec]
  rw [kernel_pairing] at hc
  change (starRingEnd ℂ) ⟪mk _ (history_posSemidef p rs) H,
    phaseTransfer p rs s (Real.pi/2) (mk _ (history_posSemidef p rs) F)⟫_ℂ = _ at hc
  rw [inner_conj_symm] at hc
  exact hc

theorem quarter_kernel_not_posSemidef_all_depths (p : Gap) (rs : List Gap)
    (s : Schedule.Data) (hp : 0<p.value) :
    ¬ Matrix.PosSemidef (kernel p rs s (Real.pi/2)) :=
  fun h => quarter_kernel_not_hermitian_all_depths p rs s hp h.isHermitian

theorem kernel_real (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (u v : Labels rs) :
    (kernel p rs s θ u v).im = 0 := by
  simp only [kernel, Complex.ofReal_im]

theorem kernel_nonnegative (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (u v : Labels rs) :
    0 ≤ (kernel p rs s θ u v).re :=
  (actual_probabilities p rs s θ).1 _

theorem central_density (p : Gap) (s : Schedule.Data) (θ : ℝ) {X : Mat2}
    (hX : IsDensityOperator X) :
    IsDensityOperator (C θ (FiniteNontracialSchedule.state s (Phi (p.value*p.value) X))) := by
  rw [← central_action]
  exact krausMap_isDensityOperator (central_normalized p s θ) hX

theorem central_joint_normalized (p : Gap) (s : Schedule.Data) (θ : ℝ) :
    IsKrausChannel (fun k => GibbsMultilevelReflection.joint (centralKraus p s θ k)) :=
  GibbsMultilevelReflection.joint_normalized _ (central_normalized p s θ)

/-- The same central channel retains complete positivity on every finite spectator. -/
theorem central_complete_positive (p : Gap) (s : Schedule.Data) (θ : ℝ) (n : ℕ)
    {X : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ} (hX : X.PosSemidef) :
    (krausMap (fun k => (centralKraus p s θ k).kronecker (1 : Matrix (Fin n) (Fin n) ℂ)) X).PosSemidef :=
  krausMap_posSemidef _ hX


theorem phase_diagonal (p : Gap) (rs : List Gap) (θ : ℝ) (z : HistorySpace p rs) :
    phaseIsometry p rs θ (historyDiagonalProjection p rs z) = historyDiagonalProjection p rs z := by
  apply historyCoordinates_injective p rs
  rw [phase_coordinates, historyDiagonalProjection_coordinates, C_diagonalPart]

theorem phase_scalar_commute (p : Gap) (rs : List Gap) (θ : ℝ) (z : HistorySpace p rs) :
    historyScalarProjection p rs (phaseIsometry p rs θ z) = historyScalarProjection p rs z := by
  apply historyCoordinates_injective p rs
  rw [historyScalarProjection_coordinates, historyScalarProjection_coordinates, phase_coordinates]
  simp only [NontracialReflectionDynamics.scalarPart, C_weighted_trace]

theorem phase_diagonal_commute (p : Gap) (rs : List Gap) (θ : ℝ) (z : HistorySpace p rs) :
    historyDiagonalProjection p rs (phaseIsometry p rs θ z) = historyDiagonalProjection p rs z := by
  apply historyCoordinates_injective p rs
  rw [historyDiagonalProjection_coordinates, historyDiagonalProjection_coordinates, phase_coordinates, diagonalPart_C]

theorem kernel_zero (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    kernel p rs s 0 = NontracialScheduleTransfer.kernel p rs s := by
  ext u v
  rw [kernel_trace, C_zero, NontracialScheduleTransfer.kernel_trace]

theorem kernel_period (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    kernel p rs s (θ+2*Real.pi) = kernel p rs s θ := by
  ext u v
  rw [kernel_trace, kernel_trace, C_periodic]

theorem kernel_reset (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) (hp : p.value=0) :
    kernel p rs s θ = historyKernel p rs := by
  ext u v
  rw [kernel_entry, transfer_reset p rs s θ hp]
  change ⟪historySingletonVector p rs u,historySingletonVector p rs v⟫_ℂ = _
  rw [history_coordinates_inner, historySingletonVector_coordinates, historySingletonVector_coordinates,
    history_kernel_form]

theorem kernel_normalized (p : Gap) (rs : List Gap) (s : Schedule.Data) (θ : ℝ) :
    (∑ u,∑ v,(kernel p rs s θ u v).re) = 1 := by
  have h : pairing (kernel p rs s θ) (fun _ => 1) (fun _ => 1) = 1 := by
    rw [kernel_pairing]
    change ⟪historyConstantVector p rs,phaseTransfer p rs s θ (historyConstantVector p rs)⟫_ℂ = _
    rw [transfer_constant, constant_inner]
  have hr := congrArg Complex.re h
  simpa [pairing,dotProduct,Matrix.mulVec] using hr

theorem central_branch_trace (p : Gap) (s : Schedule.Data) (θ : ℝ) (i : Fin 6) (A X : Mat2) :
    (A*instrument.branch i (C θ (FiniteNontracialSchedule.state s (Phi (p.value*p.value) X)))).trace =
      (Psi (p.value*p.value) (FiniteNontracialSchedule.observable s (C (-θ) (J i A)))*X).trace := by
  rw [trace_duality, C_dual, FiniteNontracialSchedule.trace_dual, Phi_Psi_duality]

theorem central_timed_correspondence (p : Gap) (s : Schedule.Data) (b ℏ : ℝ) (X : Mat2) :
    krausMap (centralKraus p s (totalPhase b ℏ s)) X =
      timedState b ℏ s (Phi (p.value*p.value) X) := by
  rw [central_action, timed_factor]

theorem transfer_timed_coordinates (p : Gap) (rs : List Gap) (s : Schedule.Data) (b ℏ : ℝ)
    (z : HistorySpace p rs) :
    historyCoordinates p rs (phaseTransfer p rs s (totalPhase b ℏ s) z) =
      timedObservable b ℏ s (historyCoordinates p rs z) := by
  rw [transfer_coordinates, free_observable, timed_observable_factor]

theorem timed_zero_duration_identity (p : Gap) (rs : List Gap) (s : Schedule.Data) (b ℏ : ℝ)
    (hz : ∀ h∈s,h.duration=0) : phaseTransfer p rs s (totalPhase b ℏ s) = 1 := by
  ext z
  apply historyCoordinates_injective p rs
  rw [transfer_timed_coordinates, (timed_zero_durations b ℏ s hz _).2]
  rfl

theorem half_logTwo_quadratic (p : Gap) (rs : List Gap) (hp : p.value=1) :
    (pairing (kernel p rs [FiniteNontracialSchedule.logTwoSlice] Real.pi)
      (historyCenteredCoefficients rs 0) (historyCenteredCoefficients rs 0)).re = -6/25 := by
  rw [half_coefficient_quadratic, FiniteNontracialSchedule.logTwo_coefficients.2, hp]
  norm_num

theorem zero_side_quarter_witness (p : Gap) (s : Schedule.Data) (n : ℕ) (hp : 0<p.value) :
    ¬ IsSelfAdjoint (phaseTransfer p
      (List.replicate n (⟨0,le_rfl,zero_le_one⟩ : Gap)) s (Real.pi/2)) :=
  quarter_not_selfAdjoint p _ s hp

end SKEFTHawking.QuantumNetwork.NontracialPhaseHistoryTransfer
