import SKEFTHawking.QuantumNetwork.FiniteNontracialSchedule
import SKEFTHawking.QuantumNetwork.FiniteNontracialInterventionProcess

/-! Actual finite schedules on the accepted weighted history quotient.
Reflection trees use (Fin 2) × Unit and six outcomes. The two-qubit memory
and the (Fin 3) × Unit recursive consumer have separate carriers and metrics.
No physical readout law or switching-time derivative is supplied here.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.NontracialScheduleTransfer
open Matrix FiniteInterventionProcess NontracialHistoryConsistency NontracialPauliReflection
open FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace
namespace Schedule
abbrev Slice := FiniteNontracialSchedule.Slice
abbrev Data := FiniteNontracialSchedule.Schedule
end Schedule

/-- State chronology is head first; the dual product pulls back the tail first. -/
def scheduleTransfer (p : Gap) (rs : List Gap) : Schedule.Data →
    HistorySpace p rs →L[ℂ] HistorySpace p rs
  | [] => 1
  | h :: t => (historyTransfer p rs h.gamma h.eta h.duration).comp
      (scheduleTransfer p rs t)

theorem scheduleTransfer_coordinates (p : Gap) (rs : List Gap) (s : Schedule.Data)
    (z : HistorySpace p rs) :
    historyCoordinates p rs (scheduleTransfer p rs s z) =
      FiniteNontracialSchedule.observable s (historyCoordinates p rs z) := by
  induction s with
  | nil => simp [scheduleTransfer]
  | cons h t ih =>
    change historyCoordinates p rs
      (historyTransfer p rs h.gamma h.eta h.duration (scheduleTransfer p rs t z)) = _
    rw [historyTransfer_coordinates p rs h.gamma h.eta h.duration h.gamma_nonneg
      h.eta_nonneg h.duration_nonneg, ih, FiniteNontracialSchedule.observable_cons]

/-- Derived from the actual schedule's observable action, including central reset. -/
theorem scheduleTransfer_effective (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    scheduleTransfer p rs s = historyTransfer p rs
      (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1 := by
  ext z
  apply historyCoordinates_injective p rs
  rw [scheduleTransfer_coordinates, historyTransfer_coordinates p rs
    (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
    (FiniteNontracialSchedule.G_nonneg s) (FiniteNontracialSchedule.D_nonneg s) zero_le_one,
    FiniteNontracialSchedule.observable_effective]

theorem scheduleTransfer_append (p : Gap) (rs : List Gap) (s t : Schedule.Data)
    (z : HistorySpace p rs) :
    scheduleTransfer p rs (s ++ t) z = scheduleTransfer p rs s (scheduleTransfer p rs t z) := by
  apply historyCoordinates_injective p rs
  simp only [scheduleTransfer_coordinates, FiniteNontracialSchedule.observable_append]

/-- Each primitive keeps the negative observable generator and actual GKSL predual. -/
theorem primitive_generator_duality (p : Gap) (rs : List Gap) (h : Schedule.Slice)
    (z : HistorySpace p rs) (X : Mat2) :
    (historyCoordinates p rs z * FiniteNontracialSchedule.generator h.gamma h.eta X).trace =
      (historyCoordinates p rs (-historyGenerator p rs h.gamma h.eta z)*X).trace :=
  history_quotient_generator_GKSL p rs h.gamma h.eta h.gamma_nonneg h.eta_nonneg z X

/-- Analytic primitive quotient orbit; no derivative through schedule switching times. -/
theorem primitive_orbit_derivative (p : Gap) (rs : List Gap) (h : Schedule.Slice)
    (u : ℝ) (z : HistorySpace p rs) :
    HasDerivAt (fun t : ℝ => historyTransfer p rs h.gamma h.eta t z)
      (-historyGenerator p rs h.gamma h.eta (historyTransfer p rs h.gamma h.eta u z)) u :=
  history_orbit_hasDerivAt p rs h.gamma h.eta u z

def halfSlice (h : Schedule.Slice) : Schedule.Slice :=
  ⟨h.gamma,h.eta,h.duration/2,h.gamma_nonneg,h.eta_nonneg,div_nonneg h.duration_nonneg (by norm_num)⟩
def halfSchedule (s : Schedule.Data) : Schedule.Data := s.map halfSlice

theorem G_half (s : Schedule.Data) :
    FiniteNontracialSchedule.G (halfSchedule s) = FiniteNontracialSchedule.G s / 2 := by
  induction s with
  | nil => simp [halfSchedule,FiniteNontracialSchedule.G]
  | cons h t ih =>
    change h.gamma*(h.duration/2)+FiniteNontracialSchedule.G (halfSchedule t) =
      (h.gamma*h.duration+FiniteNontracialSchedule.G t)/2
    rw [ih]; ring
theorem D_half (s : Schedule.Data) :
    FiniteNontracialSchedule.D (halfSchedule s) = FiniteNontracialSchedule.D s / 2 := by
  induction s with
  | nil => simp [halfSchedule,FiniteNontracialSchedule.D]
  | cons h t ih =>
    change h.eta*(h.duration/2)+FiniteNontracialSchedule.D (halfSchedule t) =
      (h.eta*h.duration+FiniteNontracialSchedule.D t)/2
    rw [ih]; ring

theorem alpha_half_sq (s : Schedule.Data) :
    FiniteNontracialSchedule.alpha (halfSchedule s)^2 = FiniteNontracialSchedule.alpha s := by
  simp only [FiniteNontracialSchedule.alpha,G_half,pow_two,← Real.exp_add]
  congr 1; ring
theorem beta_half_sq (s : Schedule.Data) :
    FiniteNontracialSchedule.beta (halfSchedule s)^2 = FiniteNontracialSchedule.beta s := by
  simp only [FiniteNontracialSchedule.beta,G_half,D_half,pow_two,← Real.exp_add]
  congr 1; ring
theorem alpha_half (s : Schedule.Data) :
    FiniteNontracialSchedule.alpha (halfSchedule s) = √(FiniteNontracialSchedule.alpha s) := by
  calc
    _ = √(FiniteNontracialSchedule.alpha (halfSchedule s)^2) :=
      (Real.sqrt_sq (Real.exp_pos _).le).symm
    _ = _ := congrArg Real.sqrt (alpha_half_sq s)
theorem beta_half (s : Schedule.Data) :
    FiniteNontracialSchedule.beta (halfSchedule s) = √(FiniteNontracialSchedule.beta s) := by
  calc
    _ = √(FiniteNontracialSchedule.beta (halfSchedule s)^2) :=
      (Real.sqrt_sq (Real.exp_pos _).le).symm
    _ = _ := congrArg Real.sqrt (beta_half_sq s)

theorem halfTransfer_effective (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    scheduleTransfer p rs (halfSchedule s) = historyTransfer p rs
      (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) (1/2) := by
  rw [scheduleTransfer_effective]
  unfold historyTransfer
  rw [G_half,D_half]
  rw [show -(FiniteNontracialSchedule.G s/2)*1 = -FiniteNontracialSchedule.G s*(1/2) by ring,
    show -(FiniteNontracialSchedule.G s/2+FiniteNontracialSchedule.D s/2)*1 =
      -(FiniteNontracialSchedule.G s+FiniteNontracialSchedule.D s)*(1/2) by ring]

/-- Actual composed evolution after the specified reset gap. -/
def resetScheduleKraus (q : Gap) (s : Schedule.Data) :=
  composeKraus (FiniteNontracialSchedule.scheduleKraus s) (channel q.value)
def resetScheduleStep (q : Gap) (s : Schedule.Data) : Step (Fin 2) Unit 6 where
  count := _
  evolution k := GibbsMultilevelReflection.joint (resetScheduleKraus q s k)
  normalized := GibbsMultilevelReflection.joint_normalized _
    (isKrausChannel_composeKraus (FiniteNontracialSchedule.normalized s)
      (channel_normalized q.nonnegative q.bounded))
  instrument := instrument

theorem resetScheduleStep_branch (q : Gap) (s : Schedule.Data) (i : Fin 6) (X : Mat2) :
    (resetScheduleStep q s).branch (Fin 2) Unit 6 i (GibbsMultilevelReflection.joint X) =
      GibbsMultilevelReflection.joint
        (instrument.branch i (FiniteNontracialSchedule.state s (Phi q.value X))) := by
  change (instrument.lift Unit).branch i
    (krausMap (fun k => GibbsMultilevelReflection.joint (resetScheduleKraus q s k))
      (GibbsMultilevelReflection.joint X)) = _
  rw [GibbsMultilevelReflection.joint_kraus,resetScheduleKraus,krausMap_composeKraus,
    channel_state q.nonnegative q.bounded]
  exact GibbsMultilevelReflection.joint_kraus _ _

/-- Actual schedule AFTER reset p squared, retaining its dependent Kraus count. -/
def centralStep (p : Gap) (s : Schedule.Data) : Step (Fin 2) Unit 6 :=
  resetScheduleStep (PauliHistoryConsistency.squaredGap p) s
/-- Actual halved schedule AFTER reset p. -/
def splitStep (p : Gap) (s : Schedule.Data) : Step (Fin 2) Unit 6 :=
  resetScheduleStep p (halfSchedule s)

theorem centralStep_branch (p : Gap) (s : Schedule.Data) (i : Fin 6) (X : Mat2) :
    (centralStep p s).branch (Fin 2) Unit 6 i (GibbsMultilevelReflection.joint X) =
      GibbsMultilevelReflection.joint
        (instrument.branch i (FiniteNontracialSchedule.state s (Phi (p.value*p.value) X))) :=
  resetScheduleStep_branch _ _ i X
theorem splitStep_branch (p : Gap) (s : Schedule.Data) (i : Fin 6) (X : Mat2) :
    (splitStep p s).branch (Fin 2) Unit 6 i (GibbsMultilevelReflection.joint X) =
      GibbsMultilevelReflection.joint
        (instrument.branch i (FiniteNontracialSchedule.state (halfSchedule s) (Phi p.value X))) :=
  resetScheduleStep_branch _ _ i X

/-- This action equality identifies no Kraus structures or indices. -/
theorem centralStep_effective_branch (p : Gap) (s : Schedule.Data) (i : Fin 6) (X : Mat2) :
    (centralStep p s).branch (Fin 2) Unit 6 i (GibbsMultilevelReflection.joint X) =
      (NontracialReflectionDynamics.centralStep p.value
        (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
        p.nonnegative p.bounded (FiniteNontracialSchedule.G_nonneg s)
        (FiniteNontracialSchedule.D_nonneg s) zero_le_one).branch
        (Fin 2) Unit 6 i (GibbsMultilevelReflection.joint X) := by
  rw [centralStep_branch,NontracialReflectionDynamics.centralStep_branch,
    FiniteNontracialSchedule.state_effective]

def positiveTree (p : Gap) (s : Schedule.Data) :
    (rs : List Gap) → Tree (Fin 2) Unit 6 (rs.length+1)
  | [] => .node (centralStep p s) (fun _ => .done)
  | r::rs => .node (centralStep p s) (fun _ => historyPositiveTree r rs)
def reflectedTree (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    Tree (Fin 2) Unit 6 ((rs.length+1)+(rs.length+1)) :=
  PauliHistoryConsistency.appendTree (historyNegativeTree rs) (positiveTree p s rs)
def kernel (p : Gap) (rs : List Gap) (s : Schedule.Data) (u v : Labels rs) : ℂ :=
  (weight (Fin 2) Unit 6 (reflectedTree p rs s)
    (PauliHistoryConsistency.reflectedHistory rs u v) (GibbsMultilevelReflection.joint rhoN) : ℂ)

theorem positiveTree_effective_run (p : Gap) (rs : List Gap) (s : Schedule.Data)
    (u : Labels rs) (X : Mat2) :
    run (Fin 2) Unit 6 (positiveTree p s rs) u (GibbsMultilevelReflection.joint X) =
      run (Fin 2) Unit 6 (historyInsertedPositiveTree p
        (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
        (FiniteNontracialSchedule.G_nonneg s) (FiniteNontracialSchedule.D_nonneg s) zero_le_one rs)
        u (GibbsMultilevelReflection.joint X) := by
  cases rs with
  | nil =>
    rcases u with ⟨i,⟨⟩⟩
    simp only [positiveTree,historyInsertedPositiveTree,FiniteInterventionProcess.run,centralStep_effective_branch]
  | cons r rs =>
    change run (Fin 2) Unit 6 (historyPositiveTree r rs) u.2
      ((centralStep p s).branch (Fin 2) Unit 6 u.1 (GibbsMultilevelReflection.joint X)) = _
    rw [centralStep_effective_branch]
    rfl

theorem reflectedTree_effective_run (p : Gap) (rs : List Gap) (s : Schedule.Data)
    (u v : Labels rs) (X : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ) :
    run (Fin 2) Unit 6 (reflectedTree p rs s)
      (PauliHistoryConsistency.reflectedHistory rs u v) X =
    run (Fin 2) Unit 6 (historyInsertedTree p rs
      (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
      (FiniteNontracialSchedule.G_nonneg s) (FiniteNontracialSchedule.D_nonneg s) zero_le_one)
      (PauliHistoryConsistency.reflectedHistory rs u v) X := by
  rw [reflectedTree,historyInsertedTree,PauliHistoryConsistency.reflectedHistory,
    PauliHistoryConsistency.run_append,PauliHistoryConsistency.run_append]
  obtain ⟨Y,hY⟩ := PauliHistoryConsistency.joint_surjective
    (run (Fin 2) Unit 6 (historyNegativeTree rs) (PauliHistoryConsistency.negativeHistory rs u) X)
  rw [← hY]
  exact positiveTree_effective_run p rs s v Y

theorem kernel_effective (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    kernel p rs s = historyInsertedKernel p rs
      (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
      (FiniteNontracialSchedule.G_nonneg s) (FiniteNontracialSchedule.D_nonneg s) zero_le_one := by
  funext u v
  simp only [kernel,historyInsertedKernel,weight,reflectedTree_effective_run]

theorem positive_trace (p : Gap) (rs : List Gap) (s : Schedule.Data) (u : Labels rs) (X : Mat2) :
    (run (Fin 2) Unit 6 (positiveTree p s rs) u (GibbsMultilevelReflection.joint X)).trace =
      (Psi (p.value*p.value) (FiniteNontracialSchedule.observable s (historyEffect rs u))*X).trace := by
  rw [positiveTree_effective_run,history_inserted_positive_trace,
    ← FiniteNontracialSchedule.observable_effective]

theorem reflected_trace (p : Gap) (rs : List Gap) (s : Schedule.Data) (u v : Labels rs) :
    (run (Fin 2) Unit 6 (reflectedTree p rs s)
      (PauliHistoryConsistency.reflectedHistory rs u v) (GibbsMultilevelReflection.joint rhoN)).trace =
      (historyEffect rs v * FiniteNontracialSchedule.state s
        (Phi (p.value*p.value) (Gamma (historyEffect rs u)))).trace := by
  rw [reflectedTree_effective_run,history_inserted_actual_trace,
    ← FiniteNontracialSchedule.state_effective]

theorem kernel_trace (p : Gap) (rs : List Gap) (s : Schedule.Data) (u v : Labels rs) :
    kernel p rs s u v = (historyEffect rs v * FiniteNontracialSchedule.state s
      (Phi (p.value*p.value) (Gamma (historyEffect rs u)))).trace := by
  rw [kernel_effective,history_inserted_kernel_trace,← FiniteNontracialSchedule.state_effective]

theorem kernel_posSemidef (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    Matrix.PosSemidef (kernel p rs s) := by
  rw [kernel_effective]
  exact history_inserted_posSemidef _ _ _ _ _ _ _ _

theorem kernel_pairing (p : Gap) (rs : List Gap) (s : Schedule.Data) (F H : Labels rs → ℂ) :
    pairing (kernel p rs s) F H =
      ⟪mk _ (history_posSemidef p rs) F,
        scheduleTransfer p rs s (mk _ (history_posSemidef p rs) H)⟫_ℂ := by
  rw [kernel_effective,scheduleTransfer_effective]
  exact history_actual_pairing_transfer _ _ _ _ _ _ _ _ F H

theorem actual_probabilities (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    (∀ h,0≤weight (Fin 2) Unit 6 (reflectedTree p rs s) h
      (GibbsMultilevelReflection.joint rhoN)) ∧
    (∑ h,weight (Fin 2) Unit 6 (reflectedTree p rs s) h
      (GibbsMultilevelReflection.joint rhoN))=1 :=
  normalized_weights (Fin 2) Unit 6 _ joint_density

theorem kernel_normalized (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    (∑ u,∑ v,(kernel p rs s u v).re)=1 := by
  rw [kernel_effective]
  exact history_inserted_kernel_normalized _ _ _ _ _ _ _ _

/-- The ordinary split effect belongs to the existing actual split tree. -/
theorem ordinary_split_effect (p : Gap) (rs : List Gap) (u : Labels rs) :
    FiniteAdaptiveProcessRobustness.effect (historyPositiveTree p rs)
      (PauliHistoryConsistency.indicatorScore u) =
      GibbsMultilevelReflection.joint (Psi p.value (historyEffect rs u)) :=
  history_split_indicator_effect p rs u

/-- Full scheduled insertion follows the central p squared reset. -/
theorem unsplit_effect (p : Gap) (rs : List Gap) (s : Schedule.Data) (u : Labels rs) :
    FiniteAdaptiveProcessRobustness.effect (positiveTree p s rs)
      (PauliHistoryConsistency.indicatorScore u) =
      GibbsMultilevelReflection.joint
        (Psi (p.value*p.value) (FiniteNontracialSchedule.observable s (historyEffect rs u))) := by
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

theorem halfState_effective (s : Schedule.Data) (X : Mat2) :
    FiniteNontracialSchedule.state (halfSchedule s) X =
      NontracialReflectionDynamics.state (FiniteNontracialSchedule.G s)
        (FiniteNontracialSchedule.D s) (1/2) X := by
  rw [FiniteNontracialSchedule.state_formula,
    NontracialReflectionDynamics.state_formula _ _ _ (FiniteNontracialSchedule.G_nonneg s)
      (FiniteNontracialSchedule.D_nonneg s) (by norm_num)]
  simp only [FiniteNontracialSchedule.stateForm,FiniteNontracialSchedule.alpha,
    FiniteNontracialSchedule.beta,G_half,D_half]
  rw [show -(FiniteNontracialSchedule.G s/2) = -FiniteNontracialSchedule.G s*(1/2) by ring,
    show -(FiniteNontracialSchedule.G s/2+FiniteNontracialSchedule.D s/2) =
      -(FiniteNontracialSchedule.G s+FiniteNontracialSchedule.D s)*(1/2) by ring]

theorem halfObservable_effective (s : Schedule.Data) (A : Mat2) :
    FiniteNontracialSchedule.observable (halfSchedule s) A =
      NontracialReflectionDynamics.observable (FiniteNontracialSchedule.G s)
        (FiniteNontracialSchedule.D s) (1/2) A := by
  apply FiniteNontracialSchedule.trace_ext
  intro X
  rw [← FiniteNontracialSchedule.trace_dual,← NontracialReflectionDynamics.trace_dual,
    halfState_effective]

/-- The independent halved schedule has the actual half-split branch action. -/
theorem splitStep_effective_branch (p : Gap) (s : Schedule.Data) (i : Fin 6) (X : Mat2) :
    (splitStep p s).branch (Fin 2) Unit 6 i (GibbsMultilevelReflection.joint X) =
      (halfSplitStep p.value (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
        p.nonnegative p.bounded (FiniteNontracialSchedule.G_nonneg s)
        (FiniteNontracialSchedule.D_nonneg s) zero_le_one).branch
        (Fin 2) Unit 6 i (GibbsMultilevelReflection.joint X) := by
  rw [splitStep_branch,halfSplitStep_branch,halfState_effective]

def halfPositiveTree (p : Gap) (s : Schedule.Data) :
    (rs : List Gap) → Tree (Fin 2) Unit 6 (rs.length+1)
  | [] => .node (splitStep p s) (fun _ => .done)
  | r::rs => .node (splitStep p s) (fun _ => historyPositiveTree r rs)

theorem halfPositiveTree_effective_run (p : Gap) (rs : List Gap) (s : Schedule.Data)
    (u : Labels rs) (X : Mat2) :
    run (Fin 2) Unit 6 (halfPositiveTree p s rs) u (GibbsMultilevelReflection.joint X) =
      run (Fin 2) Unit 6 (historyHalfSplitPositiveTree p
        (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
        (FiniteNontracialSchedule.G_nonneg s) (FiniteNontracialSchedule.D_nonneg s) zero_le_one rs)
        u (GibbsMultilevelReflection.joint X) := by
  cases rs with
  | nil =>
    rcases u with ⟨i,⟨⟩⟩
    simp only [halfPositiveTree,historyHalfSplitPositiveTree,FiniteInterventionProcess.run,
      splitStep_effective_branch]
  | cons r rs =>
    change run (Fin 2) Unit 6 (historyPositiveTree r rs) u.2
      ((splitStep p s).branch (Fin 2) Unit 6 u.1 (GibbsMultilevelReflection.joint X)) = _
    rw [splitStep_effective_branch]
    rfl

theorem half_positive_trace (p : Gap) (rs : List Gap) (s : Schedule.Data) (u : Labels rs) (X : Mat2) :
    (run (Fin 2) Unit 6 (halfPositiveTree p s rs) u (GibbsMultilevelReflection.joint X)).trace =
      (FiniteNontracialSchedule.observable (halfSchedule s) (Psi p.value (historyEffect rs u))*X).trace := by
  rw [halfPositiveTree_effective_run,history_half_split_positive_trace,halfObservable_effective]

/-- Third effect: halved schedule after split p, distinct from full unsplit insertion. -/
theorem half_split_effect (p : Gap) (rs : List Gap) (s : Schedule.Data) (u : Labels rs) :
    FiniteAdaptiveProcessRobustness.effect (halfPositiveTree p s rs)
      (PauliHistoryConsistency.indicatorScore u) =
      GibbsMultilevelReflection.joint
        (FiniteNontracialSchedule.observable (halfSchedule s) (Psi p.value (historyEffect rs u))) := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  obtain ⟨Y,rfl⟩ := PauliHistoryConsistency.joint_surjective X
  rw [PauliHistoryConsistency.effect_complex_trace]
  simp only [PauliHistoryConsistency.indicatorScore,apply_ite,ite_mul,Complex.ofReal_one,
    Complex.ofReal_zero,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [half_positive_trace]
  rw [GibbsMultilevelReflection.joint,GibbsMultilevelReflection.joint,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.trace_kronecker]
  simp [Matrix.trace]

/-- Transport only along the proved equality of operational kernels; the metric is preserved. -/
def kernelMetricTransport {ι : Type*} [Fintype ι] {K L : Matrix ι ι ℂ}
    (h : K=L) (hK : K.PosSemidef) (hL : L.PosSemidef) : Space K hK ≃ₗᵢ[ℂ] Space L hL := by
  subst L
  exact LinearIsometryEquiv.refl ℂ _

abbrev ScheduledInsertedSpace (p : Gap) (rs : List Gap) (s : Schedule.Data) :=
  Space (kernel p rs s) (kernel_posSemidef p rs s)

def insertedMetricEquiv (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    ScheduledInsertedSpace p rs s ≃ₗᵢ[ℂ] InsertedHistorySpace p rs
      (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
      (FiniteNontracialSchedule.G_nonneg s) (FiniteNontracialSchedule.D_nonneg s) zero_le_one :=
  kernelMetricTransport (kernel_effective p rs s) (kernel_posSemidef p rs s)
    (history_inserted_posSemidef _ _ _ _ _ _ _ _)

/-- Actual inserted quotient class with its operational schedule kernel metric. -/
def toInserted (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    HistorySpace p rs →ₗ[ℂ] ScheduledInsertedSpace p rs s :=
  (insertedMetricEquiv p rs s).symm.toLinearEquiv.toLinearMap.comp
    (historyToInserted p rs (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
      (FiniteNontracialSchedule.G_nonneg s) (FiniteNontracialSchedule.D_nonneg s) zero_le_one)

theorem inserted_norm_halfTransfer (p : Gap) (rs : List Gap) (s : Schedule.Data)
    (z : HistorySpace p rs) : ‖toInserted p rs s z‖ = ‖scheduleTransfer p rs (halfSchedule s) z‖ := by
  change ‖(insertedMetricEquiv p rs s).symm
    (historyToInserted p rs (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
      (FiniteNontracialSchedule.G_nonneg s) (FiniteNontracialSchedule.D_nonneg s) zero_le_one z)‖ = _
  rw [(insertedMetricEquiv p rs s).symm.norm_map,
    history_inserted_norm_half_transfer,halfTransfer_effective]

/-- Weighted quotient norm, with positive central retention; not a physical trace distance. -/
theorem centered_opNorm (p : Gap) (rs : List Gap) (s : Schedule.Data) (hp : 0<p.value) :
    ‖scheduleTransfer p rs s-historyScalarProjection p rs‖ = FiniteNontracialSchedule.alpha s := by
  rw [scheduleTransfer_effective,historyTransfer_centered_opNorm p rs hp
    (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
    (FiniteNontracialSchedule.D_nonneg s) zero_le_one]
  simp [FiniteNontracialSchedule.alpha]

theorem reset_transfer (p : Gap) (rs : List Gap) (s : Schedule.Data) (hp : p.value=0) :
    scheduleTransfer p rs s=1 := by rw [scheduleTransfer_effective,historyTransfer_reset p rs hp]
theorem reset_centered_opNorm (p : Gap) (rs : List Gap) (s : Schedule.Data) (hp : p.value=0) :
    ‖scheduleTransfer p rs s-historyScalarProjection p rs‖=0 := by
  rw [scheduleTransfer_effective,historyTransfer_centered_opNorm_reset p rs hp]

theorem constant_fixed (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    scheduleTransfer p rs s (historyConstantVector p rs)=historyConstantVector p rs := by
  rw [scheduleTransfer_effective,historyTransfer_constant]

/-- Exact full-time weighted mode norms retain squared factors. -/
theorem full_mode_norms (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    ‖scheduleTransfer p rs s (historyCenteredVector p rs 0)‖^2 =
      (24*p.value^2/25)*FiniteNontracialSchedule.beta s^2 ∧
    ‖scheduleTransfer p rs s (historyCenteredVector p rs 1)‖^2 =
      (24*p.value^2/25)*FiniteNontracialSchedule.beta s^2 ∧
    ‖scheduleTransfer p rs s (historyCenteredVector p rs 2)‖^2 =
      (576*p.value^2/625)*FiniteNontracialSchedule.alpha s^2 ∧
    ‖scheduleTransfer p rs s (historyComplexVector p rs)‖^2 =
      (48*p.value^2/25)*FiniteNontracialSchedule.beta s^2 := by
  rw [scheduleTransfer_effective]
  have h := (historyTransfer_numerical_mode_norms p rs
    (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1).2.2.2.2.2
  simpa only [FiniteNontracialSchedule.alpha,FiniteNontracialSchedule.beta,mul_one] using h

/-- Actual inserted mode norms have one factor, through the proved half-schedule identity. -/
theorem inserted_mode_norms (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    ‖toInserted p rs s (historyCenteredVector p rs 0)‖^2 =
      (24*p.value^2/25)*FiniteNontracialSchedule.beta s ∧
    ‖toInserted p rs s (historyCenteredVector p rs 1)‖^2 =
      (24*p.value^2/25)*FiniteNontracialSchedule.beta s ∧
    ‖toInserted p rs s (historyCenteredVector p rs 2)‖^2 =
      (576*p.value^2/625)*FiniteNontracialSchedule.alpha s ∧
    ‖toInserted p rs s (historyComplexVector p rs)‖^2 =
      (48*p.value^2/25)*FiniteNontracialSchedule.beta s := by
  simp only [inserted_norm_halfTransfer]
  rcases full_mode_norms p rs (halfSchedule s) with ⟨hX,hY,hZ,hC⟩
  simpa only [alpha_half_sq,beta_half_sq] using And.intro hX (And.intro hY (And.intro hZ hC))

/-- State evolution differs from quotient observable coordinates when reset dose is positive. -/
theorem constant_state_observable_guard (p : Gap) (rs : List Gap) (s : Schedule.Data)
    (hG : 0<FiniteNontracialSchedule.G s) :
    FiniteNontracialSchedule.state s (historyCoordinates p rs (historyConstantVector p rs)) ≠
      historyCoordinates p rs (scheduleTransfer p rs s (historyConstantVector p rs)) := by
  rw [FiniteNontracialSchedule.state_effective,scheduleTransfer_effective]
  exact historyTransfer_state_observable_guard p rs _ _ _ hG
    (FiniteNontracialSchedule.D_nonneg s) zero_lt_one

/-- The chronological weighted metric is distinct from the one-sided state metric. -/
theorem metric_mismatch_guard (p : Gap) (hp : p.value=1) (rs : List Gap) :
    ‖historyCenteredVector p rs 0‖^2 < (pauliX*rhoN*pauliXᴴ).trace.re :=
  history_metric_mismatch_guard p hp rs

/-- Kernel equality transports literal coefficient classes, as well as their metrics. -/
theorem kernelMetricTransport_mk {ι : Type*} [Fintype ι] {K L : Matrix ι ι ℂ}
    (h : K=L) (hK : K.PosSemidef) (hL : L.PosSemidef) (F : ι → ℂ) :
    kernelMetricTransport h hK hL (mk K hK F)=mk L hL F := by
  subst L
  rfl

theorem insertedMetricEquiv_mk (p : Gap) (rs : List Gap) (s : Schedule.Data) (F : Labels rs → ℂ) :
    insertedMetricEquiv p rs s (mk (kernel p rs s) (kernel_posSemidef p rs s) F)=
      mk _ (history_inserted_posSemidef p rs (FiniteNontracialSchedule.G s)
        (FiniteNontracialSchedule.D s) 1 (FiniteNontracialSchedule.G_nonneg s)
        (FiniteNontracialSchedule.D_nonneg s) zero_le_one) F :=
  kernelMetricTransport_mk _ _ _ F

theorem toInserted_mk (p : Gap) (rs : List Gap) (s : Schedule.Data) (F : Labels rs → ℂ) :
    toInserted p rs s (mk _ (history_posSemidef p rs) F) =
      mk (kernel p rs s) (kernel_posSemidef p rs s) F := by
  apply (insertedMetricEquiv p rs s).injective
  change insertedMetricEquiv p rs s ((insertedMetricEquiv p rs s).symm
    (historyToInserted p rs (FiniteNontracialSchedule.G s) (FiniteNontracialSchedule.D s) 1
      (FiniteNontracialSchedule.G_nonneg s) (FiniteNontracialSchedule.D_nonneg s)
      zero_le_one (mk _ (history_posSemidef p rs) F))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,insertedMetricEquiv_mk,historyToInserted_mk]

/-- Actual-kernel pairing binds the induced inserted norm to the same literal coefficients. -/
theorem inserted_norm_sq_pairing (p : Gap) (rs : List Gap) (s : Schedule.Data) (F : Labels rs → ℂ) :
    ‖toInserted p rs s (mk _ (history_posSemidef p rs) F)‖^2 =
      (pairing (kernel p rs s) F F).re := by
  rw [toInserted_mk,norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (⟪mk _ (kernel_posSemidef p rs s) F,mk _ (kernel_posSemidef p rs s) F⟫_ℂ).re = _
  rw [inner_mk]

/-- Literal outer intervention transport still commutes with the proved schedule action. -/
theorem scheduleTransfer_outer (p : Gap) (rs : List Gap) (q : Gap) (s : Schedule.Data)
    (z : HistorySpace p rs) :
    outerMap p q rs (scheduleTransfer p rs s z) =
      scheduleTransfer p (rs++[q]) s (outerMap p q rs z) := by
  rw [scheduleTransfer_effective,scheduleTransfer_effective,historyTransfer_outer]

theorem scheduleTransfer_extension (p : Gap) (rs qs : List Gap) (s : Schedule.Data)
    (z : HistorySpace p rs) :
    extensionMap p rs qs (scheduleTransfer p rs s z) =
      scheduleTransfer p (extendSchedule rs qs) s (extensionMap p rs qs z) := by
  rw [scheduleTransfer_effective,scheduleTransfer_effective,historyTransfer_extension]

/-- Positive finite transverse dose strictly changes the actual inserted metric. -/
theorem inserted_x_lt_original (p : Gap) (rs : List Gap) (s : Schedule.Data)
    (hp : 0<p.value) (hdose : 0<FiniteNontracialSchedule.G s+FiniteNontracialSchedule.D s) :
    ‖toInserted p rs s (historyCenteredVector p rs 0)‖^2 <
      ‖historyCenteredVector p rs 0‖^2 := by
  rw [(inserted_mode_norms p rs s).1,(historyProjection_mode_norms p rs).2.1]
  have hb : FiniteNontracialSchedule.beta s<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hdose)
  have hnorm : 0<24*p.value^2/25 := by positivity
  simpa only [mul_one] using mul_lt_mul_of_pos_left hb hnorm

/-- Squared full-time transverse damping is strictly smaller than the inserted half-time metric. -/
theorem full_x_lt_inserted (p : Gap) (rs : List Gap) (s : Schedule.Data)
    (hp : 0<p.value) (hdose : 0<FiniteNontracialSchedule.G s+FiniteNontracialSchedule.D s) :
    ‖scheduleTransfer p rs s (historyCenteredVector p rs 0)‖^2 <
      ‖toInserted p rs s (historyCenteredVector p rs 0)‖^2 := by
  rw [(full_mode_norms p rs s).1,(inserted_mode_norms p rs s).1]
  have hb : FiniteNontracialSchedule.beta s<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hdose)
  have hpos := (FiniteNontracialSchedule.coefficients s).1
  have hsq : FiniteNontracialSchedule.beta s^2<FiniteNontracialSchedule.beta s := by nlinarith
  exact mul_lt_mul_of_pos_left hsq (by positivity)

/-- At reflection reset all centered classes vanish independently of operational doses. -/
theorem reset_centered_classes (p : Gap) (rs : List Gap) (hp : p.value=0) :
    (∀ a,historyCenteredVector p rs a=0) ∧ historyComplexVector p rs=0 :=
  ⟨fun a => historyCenteredVector_reset p rs hp a,historyComplexVector_reset p rs hp⟩

theorem half_actual_probabilities (p : Gap) (rs : List Gap) (s : Schedule.Data) :
    (∀ h,0≤weight (Fin 2) Unit 6 (halfPositiveTree p s rs) h
      (GibbsMultilevelReflection.joint rhoN)) ∧
    (∑ h,weight (Fin 2) Unit 6 (halfPositiveTree p s rs) h
      (GibbsMultilevelReflection.joint rhoN))=1 :=
  normalized_weights (Fin 2) Unit 6 _ joint_density

end SKEFTHawking.QuantumNetwork.NontracialScheduleTransfer
