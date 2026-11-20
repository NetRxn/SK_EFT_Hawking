import SKEFTHawking.FiniteGibbsCylinderHistory

/-! Moving the positive half of an actual computational Gibbs history away from
its reflection plane. The conditional path identity precedes its reconstructed
reset interpretation. This is a finite history statement, not global time translation. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.GibbsCylinderShift
open GibbsHistoryKernel GibbsTwoTimeProcess GibbsRelaxationProcess GibbsCylinderHistory
open FinitePositiveKernel
open scoped InnerProductSpace

variable {n : ℕ}

/-- Positive times move by a; their negative partners are re-reflected. -/
def shiftData (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) : GibbsUnitalHistory.Data n where
  β := d.β
  Δ := d.Δ
  γ := d.γ
  η := d.η
  rate_nonnegative := d.rate_nonnegative
  dephasing_nonnegative := d.dephasing_nonnegative
  times := fun i => d.times i+a
  ordered := by
    intro i j hij
    have h := d.ordered hij
    dsimp
    linarith
  nonnegative := fun i => add_nonneg (d.nonnegative i) ha

theorem pathProduct_shift (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (u : Path n) :
    pathProduct d.β d.Δ d.γ (shiftData d a ha).times u = pathProduct d.β d.Δ d.γ d.times u := by
  simp [pathProduct,shiftData]

/-- The intermediate index is algebraic, not an additional intervention. -/
theorem conditional_shift (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a)
    (x : Qubit) (u : Path n) :
    conditional (shiftData d a ha) x u =
      ∑ y,transition d.β d.Δ d.γ a x y*conditional d y u := by
  unfold conditional
  change transition d.β d.Δ d.γ (d.times 0+a) x (u 0)*
    pathProduct d.β d.Δ d.γ (shiftData d a ha).times u = _
  rw [pathProduct_shift]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul,chapman_kolmogorov,add_comm a]

theorem expectation_shift (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a)
    (F : Path n → ℂ) (x : Qubit) :
    expectation (shiftData d a ha) F x =
      ∑ y,(transition d.β d.Δ d.γ a x y:ℂ)*expectation d F y := by
  unfold expectation
  simp_rw [conditional_shift,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum,mul_assoc]

/-- The actual transition acts diagonally on constant and centered expectations. -/
theorem transition_modes (β Δ γ t : ℝ) (A B : ℂ) (x : Qubit) :
    (∑ y,(transition β Δ γ t x y:ℂ)*(A+B*(centered β Δ y:ℂ)))=
      A+GibbsReflectedHistory.decay γ t*B*(centered β Δ x:ℂ) := by
  have h1 : (∑ y,(transition β Δ γ t x y:ℂ))=1 := by
    exact_mod_cast transition_sum β Δ γ t x
  have h2 : (∑ y,(transition β Δ γ t x y:ℂ)*(centered β Δ y:ℂ))=
      GibbsReflectedHistory.decay γ t*(centered β Δ x:ℂ) := by
    unfold GibbsReflectedHistory.decay
    exact_mod_cast transition_centered β Δ γ t x
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,h1,one_mul]
  have h : (∑ y,(transition β Δ γ t x y:ℂ)*(B*(centered β Δ y:ℂ)))=
      B*∑ y,(transition β Δ γ t x y:ℂ)*(centered β Δ y:ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [h,h2]
  ring

theorem expectation_shift_modes (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a)
    (F : Path n → ℂ) (x : Qubit) :
    expectation (shiftData d a ha) F x=constantAmplitude d F+
      GibbsReflectedHistory.decay d.γ a*centeredAmplitude d F*(centered d.β d.Δ x:ℂ) := by
  rw [expectation_shift]
  simp_rw [expectation_modes]
  exact transition_modes _ _ _ _ _ _ _

theorem amplitudes_shift (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (F : Path n → ℂ) :
    constantAmplitude (shiftData d a ha) F=constantAmplitude d F ∧
      centeredAmplitude (shiftData d a ha) F=GibbsReflectedHistory.decay d.γ a*centeredAmplitude d F := by
  have hb : centeredAmplitude (shiftData d a ha) F=
      GibbsReflectedHistory.decay d.γ a*centeredAmplitude d F := by
    unfold centeredAmplitude
    rw [expectation_shift_modes,expectation_shift_modes]
    simp only [centeredAmplitude,centered,sign]
    push_cast
    ring
  refine ⟨?_,hb⟩
  unfold constantAmplitude
  rw [hb,expectation_shift_modes]
  rw [constantAmplitude]
  dsimp only [shiftData]
  ring

theorem null_modes (d : GibbsUnitalHistory.Data n) (F : Path n → ℂ) :
    mk _ (positive d) F=0 ↔ constantAmplitude d F=0 ∧ centeredAmplitude d F=0 := by
  rw [null_iff]
  constructor
  · rintro ⟨h0,h1⟩
    simp [constantAmplitude,centeredAmplitude,h0,h1]
  · rintro ⟨hA,hB⟩
    constructor <;> rw [expectation_modes,hA,hB] <;> simp

/-- Finite-time exponential decay never destroys a nonzero centered mode. -/
theorem null_shift_iff (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (F : Path n → ℂ) :
    mk _ (positive (shiftData d a ha)) F=0 ↔ mk _ (positive d) F=0 := by
  rw [null_modes,null_modes,(amplitudes_shift d a ha F).1,(amplitudes_shift d a ha F).2]
  have h : GibbsReflectedHistory.decay d.γ a≠0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  simp [h]

/-- A fixed base space realizes the conditional expectation of the shifted history. -/
def realization (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (F : Path n → ℂ) :
    GibbsUnitalHistory.Reconstructed d :=
  GibbsUnitalHistory.state d (constantAmplitude (shiftData d a ha) F) (centeredAmplitude (shiftData d a ha) F)

theorem unitalEquiv_mk (d : GibbsUnitalHistory.Data n) (F : Path n → ℂ) :
    unitalEquiv d (mk _ (positive d) F)=GibbsUnitalHistory.state d (constantAmplitude d F) (centeredAmplitude d F) :=
  transferLinear_mk d F

theorem realization_reset (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (F : Path n → ℂ) :
    realization d a ha F=GibbsUnitalHistory.reset d a (unitalEquiv d (mk _ (positive d) F)) := by
  rw [unitalEquiv_mk,GibbsUnitalHistory.reset_state]
  unfold realization
  rw [(amplitudes_shift d a ha F).1,(amplitudes_shift d a ha F).2]

/-- The inner product is the pairing of the actual newly shifted full history. -/
theorem realization_inner (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (F G : Path n → ℂ) :
    ⟪realization d a ha F,realization d a ha G⟫_ℂ=cylinderPairing (shiftData d a ha) F G := by
  rw [← pairing_actual,pairing_modes]
  exact GibbsUnitalHistory.state_inner d _ _ _ _

/-- The identical function on outcome labels descends for both null relations. -/
theorem classes_shift_iff (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (F G : Path n → ℂ) :
    mk _ (positive (shiftData d a ha)) F=mk _ (positive (shiftData d a ha)) G ↔
      mk _ (positive d) F=mk _ (positive d) G := by
  rw [mk_eq_mk_iff,mk_eq_mk_iff,← mk_eq_zero_iff,← mk_eq_zero_iff]
  exact null_shift_iff d a ha (F-G)

theorem realization_well_defined (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a)
    (F G : Path n → ℂ) (h : mk _ (positive d) F=mk _ (positive d) G) :
    realization d a ha F=realization d a ha G := by
  rw [realization_reset,realization_reset,h]

/-- The channel is the actual observable-oriented time-Kraus Gibbs reset. -/
theorem realization_channel (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (F : Path n → ℂ) :
    GibbsUnitalHistory.embedding d (realization d a ha F)=
      GibbsReset.evolution _ (weights_pos d.β d.Δ) (weights_sum d.β d.Δ) d.γ a d.rate_nonnegative ha
        (GibbsUnitalHistory.embedding d (unitalEquiv d (mk _ (positive d) F))) := by
  rw [realization_reset]
  exact GibbsUnitalHistory.reset_intertwining d a ha _

theorem realization_zero (d : GibbsUnitalHistory.Data n) (F : Path n → ℂ) :
    realization d 0 (le_refl 0) F=unitalEquiv d (mk _ (positive d) F) := by
  rw [realization_reset,GibbsUnitalHistory.reset_zero]
  rfl

theorem realization_add (d : GibbsUnitalHistory.Data n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (F : Path n → ℂ) :
    realization d (a+b) (add_nonneg ha hb) F=GibbsUnitalHistory.reset d a (realization d b hb F) := by
  rw [realization_reset,realization_reset,GibbsUnitalHistory.reset_add]
  rfl

theorem realization_norm_le (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (F : Path n → ℂ) :
    ‖realization d a ha F‖ ≤ ‖mk _ (positive d) F‖ := by
  rw [realization_reset,← (unitalEquiv d).norm_map]
  exact GibbsUnitalHistory.reset_norm_le d a ha _

/-- Both reflected halves move, hence the centered pairing has twice the time. -/
theorem pairing_shift (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (F G : Path n → ℂ) :
    cylinderPairing (shiftData d a ha) F G=star (constantAmplitude d F)*constantAmplitude d G+
      ((1-meanZ d.β d.Δ^2:ℝ):ℂ)*GibbsReflectedHistory.decay d.γ (2*a)*
        star (centeredAmplitude d F)*centeredAmplitude d G := by
  rw [← realization_inner,realization_reset,realization_reset,unitalEquiv_mk,unitalEquiv_mk,
    GibbsUnitalHistory.reset_state,GibbsUnitalHistory.reset_state,GibbsUnitalHistory.state_inner]
  have he : GibbsReflectedHistory.decay d.γ (2*a)=
      GibbsReflectedHistory.decay d.γ a*GibbsReflectedHistory.decay d.γ a := by
    unfold GibbsReflectedHistory.decay
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  rw [he]
  simp only [map_mul,GibbsReflectedHistory.decay,Complex.star_def,Complex.conj_ofReal]
  ring

theorem pairing_twice (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (F G : Path n → ℂ) :
    cylinderPairing (shiftData d a ha) F G=
      ⟪unitalEquiv d (mk _ (positive d) F),
        GibbsUnitalHistory.reset d (2*a) (unitalEquiv d (mk _ (positive d) G))⟫_ℂ := by
  rw [pairing_shift,unitalEquiv_mk,unitalEquiv_mk,GibbsUnitalHistory.reset_state,GibbsUnitalHistory.state_inner]
  ring

theorem expectation_zero_rate (d : GibbsUnitalHistory.Data n) (hγ : d.γ=0)
    (a : ℝ) (ha : 0 ≤ a) (F : Path n → ℂ) (x : Qubit) :
    expectation (shiftData d a ha) F x=expectation d F x := by
  rw [expectation_shift_modes,expectation_modes]
  simp [GibbsReflectedHistory.decay,hγ]

theorem pairing_zero_rate (d : GibbsUnitalHistory.Data n) (hγ : d.γ=0)
    (a : ℝ) (ha : 0 ≤ a) (F G : Path n → ℂ) :
    cylinderPairing (shiftData d a ha) F G=cylinderPairing d F G := by
  rw [pairing_shift,← pairing_actual,pairing_modes]
  simp [GibbsReflectedHistory.decay,hγ]

theorem realization_constant (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) :
    realization d a ha (fun _ => 1)=GibbsUnitalHistory.state d 1 0 := by
  unfold realization constantAmplitude centeredAmplitude
  simp only [expectation_one,sub_self,zero_div,zero_mul,sub_zero]

/-- Equal sector times remain equal; no event label is removed. -/
theorem repeated_times (d : GibbsUnitalHistory.Data n) (a : ℝ) (ha : 0 ≤ a) (i j : Fin (n+1)) :
    (shiftData d a ha).times i=(shiftData d a ha).times j ↔ d.times i=d.times j := by
  simp [shiftData]

/-- A sector starting at the reflection plane remains admissible. -/
theorem first_time_zero (d : GibbsUnitalHistory.Data n) (h0 : d.times 0=0)
    (a : ℝ) (ha : 0 ≤ a) (x : Qubit) (u : Path n) :
    (shiftData d a ha).times 0=a ∧ conditional (shiftData d a ha) x u=
      transition d.β d.Δ d.γ a x (u 0)*pathProduct d.β d.Δ d.γ d.times u := by
  constructor
  · simp [shiftData,h0]
  · unfold conditional
    change transition d.β d.Δ d.γ (d.times 0+a) x (u 0)*
      pathProduct d.β d.Δ d.γ (shiftData d a ha).times u=_
    rw [h0,zero_add,pathProduct_shift]

/-- The nonlinear probe is literally the same two-label function after shifting. -/
theorem example_amplitudes (a : ℝ) (ha : 0 ≤ a) :
    constantAmplitude (shiftData exampleData a ha) (productProbe exampleData)=
      ((1-meanZ 1 1^2)*Real.exp (-1):ℝ) ∧
    centeredAmplitude (shiftData exampleData a ha) (productProbe exampleData)=
      (-(2*meanZ 1 1*Real.exp (-2-a)):ℝ) := by
  rw [(amplitudes_shift exampleData a ha _).1,(amplitudes_shift exampleData a ha _).2,
    (product_amplitudes exampleData).1,(product_amplitudes exampleData).2,
    example_times.1,example_times.2]
  change (((1-meanZ 1 1^2)*Real.exp (-(1:ℝ)*(2-1)):ℝ):ℂ)=_ ∧
    (Real.exp (-(1:ℝ)*a):ℂ)*((-(2*meanZ 1 1*Real.exp (-(1:ℝ)*2)):ℝ):ℂ)=_
  norm_num
  have he : Complex.exp (-2-(a:ℂ))=Complex.exp (-(a:ℂ))*Complex.exp (-2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he]
  ring

theorem example_expectation (a : ℝ) (ha : 0 ≤ a) (x : Qubit) :
    expectation (shiftData exampleData a ha) (productProbe exampleData) x=
      ((1-meanZ 1 1^2)*Real.exp (-1):ℝ)-
        (2*meanZ 1 1*Real.exp (-2-a):ℝ)*(centered 1 1 x:ℂ) := by
  rw [expectation_modes,(example_amplitudes a ha).1,(example_amplitudes a ha).2]
  dsimp only [shiftData,exampleData,GibbsUnitalHistory.exampleData]
  push_cast
  ring

theorem example_realization (a : ℝ) (ha : 0 ≤ a) :
    realization exampleData a ha (productProbe exampleData)=GibbsUnitalHistory.state exampleData
      ((1-meanZ 1 1^2)*Real.exp (-1):ℝ) (-(2*meanZ 1 1*Real.exp (-2-a)):ℝ) := by
  unfold realization
  rw [(example_amplitudes a ha).1,(example_amplitudes a ha).2]

def exampleFloor : ℝ := (1-meanZ 1 1^2)^2*Real.exp (-2)

def exampleFourPoint (a : ℝ) : ℝ := exampleFloor+4*meanZ 1 1^2*(1-meanZ 1 1^2)*Real.exp (-4-2*a)

/-- Exact four-event pairing of the same nonlinear function in the shifted history. -/
theorem example_four_point_shift (a : ℝ) (ha : 0 ≤ a) :
    cylinderPairing (shiftData exampleData a ha) (productProbe exampleData) (productProbe exampleData)=
      (exampleFourPoint a:ℂ) := by
  rw [← realization_inner,example_realization,GibbsUnitalHistory.state_inner]
  change star (((1-meanZ 1 1^2)*Real.exp (-1):ℝ):ℂ)*
      (((1-meanZ 1 1^2)*Real.exp (-1):ℝ):ℂ)+
    ((1-meanZ 1 1^2:ℝ):ℂ)*star ((-(2*meanZ 1 1*Real.exp (-2-a)):ℝ):ℂ)*
      ((-(2*meanZ 1 1*Real.exp (-2-a)):ℝ):ℂ)=_
  simp only [Complex.star_def,Complex.conj_ofReal]
  norm_cast
  norm_num
  have h1 : Real.exp (-1)*Real.exp (-1)=Real.exp (-2) := by rw [← Real.exp_add]; norm_num
  have h2 : Real.exp (-2-a)*Real.exp (-2-a)=Real.exp (-4-2*a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold exampleFourPoint exampleFloor
  rw [← h1,← h2]
  ring

theorem example_floor_positive : 0 < exampleFloor := by
  exact mul_pos (sq_pos_of_pos (stationary_variance_pos 1 1)) (Real.exp_pos _)

theorem example_above_floor (a : ℝ) : exampleFloor < exampleFourPoint a := by
  have hm := nonuniform_mean
  have hv := stationary_variance_pos 1 1
  have hp : 0 < 4*meanZ 1 1^2*(1-meanZ 1 1^2)*Real.exp (-4-2*a) := by positivity
  unfold exampleFourPoint
  linarith

theorem example_strict_decay {a b : ℝ} (hab : a < b) : exampleFourPoint b < exampleFourPoint a := by
  have hm := nonuniform_mean
  have hv := stationary_variance_pos 1 1
  have hc : 0 < 4*meanZ 1 1^2*(1-meanZ 1 1^2) := by positivity
  have he : Real.exp (-4-2*b)<Real.exp (-4-2*a) := Real.exp_lt_exp.mpr (by linarith)
  unfold exampleFourPoint
  linarith [mul_lt_mul_of_pos_left he hc]

/-- Strict comparisons concern the real part of the actual complex pairing. -/
theorem example_actual_decay {a : ℝ} (ha : 0 < a) :
    0 < exampleFloor ∧ exampleFloor <
      (cylinderPairing (shiftData exampleData a ha.le) (productProbe exampleData) (productProbe exampleData)).re ∧
    (cylinderPairing (shiftData exampleData a ha.le) (productProbe exampleData) (productProbe exampleData)).re <
      (cylinderPairing exampleData (productProbe exampleData) (productProbe exampleData)).re := by
  rw [example_four_point_shift,GibbsCylinderHistory.example_four_point]
  simp only [Complex.ofReal_re]
  refine ⟨example_floor_positive,example_above_floor a,?_⟩
  convert example_strict_decay ha using 1
  simp [exampleFourPoint,exampleFloor]

theorem example_null_shift (a : ℝ) (ha : 0 ≤ a) :
    exampleNull≠0 ∧ mk _ (positive (shiftData exampleData a ha)) exampleNull=0 :=
  ⟨example_null_nonzero,(null_shift_iff exampleData a ha exampleNull).mpr example_null⟩

/-- Re-reflection increases the central gap; it is not global chronological translation. -/
theorem example_schedule_shift (a : ℝ) (ha : 0 ≤ a) :
    GibbsReflectedHistory.symmetricSchedule (shiftData exampleData a ha).times= ![-2-a,-1-a,1+a,2+a] := by
  funext i
  fin_cases i <;> norm_num [GibbsReflectedHistory.symmetricSchedule,shiftData,exampleData,
    GibbsUnitalHistory.exampleData,GibbsReflectedHistory.exampleTimes] <;> ring

theorem example_not_global_translation {a : ℝ} (ha : 0 < a) :
    GibbsReflectedHistory.symmetricSchedule (shiftData exampleData a ha.le).times 0 ≠
      GibbsReflectedHistory.symmetricSchedule exampleData.times 0+a := by
  rw [example_schedule_shift,example_same_history]
  norm_num
  linarith

end SKEFTHawking.QuantumNetwork.GibbsCylinderShift
