import SKEFTHawking.FiniteGibbsMultilevelCylinder
import SKEFTHawking.QuantumNetwork.FiniteAdaptiveProcessRobustness

/-! Preparation dependence of actual finite reflected Gibbs histories.
All histories retain every outcome, including impossible branches. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.GibbsHistoryPreparationBounds
open Matrix FiniteInterventionProcess FinitePositiveKernel GibbsMultilevelReflection
open GibbsMultilevelProcess GibbsMultilevelCylinder
open FinitePositiveKernel.DiagonalLindblad OpenSystems
open scoped ComplexOrder Kronecker
variable {d n : ℕ}

/-- The initial matrix changes; the complete history and its maps do not. -/
def mass (R : Data d) (S : Schedule n) (σ : Matrix (Fin d) (Fin d) ℂ)
    (h : History d (2*n+1+1)) : ℝ :=
  weight (Fin d) Unit d (history R S) h (joint σ)

/-- Row/column orientation is inherited from the actual reflected history. -/
def kernel (R : Data d) (S : Schedule n) (σ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (GibbsMultilevelCylinder.Path d n) (GibbsMultilevelCylinder.Path d n) ℂ :=
  fun u v => (mass R S σ ((pairEquiv n).symm (u,v)) : ℂ)

def cylinderPairing (R : Data d) (S : Schedule n) (σ : Matrix (Fin d) (Fin d) ℂ)
    (F G : GibbsMultilevelCylinder.Path d n → ℂ) : ℂ :=
  ∑ h,(mass R S σ h : ℂ)*star (F ((pairEquiv n h).1))*G ((pairEquiv n h).2)

theorem stationary_mass (R : Data d) (S : Schedule n) (h : History d (2*n+1+1)) :
    mass R S (density R.w) h = GibbsMultilevelCylinder.mass R S h := rfl

theorem stationary_kernel (R : Data d) (S : Schedule n) :
    kernel R S (density R.w) = GibbsMultilevelCylinder.kernel R S := rfl

theorem stationary_pairing (R : Data d) (S : Schedule n) (F G : GibbsMultilevelCylinder.Path d n → ℂ) :
    cylinderPairing R S (density R.w) F G = GibbsMultilevelCylinder.cylinderPairing R S F G := rfl

theorem pairing_actual (R : Data d) (S : Schedule n) (σ : Matrix (Fin d) (Fin d) ℂ)
    (F G : GibbsMultilevelCylinder.Path d n → ℂ) :
    pairing (kernel R S σ) F G = cylinderPairing R S σ F G := by
  have he := Equiv.sum_comp (pairEquiv n).symm
    (fun h => (mass R S σ h:ℂ)*star (F ((pairEquiv n h).1))*G ((pairEquiv n h).2))
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type] at he
  unfold cylinderPairing
  rw [← he]
  simp only [pairing,dotProduct,mulVec,Finset.mul_sum,kernel]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  simp only [Pi.star_apply,Complex.star_def]
  ring

/-- The first actual intervention removes off-diagonal preparation entries. -/
theorem prepared_first_collapse (R : Data d) (σ : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    (step R.w R.positive R.normalized R.γ 0 R.rate_nonneg le_rfl).branch
      (Fin d) Unit d i (joint σ) = joint (σ i i • projector i) := by
  rw [step_branch,GibbsReset.time_state R.w (fun i => (R.positive i).le) _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one R.γ 0 R.rate_nonneg le_rfl)]
  simp [instrument_branch]

theorem prepared_history_weight (R : Data d) (k : ℕ) (s : ℕ → ℝ) (hs : ∀ i,0 ≤ s i)
    (σ : Matrix (Fin d) (Fin d) ℂ) (h : History d (k+1)) :
    weight (Fin d) Unit d (historyTree R k s hs) h (joint σ) =
      (σ h.1 h.1).re * tailMass R k s h.1 h.2 := by
  change (run (Fin d) Unit d (tailTree R k s hs) h.2
    ((step R.w R.positive R.normalized R.γ 0 R.rate_nonneg le_rfl).branch
      (Fin d) Unit d h.1 (joint σ))).trace.re = _
  rw [prepared_first_collapse,tail_trace]
  simp

theorem mass_formula (R : Data d) (S : Schedule n) (σ : Matrix (Fin d) (Fin d) ℂ)
    (h : History d (2*n+1+1)) :
    mass R S σ h = (σ h.1 h.1).re * tailMass R (2*n+1) (lags S) h.1 h.2 :=
  prepared_history_weight R _ _ _ σ h

/-- The singleton positive path pairs to two chronological observations. -/
theorem singleton_indices (u v : GibbsMultilevelCylinder.Path d 0) :
    (pairEquiv 0).symm (u,v) = (u 0,v 0,()) := by
  apply (historyEquiv _).injective
  funext i
  fin_cases i <;> simp [pairEquiv,split,historyEquiv] <;> rfl

/-- Four observations occur in order u₁,u₀,v₀,v₁. -/
theorem four_indices (u v : GibbsMultilevelCylinder.Path d 1) :
    (pairEquiv 1).symm (u,v) = (u 1,u 0,v 0,v 1,()) := by
  apply (historyEquiv _).injective
  funext i
  fin_cases i <;> simp [pairEquiv,split,historyEquiv] <;> rfl

theorem singleton_prepared_kernel (R : Data d) (S : Schedule 0)
    (σ : Matrix (Fin d) (Fin d) ℂ) (u v : GibbsMultilevelCylinder.Path d 0) :
    kernel R S σ u v = ((σ (u 0) (u 0)).re *
      transition R.w R.γ (lags S 0) (u 0) (v 0) : ℝ) := by
  rw [kernel,singleton_indices,mass_formula]
  simp [tailMass]

theorem four_prepared_kernel (R : Data d) (S : Schedule 1)
    (σ : Matrix (Fin d) (Fin d) ℂ) (u v : GibbsMultilevelCylinder.Path d 1) :
    kernel R S σ u v = ((σ (u 1) (u 1)).re *
      transition R.w R.γ (lags S 0) (u 1) (u 0) *
      transition R.w R.γ (lags S 1) (u 0) (v 0) *
      transition R.w R.γ (lags S 2) (v 0) (v 1) : ℝ) := by
  rw [kernel,four_indices,mass_formula]
  simp [tailMass,later,mul_assoc]

theorem joint_density {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) :
    IsDensityOperator (joint σ) :=
  ⟨hσ.1.kronecker Matrix.PosSemidef.one, (joint_trace σ).trans hσ.2⟩

theorem mass_probability (R : Data d) (S : Schedule n)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) :
    (∀ h,0 ≤ mass R S σ h) ∧ (∑ h,mass R S σ h)=1 :=
  normalized_weights (Fin d) Unit d (history R S) (joint_density hσ)

theorem singleton_lag (S : Schedule 0) : lags S 0 = 2*S.times 0 := by
  simp [lags,GibbsReflectedHistory.symmetricSchedule]
  ring

theorem four_lags (S : Schedule 1) :
    lags S 0 = S.times 1-S.times 0 ∧ lags S 1=2*S.times 0 ∧
      lags S 2=S.times 1-S.times 0 := by
  norm_num [lags,GibbsReflectedHistory.symmetricSchedule]
  constructor <;> ring

/-- An actual normalized Gibbs-reset channel, before the observed history begins. -/
def warm (R : Data d) (γ τ : ℝ) (σ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  krausMap (GibbsReset.timeKraus R.w (Real.exp (-γ*τ))) σ

theorem warm_normalized (R : Data d) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ) :
    IsKrausChannel (GibbsReset.timeKraus R.w (Real.exp (-γ*τ))) :=
  GibbsReset.time_normalized R.w (fun i => (R.positive i).le) R.normalized _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one γ τ hγ hτ)

theorem warm_density (R : Data d) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) :
    IsDensityOperator (warm R γ τ σ) :=
  krausMap_isDensityOperator (warm_normalized R hγ hτ) hσ

theorem warm_state (R : Data d) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) :
    warm R γ τ σ = (Real.exp (-γ*τ) : ℂ) • σ +
      (1-(Real.exp (-γ*τ) : ℂ)) • density R.w := by
  rw [warm,GibbsReset.time_state R.w (fun i => (R.positive i).le) _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one γ τ hγ hτ),hσ.2,one_smul]

theorem warm_difference (R : Data d) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) :
    warm R γ τ σ - density R.w = (Real.exp (-γ*τ) : ℂ) • (σ-density R.w) := by
  rw [warm_state R hγ hτ hσ]
  module

/-- Exact preparation-distance contraction comes from the actual Kraus action. -/
theorem warm_traceDist (R : Data d) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) :
    traceDist (warm R γ τ σ) (density R.w) =
      Real.exp (-γ*τ) * traceDist σ (density R.w) := by
  unfold traceDist
  rw [warm_difference R hγ hτ hσ,traceNorm_smul_nonneg (Real.exp_pos _).le]
  ring

theorem joint_traceDist (σ ρ : Matrix (Fin d) (Fin d) ℂ) :
    traceDist (joint σ) (joint ρ) = traceDist σ ρ := by
  exact FiniteAdaptiveProcessRobustness.traceDist_tensor_right
    (show IsDensityOperator (1 : Matrix Unit Unit ℂ) from ⟨Matrix.PosSemidef.one,by simp [Matrix.trace]⟩) σ ρ

theorem warm_joint_traceDist (R : Data d) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) :
    traceDist (joint (warm R γ τ σ)) (joint (density R.w)) =
      Real.exp (-γ*τ) * traceDist σ (density R.w) := by
  rw [joint_traceDist,warm_traceDist R hγ hτ hσ]

/-- The two observations lie at reflected schedule coordinates -1 and 1. -/
def oneTime : Schedule 0 where
  times := fun _ => 1
  ordered := monotone_const
  nonnegative := fun _ => by norm_num

theorem three_prepared_forward :
    kernel three oneTime GibbsReset.concentrated (fun _ => 0) (fun _ => 1) =
      ((1-Real.exp (-2))/3 : ℝ) := by
  rw [singleton_prepared_kernel,singleton_lag]
  norm_num [three,oneTime,GibbsReset.concentrated,GibbsReset.threeWeights,transition]
  ring

theorem three_prepared_reverse :
    kernel three oneTime GibbsReset.concentrated (fun _ => 1) (fun _ => 0) = 0 := by
  rw [singleton_prepared_kernel]
  norm_num [GibbsReset.concentrated]

theorem three_warm_forward {τ : ℝ} (hτ : 0 ≤ τ) :
    kernel three oneTime (warm three 1 τ GibbsReset.concentrated) (fun _ => 0) (fun _ => 1) =
      ((1+Real.exp (-τ))*(1-Real.exp (-2))/6 : ℝ) := by
  rw [singleton_prepared_kernel,singleton_lag,warm_state three (by norm_num) hτ GibbsReset.concentrated_density]
  norm_num [three,oneTime,GibbsReset.concentrated,GibbsReset.threeWeights,density,transition,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.mul_re,Complex.exp_re]
  ring

theorem three_warm_reverse {τ : ℝ} (hτ : 0 ≤ τ) :
    kernel three oneTime (warm three 1 τ GibbsReset.concentrated) (fun _ => 1) (fun _ => 0) =
      ((1-Real.exp (-τ))*(1-Real.exp (-2))/6 : ℝ) := by
  rw [singleton_prepared_kernel,singleton_lag,warm_state three (by norm_num) hτ GibbsReset.concentrated_density]
  norm_num [three,oneTime,GibbsReset.concentrated,GibbsReset.threeWeights,density,transition,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.mul_re,Complex.exp_re]
  ring

theorem three_warm_asymmetry {τ : ℝ} (hτ : 0 ≤ τ) :
    (kernel three oneTime (warm three 1 τ GibbsReset.concentrated) (fun _ => 0) (fun _ => 1) -
      kernel three oneTime (warm three 1 τ GibbsReset.concentrated) (fun _ => 1) (fun _ => 0)).re =
      Real.exp (-τ)*(1-Real.exp (-2))/3 := by
  rw [three_warm_forward hτ,three_warm_reverse hτ]
  simp only [Complex.sub_re,Complex.ofReal_re]
  ring

theorem three_warm_asymmetry_pos {τ : ℝ} (hτ : 0 ≤ τ) :
    0 < (kernel three oneTime (warm three 1 τ GibbsReset.concentrated) (fun _ => 0) (fun _ => 1) -
      kernel three oneTime (warm three 1 τ GibbsReset.concentrated) (fun _ => 1) (fun _ => 0)).re := by
  rw [three_warm_asymmetry hτ]
  exact div_pos (mul_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))) (by norm_num)

/-- Finite coefficient sup norm, with value zero on an empty indexing type. -/
def coefficientBound {ι : Type*} [Fintype ι] (F : ι → ℂ) : ℝ :=
  (Finset.univ.sup (fun i => ‖F i‖₊) : NNReal)

theorem coefficientBound_nonneg {ι : Type*} [Fintype ι] (F : ι → ℂ) :
    0 ≤ coefficientBound F := NNReal.coe_nonneg _

theorem norm_le_coefficientBound {ι : Type*} [Fintype ι] (F : ι → ℂ) (i : ι) :
    ‖F i‖ ≤ coefficientBound F :=
  NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun j => ‖F j‖₊) (Finset.mem_univ i))

/-- A complex signed-law estimate; cancellation need not be real or positive. -/
theorem complex_law_bound {H A B : Type*} [Fintype H] [Fintype A] [Fintype B]
    (p q : H → ℝ) (left : H → A) (right : H → B) (F : A → ℂ) (G : B → ℂ) :
    ‖∑ h,((p h-q h : ℝ):ℂ)*star (F (left h))*G (right h)‖ ≤
      (∑ h,|p h-q h|)*coefficientBound F*coefficientBound G := by
  calc
    _ ≤ ∑ h,‖((p h-q h : ℝ):ℂ)*star (F (left h))*G (right h)‖ := norm_sum_le _ _
    _ ≤ ∑ h,|p h-q h| *coefficientBound F*coefficientBound G := by
      apply Finset.sum_le_sum
      intro h _
      simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_le_coefficientBound F _) (abs_nonneg _))
        (norm_le_coefficientBound G _) (norm_nonneg _) (mul_nonneg (abs_nonneg _) (coefficientBound_nonneg F))
    _ = _ := by rw [Finset.sum_mul,Finset.sum_mul]

/-- The factor two uses total variation of the complete actual history law. -/
theorem complex_law_tv_bound {H A B : Type*} [Fintype H] [Fintype A] [Fintype B]
    (p q : H → ℝ) (left : H → A) (right : H → B) (F : A → ℂ) (G : B → ℂ)
    {δ : ℝ} (hδ : (∑ h,|p h-q h|)/2 ≤ δ) :
    ‖∑ h,((p h-q h : ℝ):ℂ)*star (F (left h))*G (right h)‖ ≤
      2*δ*coefficientBound F*coefficientBound G := by
  apply (complex_law_bound p q left right F G).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith) (coefficientBound_nonneg F)) (coefficientBound_nonneg G)

/-- Complete-history total variation; both laws use the same actual strategy. -/
theorem history_tv_bound (R : Data d) (S : Schedule n)
    {σ ρ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ) :
    (∑ h,|mass R S σ h-mass R S ρ h|)/2 ≤ traceDist σ ρ := by
  have h := FiniteAdaptiveProcessRobustness.totalVariation_bound (history R S)
    (joint_density hσ) (joint_density hρ)
  rwa [joint_traceDist] at h

theorem mass_difference_bound (R : Data d) (S : Schedule n)
    {σ ρ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ)
    (h : History d (2*n+1+1)) : |mass R S σ h-mass R S ρ h| ≤ traceDist σ ρ := by
  have he := FiniteAdaptiveProcessRobustness.event_difference_bound (history R S) {h}
    (joint_density hσ) (joint_density hρ)
  simpa [FiniteAdaptiveProcessRobustness.eventProbability,mass,joint_traceDist] using he

theorem kernel_difference_bound (R : Data d) (S : Schedule n)
    {σ ρ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ)
    (u v : GibbsMultilevelCylinder.Path d n) :
    ‖kernel R S σ u v-kernel R S ρ u v‖ ≤ traceDist σ ρ := by
  simpa only [kernel,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using
    mass_difference_bound R S hσ hρ ((pairEquiv n).symm (u,v))

theorem cylinderPairing_difference (R : Data d) (S : Schedule n)
    (σ ρ : Matrix (Fin d) (Fin d) ℂ) (F G : GibbsMultilevelCylinder.Path d n → ℂ) :
    cylinderPairing R S σ F G-cylinderPairing R S ρ F G =
      ∑ h,((mass R S σ h-mass R S ρ h : ℝ):ℂ)*star (F ((pairEquiv n h).1))*G ((pairEquiv n h).2) := by
  simp only [cylinderPairing,← Finset.sum_sub_distrib,Complex.ofReal_sub,sub_mul]

theorem cylinderPairing_difference_bound (R : Data d) (S : Schedule n)
    {σ ρ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ)
    (F G : GibbsMultilevelCylinder.Path d n → ℂ) :
    ‖cylinderPairing R S σ F G-cylinderPairing R S ρ F G‖ ≤
      2*traceDist σ ρ*coefficientBound F*coefficientBound G := by
  rw [cylinderPairing_difference]
  exact complex_law_tv_bound _ _ _ _ F G (history_tv_bound R S hσ hρ)

theorem equilibrium_density (R : Data d) : IsDensityOperator (density R.w) :=
  ⟨(density_posDef R.w R.positive).posSemidef,by rw [GibbsReset.density_trace,R.normalized]; rfl⟩

theorem preparation_pairing_bound (R : Data d) (S : Schedule n)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ)
    (F G : GibbsMultilevelCylinder.Path d n → ℂ) :
    ‖cylinderPairing R S σ F G-GibbsMultilevelCylinder.cylinderPairing R S F G‖ ≤
      2*traceDist σ (density R.w)*coefficientBound F*coefficientBound G :=
  cylinderPairing_difference_bound R S hσ (equilibrium_density R) F G

theorem stationary_quadratic_nonneg (R : Data d) (S : Schedule n)
    (F : GibbsMultilevelCylinder.Path d n → ℂ) :
    0 ≤ (GibbsMultilevelCylinder.cylinderPairing R S F F).re ∧
      (GibbsMultilevelCylinder.cylinderPairing R S F F).im=0 := by
  have h := (GibbsMultilevelCylinder.positive R S).dotProduct_mulVec_nonneg F
  change 0 ≤ pairing (GibbsMultilevelCylinder.kernel R S) F F at h
  rw [GibbsMultilevelCylinder.pairing_actual] at h
  exact ⟨h.1,h.2.symm⟩

/-- Approximate positivity is a real lower bound and an imaginary-part bound. -/
theorem quadratic_defect (R : Data d) (S : Schedule n)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ)
    (F : GibbsMultilevelCylinder.Path d n → ℂ) :
    -(2*traceDist σ (density R.w)*coefficientBound F^2) ≤ (cylinderPairing R S σ F F).re ∧
      |(cylinderPairing R S σ F F).im| ≤ 2*traceDist σ (density R.w)*coefficientBound F^2 := by
  have hb := preparation_pairing_bound R S hσ F F
  have hr := (Complex.abs_re_le_norm _).trans hb
  have hi := (Complex.abs_im_le_norm _).trans hb
  have hp := stationary_quadratic_nonneg R S F
  simp only [Complex.sub_re,Complex.sub_im,hp.2,sub_zero] at hr hi
  constructor
  · have := (abs_le.mp hr).1
    nlinarith [hp.1]
  · nlinarith

theorem warm_history_tv_bound (R : Data d) (S : Schedule n)
    {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) :
    (∑ h,|mass R S (warm R γ τ σ) h-GibbsMultilevelCylinder.mass R S h|)/2 ≤
      Real.exp (-γ*τ)*traceDist σ (density R.w) := by
  simpa only [warm_traceDist R hγ hτ hσ,stationary_mass] using
    history_tv_bound R S (warm_density R hγ hτ hσ) (equilibrium_density R)

theorem warm_kernel_bound (R : Data d) (S : Schedule n)
    {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ)
    (u v : GibbsMultilevelCylinder.Path d n) :
    ‖kernel R S (warm R γ τ σ) u v-GibbsMultilevelCylinder.kernel R S u v‖ ≤
      Real.exp (-γ*τ)*traceDist σ (density R.w) := by
  simpa only [warm_traceDist R hγ hτ hσ,stationary_kernel] using
    kernel_difference_bound R S (warm_density R hγ hτ hσ) (equilibrium_density R) u v

theorem warm_pairing_bound (R : Data d) (S : Schedule n)
    {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ)
    (F G : GibbsMultilevelCylinder.Path d n → ℂ) :
    ‖cylinderPairing R S (warm R γ τ σ) F G-GibbsMultilevelCylinder.cylinderPairing R S F G‖ ≤
      2*(Real.exp (-γ*τ)*traceDist σ (density R.w))*coefficientBound F*coefficientBound G := by
  simpa only [warm_traceDist R hγ hτ hσ] using
    preparation_pairing_bound R S (warm_density R hγ hτ hσ) F G

theorem warm_quadratic_defect (R : Data d) (S : Schedule n)
    {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ)
    (F : GibbsMultilevelCylinder.Path d n → ℂ) :
    -(2*(Real.exp (-γ*τ)*traceDist σ (density R.w))*coefficientBound F^2) ≤
      (cylinderPairing R S (warm R γ τ σ) F F).re ∧
    |(cylinderPairing R S (warm R γ τ σ) F F).im| ≤
      2*(Real.exp (-γ*τ)*traceDist σ (density R.w))*coefficientBound F^2 := by
  simpa only [warm_traceDist R hγ hτ hσ] using quadratic_defect R S (warm_density R hγ hτ hσ) F

/-- Finite warm-up convergence does not restore exact Hermitian symmetry. -/
theorem three_warm_not_hermitian {τ : ℝ} (hτ : 0 ≤ τ) :
    ¬ (kernel three oneTime (warm three 1 τ GibbsReset.concentrated)).IsHermitian := by
  intro h
  have he := h.apply (fun _ => 0) (fun _ => 1)
  rw [three_warm_reverse hτ,three_warm_forward hτ] at he
  simp only [Complex.star_def,Complex.conj_ofReal] at he
  have hr := congrArg Complex.re he
  simp only [Complex.ofReal_re] at hr
  have hp := three_warm_asymmetry_pos hτ
  rw [three_warm_forward hτ,three_warm_reverse hτ] at hp
  simp only [Complex.sub_re,Complex.ofReal_re] at hp
  linarith

theorem three_warm_not_positive {τ : ℝ} (hτ : 0 ≤ τ) :
    ¬ (kernel three oneTime (warm three 1 τ GibbsReset.concentrated)).PosSemidef :=
  fun h => three_warm_not_hermitian hτ h.isHermitian

theorem warm_zero_time (R : Data d) (γ : ℝ) (σ : Matrix (Fin d) (Fin d) ℂ) :
    warm R γ 0 σ = σ := by
  unfold warm
  simp only [mul_zero,Real.exp_zero]
  rw [GibbsReset.time_state R.w (fun i => (R.positive i).le) 1 (by norm_num) le_rfl]
  simp

theorem warm_zero_rate (R : Data d) (τ : ℝ) (σ : Matrix (Fin d) (Fin d) ℂ) :
    warm R 0 τ σ = σ := by
  unfold warm
  simp only [neg_zero,zero_mul,Real.exp_zero]
  rw [GibbsReset.time_state R.w (fun i => (R.positive i).le) 1 (by norm_num) le_rfl]
  simp

theorem warm_stationary (R : Data d) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ) :
    warm R γ τ (density R.w) = density R.w :=
  GibbsReset.time_stationary R.w (fun i => (R.positive i).le) R.normalized _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one γ τ hγ hτ)

theorem warm_stationary_error (R : Data d) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ) :
    traceDist (warm R γ τ (density R.w)) (density R.w) = 0 := by
  rw [warm_stationary R hγ hτ]
  simp [traceDist]

theorem warm_stationary_pairing (R : Data d) (S : Schedule n)
    {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ) (F G : GibbsMultilevelCylinder.Path d n → ℂ) :
    cylinderPairing R S (warm R γ τ (density R.w)) F G = GibbsMultilevelCylinder.cylinderPairing R S F G := by
  rw [warm_stationary R hγ hτ,stationary_pairing]

/-- Repeated observation times retain zero-probability incompatible outer outcomes. -/
theorem four_repeated_impossible (R : Data d) (S : Schedule 1) (ht : S.times 1=S.times 0)
    (σ : Matrix (Fin d) (Fin d) ℂ) (u v : GibbsMultilevelCylinder.Path d 1)
    (h : u 1≠u 0 ∨ v 0≠v 1) : kernel R S σ u v=0 := by
  rw [four_prepared_kernel,(four_lags S).1,(four_lags S).2.2,ht,sub_self]
  rcases h with h | h <;> simp [transition,h]

theorem singleton_zero_rate (R : Data d) (S : Schedule 0) (hγ : R.γ=0)
    (σ : Matrix (Fin d) (Fin d) ℂ) (u v : GibbsMultilevelCylinder.Path d 0) :
    kernel R S σ u v = ((σ (u 0) (u 0)).re * (if u 0=v 0 then 1 else 0) : ℝ) := by
  rw [singleton_prepared_kernel]
  simp [transition,hγ]

theorem singleton_zero_time (R : Data d) (S : Schedule 0) (ht : S.times 0=0)
    (σ : Matrix (Fin d) (Fin d) ℂ) (u v : GibbsMultilevelCylinder.Path d 0) :
    kernel R S σ u v = ((σ (u 0) (u 0)).re * (if u 0=v 0 then 1 else 0) : ℝ) := by
  rw [singleton_prepared_kernel,singleton_lag,ht]
  simp [transition]

theorem three_prepared_forward_pos :
    0 < (kernel three oneTime GibbsReset.concentrated (fun _ => 0) (fun _ => 1)).re := by
  rw [three_prepared_forward]
  simp only [Complex.ofReal_re]
  exact div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))) (by norm_num)

theorem three_prepared_not_hermitian :
    ¬ (kernel three oneTime GibbsReset.concentrated).IsHermitian := by
  simpa only [warm_zero_time] using three_warm_not_hermitian (τ := 0) le_rfl

theorem three_prepared_not_positive :
    ¬ (kernel three oneTime GibbsReset.concentrated).PosSemidef :=
  fun h => three_prepared_not_hermitian h.isHermitian

/- These estimates compare complete finite histories without postselection.
The warm-up precedes the fixed reflected schedule; it is not a schedule shift
or a physical clock identification. No positive perturbed quotient is constructed. -/

end SKEFTHawking.QuantumNetwork.GibbsHistoryPreparationBounds
