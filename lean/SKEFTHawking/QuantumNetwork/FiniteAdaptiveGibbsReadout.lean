import SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness
import SKEFTHawking.FiniteGibbsHistoryPreparationBounds

/-! Actual Unit-spectator Gibbs preparation and complete finite readout laws. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveGibbsReadout
open Matrix FiniteInterventionProcess GibbsMultilevelReflection GibbsHistoryPreparationBounds
open GibbsMultilevelCylinder GibbsMultilevelProcess FiniteAdaptiveReadoutRobustness
open FiniteAdaptiveReadoutDiscrimination FiniteAdaptiveMapPerturbation FiniteAdaptiveMixtureSurvival
open SKEFTHawking.FinitePositiveKernel SKEFTHawking.FinitePositiveKernel.DiagonalLindblad
open scoped ComplexOrder Kronecker
variable {d o k : ℕ}

/-- The common equilibrium term cancels for two arbitrary density preparations. -/
theorem warm_pair_difference (R : Data d) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ ρ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ) :
    warm R γ τ σ - warm R γ τ ρ = (Real.exp (-γ*τ) : ℂ) • (σ-ρ) := by
  rw [warm_state R hγ hτ hσ,warm_state R hγ hτ hρ]
  module

theorem warm_pair_traceDist (R : Data d) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ ρ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ) :
    traceDist (warm R γ τ σ) (warm R γ τ ρ) =
      Real.exp (-γ*τ)*traceDist σ ρ := by
  unfold traceDist
  rw [warm_pair_difference R hγ hτ hσ hρ,traceNorm_smul_nonneg (Real.exp_pos _).le]
  ring

theorem warm_pair_joint_traceDist (R : Data d) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    {σ ρ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ) :
    traceDist (joint (warm R γ τ σ)) (joint (warm R γ τ ρ)) =
      Real.exp (-γ*τ)*traceDist σ ρ := by
  rw [joint_traceDist,warm_pair_traceDist R hγ hτ hσ hρ]

theorem equilibrium_density (R : Data d) : IsDensityOperator (density R.w) := by
  refine ⟨(density_posDef R.w R.positive).posSemidef,?_⟩
  rw [GibbsReset.density_trace,R.normalized]
  simp

theorem projector_density (i : Fin d) : IsDensityOperator (projector i) := by
  refine ⟨?_,projector_trace i⟩
  apply Matrix.PosSemidef.diagonal
  intro j
  change 0 ≤ if j=i then (1:ℂ) else 0
  split_ifs <;> simp


/-- Distinct computational preparations have exact distance one. -/
theorem projector_pair_distance : traceDist (projector (0:Fin 3)) (projector (1:Fin 3)) = 1 := by
  have hd : projector (0:Fin 3)-projector (1:Fin 3) =
      diagonal (fun i : Fin 3 => ((if i=0 then 1 else if i=1 then -1 else 0 : ℝ):ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [projector,Matrix.diagonal_apply]
  rw [traceDist,hd,traceNorm_real_diagonal]
  norm_num [Fin.sum_univ_three,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]


def preparedJoint (R : Data d) (γ τ : ℝ) (σ : Matrix (Fin d) (Fin d) ℂ) := joint (warm R γ τ σ)
theorem preparedJoint_density (R : Data d) {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) :
    IsDensityOperator (preparedJoint R γ τ σ) := joint_density (warm_density R hγ hτ hσ)

theorem equilibrium_output_budget (R : Data d) {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ)
    (T : Tree (Fin d) Unit o k) {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : IsDensityOperator σ) :
    outputDistance (Fin d) Unit o T T (preparedJoint R γ τ σ) (joint (density R.w)) ≤
      Real.exp (-γ*τ)*traceDist σ (density R.w) := by
  have h := outputDistance_common (Fin d) Unit o T
    (preparedJoint_density R hγ hτ hσ).1.isHermitian (joint_density (equilibrium_density R)).1.isHermitian
  simpa only [preparedJoint,warm_joint_traceDist R hγ hτ hσ] using h

theorem warm_equilibrium_stability (R : Data d) {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ)
    (T_A T_B : Tree (Fin d) Unit o k)
    {σA σB : Matrix (Fin d) (Fin d) ℂ}
    (hσA : IsDensityOperator σA) (hσB : IsDensityOperator σB)
    (F : History o k → Matrix (Fin d × Unit) (Fin d × Unit) ℂ) (hF : ∀ h, IsBinaryPOVM (F h))
    (a : History o k → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    (|(1-outputDistance (Fin d) Unit o T_A T_B (preparedJoint R γ τ σA) (preparedJoint R γ τ σB))/2 -
       (1-outputDistance (Fin d) Unit o T_A T_B (joint (density R.w)) (joint (density R.w)))/2| ≤ ((Real.exp (-γ*τ)*traceDist σA (density R.w))+(Real.exp (-γ*τ)*traceDist σB (density R.w)))/2) ∧
    (|readoutError (fun h => run (Fin d) Unit o T_A h (preparedJoint R γ τ σA)) (fun h => run (Fin d) Unit o T_B h (preparedJoint R γ τ σB)) F - readoutError (fun h => run (Fin d) Unit o T_A h (joint (density R.w))) (fun h => run (Fin d) Unit o T_B h (joint (density R.w))) F| ≤ ((Real.exp (-γ*τ)*traceDist σA (density R.w))+(Real.exp (-γ*τ)*traceDist σB (density R.w)))/2) ∧
    (|instrumentError (fun h => run (Fin d) Unit o T_A h (joint (density R.w))) (fun h => run (Fin d) Unit o T_B h (joint (density R.w)))
      (optimalReadout (run_family T_A (preparedJoint_density R hγ hτ hσA)) (run_family T_B (preparedJoint_density R hγ hτ hσB))) -
      (1-outputDistance (Fin d) Unit o T_A T_B (preparedJoint R γ τ σA) (preparedJoint R γ τ σB))/2| ≤ ((Real.exp (-γ*τ)*traceDist σA (density R.w))+(Real.exp (-γ*τ)*traceDist σB (density R.w)))/2) ∧
    (|historyError (fun h => run (Fin d) Unit o T_A h (preparedJoint R γ τ σA)) (fun h => run (Fin d) Unit o T_B h (preparedJoint R γ τ σB)) a - historyError (fun h => run (Fin d) Unit o T_A h (joint (density R.w))) (fun h => run (Fin d) Unit o T_B h (joint (density R.w))) a| ≤ ((Real.exp (-γ*τ)*traceDist σA (density R.w))+(Real.exp (-γ*τ)*traceDist σB (density R.w)))/2) := by
  exact tree_budget_stability T_A T_B T_A T_B
    (preparedJoint_density R hγ hτ hσA) (preparedJoint_density R hγ hτ hσB)
    (joint_density (equilibrium_density R)) (joint_density (equilibrium_density R)) _ _
    (equilibrium_output_budget R hγ hτ T_A hσA) (equilibrium_output_budget R hγ hτ T_B hσB) F hF a ha

theorem warm_paired_errors_stability (R : Data d) {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ)
    (T_A T_B U_A U_B : Tree (Fin d) Unit o k)
    {σA σB : Matrix (Fin d) (Fin d) ℂ}
    (hσA : IsDensityOperator σA) (hσB : IsDensityOperator σB)
    {esA esB : List ℝ}
    (cA : PairedErrors (Fin d) Unit o T_A U_A esA)
    (cB : PairedErrors (Fin d) Unit o T_B U_B esB)
    (F : History o k → Matrix (Fin d × Unit) (Fin d × Unit) ℂ) (hF : ∀ h, IsBinaryPOVM (F h))
    (a : History o k → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    let βA := min 1 ((Real.exp (-γ*τ)*traceDist σA (density R.w)) + esA.sum)
    let βB := min 1 ((Real.exp (-γ*τ)*traceDist σB (density R.w)) + esB.sum)
    (|(1-outputDistance (Fin d) Unit o T_A T_B (preparedJoint R γ τ σA) (preparedJoint R γ τ σB))/2 -
       (1-outputDistance (Fin d) Unit o U_A U_B (joint (density R.w)) (joint (density R.w)))/2| ≤ (βA+βB)/2) ∧
    (|readoutError (fun h => run (Fin d) Unit o T_A h (preparedJoint R γ τ σA)) (fun h => run (Fin d) Unit o T_B h (preparedJoint R γ τ σB)) F - readoutError (fun h => run (Fin d) Unit o U_A h (joint (density R.w))) (fun h => run (Fin d) Unit o U_B h (joint (density R.w))) F| ≤ (βA+βB)/2) ∧
    (|instrumentError (fun h => run (Fin d) Unit o U_A h (joint (density R.w))) (fun h => run (Fin d) Unit o U_B h (joint (density R.w)))
      (optimalReadout (run_family T_A (preparedJoint_density R hγ hτ hσA)) (run_family T_B (preparedJoint_density R hγ hτ hσB))) -
      (1-outputDistance (Fin d) Unit o T_A T_B (preparedJoint R γ τ σA) (preparedJoint R γ τ σB))/2| ≤ (βA+βB)/2) ∧
    (|historyError (fun h => run (Fin d) Unit o T_A h (preparedJoint R γ τ σA)) (fun h => run (Fin d) Unit o T_B h (preparedJoint R γ τ σB)) a - historyError (fun h => run (Fin d) Unit o U_A h (joint (density R.w))) (fun h => run (Fin d) Unit o U_B h (joint (density R.w))) a| ≤ (βA+βB)/2) := by
  have h := tree_paired_errors_stability T_A T_B U_A U_B
    (preparedJoint_density R hγ hτ hσA) (preparedJoint_density R hγ hτ hσB)
    (joint_density (equilibrium_density R)) (joint_density (equilibrium_density R)) cA cB F hF a ha
  simpa only [preparedJoint,warm_joint_traceDist R hγ hτ hσA,warm_joint_traceDist R hγ hτ hσB] using h

theorem warm_paired_mixture_stability (R : Data d) {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ)
    (T_A T_B U_A U_B : Tree (Fin d) Unit o k)
    {σA σB : Matrix (Fin d) (Fin d) ℂ}
    (hσA : IsDensityOperator σA) (hσB : IsDensityOperator σB)
    {rsA rsB : List NoiseRates}
    (cA : PairedMixture (Fin d) Unit o T_A U_A rsA)
    (cB : PairedMixture (Fin d) Unit o T_B U_B rsB)
    (F : History o k → Matrix (Fin d × Unit) (Fin d × Unit) ℂ) (hF : ∀ h, IsBinaryPOVM (F h))
    (a : History o k → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    let βA := survival rsA * (Real.exp (-γ*τ)*traceDist σA (density R.w)) + 1 - survival rsA
    let βB := survival rsB * (Real.exp (-γ*τ)*traceDist σB (density R.w)) + 1 - survival rsB
    (|(1-outputDistance (Fin d) Unit o T_A T_B (preparedJoint R γ τ σA) (preparedJoint R γ τ σB))/2 -
       (1-outputDistance (Fin d) Unit o U_A U_B (joint (density R.w)) (joint (density R.w)))/2| ≤ (βA+βB)/2) ∧
    (|readoutError (fun h => run (Fin d) Unit o T_A h (preparedJoint R γ τ σA)) (fun h => run (Fin d) Unit o T_B h (preparedJoint R γ τ σB)) F - readoutError (fun h => run (Fin d) Unit o U_A h (joint (density R.w))) (fun h => run (Fin d) Unit o U_B h (joint (density R.w))) F| ≤ (βA+βB)/2) ∧
    (|instrumentError (fun h => run (Fin d) Unit o U_A h (joint (density R.w))) (fun h => run (Fin d) Unit o U_B h (joint (density R.w)))
      (optimalReadout (run_family T_A (preparedJoint_density R hγ hτ hσA)) (run_family T_B (preparedJoint_density R hγ hτ hσB))) -
      (1-outputDistance (Fin d) Unit o T_A T_B (preparedJoint R γ τ σA) (preparedJoint R γ τ σB))/2| ≤ (βA+βB)/2) ∧
    (|historyError (fun h => run (Fin d) Unit o T_A h (preparedJoint R γ τ σA)) (fun h => run (Fin d) Unit o T_B h (preparedJoint R γ τ σB)) a - historyError (fun h => run (Fin d) Unit o U_A h (joint (density R.w))) (fun h => run (Fin d) Unit o U_B h (joint (density R.w))) a| ≤ (βA+βB)/2) := by
  have h := tree_paired_mixture_stability T_A T_B U_A U_B
    (preparedJoint_density R hγ hτ hσA) (preparedJoint_density R hγ hτ hσB)
    (joint_density (equilibrium_density R)) (joint_density (equilibrium_density R)) cA cB F hF a ha
  simpa only [preparedJoint,warm_joint_traceDist R hγ hτ hσA,warm_joint_traceDist R hγ hτ hσB] using h

/-! The same actual three-level history is used for every warmup rate and wait. -/
def threeTree : Tree (Fin 3) Unit 3 2 := history three oneTime
def threePrep (γ τ : ℝ) (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ := warm three γ τ (projector j)
def threeInput (γ τ : ℝ) (j : Fin 3) := joint (threePrep γ τ j)
def threeFamily (γ τ : ℝ) (j : Fin 3) (h : History 3 2) := run (Fin 3) Unit 3 threeTree h (threeInput γ τ j)
def retention (γ τ : ℝ) : ℝ := Real.exp (-γ*τ)
def diagonalWeight (γ τ : ℝ) (j i : Fin 3) : ℝ :=
  retention γ τ*(if i=j then 1 else 0)+(1-retention γ τ)*three.w i
def continuation (i : Fin 3) (h : History 3 1) : ℝ := tailMass three 1 (lags oneTime) i h

theorem three_input_density {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (j : Fin 3) :
    IsDensityOperator (threeInput γ τ j) := joint_density (warm_density three hγ hτ (projector_density j))
theorem three_family {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (j : Fin 3) :
    IsBranchFamily (threeFamily γ τ j) := run_family threeTree (three_input_density hγ hτ j)

theorem three_diagonal {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (j i : Fin 3) :
    (threePrep γ τ j i i).re = diagonalWeight γ τ j i := by
  rw [threePrep,warm_state three hγ hτ (projector_density j)]
  simp only [diagonalWeight,retention,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    density,projector,Matrix.diagonal_apply_eq]
  split_ifs <;> simp only [Complex.add_re,Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.one_re,Complex.zero_re,mul_one,mul_zero,sub_zero]

theorem three_lag : lags oneTime 0 = 2 := by rw [singleton_lag]; norm_num [oneTime]
theorem three_history_card : Fintype.card (History 3 2) = 9 := by
  rw [history_card]; norm_num

theorem continuation_formula (i j : Fin 3) : continuation i (j,()) =
    transition three.w three.γ 2 i j := by simp [continuation,tailMass,three_lag]
theorem continuation_nonneg (i : Fin 3) (h : History 3 1) : 0≤continuation i h := by
  have hp := (normalized_weights (Fin 3) Unit 3 (tailTree three 1 (lags oneTime) (lags_nonnegative oneTime))
    (joint_density (projector_density i))).1 h
  have he := tail_trace three 1 (lags oneTime) (lags_nonnegative oneTime) i h 1
  change 0 ≤ (run (Fin 3) Unit 3 (tailTree three 1 (lags oneTime) (lags_nonnegative oneTime)) h (joint (projector i))).trace.re at hp
  have hr := congrArg Complex.re he
  simp only [one_smul,one_mul,Complex.ofReal_re] at hr
  rw [hr] at hp
  exact hp

theorem continuation_total (i : Fin 3) : ∑ h,continuation i h = 1 := tailMass_sum three 1 (lags oneTime) i

/-- Every one of the nine evaluated histories, including every zero cell. -/
theorem three_complete_law {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (j : Fin 3) (h : History 3 2) :
    (threeFamily γ τ j h).trace.re = diagonalWeight γ τ j h.1 * continuation h.1 h.2 := by
  change weight (Fin 3) Unit 3 threeTree h (joint (threePrep γ τ j)) = _
  rw [threeTree,history,prepared_history_weight,three_diagonal hγ hτ]
  rfl

theorem three_first_marginal {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (j i : Fin 3) :
    ∑ h : History 3 1,(threeFamily γ τ j (i,h)).trace.re = diagonalWeight γ τ j i := by
  simp only [three_complete_law hγ hτ,← Finset.mul_sum,continuation_total,mul_one]

theorem three_signed_law {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (h : History 3 2) :
    (threeFamily γ τ 0 h).trace.re-(threeFamily γ τ 1 h).trace.re =
      retention γ τ*((if h.1=0 then 1 else 0)-(if h.1=1 then 1 else 0))*continuation h.1 h.2 := by
  rw [three_complete_law hγ hτ,three_complete_law hγ hτ]
  unfold diagonalWeight
  ring

theorem three_full_history_variation {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    familyHistoryVariation (threeFamily γ τ 0) (threeFamily γ τ 1) = retention γ τ := by
  unfold familyHistoryVariation
  change (∑ h : Fin 3 × History 3 1, |(threeFamily γ τ 0 h).trace.re-(threeFamily γ τ 1 h).trace.re|)/2 = _
  rw [Fintype.sum_prod_type]
  simp only [three_signed_law hγ hτ,abs_mul,
    abs_of_nonneg (show 0≤retention γ τ from (Real.exp_pos _).le),
    abs_of_nonneg (continuation_nonneg _ _)]
  norm_num [Fin.sum_univ_three,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]
  rw [← Finset.mul_sum,← Finset.mul_sum,continuation_total,continuation_total]
  ring

theorem three_input_distance {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    traceDist (threeInput γ τ 0) (threeInput γ τ 1) = retention γ τ := by
  rw [threeInput,threeInput,threePrep,threePrep,
    warm_pair_joint_traceDist three hγ hτ (projector_density _) (projector_density _),projector_pair_distance,mul_one]
  rfl

theorem three_output_distance {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    outputDistance (Fin 3) Unit 3 threeTree threeTree (threeInput γ τ 0) (threeInput γ τ 1) = retention γ τ := by
  apply le_antisymm
  · simpa only [three_input_distance hγ hτ] using
      outputDistance_common (Fin 3) Unit 3 threeTree (three_input_density hγ hτ 0).1.isHermitian
        (three_input_density hγ hτ 1).1.isHermitian
  · have h := familyHistoryVariation_le_branchDistance (three_family hγ hτ 0) (three_family hγ hτ 1)
    rw [three_full_history_variation hγ hτ] at h
    change retention γ τ ≤ branchDistance (fun h => run (Fin 3) Unit 3 threeTree h (threeInput γ τ 0))
      (fun h => run (Fin 3) Unit 3 threeTree h (threeInput γ τ 1)) at h
    rw [tree_branchDistance] at h
    exact h


/-- Choose the preparation-zero hypothesis exactly on first label zero. -/
def eventScore (h : History 3 2) : ℝ := if h.1=0 then 1 else 0
def eventProjection (h : History 3 2) : Matrix (Fin 3 × Unit) (Fin 3 × Unit) ℂ := (eventScore h:ℂ) • 1

theorem eventScore_admissible (h : History 3 2) : eventScore h ∈ Set.Icc (0:ℝ) 1 := by
  unfold eventScore
  split_ifs <;> constructor <;> norm_num

theorem eventProjection_hermitian (h : History 3 2) : (eventProjection h).IsHermitian := by
  unfold eventProjection eventScore
  split_ifs <;> simp

theorem eventProjection_square (h : History 3 2) : eventProjection h*eventProjection h=eventProjection h := by
  unfold eventProjection eventScore
  split_ifs <;> simp

def eventReadout (h : History 3 2) : FiniteInstrument (Fin 3 × Unit) 2 :=
  projectiveReadout (eventProjection h) (eventProjection_hermitian h) (eventProjection_square h)

theorem eventReadout_count (h : History 3 2) : (eventReadout h).count=1 := rfl

theorem eventReadout_zero (h : History 3 2) (Z : Matrix (Fin 3 × Unit) (Fin 3 × Unit) ℂ) :
    (eventReadout h).weight 0 Z = eventScore h*Z.trace.re := by
  rw [eventReadout,projectiveReadout_weight_zero]
  simp only [eventProjection,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_smul]
  simp

theorem eventReadout_one (h : History 3 2) (Z : Matrix (Fin 3 × Unit) (Fin 3 × Unit) ℂ) :
    (eventReadout h).weight 1 Z = (1-eventScore h)*Z.trace.re := by
  rw [eventReadout,projectiveReadout_weight_one]
  by_cases hh : h.1=0 <;> simp [eventProjection,eventScore,hh]

theorem eventTable_complete {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (j : Fin 3) (h : History 3 2) (a : Fin 2) :
    readoutTable eventReadout (threeFamily γ τ j) h a =
      (if a=0 then eventScore h else 1-eventScore h)*diagonalWeight γ τ j h.1*continuation h.1 h.2 := by
  by_cases ha : a=0
  · subst a
    rw [readoutTable,eventReadout_zero,three_complete_law hγ hτ]
    simp only [ite_true]
    ring
  · have ha1 : a=1 := by omega
    subst a
    rw [readoutTable,eventReadout_one,three_complete_law hγ hτ]
    simp only [show (1:Fin 2) ≠ 0 by decide,if_false]
    ring

theorem eventTable_probabilities {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (j : Fin 3) :
    (∀ h a,0≤readoutTable eventReadout (threeFamily γ τ j) h a) ∧
      (∑ h,∑ a,readoutTable eventReadout (threeFamily γ τ j) h a)=1 :=
  ⟨readoutTable_nonneg eventReadout (three_family hγ hτ j),readoutTable_total eventReadout (three_family hγ hτ j)⟩

theorem eventExpectation {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (j : Fin 3) :
    ∑ h,eventScore h*(threeFamily γ τ j h).trace.re = diagonalWeight γ τ j 0 := by
  change (∑ h : Fin 3 × History 3 1,eventScore h*(threeFamily γ τ j h).trace.re)=_
  rw [Fintype.sum_prod_type]
  have hx (i : Fin 3) : (∑ h : History 3 1,eventScore (i,h)*(threeFamily γ τ j (i,h)).trace.re)=
      if i=0 then diagonalWeight γ τ j i else 0 := by
    by_cases hi : i=0
    · simp only [eventScore,hi,ite_true,one_mul]
      exact three_first_marginal hγ hτ j 0
    · simp [eventScore,hi]
  simp only [hx]
  simp

theorem eventHistory_error {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    historyError (threeFamily γ τ 0) (threeFamily γ τ 1) eventScore = (1-retention γ τ)/2 := by
  rw [historyError_eq (three_family hγ hτ 0)]
  simp only [mul_sub,Finset.sum_sub_distrib,eventExpectation hγ hτ]
  simp only [diagonalWeight,ite_true,show (0:Fin 3) ≠ 1 by decide,if_false,mul_one,mul_zero]
  ring

theorem eventPhysical_error {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    instrumentError (threeFamily γ τ 0) (threeFamily γ τ 1) eventReadout = (1-retention γ τ)/2 := by
  rw [← eventHistory_error hγ hτ]
  simp only [instrumentError,readoutTable,eventReadout_zero,eventReadout_one,historyError]

theorem eventEffect_error {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    readoutError (threeFamily γ τ 0) (threeFamily γ τ 1) eventProjection = (1-retention γ τ)/2 := by
  change readoutError (threeFamily γ τ 0) (threeFamily γ τ 1) (fun h => (eventScore h:ℂ) • 1) = _
  rw [historyError_scalar_effect,eventHistory_error hγ hτ]

theorem three_all_effect_isLeast {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    IsLeast {x : ℝ | ∃ F : History 3 2 → Matrix (Fin 3 × Unit) (Fin 3 × Unit) ℂ,
      (∀ h,IsBinaryPOVM (F h)) ∧ readoutError (threeFamily γ τ 0) (threeFamily γ τ 1) F=x}
      ((1-retention γ τ)/2) := by
  have h := readoutError_isLeast (three_family hγ hτ 0) (three_family hγ hτ 1)
  have hd : branchDistance (threeFamily γ τ 0) (threeFamily γ τ 1)=retention γ τ := by
    change branchDistance (fun h => run (Fin 3) Unit 3 threeTree h (threeInput γ τ 0))
      (fun h => run (Fin 3) Unit 3 threeTree h (threeInput γ τ 1)) = _
    rw [tree_branchDistance,three_output_distance hγ hτ]
  simpa only [hd] using h

theorem three_every_randomized_isLeast {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    IsLeast {x : ℝ | ∃ a : History 3 2 → ℝ,(∀ h,a h ∈ Set.Icc (0:ℝ) 1) ∧
      historyError (threeFamily γ τ 0) (threeFamily γ τ 1) a=x} ((1-retention γ τ)/2) := by
  simpa only [three_full_history_variation hγ hτ] using
    historyError_isLeast (three_family hγ hτ 0) (three_family hγ hτ 1)


/-- Actual warmed inputs have an attained optimum over every joint effect. -/
theorem warm_error_isLeast (R : Data d) {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ)
    (T_A T_B : Tree (Fin d) Unit o k) {σA σB : Matrix (Fin d) (Fin d) ℂ}
    (hσA : IsDensityOperator σA) (hσB : IsDensityOperator σB) :
    IsLeast {x : ℝ | ∃ F : History o k → Matrix (Fin d × Unit) (Fin d × Unit) ℂ,
      (∀ h,IsBinaryPOVM (F h)) ∧ readoutError
        (fun h => run (Fin d) Unit o T_A h (preparedJoint R γ τ σA))
        (fun h => run (Fin d) Unit o T_B h (preparedJoint R γ τ σB)) F=x}
      ((1-outputDistance (Fin d) Unit o T_A T_B (preparedJoint R γ τ σA) (preparedJoint R γ τ σB))/2) :=
  tree_error_isLeast T_A T_B (preparedJoint_density R hγ hτ hσA) (preparedJoint_density R hγ hτ hσB)

theorem warm_history_isLeast (R : Data d) {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ)
    (T_A T_B : Tree (Fin d) Unit o k) {σA σB : Matrix (Fin d) (Fin d) ℂ}
    (hσA : IsDensityOperator σA) (hσB : IsDensityOperator σB) :
    IsLeast {x : ℝ | ∃ a : History o k → ℝ,(∀ h,a h ∈ Set.Icc (0:ℝ) 1) ∧ historyError
        (fun h => run (Fin d) Unit o T_A h (preparedJoint R γ τ σA))
        (fun h => run (Fin d) Unit o T_B h (preparedJoint R γ τ σB)) a=x}
      ((1-historyVariation (Fin d) Unit o T_A T_B (preparedJoint R γ τ σA) (preparedJoint R γ τ σB))/2) :=
  tree_history_isLeast T_A T_B (preparedJoint_density R hγ hτ hσA) (preparedJoint_density R hγ hτ hσB)

theorem equilibrium_error_isLeast (R : Data d) (T_A T_B : Tree (Fin d) Unit o k) :
    IsLeast {x : ℝ | ∃ F : History o k → Matrix (Fin d × Unit) (Fin d × Unit) ℂ,
      (∀ h,IsBinaryPOVM (F h)) ∧ readoutError
        (fun h => run (Fin d) Unit o T_A h (joint (density R.w)))
        (fun h => run (Fin d) Unit o T_B h (joint (density R.w))) F=x}
      ((1-outputDistance (Fin d) Unit o T_A T_B (joint (density R.w)) (joint (density R.w)))/2) :=
  tree_error_isLeast T_A T_B (joint_density (equilibrium_density R)) (joint_density (equilibrium_density R))

theorem equilibrium_history_isLeast (R : Data d) (T_A T_B : Tree (Fin d) Unit o k) :
    IsLeast {x : ℝ | ∃ a : History o k → ℝ,(∀ h,a h ∈ Set.Icc (0:ℝ) 1) ∧ historyError
        (fun h => run (Fin d) Unit o T_A h (joint (density R.w)))
        (fun h => run (Fin d) Unit o T_B h (joint (density R.w))) a=x}
      ((1-historyVariation (Fin d) Unit o T_A T_B (joint (density R.w)) (joint (density R.w)))/2) :=
  tree_history_isLeast T_A T_B (joint_density (equilibrium_density R)) (joint_density (equilibrium_density R))

/-- The nominal physical instrument has all four normalized tables and the perturbed optimizer has two. -/
theorem warm_physical_probabilities (R : Data d) {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ)
    (T_A T_B U_A U_B : Tree (Fin d) Unit o k) {σA σB : Matrix (Fin d) (Fin d) ℂ}
    (hσA : IsDensityOperator σA) (hσB : IsDensityOperator σB) :
    let I := optimalReadout (run_family T_A (preparedJoint_density R hγ hτ hσA)) (run_family T_B (preparedJoint_density R hγ hτ hσB))
    let J := optimalReadout (run_family U_A (joint_density (equilibrium_density R))) (run_family U_B (joint_density (equilibrium_density R)))
    ((∀ h a, 0 ≤ readoutTable I (fun h => run (Fin d) Unit o T_A h (preparedJoint R γ τ σA)) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run (Fin d) Unit o T_A h (preparedJoint R γ τ σA)) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable I (fun h => run (Fin d) Unit o T_B h (preparedJoint R γ τ σB)) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run (Fin d) Unit o T_B h (preparedJoint R γ τ σB)) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable I (fun h => run (Fin d) Unit o U_A h (joint (density R.w))) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run (Fin d) Unit o U_A h (joint (density R.w))) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable I (fun h => run (Fin d) Unit o U_B h (joint (density R.w))) h a) ∧ (∑ h, ∑ a, readoutTable I (fun h => run (Fin d) Unit o U_B h (joint (density R.w))) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable J (fun h => run (Fin d) Unit o U_A h (joint (density R.w))) h a) ∧ (∑ h, ∑ a, readoutTable J (fun h => run (Fin d) Unit o U_A h (joint (density R.w))) h a) = 1) ∧
    ((∀ h a, 0 ≤ readoutTable J (fun h => run (Fin d) Unit o U_B h (joint (density R.w))) h a) ∧ (∑ h, ∑ a, readoutTable J (fun h => run (Fin d) Unit o U_B h (joint (density R.w))) h a) = 1) :=
  tree_physical_probabilities T_A T_B U_A U_B
    (preparedJoint_density R hγ hτ hσA) (preparedJoint_density R hγ hτ hσB)
    (joint_density (equilibrium_density R)) (joint_density (equilibrium_density R))

/-- Actual zero wait/rate and stationary identities are on the same Unit carrier. -/
theorem preparation_endpoint_identities (R : Data d) {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ)
    (σ : Matrix (Fin d) (Fin d) ℂ) :
    preparedJoint R γ 0 σ=joint σ ∧ preparedJoint R 0 τ σ=joint σ ∧
      preparedJoint R γ τ (density R.w)=joint (density R.w) := by
  simp only [preparedJoint,warm_zero_time,warm_zero_rate,warm_stationary R hγ hτ,and_self]


/-- The finite observation rate is one; warmup rate remains independently specified. -/
theorem three_observation_lags : three.γ=1 ∧ lags oneTime 0=2 := ⟨rfl,three_lag⟩

theorem three_history_variation {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    historyVariation (Fin 3) Unit 3 threeTree threeTree (threeInput γ τ 0) (threeInput γ τ 1)=retention γ τ :=
  three_full_history_variation hγ hτ

/-- Zero waiting changes the preparation itself by the actual channel identity. -/
theorem three_zero_wait_inputs (γ : ℝ) (j : Fin 3) : threeInput γ 0 j=joint (projector j) := by
  rw [threeInput,threePrep,warm_zero_time]

theorem three_zero_rate_inputs (τ : ℝ) (j : Fin 3) : threeInput 0 τ j=joint (projector j) := by
  rw [threeInput,threePrep,warm_zero_rate]

theorem three_zero_wait {γ : ℝ} (hγ : 0≤γ) :
    outputDistance (Fin 3) Unit 3 threeTree threeTree (threeInput γ 0 0) (threeInput γ 0 1)=1 ∧
    historyVariation (Fin 3) Unit 3 threeTree threeTree (threeInput γ 0 0) (threeInput γ 0 1)=1 ∧
    instrumentError (threeFamily γ 0 0) (threeFamily γ 0 1) eventReadout=0 := by
  rw [three_output_distance hγ le_rfl,three_history_variation hγ le_rfl,eventPhysical_error hγ le_rfl]
  norm_num [retention]

theorem three_zero_rate {τ : ℝ} (hτ : 0≤τ) :
    outputDistance (Fin 3) Unit 3 threeTree threeTree (threeInput 0 τ 0) (threeInput 0 τ 1)=1 ∧
    historyVariation (Fin 3) Unit 3 threeTree threeTree (threeInput 0 τ 0) (threeInput 0 τ 1)=1 ∧
    instrumentError (threeFamily 0 τ 0) (threeFamily 0 τ 1) eventReadout=0 := by
  rw [three_output_distance le_rfl hτ,three_history_variation le_rfl hτ,eventPhysical_error le_rfl hτ]
  norm_num [retention]

theorem log_two_nonnegative : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
theorem retention_log_two : retention 1 (Real.log 2)=1/2 := by
  simp only [retention,neg_mul,one_mul,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
  norm_num

theorem three_log_two_distances :
    outputDistance (Fin 3) Unit 3 threeTree threeTree (threeInput 1 (Real.log 2) 0) (threeInput 1 (Real.log 2) 1)=1/2 ∧
    historyVariation (Fin 3) Unit 3 threeTree threeTree (threeInput 1 (Real.log 2) 0) (threeInput 1 (Real.log 2) 1)=1/2 ∧
    instrumentError (threeFamily 1 (Real.log 2) 0) (threeFamily 1 (Real.log 2) 1) eventReadout=1/4 := by
  rw [three_output_distance (by norm_num) log_two_nonnegative,
    three_history_variation (by norm_num) log_two_nonnegative,eventPhysical_error (by norm_num) log_two_nonnegative,retention_log_two]
  norm_num

theorem three_log_two_all_effects :
    IsLeast {x : ℝ | ∃ F : History 3 2 → Matrix (Fin 3 × Unit) (Fin 3 × Unit) ℂ,
      (∀ h,IsBinaryPOVM (F h)) ∧ readoutError (threeFamily 1 (Real.log 2) 0) (threeFamily 1 (Real.log 2) 1) F=x} (1/4) := by
  convert three_all_effect_isLeast (by norm_num : (0:ℝ)≤1) log_two_nonnegative using 1
  norm_num [retention_log_two]

theorem three_log_two_every_randomized :
    IsLeast {x : ℝ | ∃ a : History 3 2 → ℝ,(∀ h,a h ∈ Set.Icc (0:ℝ) 1) ∧
      historyError (threeFamily 1 (Real.log 2) 0) (threeFamily 1 (Real.log 2) 1) a=x} (1/4) := by
  convert three_every_randomized_isLeast (by norm_num : (0:ℝ)≤1) log_two_nonnegative using 1
  norm_num [retention_log_two]

theorem three_positive_finite_wait {τ : ℝ} (hτ : 0<τ) :
    0<outputDistance (Fin 3) Unit 3 threeTree threeTree (threeInput 1 τ 0) (threeInput 1 τ 1) ∧
    outputDistance (Fin 3) Unit 3 threeTree threeTree (threeInput 1 τ 0) (threeInput 1 τ 1)<1 ∧
    0 < instrumentError (threeFamily 1 τ 0) (threeFamily 1 τ 1) eventReadout ∧
    instrumentError (threeFamily 1 τ 0) (threeFamily 1 τ 1) eventReadout<1/2 := by
  rw [three_output_distance (by norm_num) hτ.le,eventPhysical_error (by norm_num) hτ.le]
  have hp : 0<retention 1 τ := Real.exp_pos _
  have h1 : retention 1 τ<1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  exact ⟨hp,h1,by linarith,by linarith⟩

/-- Identical stationary inputs under this same tree have distance zero and error one half. -/
def stationaryFamily (γ τ : ℝ) (h : History 3 2) :=
  run (Fin 3) Unit 3 threeTree h (preparedJoint three γ τ (density three.w))

theorem stationary_input {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    preparedJoint three γ τ (density three.w)=joint (density three.w) := by
  rw [preparedJoint,warm_stationary three hγ hτ]

theorem stationary_family {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    IsBranchFamily (stationaryFamily γ τ) :=
  run_family threeTree (preparedJoint_density three hγ hτ (equilibrium_density three))

theorem stationary_same_tree {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    outputDistance (Fin 3) Unit 3 threeTree threeTree
      (preparedJoint three γ τ (density three.w)) (preparedJoint three γ τ (density three.w))=0 ∧
    historyVariation (Fin 3) Unit 3 threeTree threeTree
      (preparedJoint three γ τ (density three.w)) (preparedJoint three γ τ (density three.w))=0 ∧
    instrumentError (stationaryFamily γ τ) (stationaryFamily γ τ) eventReadout=1/2 := by
  have hZ := stationary_family hγ hτ
  constructor
  · simp [outputDistance,traceNorm_zero]
  constructor
  · simp [historyVariation]
  · simp only [instrumentError,readoutTable,eventReadout_zero,eventReadout_one]
    have hs : (∑ h,(eventScore h*(stationaryFamily γ τ h).trace.re +
      (1-eventScore h)*(stationaryFamily γ τ h).trace.re))=1 := by
      convert hZ.2 using 1
      apply Finset.sum_congr rfl
      intro h _
      ring
    rw [← Finset.sum_add_distrib,hs]

theorem stationary_all_effects {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    IsLeast {x : ℝ | ∃ F : History 3 2 → Matrix (Fin 3 × Unit) (Fin 3 × Unit) ℂ,
      (∀ h,IsBinaryPOVM (F h)) ∧ readoutError (stationaryFamily γ τ) (stationaryFamily γ τ) F=x} (1/2) := by
  simpa only [branchDistance_self,sub_zero] using readoutError_isLeast (stationary_family hγ hτ) (stationary_family hγ hτ)

theorem stationary_every_randomized {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    IsLeast {x : ℝ | ∃ a : History 3 2 → ℝ,(∀ h,a h ∈ Set.Icc (0:ℝ) 1) ∧
      historyError (stationaryFamily γ τ) (stationaryFamily γ τ) a=x} (1/2) := by
  simpa only [familyHistoryVariation,sub_self,abs_zero,Finset.sum_const_zero,zero_div,sub_zero] using historyError_isLeast (stationary_family hγ hτ) (stationary_family hγ hτ)


/-- Repeated observations are retained in a complete nine-history carrier. -/
def zeroTime : Schedule 0 where
  times := fun _ => 0
  ordered := monotone_const
  nonnegative := fun _ => le_rfl

def zeroTree : Tree (Fin 3) Unit 3 2 := history three zeroTime
def zeroFamily (γ τ : ℝ) (j : Fin 3) (h : History 3 2) :=
  run (Fin 3) Unit 3 zeroTree h (threeInput γ τ j)

theorem zero_history_lag : lags zeroTime 0=0 := by rw [singleton_lag]; simp [zeroTime]

theorem zero_complete_law {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (j : Fin 3) (h : History 3 2) :
    (zeroFamily γ τ j h).trace.re =
      diagonalWeight γ τ j h.1*(if h.1=h.2.1 then 1 else 0) := by
  change weight (Fin 3) Unit 3 zeroTree h (joint (threePrep γ τ j)) = _
  rw [zeroTree,history,prepared_history_weight,three_diagonal hγ hτ]
  simp [tailMass,zero_history_lag,GibbsMultilevelReflection.transition]

theorem zero_impossible_under_both {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ)
    (h : History 3 2) (hi : h.1≠h.2.1) :
    (zeroFamily γ τ 0 h).trace.re=0 ∧ (zeroFamily γ τ 1 h).trace.re=0 := by
  simp only [zero_complete_law hγ hτ,hi,if_false,mul_zero,and_self]

theorem zero_full_normalized_law {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (j : Fin 3) :
    (∀ h,0≤(zeroFamily γ τ j h).trace.re) ∧ (∑ h,(zeroFamily γ τ j h).trace.re)=1 :=
  normalized_weights (Fin 3) Unit 3 zeroTree (three_input_density hγ hτ j)

/-- The original preparation-dependent reflected kernel retains both negative guards. -/
theorem original_reflected_kernel_guards {τ : ℝ} (hτ : 0≤τ) :
    ¬ (GibbsHistoryPreparationBounds.kernel three oneTime (warm three 1 τ GibbsReset.concentrated)).IsHermitian ∧
    ¬ (GibbsHistoryPreparationBounds.kernel three oneTime (warm three 1 τ GibbsReset.concentrated)).PosSemidef :=
  ⟨three_warm_not_hermitian hτ,three_warm_not_positive hτ⟩

/-- Numerical nonuniform preparation weights are derived from the actual warm channel. -/
def preparationTable (γ τ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![(1+retention γ τ)/2,(1-retention γ τ)/3,(1-retention γ τ)/6],
    ![(1-retention γ τ)/2,(1+2*retention γ τ)/3,(1-retention γ τ)/6],
    ![(1-retention γ τ)/2,(1-retention γ τ)/3,(1+5*retention γ τ)/6]]

/-- The observation rate remains one and the second observation lag remains two. -/
def observedTransition : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![(1+Real.exp (-2))/2,(1-Real.exp (-2))/3,(1-Real.exp (-2))/6],
    ![(1-Real.exp (-2))/2,(1+2*Real.exp (-2))/3,(1-Real.exp (-2))/6],
    ![(1-Real.exp (-2))/2,(1-Real.exp (-2))/3,(1+5*Real.exp (-2))/6]]

theorem preparationTable_actual (γ τ : ℝ) (j i : Fin 3) :
    diagonalWeight γ τ j i=preparationTable γ τ j i := by
  fin_cases j <;> fin_cases i <;> norm_num [diagonalWeight,preparationTable,three,GibbsReset.threeWeights] <;> ring

theorem observedTransition_actual (i j : Fin 3) :
    transition three.w three.γ 2 i j=observedTransition i j := by
  fin_cases i <;> fin_cases j <;> norm_num [GibbsMultilevelReflection.transition,observedTransition,three,GibbsReset.threeWeights] <;> ring

/-- All nine explicitly evaluated cells under each warmed hypothesis use this same table. -/
theorem three_all_nine_cells {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) (j i l : Fin 3) :
    (threeFamily γ τ j (i,l,())).trace.re=preparationTable γ τ j i*observedTransition i l := by
  rw [three_complete_law hγ hτ,continuation_formula,preparationTable_actual,observedTransition_actual]

/-- The zero-lag first branch is the actual computational collapse, before the normalized lag-two tail. -/
theorem three_first_branch_actual (γ τ : ℝ) (j i : Fin 3) :
    (step three.w three.positive three.normalized three.γ 0 three.rate_nonneg le_rfl).branch
      (Fin 3) Unit 3 i (threeInput γ τ j) = joint (threePrep γ τ j i i • projector i) :=
  prepared_first_collapse three (threePrep γ τ j) i


theorem eventProjection_admissible (h : History 3 2) : IsBinaryPOVM (eventProjection h) :=
  scalar_effect_admissible eventScore eventScore_admissible h

/-- The explicitly evaluated physical event is an actual member of the all-effect admissible set. -/
theorem three_event_attaining_member {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    ((1-retention γ τ)/2) ∈ {x : ℝ | ∃ F : History 3 2 → Matrix (Fin 3 × Unit) (Fin 3 × Unit) ℂ,
      (∀ h,IsBinaryPOVM (F h)) ∧ readoutError (threeFamily γ τ 0) (threeFamily γ τ 1) F=x} :=
  ⟨eventProjection,eventProjection_admissible,eventEffect_error hγ hτ⟩

theorem three_event_randomized_member {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ) :
    ((1-retention γ τ)/2) ∈ {x : ℝ | ∃ a : History 3 2 → ℝ,(∀ h,a h ∈ Set.Icc (0:ℝ) 1) ∧
      historyError (threeFamily γ τ 0) (threeFamily γ τ 1) a=x} :=
  ⟨eventScore,eventScore_admissible,eventHistory_error hγ hτ⟩

theorem warm_optimalReadout_attains (R : Data d) {γ τ : ℝ} (hγ : 0≤γ) (hτ : 0≤τ)
    (T_A T_B : Tree (Fin d) Unit o k) {σA σB : Matrix (Fin d) (Fin d) ℂ}
    (hσA : IsDensityOperator σA) (hσB : IsDensityOperator σB) :
    let hA := run_family T_A (preparedJoint_density R hγ hτ hσA)
    let hB := run_family T_B (preparedJoint_density R hγ hτ hσB)
    instrumentError (fun h => run (Fin d) Unit o T_A h (preparedJoint R γ τ σA))
      (fun h => run (Fin d) Unit o T_B h (preparedJoint R γ τ σB)) (optimalReadout hA hB) =
      (1-outputDistance (Fin d) Unit o T_A T_B (preparedJoint R γ τ σA) (preparedJoint R γ τ σB))/2 := by
  dsimp only
  simpa only [instrumentError,tree_branchDistance] using
    optimalReadout_error (run_family T_A (preparedJoint_density R hγ hτ hσA))
      (run_family T_B (preparedJoint_density R hγ hτ hσB))

theorem equilibrium_optimalReadout_attains (R : Data d) (T_A T_B : Tree (Fin d) Unit o k) :
    let hA := run_family T_A (joint_density (equilibrium_density R))
    let hB := run_family T_B (joint_density (equilibrium_density R))
    instrumentError (fun h => run (Fin d) Unit o T_A h (joint (density R.w)))
      (fun h => run (Fin d) Unit o T_B h (joint (density R.w))) (optimalReadout hA hB) =
      (1-outputDistance (Fin d) Unit o T_A T_B (joint (density R.w)) (joint (density R.w)))/2 := by
  dsimp only
  simpa only [instrumentError,tree_branchDistance] using
    optimalReadout_error (run_family T_A (joint_density (equilibrium_density R)))
      (run_family T_B (joint_density (equilibrium_density R)))

/-- The rate-one preparation gives the original alpha = exp(-tau) on this same actual history. -/
theorem three_main_values {τ : ℝ} (hτ : 0≤τ) :
    outputDistance (Fin 3) Unit 3 threeTree threeTree (threeInput 1 τ 0) (threeInput 1 τ 1)=Real.exp (-τ) ∧
    historyVariation (Fin 3) Unit 3 threeTree threeTree (threeInput 1 τ 0) (threeInput 1 τ 1)=Real.exp (-τ) ∧
    instrumentError (threeFamily 1 τ 0) (threeFamily 1 τ 1) eventReadout=(1-Real.exp (-τ))/2 := by
  rw [three_output_distance (by norm_num) hτ,three_history_variation (by norm_num) hτ,eventPhysical_error (by norm_num) hτ]
  simp [retention]

end SKEFTHawking.QuantumNetwork.FiniteAdaptiveGibbsReadout
