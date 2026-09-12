import SKEFTHawking.FiniteGibbsRelaxationProcess

/-! Two-time equilibrium statistics of actual finite intervention trees.
The initial instrument collapses the state before the lag channel acts.
These are finite operational correlations, with all branches unnormalized. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.GibbsTwoTimeProcess
open Matrix FiniteInterventionProcess FinitePositiveKernel GibbsRelaxationProcess
open FinitePositiveKernel.DiagonalLindblad
open scoped ComplexOrder

def equilibrium (β Δ : ℝ) : Matrix Qubit Qubit ℂ := density (weights β Δ)

theorem equilibrium_density (β Δ : ℝ) : IsDensityOperator (equilibrium β Δ) := by
  refine ⟨(density_posDef _ (weights_pos β Δ)).posSemidef,?_⟩
  rw [equilibrium,GibbsReset.density_trace,weights_sum]
  norm_num

theorem equilibrium_gibbs (β Δ : ℝ) : equilibrium β Δ = FiniteGibbsClock.gibbs (density (energies Δ)) β :=
  GibbsReset.density_gibbsWeights _ _

theorem channel_zero (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (X : Matrix Qubit Qubit ℂ) :
    krausMap (channel β Δ γ η 0) X=X := by
  ext i j
  by_cases hij : i=j
  · subst j
    rw [channel_diagonal β Δ γ η 0 hγ hη (by norm_num)]
    norm_num
  · rw [channel_offdiagonal β Δ γ η 0 hγ hη (by norm_num) X i j hij]
    norm_num

theorem joint_smul (c : ℂ) (X : Matrix Qubit Qubit ℂ) : joint (c • X)=c • joint X := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [joint_apply]

/-- Computational Gibbs branches retain their actual equilibrium masses. -/
theorem computational_collapse (β Δ : ℝ) (a : Fin 2) :
    FiniteInstrument.computational.branch a (equilibrium β Δ) =
      (weights β Δ a:ℂ) • FiniteMemoryProcess.basisState a := by
  simp only [FiniteInstrument.branch,FiniteInstrument.computational,krausMap]
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [equilibrium,density,FiniteMemoryProcess.basisState,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Fin.sum_univ_two]

/-- A plus/minus observation of the diagonal Gibbs state has mass one half in each branch. -/
theorem x_collapse (β Δ : ℝ) (a : Fin 2) :
    xInstrument.branch a (equilibrium β Δ) = (1/2:ℂ) • xProjector a := by
  have hn : (weights β Δ 0:ℂ)+weights β Δ 1=1 := by
    exact_mod_cast (show weights β Δ 0+weights β Δ 1=1 by simpa [Fin.sum_univ_two] using weights_sum β Δ)
  simp only [FiniteInstrument.branch,xInstrument,krausMap]
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [equilibrium,density,xProjector,plus,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_two,Matrix.vecMul,dotProduct] <;>
    simp only [map_ofNat] <;> first | linear_combination hn/4 | linear_combination -hn/4

/-- Initial observation at time zero, followed by the actual lag channel and second observation. -/
def twoTree (I : FiniteInstrument Qubit 2) (β Δ γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : Tree Qubit Unit 2 2 :=
  .node (step I β Δ γ η 0 hγ hη (by norm_num))
    (fun _ => tree I β Δ γ η t hγ hη ht)

theorem initial_branch (I : FiniteInstrument Qubit 2) (β Δ γ η : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (a : Fin 2) :
    (step I β Δ γ η 0 hγ hη (by norm_num)).branch Qubit Unit 2 a (joint (equilibrium β Δ)) =
      joint (I.branch a (equilibrium β Δ)) := by
  rw [step_branch,channel_zero β Δ γ η hγ hη]

/-- Joint weights follow the postmeasurement state, rather than an independent-product assumption. -/
theorem two_weight (I : FiniteInstrument Qubit 2) (β Δ γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (a b : Fin 2) :
    weight Qubit Unit 2 (twoTree I β Δ γ η t hγ hη ht) (a,b,()) (joint (equilibrium β Δ)) =
      weight Qubit Unit 2 (tree I β Δ γ η t hγ hη ht) (b,()) (joint (I.branch a (equilibrium β Δ))) := by
  change weight Qubit Unit 2 (tree I β Δ γ η t hγ hη ht) (b,())
    ((step I β Δ γ η 0 hγ hη (by norm_num)).branch Qubit Unit 2 a (joint (equilibrium β Δ))) = _
  rw [initial_branch]

theorem weight_real_smul {n : ℕ} (T : Tree Qubit Unit 2 n) (h : History 2 n)
    (c : ℝ) (X : Matrix (Qubit × Unit) (Qubit × Unit) ℂ) :
    weight Qubit Unit 2 T h ((c:ℂ) • X)=c*weight Qubit Unit 2 T h X := by
  simp only [weight,run_smul,Matrix.trace_smul]
  simp

/-- Actual depth-two computational joint probabilities. -/
theorem population_joint (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (a b : Fin 2) :
    weight Qubit Unit 2 (twoTree FiniteInstrument.computational β Δ γ η t hγ hη ht)
      (a,b,()) (joint (equilibrium β Δ)) =
      weights β Δ a*((1-Real.exp (-γ*t))*weights β Δ b+Real.exp (-γ*t)*(if b=a then 1 else 0)) := by
  rw [two_weight,computational_collapse,joint_smul,weight_real_smul,population_weight]

theorem equilibrium_stationary (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    krausMap (channel β Δ γ η t) (equilibrium β Δ)=equilibrium β Δ :=
  GibbsHamiltonianRelaxation.time_stationary _ _ _ (fun i => (weights_pos β Δ i).le)
    (weights_sum β Δ) γ η t hγ hη ht

/-- Reversal symmetry of the observed equilibrium population pair. -/
theorem population_reversal (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (a b : Fin 2) :
    weight Qubit Unit 2 (twoTree FiniteInstrument.computational β Δ γ η t hγ hη ht)
      (a,b,()) (joint (equilibrium β Δ)) =
    weight Qubit Unit 2 (twoTree FiniteInstrument.computational β Δ γ η t hγ hη ht)
      (b,a,()) (joint (equilibrium β Δ)) := by
  rw [population_joint,population_joint]
  by_cases hab : a=b
  · subst b; rfl
  · simp [hab,Ne.symm hab]; ring

/-- The first observed population marginal is the Gibbs distribution. -/
theorem population_first_marginal (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (a : Fin 2) :
    (∑ b,weight Qubit Unit 2 (twoTree FiniteInstrument.computational β Δ γ η t hγ hη ht)
      (a,b,()) (joint (equilibrium β Δ)))=weights β Δ a := by
  have hn : weights β Δ 0+weights β Δ 1=1 := by simpa [Fin.sum_univ_two] using weights_sum β Δ
  simp only [population_joint,Fin.sum_univ_two]
  fin_cases a <;> norm_num <;> linear_combination weights β Δ _*(1-Real.exp (-(γ*t)))*hn

/-- The second observed population marginal is the same stationary distribution. -/
theorem population_second_marginal (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (b : Fin 2) :
    (∑ a,weight Qubit Unit 2 (twoTree FiniteInstrument.computational β Δ γ η t hγ hη ht)
      (a,b,()) (joint (equilibrium β Δ)))=weights β Δ b := by
  calc
    _ = ∑ a,weight Qubit Unit 2 (twoTree FiniteInstrument.computational β Δ γ η t hγ hη ht)
        (b,a,()) (joint (equilibrium β Δ)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact population_reversal β Δ γ η t hγ hη ht a b
    _ = _ := population_first_marginal β Δ γ η t hγ hη ht b

/-- Signed readout, plus for index zero and minus for index one. -/
def sign (a : Fin 2) : ℝ := if a=0 then 1 else -1

def meanZ (β Δ : ℝ) : ℝ := weights β Δ 0-weights β Δ 1

/-- The signed first-observation mean is the nonuniform Gibbs bias. -/
theorem observed_meanZ (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (∑ a,sign a*(∑ b,weight Qubit Unit 2
      (twoTree FiniteInstrument.computational β Δ γ η t hγ hη ht)
      (a,b,()) (joint (equilibrium β Δ))))=meanZ β Δ := by
  simp only [population_first_marginal]
  simp [Fin.sum_univ_two,sign,meanZ,sub_eq_add_neg]

/-- The correlation is a sum over the actual joint outcome distribution. -/
def correlation (I : FiniteInstrument Qubit 2) (β Δ γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : ℝ :=
  ∑ a, ∑ b, sign a*sign b*weight Qubit Unit 2 (twoTree I β Δ γ η t hγ hη ht)
    (a,b,()) (joint (equilibrium β Δ))

theorem z_correlation (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    correlation FiniteInstrument.computational β Δ γ η t hγ hη ht =
      meanZ β Δ^2+(1-meanZ β Δ^2)*Real.exp (-γ*t) := by
  have hn : weights β Δ 0+weights β Δ 1=1 := by simpa [Fin.sum_univ_two] using weights_sum β Δ
  simp only [correlation,population_joint,Fin.sum_univ_two]
  norm_num [sign,meanZ]
  linear_combination Real.exp (-(γ*t))*hn

theorem xProjector_trace (a : Fin 2) : (xProjector a).trace=1 := by
  fin_cases a <;> norm_num [xProjector,plus,Matrix.trace,Fin.sum_univ_two]

theorem xProjector_density (a : Fin 2) : IsDensityOperator (xProjector a) := by
  refine ⟨?_,xProjector_trace a⟩
  have hp := Matrix.posSemidef_self_mul_conjTranspose (xProjector a)
  rwa [xProjector_adjoint,xProjector_square] at hp

theorem x_readout (b : Fin 2) (X : Matrix Qubit Qubit ℂ) :
    (xInstrument.branch b X).trace=(X 0 0+X 1 1+(sign b:ℂ)*(X 0 1+X 1 0))/2 := by
  simp only [FiniteInstrument.branch,xInstrument,krausMap]
  fin_cases b <;> norm_num [sign,xProjector,plus,Matrix.trace,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two,Matrix.vecMul,dotProduct] <;>
    simp only [map_ofNat] <;> ring

/-- Transition probabilities for both actual coherent postmeasurement states. -/
theorem x_transition (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (a b : Fin 2) :
    weight Qubit Unit 2 (tree xInstrument β Δ γ η t hγ hη ht) (b,()) (joint (xProjector a)) =
      (1+sign a*sign b*Real.exp (-(γ+η)*t)*Real.cos (Δ*t))/2 := by
  rw [tree_weight,x_readout,
    channel_diagonal β Δ γ η t hγ hη ht (xProjector a) 0,
    channel_diagonal β Δ γ η t hγ hη ht (xProjector a) 1,
    channel_offdiagonal β Δ γ η t hγ hη ht (xProjector a) 0 1 (by decide),
    channel_offdiagonal β Δ γ η t hγ hη ht (xProjector a) 1 0 (by decide),xProjector_trace]
  have hn : weights β Δ 0+weights β Δ 1=1 := by simpa [Fin.sum_univ_two] using weights_sum β Δ
  fin_cases a <;> fin_cases b <;>
    norm_num [sign,xProjector,plus,energies,Complex.exp_re,Complex.exp_im] <;>
    rw [mul_comm t Δ] <;> linear_combination (1-Real.exp (-(γ*t)))*hn

/-- Actual coherent depth-two joint distribution, independent of the diagonal equilibrium bias. -/
theorem x_joint (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (a b : Fin 2) :
    weight Qubit Unit 2 (twoTree xInstrument β Δ γ η t hγ hη ht) (a,b,()) (joint (equilibrium β Δ)) =
      (1+sign a*sign b*Real.exp (-(γ+η)*t)*Real.cos (Δ*t))/4 := by
  rw [two_weight,x_collapse,joint_smul]
  have he : (1/2:ℂ)=((1/2:ℝ):ℂ) := by norm_num
  rw [he,weight_real_smul,x_transition]
  ring

theorem x_correlation (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    correlation xInstrument β Δ γ η t hγ hη ht=Real.exp (-(γ+η)*t)*Real.cos (Δ*t) := by
  simp only [correlation,x_joint,Fin.sum_univ_two]
  norm_num [sign]
  ring

/-- Both actual measurement trees define normalized, nonnegative distributions. -/
theorem joint_probabilities (I : FiniteInstrument Qubit 2) (β Δ γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (∀ h,0 ≤ weight Qubit Unit 2 (twoTree I β Δ γ η t hγ hη ht) h (joint (equilibrium β Δ))) ∧
    (∑ h,weight Qubit Unit 2 (twoTree I β Δ γ η t hγ hη ht) h (joint (equilibrium β Δ)))=1 :=
  normalized_weights Qubit Unit 2 _ (joint_density _ (equilibrium_density β Δ))

/-- The nonuniform Gibbs example has a nonzero observed equilibrium bias. -/
theorem nonuniform_mean : 0 < meanZ 1 1 := sub_pos.mpr nonuniform_equilibrium

/-- Faithfulness gives a strictly positive stationary signed-population variance. -/
theorem stationary_variance_pos (β Δ : ℝ) : 0 < 1-meanZ β Δ^2 := by
  have hn : weights β Δ 0+weights β Δ 1=1 := by simpa [Fin.sum_univ_two] using weights_sum β Δ
  have he : 1-meanZ β Δ^2=4*weights β Δ 0*weights β Δ 1 := by
    unfold meanZ
    nlinarith [sq_nonneg (weights β Δ 0+weights β Δ 1-1)]
  rw [he]
  exact mul_pos (mul_pos (by norm_num) (weights_pos β Δ 0)) (weights_pos β Δ 1)

/-- An actual equilibrium cross-outcome event has positive mass at unit lag. -/
theorem nonuniform_joint_transfer :
    0 < weight Qubit Unit 2
      (twoTree FiniteInstrument.computational 1 1 1 0 1 (by norm_num) (by norm_num) (by norm_num))
      (0,1,()) (joint (equilibrium 1 1)) := by
  rw [population_joint]
  norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_false,mul_zero,add_zero]
  exact mul_pos (weights_pos 1 1 0)
    (mul_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))) (weights_pos 1 1 1))

/-- Pure Hamiltonian pi evolution gives perfect anticorrelation of the two actual X observations. -/
theorem pureHamiltonian_anticorrelation :
    correlation xInstrument 1 1 0 0 Real.pi (by norm_num) (by norm_num) Real.pi_pos.le = -1 := by
  rw [x_correlation]
  norm_num

/-- In the anticorrelated experiment, equal outcomes have zero mass and unequal outcomes mass one half. -/
theorem pureHamiltonian_joint (a b : Fin 2) :
    weight Qubit Unit 2
      (twoTree xInstrument 1 1 0 0 Real.pi (by norm_num) (by norm_num) Real.pi_pos.le)
      (a,b,()) (joint (equilibrium 1 1)) = if a=b then 0 else 1/2 := by
  rw [x_joint]
  fin_cases a <;> fin_cases b <;> norm_num [sign]

end SKEFTHawking.QuantumNetwork.GibbsTwoTimeProcess
