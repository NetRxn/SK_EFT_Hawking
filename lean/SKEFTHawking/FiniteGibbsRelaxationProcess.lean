import SKEFTHawking.FiniteGibbsHamiltonianRelaxation
import SKEFTHawking.QuantumNetwork.FiniteInterventionProcess

/-! Actual finite Gibbs relaxation followed by an instrument, with a trivial environment.
All future marginals sum every outcome, without postselection. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.GibbsRelaxationProcess
open Matrix Filter FiniteInterventionProcess FinitePositiveKernel
open FinitePositiveKernel.DiagonalLindblad OpenSystems
open scoped ComplexOrder Kronecker Topology
abbrev Qubit := Fin 2

/-- Singleton-environment reindexing, represented by the canonical tensor with identity. -/
def joint (X : Matrix Qubit Qubit ℂ) : Matrix (Qubit × Unit) (Qubit × Unit) ℂ := X ⊗ₖ 1

theorem joint_apply (X : Matrix Qubit Qubit ℂ) (i j : Qubit) (u v : Unit) :
    joint X (i,u) (j,v)=X i j := by simp [joint]

def system (X : Matrix (Qubit × Unit) (Qubit × Unit) ℂ) : Matrix Qubit Qubit ℂ :=
  fun i j => X (i,()) (j,())

theorem system_joint (X : Matrix Qubit Qubit ℂ) : system (joint X)=X := by ext i j; exact joint_apply _ _ _ _ _

theorem joint_system (X : Matrix (Qubit × Unit) (Qubit × Unit) ℂ) : joint (system X)=X := by
  ext ⟨i,u⟩ ⟨j,v⟩
  cases u; cases v
  exact joint_apply _ _ _ _ _

theorem joint_trace (X : Matrix Qubit Qubit ℂ) : (joint X).trace=X.trace := by
  rw [joint,Matrix.trace_kronecker]
  simp [Matrix.trace]

theorem joint_density (X : Matrix Qubit Qubit ℂ) (hX : IsDensityOperator X) : IsDensityOperator (joint X) :=
  ⟨hX.1.kronecker Matrix.PosSemidef.one, by rw [joint_trace]; exact hX.2⟩

theorem joint_kraus {m : ℕ} (V : Fin m → Matrix Qubit Qubit ℂ) (X : Matrix Qubit Qubit ℂ) :
    krausMap (fun k => joint (V k)) (joint X)=joint (krausMap V X) := by
  simp only [krausMap,joint,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul]
  exact sum_kronOne_general _

theorem joint_normalized {m : ℕ} (V : Fin m → Matrix Qubit Qubit ℂ) (hV : IsKrausChannel V) :
    IsKrausChannel (fun k => joint (V k)) := by
  unfold IsKrausChannel
  simp only [joint,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul]
  rw [sum_kronOne_general,show ∑ k,(V k)ᴴ*V k=1 from hV,Matrix.one_kronecker_one]

theorem lift_branch (I : FiniteInstrument Qubit 2) (a : Fin 2) (X : Matrix Qubit Qubit ℂ) :
    (I.lift Unit).branch a (joint X)=joint (I.branch a X) := joint_kraus _ _

def energies (Δ : ℝ) : Qubit → ℝ := ![0,Δ]
def weights (β Δ : ℝ) := GibbsReset.gibbsWeights (energies Δ) β

theorem weights_pos (β Δ : ℝ) (a : Qubit) : 0 < weights β Δ a := GibbsReset.gibbsWeights_pos _ _ _
theorem weights_sum (β Δ : ℝ) : ∑ a,weights β Δ a=1 := GibbsReset.gibbsWeights_normalized _ _

/-- Distinct labels distinguish the two noise-signature blocks even at degenerate energy. -/
def labels : Fin 1 → Qubit → ℝ := fun _ i => i.val

def channel (β Δ γ η t : ℝ) := GibbsHamiltonianRelaxation.timeKraus (energies Δ) labels (weights β Δ) γ η t

theorem channel_normalized (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    IsKrausChannel (channel β Δ γ η t) :=
  GibbsHamiltonianRelaxation.time_normalized _ _ _ (fun i => (weights_pos β Δ i).le)
    (weights_sum β Δ) γ η t hγ hη ht

theorem channel_actual (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (X : Matrix Qubit Qubit ℂ) :
    krausMap (channel β Δ γ η t) X =
      lindbladPropagatorAction (density (energies Δ)) (GibbsBlockRelaxation.jumps labels (weights β Δ) γ η) t X :=
  GibbsHamiltonianRelaxation.time_state_eq_propagator _ _ _ (fun i => (weights_pos β Δ i).le)
    (weights_sum β Δ) γ η t hγ hη ht X

def step (I : FiniteInstrument Qubit 2) (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    Step Qubit Unit 2 where
  count := _
  evolution k := joint (channel β Δ γ η t k)
  normalized := joint_normalized _ (channel_normalized β Δ γ η t hγ hη ht)
  instrument := I

def tree (I : FiniteInstrument Qubit 2) (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    Tree Qubit Unit 2 1 := .node (step I β Δ γ η t hγ hη ht) (fun _ => .done)

theorem step_branch (I : FiniteInstrument Qubit 2) (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (a : Fin 2) (X : Matrix Qubit Qubit ℂ) :
    (step I β Δ γ η t hγ hη ht).branch Qubit Unit 2 a (joint X)=joint (I.branch a (krausMap (channel β Δ γ η t) X)) := by
  change (I.lift Unit).branch a (krausMap (fun k => joint (channel β Δ γ η t k)) (joint X))=_
  rw [joint_kraus,lift_branch]

theorem tree_weight (I : FiniteInstrument Qubit 2) (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (a : Fin 2) (X : Matrix Qubit Qubit ℂ) :
    weight Qubit Unit 2 (tree I β Δ γ η t hγ hη ht) (a,()) (joint X)=
      (I.branch a (krausMap (channel β Δ γ η t) X)).trace.re := by
  change ((step I β Δ γ η t hγ hη ht).branch Qubit Unit 2 a (joint X)).trace.re=_
  rw [step_branch,joint_trace]

theorem computational_trace (a : Fin 2) (X : Matrix Qubit Qubit ℂ) :
    (FiniteInstrument.computational.branch a X).trace=X a a := by
  simp only [FiniteInstrument.branch,FiniteInstrument.computational,krausMap]
  fin_cases a <;> norm_num [
    FiniteMemoryProcess.basisState,Matrix.trace,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]

/-- The plus state is also the plus readout projector. -/
def plus : Matrix Qubit Qubit ℂ := !![1/2,1/2;1/2,1/2]
def xProjector (a : Fin 2) : Matrix Qubit Qubit ℂ := if a=0 then plus else 1-plus

theorem xProjector_adjoint (a : Fin 2) : (xProjector a)ᴴ=xProjector a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> norm_num [xProjector,plus,Matrix.conjTranspose_apply]

theorem xProjector_square (a : Fin 2) : xProjector a*xProjector a=xProjector a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> norm_num [xProjector,plus,Matrix.mul_apply,Fin.sum_univ_two]

theorem plus_density : IsDensityOperator plus := by
  constructor
  · have hp := Matrix.posSemidef_self_mul_conjTranspose (xProjector 0)
    rw [xProjector_adjoint,xProjector_square] at hp
    simpa [xProjector] using hp
  · norm_num [plus,Matrix.trace,Fin.sum_univ_two]

def xInstrument : FiniteInstrument Qubit 2 where
  count := 1
  operators a _ := xProjector a
  normalized := by
    simp only [Fin.sum_univ_one,xProjector_adjoint,xProjector_square]
    simp [Fin.sum_univ_two,xProjector]

theorem plus_readout (X : Matrix Qubit Qubit ℂ) :
    (xInstrument.branch 0 X).trace=(X 0 0+X 0 1+X 1 0+X 1 1)/2 := by
  simp only [FiniteInstrument.branch,xInstrument,krausMap]
  norm_num [xProjector,plus,Matrix.trace,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two,Matrix.vecMul,dotProduct]
  simp only [map_ofNat]
  ring

theorem labels_block (X : Matrix Qubit Qubit ℂ) : blockExpectation labels X=diagonal (fun i => X i i) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [blockExpectation,rate,labels,Fin.sum_univ_one]

/-- The reindexed process uses the actual vectorized GKSL exponential. -/
theorem joint_channel_actual (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (X : Matrix Qubit Qubit ℂ) :
    krausMap (fun k => joint (channel β Δ γ η t k)) (joint X)=
      joint (lindbladPropagatorAction (density (energies Δ))
        (GibbsBlockRelaxation.jumps labels (weights β Δ) γ η) t X) := by
  rw [joint_kraus,channel_actual β Δ γ η t hγ hη ht]

theorem channel_diagonal (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (X : Matrix Qubit Qubit ℂ) (a : Qubit) :
    krausMap (channel β Δ γ η t) X a a=
      ((1-Real.exp (-γ*t):ℝ):ℂ)*X.trace*(weights β Δ a:ℂ)+(Real.exp (-γ*t):ℂ)*X a a := by
  rw [channel_actual β Δ γ η t hγ hη ht,
    GibbsHamiltonianRelaxation.propagator_state _ _ _ (fun i => (weights_pos β Δ i).le)
      (weights_sum β Δ) γ η t hγ hη,
    GibbsHamiltonianRelaxation.rotation_entry,
    GibbsBlockRelaxation.propagator_state _ _ (fun i => (weights_pos β Δ i).le)
      (weights_sum β Δ) γ η t hγ hη]
  simp [blockExpectation,density]
  ring

/-- Actual tree probabilities for preparation in a computational basis state. -/
theorem population_weight (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (a b : Fin 2) :
    weight Qubit Unit 2 (tree FiniteInstrument.computational β Δ γ η t hγ hη ht) (a,())
      (joint (FiniteMemoryProcess.basisState b)) =
      (1-Real.exp (-γ*t))*weights β Δ a+Real.exp (-γ*t)*(if a=b then 1 else 0) := by
  rw [tree_weight,computational_trace,channel_diagonal β Δ γ η t hγ hη ht,
    (FiniteMemoryProcess.basisState_density b).2]
  fin_cases a <;> fin_cases b <;> norm_num [FiniteMemoryProcess.basisState,Complex.exp_re]

theorem population_probabilities (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (b : Fin 2) :
    (∀ a, 0 ≤ weight Qubit Unit 2 (tree FiniteInstrument.computational β Δ γ η t hγ hη ht) (a,())
      (joint (FiniteMemoryProcess.basisState b))) ∧
    (∑ a,weight Qubit Unit 2 (tree FiniteInstrument.computational β Δ γ η t hγ hη ht) (a,())
      (joint (FiniteMemoryProcess.basisState b)))=1 := by
  have h := normalized_weights Qubit Unit 2 (tree FiniteInstrument.computational β Δ γ η t hγ hη ht)
    (joint_density _ (FiniteMemoryProcess.basisState_density b))
  constructor
  · intro a; exact h.1 (a,())
  · have hh := h.2
    change (∑ p : Fin 2 × Unit, weight Qubit Unit 2
      (tree FiniteInstrument.computational β Δ γ η t hγ hη ht) p
      (joint (FiniteMemoryProcess.basisState b)))=1 at hh
    simp only [Fintype.sum_prod_type,Fintype.sum_unique] at hh
    exact hh

theorem population_tendsto (β Δ γ η : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (a b : Fin 2) :
    Tendsto (fun t : NNReal => weight Qubit Unit 2
      (tree FiniteInstrument.computational β Δ γ η t hγ.le hη t.coe_nonneg) (a,())
      (joint (FiniteMemoryProcess.basisState b))) atTop (𝓝 (weights β Δ a)) := by
  simp only [population_weight]
  have he : Tendsto (fun t : NNReal => Real.exp (-γ*(t:ℝ))) atTop (𝓝 0) := by
    have hm := NNReal.tendsto_coe_atTop.mpr (tendsto_id : Tendsto (fun t : NNReal => t) atTop atTop)
    have hh := hm.const_mul_atTop hγ
    simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hh)
  convert ((tendsto_const_nhds.sub he).mul_const (weights β Δ a)).add
    (he.mul_const (if a=b then 1 else 0)) using 1; simp

theorem channel_offdiagonal (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (X : Matrix Qubit Qubit ℂ) (i j : Qubit) (hij : i ≠ j) :
    krausMap (channel β Δ γ η t) X i j=
      Complex.exp (-Complex.I*t*((energies Δ i:ℂ)-energies Δ j)) *
        (Real.exp (-(γ+η)*t):ℂ)*X i j := by
  rw [channel_actual β Δ γ η t hγ hη ht,
    GibbsHamiltonianRelaxation.propagator_state _ _ _ (fun a => (weights_pos β Δ a).le)
      (weights_sum β Δ) γ η t hγ hη,
    GibbsHamiltonianRelaxation.rotation_entry,
    GibbsBlockRelaxation.propagator_state _ _ (fun a => (weights_pos β Δ a).le)
      (weights_sum β Δ) γ η t hγ hη,labels_block]
  simp [density,hij]
  ring

/-- The actual plus-outcome tree weight reveals both Hamiltonian phase and dissipation. -/
theorem plus_weight (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    weight Qubit Unit 2 (tree xInstrument β Δ γ η t hγ hη ht) (0,()) (joint plus)=
      (1+Real.exp (-(γ+η)*t)*Real.cos (Δ*t))/2 := by
  rw [tree_weight,plus_readout,
    channel_diagonal β Δ γ η t hγ hη ht plus 0,
    channel_diagonal β Δ γ η t hγ hη ht plus 1,
    channel_offdiagonal β Δ γ η t hγ hη ht plus 0 1 (by decide),
    channel_offdiagonal β Δ γ η t hγ hη ht plus 1 0 (by decide),plus_density.2]
  have hn : weights β Δ 0+weights β Δ 1=1 := by simpa [Fin.sum_univ_two] using weights_sum β Δ
  norm_num [plus,energies,Complex.exp_re,Complex.exp_im]
  rw [mul_comm t Δ]
  linear_combination (1-Real.exp (-(γ*t))) * hn

/-- All outcomes of the plus/minus readout form a normalized distribution. -/
theorem plus_probabilities (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (∀ h,0 ≤ weight Qubit Unit 2 (tree xInstrument β Δ γ η t hγ hη ht) h (joint plus)) ∧
      (∑ h,weight Qubit Unit 2 (tree xInstrument β Δ γ η t hγ hη ht) h (joint plus))=1 :=
  normalized_weights Qubit Unit 2 _ (joint_density plus plus_density)

/-- Arbitrary-depth arity-two future interventions preserve the unpostselected earlier outcome. -/
theorem future_population_marginal (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (a b : Fin 2) {n : ℕ} (F : Tree Qubit Unit 2 n) :
    (∑ f,weight Qubit Unit 2 F f
      (run Qubit Unit 2 (tree FiniteInstrument.computational β Δ γ η t hγ hη ht) (a,())
        (joint (FiniteMemoryProcess.basisState b)))) =
      (1-Real.exp (-γ*t))*weights β Δ a+Real.exp (-γ*t)*(if a=b then 1 else 0) := by
  rw [prefix_marginal,population_weight]

theorem future_plus_marginal (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    {n : ℕ} (F : Tree Qubit Unit 2 n) :
    (∑ f,weight Qubit Unit 2 F f
      (run Qubit Unit 2 (tree xInstrument β Δ γ η t hγ hη ht) (0,()) (joint plus))) =
      (1+Real.exp (-(γ+η)*t)*Real.cos (Δ*t))/2 := by
  rw [prefix_marginal,plus_weight]

theorem future_choice_independent (I : FiniteInstrument Qubit 2) (β Δ γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (a : Fin 2) (X : Matrix Qubit Qubit ℂ)
    {n m : ℕ} (F : Tree Qubit Unit 2 n) (G : Tree Qubit Unit 2 m) :
    (∑ f,weight Qubit Unit 2 F f (run Qubit Unit 2 (tree I β Δ γ η t hγ hη ht) (a,()) (joint X))) =
    (∑ g,weight Qubit Unit 2 G g (run Qubit Unit 2 (tree I β Δ γ η t hγ hη ht) (a,()) (joint X))) :=
  no_future_signaling Qubit Unit 2 _ _ F G _

theorem nonuniform_equilibrium : weights 1 1 1 < weights 1 1 0 := by
  unfold weights GibbsReset.gibbsWeights
  apply (mul_lt_mul_iff_of_pos_left (inv_pos.mpr (FiniteGibbsClock.partition_pos
    (GibbsReset.energy_hermitian (energies 1)) 1))).mpr
  apply Real.exp_lt_exp.mpr
  norm_num [energies]

/-- Both readout projectors have rank one; neither is a zero or full-space outcome. -/
theorem xProjector_rank (a : Fin 2) : (xProjector a).rank=1 := by
  have hf : xProjector a=Matrix.vecMulVec
      (![1/2,if a=0 then 1/2 else -1/2] : Qubit → ℂ)
      (![1,if a=0 then 1 else -1] : Qubit → ℂ) := by
    ext i j
    fin_cases a <;> fin_cases i <;> fin_cases j <;> norm_num [xProjector,plus,Matrix.vecMulVec]
  have hu : (xProjector a).rank ≤ 1 := by rw [hf]; exact Matrix.rank_vecMulVec_le _ _
  have hn : (xProjector a).rank ≠ 0 := by
    intro h
    change Module.finrank ℂ (LinearMap.range (xProjector a).mulVecLin)=0 at h
    have hb := Submodule.finrank_eq_zero.mp h
    have hz := LinearMap.range_eq_bot.mp hb
    have he := congrArg (fun T : (Qubit → ℂ) →ₗ[ℂ] (Qubit → ℂ) => T ![1,0] 0) hz
    fin_cases a <;> norm_num [xProjector,plus,Matrix.mulVecLin,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at he
  omega

theorem appended_population_marginal (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (a b : Fin 2) {n : ℕ} (F : Fin 2 → Tree Qubit Unit 2 n) :
    (∑ h : History 2 n, weight Qubit Unit 2
      (.node (step FiniteInstrument.computational β Δ γ η t hγ hη ht) F) (a,h)
      (joint (FiniteMemoryProcess.basisState b))) =
      (1-Real.exp (-γ*t))*weights β Δ a+Real.exp (-γ*t)*(if a=b then 1 else 0) := by
  exact future_population_marginal β Δ γ η t hγ hη ht a b (F a)

theorem appended_plus_marginal (β Δ γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    {n : ℕ} (F : Fin 2 → Tree Qubit Unit 2 n) :
    (∑ h : History 2 n, weight Qubit Unit 2
      (.node (step xInstrument β Δ γ η t hγ hη ht) F) (0,h) (joint plus)) =
      (1+Real.exp (-(γ+η)*t)*Real.cos (Δ*t))/2 := by
  exact future_plus_marginal β Δ γ η t hγ hη ht (F 0)

/-- A genuine population transfer in the beta = Delta = 1 nonuniform example. -/
theorem nonuniform_transfer_pos :
    0 < weight Qubit Unit 2
      (tree FiniteInstrument.computational 1 1 1 0 1 (by norm_num) (by norm_num) (by norm_num))
      (1,()) (joint (FiniteMemoryProcess.basisState 0)) := by
  rw [population_weight]
  simp only [show (1:Fin 2) ≠ 0 by decide,ite_false,mul_zero,add_zero]
  exact mul_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))) (weights_pos 1 1 1)

/-- Pure Hamiltonian evolution gives a directly observable plus/minus phase flip. -/
theorem coherent_pi_readout :
    weight Qubit Unit 2 (tree xInstrument 1 1 0 0 Real.pi (by norm_num) (by norm_num) Real.pi_pos.le)
      (0,()) (joint plus)=0 := by
  rw [plus_weight]
  norm_num

theorem initial_plus_readout (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    weight Qubit Unit 2 (tree xInstrument β Δ γ η 0 hγ hη (by norm_num)) (0,()) (joint plus)=1 := by
  rw [plus_weight]
  norm_num

end SKEFTHawking.QuantumNetwork.GibbsRelaxationProcess
