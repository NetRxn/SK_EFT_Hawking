import SKEFTHawking.QuantumNetwork.FiniteQutritAveragedMixing

/-!
# Actual selected joint weights and exact negative controls

The selected prefix and suffix are events in the original chronological
instrument process. Intermediate fresh uniform settings and outcomes are
summed, never conditioned on a selected prefix.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritAveragedExamples
open Matrix FiniteInterventionProcess FiniteAdaptiveKrausRealization
open FiniteQutritPhysicalMemory FiniteQutritInvariantCarrier
open FiniteQutritInvariantReconstruction FiniteQutritAveragedTransfer FiniteQutritAveragedMixing
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

private theorem vec6_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

/-- A deterministic empty external record; the ten internal channel alternatives
are discarded. The impossible second outcome remains part of the process. -/
def silentInstrument : FiniteInstrument Q 2 where
  count := 1
  operators a _ := if a=0 then 1 else 0
  normalized := by simp [Fin.sum_univ_two]

variable (E : Type*) [Fintype E] [DecidableEq E]

def silentStep : Step Q E 2 where
  count := 10
  evolution k := krausOperator k ⊗ₖ (1 : Matrix E E ℂ)
  normalized := by
    unfold IsKrausChannel
    simp_rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, sum_kronOne_general]
    rw [kraus_normalized, Matrix.one_kronecker_one]
  instrument := silentInstrument

theorem silent_zero_branch (X : Matrix (Q × E) (Q × E) ℂ) :
    (silentStep E).branch Q E 2 0 X = amplified E X := by
  simp [Step.branch, silentStep, silentInstrument, FiniteInstrument.branch,
    FiniteInstrument.lift, krausMap, Matrix.one_kronecker_one]
  rfl

theorem silent_impossible_branch (X : Matrix (Q × E) (Q × E) ℂ) :
    (silentStep E).branch Q E 2 1 X = 0 := by
  simp [Step.branch, silentStep, silentInstrument, FiniteInstrument.branch,
    FiniteInstrument.lift, krausMap]

def silentTree : (n : ℕ) → Tree Q E 2 n
  | 0 => .done
  | n+1 => .node (silentStep E) (fun _ => silentTree n)

def silentHistory : (n : ℕ) → History 2 n
  | 0 => ()
  | n+1 => (0,silentHistory n)

theorem silent_run (n : ℕ) (X : Matrix (Q × E) (Q × E) ℂ) :
    run Q E 2 (silentTree E n) (silentHistory n) X = amplifiedIterate E n X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change run Q E 2 (silentTree E n) (silentHistory n)
      ((silentStep E).branch Q E 2 0 X) = _
    rw [silent_zero_branch, ih]
    rfl

def experimentTree (j : Index) (n : ℕ) : Tree Q Unit 2 (((suffixWord 1).length+n)+(prefixWord j).length) :=
  appendTree (wordTree Unit (prefixWord j)) (fun _ =>
    appendTree (silentTree Unit n) (fun _ => wordTree Unit (suffixWord 1)))

def experimentHistory (j : Index) (n : ℕ) :
    History 2 (((suffixWord 1).length+n)+(prefixWord j).length) :=
  appendHistory (prefixHistory j) (appendHistory (silentHistory n) (suffixHistory 1))

/-- Actual prefix-and-suffix JOINT weight: the prefix mass is not divided out. -/
def jointWeight (j : Index) (n : ℕ) : ℝ :=
  weight Q Unit 2 (experimentTree j n) (experimentHistory j n) (joint rho)

theorem jointWeight_trace (j : Index) (n : ℕ) :
    jointWeight j n = ((effect 1 * iterate n ((1/3 : ℂ) • effect j)).trace).re := by
  have ha (Y : Mat) : amplifiedIterate Unit n (joint Y) = joint (iterate n Y) :=
    amplified_iterate_product Unit n Y 1
  unfold jointWeight FiniteInterventionProcess.weight experimentTree experimentHistory
  rw [append_run, append_run, actual_run_joint, prefix_systemState, silent_run,
    ha, actual_run_joint, joint_trace, suffix_trace]

/-- Coarse-graining all actual fresh ten-valued intermediate records gives the
same selected joint event as the composed normalized channel. -/
theorem jointWeight_fine_records (j : Index) (n : ℕ) :
    jointWeight j n = ∑ h : History 10 n,
      (run Q Unit 2 (wordTree Unit (suffixWord 1)) (suffixHistory 1)
        (run Q Unit 10 (recordTree Unit n) h
          (run Q Unit 2 (wordTree Unit (prefixWord j)) (prefixHistory j) (joint rho)))).trace.re := by
  let L : Matrix (Q × Unit) (Q × Unit) ℂ →ₗ[ℂ] Matrix (Q × Unit) (Q × Unit) ℂ :=
    { toFun := run Q Unit 2 (wordTree Unit (suffixWord 1)) (suffixHistory 1)
      map_add' := run_add Q Unit 2 _ _
      map_smul' := run_smul Q Unit 2 _ _ }
  have hs := congrArg (fun X => (L X).trace.re)
    (discarded_history_system n ((1/3 : ℂ) • effect j))
  rw [map_sum, Matrix.trace_sum, Complex.re_sum] at hs
  rw [jointWeight_trace]
  dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk] at hs
  rw [actual_run_joint, joint_trace, suffix_trace] at hs
  simpa only [actual_run_joint, prefix_systemState] using hs.symm

theorem experiment_normalized (j : Index) (n : ℕ) :
    (∀ h, 0 ≤ weight Q Unit 2 (experimentTree j n) h (joint rho)) ∧
      (∑ h, weight Q Unit 2 (experimentTree j n) h (joint rho)) = 1 :=
  normalized_weights Q Unit 2 _ FiniteQutritPhysicalMemoryExamples.attainer.density

theorem jointWeight_nonneg (j : Index) (n : ℕ) : 0 ≤ jointWeight j n :=
  (experiment_normalized j n).1 _

theorem original_prefix_mass (j : Setting) :
    weight Q Unit 2 (wordTree Unit [j,j]) (0,0,()) (joint rho) = 1/3 := by
  unfold FiniteInterventionProcess.weight
  have hp : systemRun [j,j] (0,0,()) rho = (1/3 : ℂ) • projector j := by
    have h := prefix_systemState j.castSucc
    fin_cases j <;> exact h
  rw [actual_run_joint, hp, joint_trace, Matrix.trace_smul, projector_trace]
  norm_num

theorem selected_eigen_readout (i : Index) :
    (effect 1 * eigenvector i).trace = if i=0 ∨ i=1 ∨ i=2 then 1 else 0 := by
  fin_cases i <;>
    norm_num [effect, projector, eigenvector, eigenCoordinates, symmetricMatrix,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, vec6_last, Fin.ext_iff]

theorem selected_trace_formula (j : Index) (n : ℕ) :
    (effect 1 * iterate n ((1/3 : ℂ) • effect j)).trace =
      ∑ i, (eigenvalue i : ℂ)^n * coefficients ((1/3 : ℂ) • effect j) i *
        (if i=0 ∨ i=1 ∨ i=2 then 1 else 0) := by
  have hm : (1/3 : ℂ) • effect j ∈ symmetricCarrier := (effect_symmetric j).smul _
  rw [iterate_expansion n ⟨_,hm⟩]
  simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_sum,
    Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, selected_eigen_readout,
    smul_eq_mul]

private theorem selected_scalar_sum (c : Index → ℂ) (n : ℕ) :
    (∑ i, (eigenvalue i : ℂ)^n*c i*(if i=0 ∨ i=1 ∨ i=2 then 1 else 0)) =
      c 0+(9/10:ℂ)^n*c 1+(7/10:ℂ)^n*c 2 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (1:ℂ)^n*c 0*1 + (((9/10:ℝ):ℂ)^n*c 1*1 +
    (((7/10:ℝ):ℂ)^n*c 2*1 + (((3/5:ℝ):ℂ)^n*c 3*0 +
    (((1/2:ℝ):ℂ)^n*c 4*0 + (((3/10:ℝ):ℂ)^n*c 5*0 + 0))))) = _
  simp only [one_pow, mul_one, mul_zero, add_zero, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem selected_trace_three (j : Index) (n : ℕ) :
    (effect 1 * iterate n ((1/3 : ℂ) • effect j)).trace =
      coefficients ((1/3 : ℂ) • effect j) 0 +
      (9/10 : ℂ)^n * coefficients ((1/3 : ℂ) • effect j) 1 +
      (7/10 : ℂ)^n * coefficients ((1/3 : ℂ) • effect j) 2 := by
  rw [selected_trace_formula]
  exact selected_scalar_sum _ n

theorem prefix_one_coefficients :
    coefficients ((1/3 : ℂ) • effect 1) = ![1/9,1/6,1/18,0,0,0] := by
  ext i
  fin_cases i <;> norm_num [coefficients, effect, projector, Matrix.smul_apply,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem prefix_two_coefficients :
    coefficients ((1/3 : ℂ) • effect 2) = ![1/9,-1/6,1/18,0,0,0] := by
  ext i
  fin_cases i <;> norm_num [coefficients, effect, projector, Matrix.smul_apply,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem weight_one (n : ℕ) :
    jointWeight 1 n = 1/9 + (9/10 : ℝ)^n/6 + (7/10 : ℝ)^n/18 := by
  have h : (effect 1 * iterate n ((1/3 : ℂ) • effect 1)).trace =
      ((1/9 + (9/10 : ℝ)^n/6 + (7/10 : ℝ)^n/18 : ℝ) : ℂ) := by
    rw [selected_trace_three, prefix_one_coefficients]
    push_cast
    norm_num [Matrix.cons_val_two]
    ring
  rw [jointWeight_trace, h, Complex.ofReal_re]

theorem weight_two (n : ℕ) :
    jointWeight 2 n = 1/9 - (9/10 : ℝ)^n/6 + (7/10 : ℝ)^n/18 := by
  have h : (effect 1 * iterate n ((1/3 : ℂ) • effect 2)).trace =
      ((1/9 - (9/10 : ℝ)^n/6 + (7/10 : ℝ)^n/18 : ℝ) : ℂ) := by
    rw [selected_trace_three, prefix_two_coefficients]
    push_cast
    norm_num [Matrix.cons_val_two]
    ring
  rw [jointWeight_trace, h, Complex.ofReal_re]

theorem weight_difference (n : ℕ) :
    jointWeight 1 n-jointWeight 2 n = (1/3 : ℝ)*(9/10 : ℝ)^n := by
  rw [weight_one, weight_two]
  ring

theorem zero_step_weights : jointWeight 1 0 = 1/3 ∧ jointWeight 2 0 = 0 := by
  rw [weight_one, weight_two]
  norm_num

/-- The actual nonzero trace-zero eigenvector attains the sharp bound. -/
theorem sharp_contraction_witness :
    (eigenvector 1).trace = 0 ∧ eigenvector 1 ≠ 0 ∧
      hsNorm (transfer (eigenvector 1)) = (9/10 : ℝ)*hsNorm (eigenvector 1) := by
  refine ⟨?_,?_,?_⟩
  · norm_num [eigenvector, eigenCoordinates, symmetricMatrix, Matrix.trace, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three]
  · intro h
    have he := congrArg (fun X : Mat => X 1 1) h
    norm_num [eigenvector, eigenCoordinates, symmetricMatrix] at he
  · rw [actual_eigenvector]
    change ‖operatorEmbedding ((eigenvalue 1 : ℂ) • eigenvector 1)‖ = _
    rw [map_smul, norm_smul]
    norm_num [eigenvalue, hsNorm]

/-- Omitting uniform-setting normalization multiplies the trace by five. -/
def unnormalized : Mat →ₗ[ℂ] Mat := ∑ j : Setting, pinching j

theorem unnormalized_eq (X : Mat) : unnormalized X = (5 : ℂ) • transfer X := by
  rw [transfer_apply, smul_smul]
  norm_num [unnormalized, LinearMap.sum_apply]

theorem unnormalized_one : unnormalized 1 = (5 : ℂ) • (1 : Mat) := by
  rw [unnormalized_eq, transfer_one]

theorem unnormalized_density_trace : (unnormalized rho).trace = 5 := by
  rw [unnormalized_eq, Matrix.trace_smul, transfer_trace, rho_density.2]
  norm_num

/-- A completely positive unitary conjugation with a negative Hilbert quadratic value. -/
def signUnitary : Mat := !![1,0,0; 0,-1,0; 0,0,1]
def negativeDirection : Mat := !![0,1,0; 1,0,0; 0,0,0]
def signConjugation (X : Mat) : Mat := signUnitary * X * signUnitaryᴴ

theorem sign_unitary : signUnitaryᴴ * signUnitary = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [signUnitary, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem sign_conjugation_ambient_CP {X : Matrix (Q × E) (Q × E) ℂ}
    (hX : X.PosSemidef) :
    ((signUnitary ⊗ₖ (1 : Matrix E E ℂ)) * X *
      (signUnitary ⊗ₖ (1 : Matrix E E ℂ))ᴴ).PosSemidef :=
  hX.mul_mul_conjTranspose_same _

theorem sign_hilbert_negative :
    pairing negativeDirection (signConjugation negativeDirection) = -2/3 := by
  norm_num [pairing_trace, signConjugation, signUnitary, negativeDirection,
    Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ,
    Matrix.vecMul, dotProduct, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Global trace-zero does not remove spectator fixed degrees of freedom. -/
def spectatorFixedWitness : Matrix (Q × Fin 2) (Q × Fin 2) ℂ :=
  (1 : Mat) ⊗ₖ (!![1,0; 0,-1] : Matrix (Fin 2) (Fin 2) ℂ)

theorem spectator_fixed_counterexample :
    spectatorFixedWitness ≠ 0 ∧ spectatorFixedWitness.trace = 0 ∧
      amplified (Fin 2) spectatorFixedWitness = spectatorFixedWitness ∧
      spectatorFixedWitness ∈ FiniteQutritInvariantExamples.matrixCarrier (Fin 2) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    have he := congrArg (fun X : Matrix (Q × Fin 2) (Q × Fin 2) ℂ => X (0,0) (0,0)) h
    norm_num [spectatorFixedWitness, Matrix.kronecker_apply, Matrix.one_apply] at he
  · rw [spectatorFixedWitness, Matrix.trace_kronecker]
    norm_num [Matrix.trace, Fin.sum_univ_succ]
  · rw [spectatorFixedWitness, amplified_product, transfer_one]
  · intro e f
    have hb : FiniteQutritInvariantExamples.block (Fin 2) e f spectatorFixedWitness =
        (!![1,0; 0,-1] : Matrix (Fin 2) (Fin 2) ℂ) e f • (1 : Mat) := by
      ext a b
      simp [spectatorFixedWitness, FiniteQutritInvariantExamples.block,
        Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]
    rw [hb]
    exact Matrix.isSymm_one.smul _


theorem amplified_iterate_positive (n : ℕ) {X : Matrix (Q × E) (Q × E) ℂ}
    (hX : X.PosSemidef) : (amplifiedIterate E n X).PosSemidef := by
  induction n generalizing X with
  | zero => exact hX
  | succ n ih => exact ih (amplified_positive E hX)

theorem amplified_iterate_invariant (n : ℕ) {X : Matrix (Q × E) (Q × E) ℂ}
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCarrier E) :
    amplifiedIterate E n X ∈ FiniteQutritInvariantExamples.matrixCarrier E := by
  intro e f
  rw [amplified_iterate_block]
  exact iterate_invariant n (hX e f)

theorem amplified_iterate_cone (n : ℕ) {X : Matrix (Q × E) (Q × E) ℂ}
    (hX : X ∈ FiniteQutritInvariantExamples.matrixCone E) :
    amplifiedIterate E n X ∈ FiniteQutritInvariantExamples.matrixCone E :=
  ⟨amplified_iterate_invariant E n hX.1, amplified_iterate_positive E n hX.2⟩

/-- Fixed normalized spectators preserve the actual selected joint probability.
The trace-one premise is explicitly impossible for an empty density space. -/
theorem spectator_selected_probability (j : Index) (n : ℕ) {σ : Matrix E E ℂ}
    (hσ : σ.trace = 1) :
    (run Q E 2 (wordTree E (suffixWord 1)) (suffixHistory 1)
      (amplifiedIterate E n
        (run Q E 2 (wordTree E (prefixWord j)) (prefixHistory j) (rho ⊗ₖ σ)))).trace.re =
      jointWeight j n := by
  rw [word_product_input, ← systemRun_product, prefix_systemState,
    amplified_iterate_product, word_product_input, ← systemRun_product,
    Matrix.trace_kronecker, hσ, mul_one, suffix_trace, jointWeight_trace]

/-- The old selected five-dimensional space retains its existing isometric
embedding; physical dimension and the reachable six-dimensional carrier differ. -/
theorem retained_three_five_six :
    Fintype.card (Q × Unit) = 3 ∧
    Module.finrank ℂ FiniteQutritPhysicalMemoryExamples.FeatureSpace = 5 ∧
    Module.finrank ℂ FeatureSpace = 6 ∧ Module.finrank ℂ symmetricCarrier = 6 :=
  FiniteQutritInvariantExamples.three_five_six

theorem pinching_orthogonal_residual (j : Setting) (X : Mat) :
    pairing (X-pinching j X) (pinching j X) = 0 := by
  change ⟪operatorEmbedding (X-pinching j X), operatorEmbedding (pinching j X)⟫_ℂ = 0
  rw [map_sub, inner_sub_left]
  change pairing X (pinching j X)-pairing (pinching j X) (pinching j X) = 0
  rw [pinching_energy, pairing_self, sub_self]


/-- Decode the actual ten-valued record into its original commanded setting. -/
def recordSettings : {n : ℕ} → History 10 n → List Setting
  | 0, _ => []
  | n+1, (k,h) => ((finProdFinEquiv (m := 5) (n := 2)).symm k).1 :: recordSettings h

/-- Decode every original binary outcome, including zero-probability leaves. -/
def recordOutcomes : {n : ℕ} → (h : History 10 n) → History 2 (recordSettings h).length
  | 0, _ => ()
  | n+1, (k,h) => (((finProdFinEquiv (m := 5) (n := 2)).symm k).2, recordOutcomes h)

theorem recordSettings_length {n : ℕ} (h : History 10 n) : (recordSettings h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ (ih h.2)

theorem fine_record_branch (k : Fin 10) (X : Mat) :
    (localStep Q Unit 10 instrument).branch Q Unit 10 k (joint X) =
      joint ((1/5 : ℂ) • systemBranch
        ((finProdFinEquiv (m := 5) (n := 2)).symm k).1
        ((finProdFinEquiv (m := 5) (n := 2)).symm k).2 X) := by
  obtain ⟨⟨j,a⟩,rfl⟩ := (finProdFinEquiv (m := 5) (n := 2)).surjective k
  rw [localStep_branch]
  unfold joint
  rw [FiniteAdaptiveMapPerturbation.lift_branch_tensor, record_action]
  simp only [Equiv.symm_apply_apply]

theorem systemRun_smul (w : List Setting) (h : History 2 w.length) (c : ℂ) (X : Mat) :
    systemRun w h (c • X) = c • systemRun w h X := by
  simp only [systemRun_product, Matrix.mul_smul, Matrix.smul_mul]

/-- A fresh setting contributes exactly 1/5 independently at every chronological
node. This is an unnormalized fine history, with no conditional division. -/
theorem independent_uniform_record (n : ℕ) (h : History 10 n) (X : Mat) :
    run Q Unit 10 (recordTree Unit n) h (joint X) =
      joint (((1/5 : ℂ)^n) • systemRun (recordSettings h) (recordOutcomes h) X) := by
  induction n generalizing X with
  | zero => simp [recordTree, run, recordSettings, recordOutcomes, systemRun]
  | succ n ih =>
    rcases h with ⟨k,h⟩
    change run Q Unit 10 (recordTree Unit n) h
      ((localStep Q Unit 10 instrument).branch Q Unit 10 k (joint X)) = _
    rw [fine_record_branch, ih, systemRun_smul, smul_smul]
    simp only [recordSettings, recordOutcomes, systemRun, pow_succ]


theorem actual_selected_commands :
    prefixWord 1 = [1,1] ∧ prefixHistory 1 = (0,0,()) ∧
    prefixWord 2 = [2,2] ∧ prefixHistory 2 = (0,0,()) ∧
    suffixWord 1 = [1,1] ∧ suffixHistory 1 = (0,0,()) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem amplified_partialTrace (X : Matrix (Q × E) (Q × E) ℂ) :
    FiniteQutritAveragedMixing.partialTrace E (amplified E X) = FiniteQutritAveragedMixing.partialTrace E X := by
  ext e f
  rw [partialTrace_block, amplified_block, transfer_trace, ← partialTrace_block]

theorem amplified_iterate_partialTrace (n : ℕ) (X : Matrix (Q × E) (Q × E) ℂ) :
    FiniteQutritAveragedMixing.partialTrace E (amplifiedIterate E n X) = FiniteQutritAveragedMixing.partialTrace E X := by
  ext e f
  rw [partialTrace_block, amplified_iterate_block, iterate_trace, ← partialTrace_block]

theorem trace_partialTrace (X : Matrix (Q × E) (Q × E) ℂ) :
    (FiniteQutritAveragedMixing.partialTrace E X).trace = X.trace := by
  simp only [FiniteQutritAveragedMixing.partialTrace, Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem amplified_trace (X : Matrix (Q × E) (Q × E) ℂ) :
    (amplified E X).trace = X.trace := by
  rw [← trace_partialTrace, amplified_partialTrace, trace_partialTrace]

theorem relative_partialTrace (X : Matrix (Q × E) (Q × E) ℂ) :
    FiniteQutritAveragedMixing.partialTrace E (relativeProjection E X) = FiniteQutritAveragedMixing.partialTrace E X := by
  ext e f
  rw [partialTrace_block, relative_block, stationary_trace, ← partialTrace_block]

theorem relative_idempotent (X : Matrix (Q × E) (Q × E) ℂ) :
    relativeProjection E (relativeProjection E X) = relativeProjection E X := by
  change ((1/3 : ℂ) • (1 : Mat)) ⊗ₖ
    FiniteQutritAveragedMixing.partialTrace E (relativeProjection E X) = _
  rw [relative_partialTrace]
  rfl

end SKEFTHawking.QuantumNetwork.FiniteQutritAveragedExamples
