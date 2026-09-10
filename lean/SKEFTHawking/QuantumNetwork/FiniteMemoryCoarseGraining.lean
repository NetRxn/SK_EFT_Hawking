import SKEFTHawking.QuantumNetwork.FiniteMemoryPartialInteraction

/-! Exact forgetting for a finite collision model. Each step injects a fresh
basis-state system, uses probabilistic identity/SWAP, then discards the system.
This proves model-specific approximation and obstruction, not computational
advantage or a numerical-error certificate. Lists are in chronological order. -/
namespace SKEFTHawking.QuantumNetwork.FiniteMemoryCoarseGraining

open Matrix FiniteMemoryProcess
open scoped ComplexOrder Kronecker

/-- Actual environment update from the joint interaction, including on unnormalized input. -/
noncomputable def collision (κ : ℝ) (b : Qubit) (X : Matrix Qubit Qubit ℂ) :=
  ptrace1 (partialInteraction (1 - κ) (basisState b ⊗ₖ X))

theorem swap_tensor (A B : Matrix Qubit Qubit ℂ) :
    swapJoint (A ⊗ₖ B) = B ⊗ₖ A := by
  rw [swapJoint_eq]
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [swapMat, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

theorem collision_linear (κ : ℝ) (b : Qubit) (X : Matrix Qubit Qubit ℂ) :
    collision κ b X = (κ : ℂ) • X + ((1 - κ : ℝ) : ℂ) • (X.trace • basisState b) := by
  unfold collision partialInteraction
  rw [swap_tensor]
  ext i j
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [ptrace1, basisState, Fin.sum_univ_two, Matrix.trace,
      Complex.real_smul, Complex.ofReal_sub] <;> ring

theorem collision_density {κ : ℝ} (hκ : κ ∈ Set.Icc (0 : ℝ) 1)
    (b : Qubit) {ρ : Matrix Qubit Qubit ℂ} (hρ : IsDensityOperator ρ) :
    IsDensityOperator (collision κ b ρ) := by
  have hin : IsDensityOperator (basisState b ⊗ₖ ρ) :=
    ⟨(basisState_density b).1.kronecker hρ.1, by
      rw [Matrix.trace_kronecker, (basisState_density b).2, hρ.2, mul_one]⟩
  have hout := partialInteraction_density
    (show 1 - κ ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith [hκ.2], by linarith [hκ.1]⟩) hin
  exact ⟨ptrace1_posSemidef hout.1, (trace_ptrace1 _).trans hout.2⟩

theorem collision_on_density (κ : ℝ) (b : Qubit) {ρ : Matrix Qubit Qubit ℂ}
    (hρ : IsDensityOperator ρ) :
    collision κ b ρ = (κ : ℂ) • ρ + ((1 - κ : ℝ) : ℂ) • basisState b := by
  rw [collision_linear, hρ.2, one_smul]

/-- One physically admissible fresh-input collision. -/
structure Step where
  retention : ℝ
  bit : Qubit
  admissible : retention ∈ Set.Icc (0 : ℝ) 1

/-- Execute the head first, then the chronological tail. -/
noncomputable def run : List Step → Matrix Qubit Qubit ℂ → Matrix Qubit Qubit ℂ
  | [], ρ => ρ
  | s :: ss, ρ => run ss (collision s.retention s.bit ρ)

def retentionProduct : List Step → ℝ
  | [] => 1
  | s :: ss => s.retention * retentionProduct ss

theorem retentionProduct_nonneg (ss : List Step) : 0 ≤ retentionProduct ss := by
  induction ss with
  | nil => norm_num [retentionProduct]
  | cons s ss ih => exact mul_nonneg s.admissible.1 ih

theorem retentionProduct_le_one (ss : List Step) : retentionProduct ss ≤ 1 := by
  induction ss with
  | nil => simp [retentionProduct]
  | cons s ss ih =>
    exact (mul_le_mul_of_nonneg_right s.admissible.2 (retentionProduct_nonneg ss)).trans
      (by simpa using ih)

theorem run_density (ss : List Step) {ρ : Matrix Qubit Qubit ℂ}
    (hρ : IsDensityOperator ρ) : IsDensityOperator (run ss ρ) := by
  induction ss generalizing ρ with
  | nil => exact hρ
  | cons s ss ih => exact ih (collision_density s.admissible s.bit hρ)

theorem run_difference (ss : List Step) {ρ σ : Matrix Qubit Qubit ℂ}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    run ss ρ - run ss σ = (retentionProduct ss : ℂ) • (ρ - σ) := by
  induction ss generalizing ρ σ with
  | nil => simp [run, retentionProduct]
  | cons s ss ih =>
    rw [run, run, ih (collision_density s.admissible s.bit hρ)
      (collision_density s.admissible s.bit hσ), collision_on_density _ _ hρ,
      collision_on_density _ _ hσ]
    simp only [add_sub_add_right_eq_sub, ← smul_sub, smul_smul, retentionProduct,
      Complex.ofReal_mul, mul_comm]

theorem run_traceDist (ss : List Step) {ρ σ : Matrix Qubit Qubit ℂ}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    traceDist (run ss ρ) (run ss σ) = retentionProduct ss * traceDist ρ σ := by
  unfold traceDist
  rw [run_difference ss hρ hσ, traceNorm_smul_nonneg (retentionProduct_nonneg ss)]
  ring

theorem run_append (pre suffix : List Step) (ρ : Matrix Qubit Qubit ℂ) :
    run (pre ++ suffix) ρ = run suffix (run pre ρ) := by
  induction pre generalizing ρ with
  | nil => rfl
  | cons s ss ih => exact ih _

/-- Discarded history replaced by an arbitrary density reference. -/
theorem suffix_prediction_bound (pre suffix : List Step) {ρ τ : Matrix Qubit Qubit ℂ}
    (hρ : IsDensityOperator ρ) (hτ : IsDensityOperator τ) :
    traceDist (run (pre ++ suffix) ρ) (run suffix τ) ≤ retentionProduct suffix := by
  rw [run_append, run_traceDist suffix (run_density pre hρ) hτ]
  exact (mul_le_mul_of_nonneg_left (traceDist_mem_Icc (run_density pre hρ) hτ).2
    (retentionProduct_nonneg suffix)).trans_eq (mul_one _)

/-- The same error budget survives any shared downstream channel and binary test. -/
theorem suffix_binary_prediction_bound {m : ℕ} (pre suffix : List Step)
    {ρ τ E : Matrix Qubit Qubit ℂ} {K : Fin m → Matrix Qubit Qubit ℂ}
    (hρ : IsDensityOperator ρ) (hτ : IsDensityOperator τ)
    (hK : IsKrausChannel K) (hE : IsBinaryPOVM E) :
    |binaryOutcomeProb E (krausMap K (run (pre ++ suffix) ρ)) -
      binaryOutcomeProb E (krausMap K (run suffix τ))| ≤ retentionProduct suffix := by
  have hfull := run_density (pre ++ suffix) hρ
  have hshort := run_density suffix hτ
  exact (abs_binaryOutcomeProb_sub_le_traceDist hE
    (krausMap_isDensityOperator hK hfull) (krausMap_isDensityOperator hK hshort)).trans
    ((traceDist_krausMap_le hK hfull.1.isHermitian hshort.1.isHermitian).trans
      (suffix_prediction_bound pre suffix hρ hτ))

/-- Computational-basis measurement distinguishes the two basis inputs. -/
theorem basis_binary_probability (b : Qubit) :
    binaryOutcomeProb binaryOneEffect (basisState b) = if b = 1 then 1 else 0 := by
  fin_cases b <;> simp [binaryOutcomeProb, binaryOneEffect, basisState,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- The sharp operational separation holds for every common driven suffix. -/
theorem run_binary_separation (ss : List Step) :
    |binaryOutcomeProb binaryOneEffect (run ss (basisState 0)) -
      binaryOutcomeProb binaryOneEffect (run ss (basisState 1))| = retentionProduct ss := by
  have hh := congrArg (fun X : Matrix Qubit Qubit ℂ => (binaryOneEffect * X).trace.re)
    (run_difference ss (basisState_density 0) (basisState_density 1))
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hh
  change binaryOutcomeProb binaryOneEffect (run ss (basisState 0)) -
    binaryOutcomeProb binaryOneEffect (run ss (basisState 1)) =
    retentionProduct ss * (binaryOutcomeProb binaryOneEffect (basisState 0) -
      binaryOutcomeProb binaryOneEffect (basisState 1)) at hh
  rw [basis_binary_probability, basis_binary_probability] at hh
  norm_num at hh
  rw [hh, abs_neg, abs_of_nonneg (retentionProduct_nonneg ss)]

/-- No predictor using only the common suffix can fit both forgotten histories
more accurately than half their operational separation. -/
theorem suffix_predictor_lower_bound (ss : List Step) (z : ℝ) :
    retentionProduct ss / 2 ≤ max
      |binaryOutcomeProb binaryOneEffect (run ss (basisState 0)) - z|
      |binaryOutcomeProb binaryOneEffect (run ss (basisState 1)) - z| := by
  have ht := abs_sub_le (binaryOutcomeProb binaryOneEffect (run ss (basisState 0)))
    z (binaryOutcomeProb binaryOneEffect (run ss (basisState 1)))
  rw [run_binary_separation, abs_sub_comm z] at ht
  have h0 := le_max_left
    |binaryOutcomeProb binaryOneEffect (run ss (basisState 0)) - z|
    |binaryOutcomeProb binaryOneEffect (run ss (basisState 1)) - z|
  have h1 := le_max_right
    |binaryOutcomeProb binaryOneEffect (run ss (basisState 0)) - z|
    |binaryOutcomeProb binaryOneEffect (run ss (basisState 1)) - z|
  linarith

/-- A final SWAP exposes the retained environment on the controlled system. -/
theorem finalSwap_readout (b : Qubit) (X : Matrix Qubit Qubit ℂ) :
    systemProbability 1 (swapJoint (basisState b ⊗ₖ X)) = binaryOutcomeProb binaryOneEffect X := by
  rw [swap_tensor]
  fin_cases b <;> simp [systemProbability, binaryOutcomeProb, basisState, binaryOneEffect,
    Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem retentionProduct_replicate (s : Step) (L : ℕ) :
    retentionProduct (List.replicate L s) = s.retention ^ L := by
  induction L with
  | zero => simp [retentionProduct]
  | succ L ih => simp [List.replicate_succ, retentionProduct, ih, pow_succ, mul_comm]

/-- Constant retention gives the usual exponential finite-history error bound. -/
theorem suffix_constant_prediction_bound (pre : List Step) (s : Step) (L : ℕ)
    {ρ τ : Matrix Qubit Qubit ℂ} (hρ : IsDensityOperator ρ) (hτ : IsDensityOperator τ) :
    traceDist (run (pre ++ List.replicate L s) ρ) (run (List.replicate L s) τ) ≤
      s.retention ^ L := by
  simpa [retentionProduct_replicate] using suffix_prediction_bound pre (List.replicate L s) hρ hτ

/-- Retention one prevents forgetting, regardless of how long this suffix is. -/
theorem no_forgetting_lower_bound (s : Step) (hs : s.retention = 1) (L : ℕ) (z : ℝ) :
    (1 : ℝ) / 2 ≤ max
      |binaryOutcomeProb binaryOneEffect (run (List.replicate L s) (basisState 0)) - z|
      |binaryOutcomeProb binaryOneEffect (run (List.replicate L s) (basisState 1)) - z| := by
  simpa [retentionProduct_replicate, hs] using suffix_predictor_lower_bound (List.replicate L s) z

/-- A zero-retention collision erases the incoming state after one step. -/
theorem zero_retention_erases (b : Qubit) {ρ : Matrix Qubit Qubit ℂ}
    (hρ : IsDensityOperator ρ) : collision 0 b ρ = basisState b := by
  simp [collision_on_density _ _ hρ]

theorem zero_retention_suffix_independent (s : Step) (hs : s.retention = 0)
    (ss : List Step) {ρ σ : Matrix Qubit Qubit ℂ}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) : run (s :: ss) ρ = run (s :: ss) σ := by
  simp [run, hs, zero_retention_erases _ hρ, zero_retention_erases _ hσ]

end SKEFTHawking.QuantumNetwork.FiniteMemoryCoarseGraining
