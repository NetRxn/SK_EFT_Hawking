import SKEFTHawking.QuantumNetwork.FiniteMemoryResetMixture
import SKEFTHawking.QuantumNetwork.BinaryMemoryFixture

/-! Probabilistic identity/SWAP interactions, not coherent partial SWAP.
The basis witness has classical realizations. Exact real/matrix results do not
certify numerical tolerances or imply computational advantage. -/
namespace SKEFTHawking.QuantumNetwork.FiniteMemoryProcess
open Matrix
open scoped ComplexOrder Kronecker

noncomputable def partialInteraction (t : ℝ) (X : Matrix Joint Joint ℂ) :=
  (1-t) • X + t • swapJoint X
noncomputable def partialInteractionKraus (t : ℝ) : Fin 2 → Matrix Joint Joint ℂ :=
  ![Real.sqrt (1-t) • 1, Real.sqrt t • swapMat 2]

private theorem sqrt_conj (t : ℝ) (ht : 0 ≤ t) (A X : Matrix Joint Joint ℂ) :
    (Real.sqrt t • A) * X * (Real.sqrt t • A)ᴴ = t • (A * X * Aᴴ) := by
  simp [Matrix.conjTranspose_smul, smul_smul, mul_assoc, Real.mul_self_sqrt ht]
private theorem sqrt_norm (t : ℝ) (ht : 0 ≤ t) (A : Matrix Joint Joint ℂ) :
    (Real.sqrt t • A)ᴴ * (Real.sqrt t • A) = t • (Aᴴ * A) := by
  simp [Matrix.conjTranspose_smul, smul_smul, Real.mul_self_sqrt ht]

theorem partialInteractionKraus_eq {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (X : Matrix Joint Joint ℂ) : krausMap (partialInteractionKraus t) X = partialInteraction t X := by
  simp only [krausMap, partialInteractionKraus, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [sqrt_conj _ (sub_nonneg.mpr ht.2), sqrt_conj _ ht.1]
  simp [partialInteraction, swapJoint_eq, swapMat_isHermitian]

theorem partialInteractionKraus_normalized {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    IsKrausChannel (partialInteractionKraus t) := by
  simp only [IsKrausChannel, partialInteractionKraus, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [sqrt_norm _ (sub_nonneg.mpr ht.2), sqrt_norm _ ht.1]
  simp [swapMat_isHermitian, swapMat_mul_self, ← add_smul]

theorem partialInteraction_density {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (partialInteraction t X) := by
  rw [← partialInteractionKraus_eq ht]
  exact krausMap_isDensityOperator (partialInteractionKraus_normalized ht) hX

noncomputable def partialPostReset (t p : ℝ) (X : Matrix Joint Joint ℂ) :=
  resetMixture p (partialInteraction t X)
noncomputable def partialRetainedRun (t p : ℝ) (X : Matrix Joint Joint ℂ) :=
  partialInteraction t (partialPostReset t p X)
noncomputable def partialControlRun (t p : ℝ) (X : Matrix Joint Joint ℂ) :=
  partialInteraction t (resetEnvironment (partialPostReset t p X))

theorem partialPostReset_density {t p : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hp : p ∈ Set.Icc (0:ℝ) 1) {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (partialPostReset t p X) :=
  resetMixture_density p hp.1 hp.2 (partialInteraction_density ht hX)
theorem partialRetainedRun_density {t p : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hp : p ∈ Set.Icc (0:ℝ) 1) {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (partialRetainedRun t p X) :=
  partialInteraction_density ht (partialPostReset_density ht hp hX)
theorem partialControlRun_density {t p : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hp : p ∈ Set.Icc (0:ℝ) 1) {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (partialControlRun t p X) :=
  partialInteraction_density ht (resetEnvironment_density (partialPostReset_density ht hp hX))

private theorem swap_add (X Y : Matrix Joint Joint ℂ) :
    swapJoint (X+Y) = swapJoint X + swapJoint Y := by simp [swapJoint_eq, mul_add, add_mul]
private theorem swap_smul (r : ℝ) (X : Matrix Joint Joint ℂ) :
    swapJoint (r • X) = r • swapJoint X := by simp [swapJoint_eq]
private theorem reset_add (X Y : Matrix Joint Joint ℂ) :
    resetSystem (X+Y) = resetSystem X + resetSystem Y := by
  ext i j
  simp [resetSystem_eq, ptrace1, Finset.sum_add_distrib, mul_add]
private theorem reset_smul (r : ℝ) (X : Matrix Joint Joint ℂ) :
    resetSystem (r • X) = r • resetSystem X := by
  ext i j
  simp [resetSystem_eq, ptrace1]
  ring

/-- Full joint trajectory at the intervention, including residual S information. -/
theorem partialPostReset_basis (t p : ℝ) (b : Qubit) :
    partialPostReset t p (basisState b ⊗ₖ basisState 0) =
      ((1-p)*(1-t)) • (basisState 0 ⊗ₖ basisState 0) +
      (p*(1-t)) • (basisState b ⊗ₖ basisState 0) +
      t • (basisState 0 ⊗ₖ basisState b) := by
  simp only [partialPostReset, partialInteraction, swapJoint_basis, resetMixture,
    reset_add, reset_smul, resetSystem_basis, smul_add, smul_smul]
  module

private theorem marginal_add (X Y : Matrix Joint Joint ℂ) :
    systemMarginal (X+Y) = systemMarginal X + systemMarginal Y := by
  ext i j
  simp [systemMarginal, swap_add, ptrace1, Finset.sum_add_distrib]
private theorem marginal_smul (r : ℝ) (X : Matrix Joint Joint ℂ) :
    systemMarginal (r • X) = r • systemMarginal X := by
  ext i j
  simp [systemMarginal, swap_smul, ptrace1]
private theorem marginal_basis (a b : Qubit) :
    systemMarginal (basisState a ⊗ₖ basisState b) = basisState a := by
  rw [systemMarginal, swapJoint_basis, ptrace1_basis]

theorem partialPostReset_marginal (t p : ℝ) (b : Qubit) :
    systemMarginal (partialPostReset t p (basisState b ⊗ₖ basisState 0)) =
      binaryDiagonalState (if b=1 then p*(1-t) else 0) := by
  rw [partialPostReset_basis]
  simp only [marginal_add, marginal_smul, marginal_basis]
  ext i j
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [basisState, binaryDiagonalState, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.real_smul] <;> ring

private theorem prob_add (o : Qubit) (X Y : Matrix Joint Joint ℂ) :
    systemProbability o (X+Y) = systemProbability o X + systemProbability o Y := by
  simp [systemProbability, mul_add, Matrix.trace_add]
private theorem prob_smul (o : Qubit) (r : ℝ) (X : Matrix Joint Joint ℂ) :
    systemProbability o (r • X) = r * systemProbability o X := by
  simp [systemProbability, Matrix.trace_smul]

theorem partialRetained_probability (t p : ℝ) (b : Qubit) :
    systemProbability 1 (partialRetainedRun t p (basisState b ⊗ₖ basisState 0)) =
      if b=1 then t^2+p*(1-t)^2 else 0 := by
  simp only [partialRetainedRun, partialPostReset_basis, partialInteraction,
    swap_add, swap_smul, swapJoint_basis, prob_add, prob_smul, systemProbability_basis]
  fin_cases b <;> norm_num; ring

theorem partialControl_probability (t p : ℝ) (b : Qubit) :
    systemProbability 1 (partialControlRun t p (basisState b ⊗ₖ basisState 0)) =
      if b=1 then p*(1-t)^2 else 0 := by
  simp only [partialControlRun, partialPostReset_basis, resetEnvironment, swap_add,
    swap_smul, swapJoint_basis, reset_add, reset_smul, resetSystem_basis,
    partialInteraction, prob_add, prob_smul, systemProbability_basis]
  fin_cases b <;> norm_num; ring

/-- Exact leakage budget; the common reference is the zero preparation. -/
theorem partialPostReset_traceDist {t p : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hp : p ∈ Set.Icc (0:ℝ) 1) (b : Qubit) :
    traceDist (systemMarginal (partialPostReset t p (basisState b ⊗ₖ basisState 0)))
      (binaryDiagonalState 0) = if b=1 then p*(1-t) else 0 := by
  rw [partialPostReset_marginal, binaryDiagonalState_traceDist]
  split_ifs <;> simp [abs_of_nonneg (mul_nonneg hp.1 (sub_nonneg.mpr ht.2))]

/-- Reset marginals are valid states, independently of the joint continuation. -/
theorem partialPostReset_marginal_density {t p : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hp : p ∈ Set.Icc (0:ℝ) 1) (b : Qubit) :
    IsDensityOperator (systemMarginal (partialPostReset t p (basisState b ⊗ₖ basisState 0))) := by
  rw [partialPostReset_marginal]
  apply binaryDiagonalState_density
  split_ifs
  · exact ⟨mul_nonneg hp.1 (sub_nonneg.mpr ht.2),
      le_trans (mul_le_mul_of_nonneg_right hp.2 (sub_nonneg.mpr ht.2)) (by linarith [ht.1])⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- Every common normalized system channel and common binary effect obeys the
actual postreset leakage allowance. -/
theorem partial_common_channel_bound {t p : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hp : p ∈ Set.Icc (0:ℝ) 1) {k : ℕ}
    (K : Fin k → Matrix Qubit Qubit ℂ) (hK : IsKrausChannel K)
    (E : Matrix Qubit Qubit ℂ) (hE : IsBinaryPOVM E) :
    |binaryOutcomeProb E (krausMap K
      (systemMarginal (partialPostReset t p (basisState 0 ⊗ₖ basisState 0)))) -
    binaryOutcomeProb E (krausMap K
      (systemMarginal (partialPostReset t p (basisState 1 ⊗ₖ basisState 0))))| ≤ p*(1-t) := by
  have d0 := partialPostReset_traceDist ht hp 0
  have d1 := partialPostReset_traceDist ht hp 1
  norm_num at d0 d1
  have h := binary_memoryless_separation_le
    (partialPostReset_marginal_density ht hp 0)
    (partialPostReset_marginal_density ht hp 1)
    (binaryDiagonalState_density (r := 0) ⟨le_rfl, zero_le_one⟩) hK hE d0.le d1.le
  exact le_trans h (by simp only [zero_add]; exact min_le_right _ _)

/-- Quantitative margin above every allowed common system-only model. -/
theorem partialRetained_margin (t p : ℝ) :
    systemProbability 1 (partialRetainedRun t p (basisState 1 ⊗ₖ basisState 0)) -
      p*(1-t) = t*(t-p*(1-t)) := by
  rw [partialRetained_probability]
  norm_num
  ring

/-- A single normalized K and binary E cannot reproduce both retained histories
in the strict regime. The quantifiers require the SAME continuation and effect. -/
theorem partial_no_common_system_model {t p : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hp : p ∈ Set.Icc (0:ℝ) 1) (htpos : 0 < t) (hstrict : p*(1-t) < t)
    {k : ℕ} (K : Fin k → Matrix Qubit Qubit ℂ)
    (hK : IsKrausChannel K) (E : Matrix Qubit Qubit ℂ) (hE : IsBinaryPOVM E) :
    ¬ (∀ b : Qubit, binaryOutcomeProb E (krausMap K
      (systemMarginal (partialPostReset t p (basisState b ⊗ₖ basisState 0)))) =
      systemProbability 1 (partialRetainedRun t p (basisState b ⊗ₖ basisState 0))) := by
  intro h
  have bound := partial_common_channel_bound ht hp K hK E hE
  rw [h 0, h 1, partialRetained_probability, partialRetained_probability] at bound
  norm_num only [show (0:Qubit) ≠ 1 by decide, if_false, if_true, zero_sub, abs_neg] at bound
  have hn : 0 ≤ t^2+p*(1-t)^2 := add_nonneg (sq_nonneg _) (mul_nonneg hp.1 (sq_nonneg _))
  rw [abs_of_nonneg hn] at bound
  have pos := mul_pos htpos (sub_pos.mpr hstrict)
  nlinarith

/-- The control removes the environment contribution but can retain reset leakage. -/
theorem partial_control_gap (t p : ℝ) :
    systemProbability 1 (partialRetainedRun t p (basisState 1 ⊗ₖ basisState 0)) -
      systemProbability 1 (partialControlRun t p (basisState 1 ⊗ₖ basisState 0)) = t^2 := by
  simp only [partialRetained_probability, partialControl_probability, if_true]
  ring

theorem partial_interior_example :
    systemProbability 1 (partialRetainedRun (1/2) (1/4) (basisState 1 ⊗ₖ basisState 0)) = 5/16 ∧
    systemProbability 1 (partialControlRun (1/2) (1/4) (basisState 1 ⊗ₖ basisState 0)) = 1/16 ∧
    traceDist (systemMarginal (partialPostReset (1/2) (1/4) (basisState 1 ⊗ₖ basisState 0)))
      (binaryDiagonalState 0) = 1/8 := by
  rw [partialRetained_probability, partialControl_probability,
    partialPostReset_traceDist (by constructor <;> norm_num) (by constructor <;> norm_num)]
  norm_num

/-- The strict exclusion regime is inhabited at interior physical parameters. -/
theorem partial_interior_exclusion {k : ℕ} (K : Fin k → Matrix Qubit Qubit ℂ)
    (hK : IsKrausChannel K) (E : Matrix Qubit Qubit ℂ) (hE : IsBinaryPOVM E) :
    ¬ (∀ b : Qubit, binaryOutcomeProb E (krausMap K
      (systemMarginal (partialPostReset (1/2) (1/4) (basisState b ⊗ₖ basisState 0)))) =
      systemProbability 1 (partialRetainedRun (1/2) (1/4) (basisState b ⊗ₖ basisState 0))) :=
  partial_no_common_system_model (by constructor <;> norm_num)
    (by constructor <;> norm_num) (by norm_num) (by norm_num) K hK E hE

/-- No interaction: any residual signal is entirely reset leakage. -/
theorem partial_zero_interaction (p : ℝ) :
    systemProbability 1 (partialRetainedRun 0 p (basisState 1 ⊗ₖ basisState 0)) = p ∧
    systemProbability 1 (partialControlRun 0 p (basisState 1 ⊗ₖ basisState 0)) = p := by
  simp [partialRetained_probability, partialControl_probability]

/-- At full interaction the earlier reset-insensitive witness is recovered. -/
theorem partial_full_interaction (p : ℝ) :
    systemProbability 1 (partialRetainedRun 1 p (basisState 1 ⊗ₖ basisState 0)) = 1 ∧
    systemProbability 1 (partialControlRun 1 p (basisState 1 ⊗ₖ basisState 0)) = 0 := by
  simp [partialRetained_probability, partialControl_probability]

/-- Equality at this boundary is inconclusive for this criterion, not memory absence. -/
theorem partial_inconclusive_boundary :
    systemProbability 1 (partialRetainedRun (1/2) 1 (basisState 1 ⊗ₖ basisState 0)) =
      (1:ℝ)*(1-1/2) := by
  norm_num [partialRetained_probability]

end SKEFTHawking.QuantumNetwork.FiniteMemoryProcess
