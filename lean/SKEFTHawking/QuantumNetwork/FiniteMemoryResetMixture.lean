import SKEFTHawking.QuantumNetwork.FiniteMemoryProcess
import SKEFTHawking.QuantumNetwork.BinaryMemoryRobustness

/-!
# Exact reset-mixture and measurement bridges

The reset-skip model applies local discard-and-prepare with weight `1-p` and
the identity with weight `p`. Its three Kraus operators establish physicality
for `p ∈ [0,1]`. This model fixes every state with system factor `|0⟩⟨0|`, so
the ideal SWAP experiment is insensitive to this particular reset imperfection.
The results concern exact matrices and real parameters, not floating-point
validation, clipping, or error certification of a numerical implementation.
-/

namespace SKEFTHawking.QuantumNetwork.FiniteMemoryProcess

open Matrix
open scoped ComplexOrder Kronecker

/-- The exact reset-skip mixture, with real scalar action on complex matrices. -/
noncomputable def resetMixture (p : ℝ) (X : Matrix Joint Joint ℂ) : Matrix Joint Joint ℂ :=
  (1 - p) • resetSystem X + p • X

/-- Two reset branches and one identity branch; there is no postselection. -/
noncomputable def resetMixtureKraus (p : ℝ) : Fin 3 → Matrix Joint Joint ℂ :=
  ![Real.sqrt (1 - p) • tensorKraus resetKraus 0,
    Real.sqrt (1 - p) • tensorKraus resetKraus 1,
    Real.sqrt p • (1 : Matrix Joint Joint ℂ)]

private theorem sqrt_conj (t : ℝ) (ht : 0 ≤ t) (A X : Matrix Joint Joint ℂ) :
    (Real.sqrt t • A) * X * (Real.sqrt t • A)ᴴ = t • (A * X * Aᴴ) := by
  simp [Matrix.conjTranspose_smul, smul_smul, mul_assoc, Real.mul_self_sqrt ht]

private theorem sqrt_norm (t : ℝ) (ht : 0 ≤ t) (A : Matrix Joint Joint ℂ) :
    (Real.sqrt t • A)ᴴ * (Real.sqrt t • A) = t • (Aᴴ * A) := by
  simp [Matrix.conjTranspose_smul, smul_smul, Real.mul_self_sqrt ht]

/-- The Kraus realization is exactly the reset-skip mixture on arbitrary inputs. -/
theorem resetMixtureKraus_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Matrix Joint Joint ℂ) :
    krausMap (resetMixtureKraus p) X = resetMixture p X := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  simp only [krausMap, resetMixtureKraus, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  rw [sqrt_conj _ hq, sqrt_conj _ hq, sqrt_conj _ hp0]
  simp [resetMixture, resetSystem, krausMap, Fin.sum_univ_two, smul_add, add_assoc]

/-- Normalization is proved for the full three-branch channel. -/
theorem resetMixtureKraus_normalized (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsKrausChannel (resetMixtureKraus p) := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hR := resetSystem_normalized
  simp only [IsKrausChannel, Fin.sum_univ_two] at hR
  simp only [IsKrausChannel, resetMixtureKraus, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  rw [sqrt_norm _ hq, sqrt_norm _ hq, sqrt_norm _ hp0]
  rw [← add_assoc, ← smul_add, hR]
  simp [← add_smul]

/-- The reset-skip mixture maps every joint density operator to a density operator. -/
theorem resetMixture_density (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (resetMixture p X) := by
  rw [← resetMixtureKraus_eq p hp0 hp1]
  exact krausMap_isDensityOperator (resetMixtureKraus_normalized p hp0 hp1) hX

/-- A system already prepared in zero is unchanged by local reset, for any environment matrix. -/
theorem resetSystem_zero_tensor (E : Matrix Qubit Qubit ℂ) :
    resetSystem (basisState 0 ⊗ₖ E) = basisState 0 ⊗ₖ E := by
  rw [resetSystem_eq]
  congr 1
  ext i j
  simp [ptrace1, basisState]

/-- This particular imperfection has no effect on the fixed subspace of reset.
The algebraic identity holds for every real weight; physicality uses `[0,1]`. -/
theorem resetMixture_zero_tensor (p : ℝ) (E : Matrix Qubit Qubit ℂ) :
    resetMixture p (basisState 0 ⊗ₖ E) = basisState 0 ⊗ₖ E := by
  rw [resetMixture, resetSystem_zero_tensor, ← add_smul]
  simp

/-- Retained-memory experiment with the reset-skip mixture at the intervention. -/
noncomputable def retainedMixtureRun (p : ℝ) (X : Matrix Joint Joint ℂ) :
    Matrix Joint Joint ℂ := swapJoint (resetMixture p (swapJoint X))

/-- Every joint density input follows a physical mixture experiment for valid weights. -/
theorem retainedMixtureRun_density (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (retainedMixtureRun p X) :=
  swapJoint_density (resetMixture_density p hp0 hp1 (swapJoint_density hX))

/-- The ideal retained-memory basis witness is insensitive to reset skipping. -/
theorem retainedMixtureRun_basis (p : ℝ) (b : Qubit) :
    retainedMixtureRun p (basisState b ⊗ₖ basisState 0) =
      basisState b ⊗ₖ basisState 0 := by
  rw [retainedMixtureRun, swapJoint_basis, resetMixture_zero_tensor, swapJoint_basis]

/-- The mixture experiment retains deterministic system outcomes. -/
theorem retainedMixtureRun_probability (p : ℝ) (b outcome : Qubit) :
    systemProbability outcome (retainedMixtureRun p (basisState b ⊗ₖ basisState 0)) =
      if outcome = b then 1 else 0 := by
  rw [retainedMixtureRun_basis, systemProbability_basis]

/-- Perfect reset of E alone, preserving S through conjugation by SWAP. -/
noncomputable def resetEnvironment (X : Matrix Joint Joint ℂ) : Matrix Joint Joint ℂ :=
  swapJoint (resetSystem (swapJoint X))

theorem resetEnvironment_density {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (resetEnvironment X) :=
  swapJoint_density (resetSystem_density (swapJoint_density hX))

theorem resetEnvironment_basis (a b : Qubit) :
    resetEnvironment (basisState a ⊗ₖ basisState b) = basisState a ⊗ₖ basisState 0 := by
  rw [resetEnvironment, swapJoint_basis, resetSystem_basis, swapJoint_basis]

/-- Control: SWAP, reset-skip mixture on S, perfect reset of E, then SWAP.
The perfect E reset does not add an extra perfect reset of S. -/
noncomputable def controlMixtureRun (p : ℝ) (X : Matrix Joint Joint ℂ) :
    Matrix Joint Joint ℂ :=
  swapJoint (resetEnvironment (resetMixture p (swapJoint X)))

theorem controlMixtureRun_density (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (controlMixtureRun p X) :=
  swapJoint_density (resetEnvironment_density
    (resetMixture_density p hp0 hp1 (swapJoint_density hX)))

/-- The specified basis control erases the history for every reset-skip weight. -/
theorem controlMixtureRun_basis (p : ℝ) (b : Qubit) :
    controlMixtureRun p (basisState b ⊗ₖ basisState 0) =
      basisState 0 ⊗ₖ basisState 0 := by
  rw [controlMixtureRun, swapJoint_basis, resetMixture_zero_tensor,
    resetEnvironment_basis, swapJoint_basis]

/-- Both basis histories yield outcome zero in the control. -/
theorem controlMixtureRun_probability (p : ℝ) (b outcome : Qubit) :
    systemProbability outcome (controlMixtureRun p (basisState b ⊗ₖ basisState 0)) =
      if outcome = 0 then 1 else 0 := by
  rw [controlMixtureRun_basis, systemProbability_basis]

/-- Summing the diagonal entries with fixed system outcome equals its Born probability.
This holds for arbitrary matrices before any numerical real-part/clipping procedure. -/
theorem systemProbability_diagonal_sum (outcome : Qubit) (X : Matrix Joint Joint ℂ) :
    systemProbability outcome X = ∑ e : Qubit, (X (outcome,e) (outcome,e)).re := by
  fin_cases outcome <;>
    simp [systemProbability, basisState, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem systemEffect_complement :
    1 - (basisState 0 ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) =
      basisState 1 ⊗ₖ (1 : Matrix Qubit Qubit ℂ) := by
  have hsum : (basisState 0 ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) +
      (basisState 1 ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) = 1 := by
    rw [← Matrix.add_kronecker, basisEffects_sum, Matrix.one_kronecker_one]
  rw [← hsum, add_sub_cancel_left]

/-- Outcome probabilities are complementary on normalized density inputs. -/
theorem systemProbability_complement {X : Matrix Joint Joint ℂ}
    (hX : IsDensityOperator X) : systemProbability 1 X = 1 - systemProbability 0 X := by
  have h := binaryOutcomeProb_complement
    (E := basisState 0 ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) hX
  rw [systemEffect_complement] at h
  exact h

/-- Computational-basis probabilities lie in the unit interval. -/
theorem systemProbability_mem_Icc (outcome : Qubit) {X : Matrix Joint Joint ℂ}
    (hX : IsDensityOperator X) : systemProbability outcome X ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : systemProbability 0 X ∈ Set.Icc (0 : ℝ) 1 :=
    binaryOutcomeProb_mem_Icc systemEffect_binary hX
  fin_cases outcome
  · exact h0
  · change systemProbability (1 : Qubit) X ∈ Set.Icc (0 : ℝ) 1
    rw [systemProbability_complement hX]
    exact ⟨by linarith [h0.2], by linarith [h0.1]⟩

/-- The two probabilities sum to one without renormalization. -/
theorem systemProbability_sum {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    systemProbability 0 X + systemProbability 1 X = 1 := by
  rw [systemProbability_complement hX]
  ring

end SKEFTHawking.QuantumNetwork.FiniteMemoryProcess
