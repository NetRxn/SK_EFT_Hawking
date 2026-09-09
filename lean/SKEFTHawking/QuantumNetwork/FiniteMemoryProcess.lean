import SKEFTHawking.QuantumNetwork.DiamondNormChoiUpper
import SKEFTHawking.QuantumNetwork.MaxEntNegativity
import SKEFTHawking.QuantumNetwork.HelstromDiscrimination

/-!
# Retained memory in a finite intervention experiment

The first factor is the controlled system, the second its retained environment.
Local reset is a normalized Kraus channel on arbitrary joint inputs, including
correlated states. SWAP transfers a classical basis label to the environment and
back after reset. This witness excludes a common continuation depending only on
the reset system state; it does not distinguish classical from quantum memory.
-/

namespace SKEFTHawking.QuantumNetwork.FiniteMemoryProcess

open Matrix
open scoped ComplexOrder Kronecker

abbrev Qubit := Fin 2
abbrev Joint := Qubit × Qubit

/-- Computational basis density matrix `|b⟩⟨b|`. -/
noncomputable def basisState (b : Qubit) : Matrix Qubit Qubit ℂ :=
  fun i j => if i = b ∧ j = b then 1 else 0

/-- Discard-and-prepare reset operators `|0⟩⟨k|`, with both outcomes summed. -/
noncomputable def resetKraus (k : Fin 2) : Matrix Qubit Qubit ℂ :=
  fun i j => if i = 0 ∧ j = k then 1 else 0

/-- The local reset is trace-preserving without postselection. -/
theorem resetKraus_normalized : IsKrausChannel resetKraus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [IsKrausChannel, resetKraus, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- Reset the system while retaining the environment. -/
noncomputable def resetSystem (X : Matrix Joint Joint ℂ) : Matrix Joint Joint ℂ :=
  krausMap (tensorKraus resetKraus) X

/-- The tensor reset has normalized Kraus operators. -/
theorem resetSystem_normalized : IsKrausChannel (tensorKraus resetKraus) :=
  isKrausChannel_tensorKraus resetKraus_normalized

/-- Exact reset semantics for arbitrary matrices, with no product-state assumption. -/
theorem resetSystem_eq (X : Matrix Joint Joint ℂ) :
    resetSystem X = basisState 0 ⊗ₖ ptrace1 X := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [resetSystem, krausMap, tensorKraus, resetKraus, basisState, ptrace1,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two]

/-- Reset preserves validity of joint density operators. -/
theorem resetSystem_density {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (resetSystem X) :=
  krausMap_isDensityOperator resetSystem_normalized hX

/-- SWAP as a singleton Kraus family on the joint carrier. -/
noncomputable def swapKraus (_ : Fin 1) : Matrix Joint Joint ℂ := swapMat 2

theorem swapKraus_normalized : IsKrausChannel swapKraus := by
  simp [IsKrausChannel, swapKraus, swapMat_isHermitian, swapMat_mul_self]

/-- Physical joint SWAP channel. -/
noncomputable def swapJoint (X : Matrix Joint Joint ℂ) : Matrix Joint Joint ℂ :=
  krausMap swapKraus X

theorem swapJoint_eq (X : Matrix Joint Joint ℂ) :
    swapJoint X = swapMat 2 * X * swapMat 2 := by
  simp [swapJoint, krausMap, swapKraus, swapMat_isHermitian]

theorem swapJoint_density {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (swapJoint X) :=
  krausMap_isDensityOperator swapKraus_normalized hX

/-- SWAP exchanges independently prepared basis labels. -/
theorem swapJoint_basis (a b : Qubit) :
    swapJoint (basisState a ⊗ₖ basisState b) = basisState b ⊗ₖ basisState a := by
  rw [swapJoint_eq]
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases l <;>
    simp [swapMat, basisState, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The environment's basis label survives local reset. -/
theorem resetSystem_basis (a b : Qubit) :
    resetSystem (basisState a ⊗ₖ basisState b) = basisState 0 ⊗ₖ basisState b := by
  rw [resetSystem_eq]
  congr 1
  ext i j
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [ptrace1, basisState]

/-- Basis projectors are valid density operators. -/
theorem basisState_density (b : Qubit) : IsDensityOperator (basisState b) := by
  have hfactor : basisState b * (basisState b)ᴴ = basisState b := by
    ext i j
    fin_cases b <;> fin_cases i <;> fin_cases j <;>
      simp [basisState, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine ⟨?_, ?_⟩
  · rw [← hfactor]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  · fin_cases b <;> simp [Matrix.trace, basisState]

/-- Joint preparation contains two valid, normalized factors. -/
theorem basisJoint_density (a b : Qubit) :
    IsDensityOperator (basisState a ⊗ₖ basisState b) := by
  exact ⟨(basisState_density a).1.kronecker (basisState_density b).1,
    by rw [Matrix.trace_kronecker, (basisState_density a).2,
      (basisState_density b).2, mul_one]⟩

/-- Tracing the first factor of a basis preparation recovers the second label. -/
theorem ptrace1_basis (a b : Qubit) :
    ptrace1 (basisState a ⊗ₖ basisState b) = basisState b := by
  ext i j
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [ptrace1, basisState]

/-- Local reset leaves the environment marginal unchanged, including for correlated inputs. -/
theorem resetSystem_environment (X : Matrix Joint Joint ℂ) :
    ptrace1 (resetSystem X) = ptrace1 X := by
  rw [resetSystem_eq]
  ext i j
  simp [ptrace1, basisState]

/-- The intervention sequence SWAP, local reset, SWAP. -/
noncomputable def retainedRun (X : Matrix Joint Joint ℂ) : Matrix Joint Joint ℂ :=
  swapJoint (resetSystem (swapJoint X))

/-- The full retained-memory experiment is physical on every joint density operator. -/
theorem retainedRun_density {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (retainedRun X) :=
  swapJoint_density (resetSystem_density (swapJoint_density hX))

/-- The basis label is stored outside the reset system and returns in the last SWAP. -/
theorem retainedRun_basis (b : Qubit) :
    retainedRun (basisState b ⊗ₖ basisState 0) = basisState b ⊗ₖ basisState 0 := by
  rw [retainedRun, swapJoint_basis, resetSystem_basis, swapJoint_basis]

/-- Reset the environment through SWAP, then reset the system. Both resets are channels. -/
noncomputable def resetBoth (X : Matrix Joint Joint ℂ) : Matrix Joint Joint ℂ :=
  resetSystem (swapJoint (resetSystem (swapJoint X)))

theorem resetBoth_density {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (resetBoth X) :=
  resetSystem_density (swapJoint_density (resetSystem_density (swapJoint_density hX)))

theorem resetBoth_basis (a b : Qubit) :
    resetBoth (basisState a ⊗ₖ basisState b) = basisState 0 ⊗ₖ basisState 0 := by
  rw [resetBoth, swapJoint_basis, resetSystem_basis, swapJoint_basis, resetSystem_basis]

/-- Control sequence with both factors reset at the intervention. -/
noncomputable def controlRun (X : Matrix Joint Joint ℂ) : Matrix Joint Joint ℂ :=
  swapJoint (resetBoth (swapJoint X))

theorem controlRun_density {X : Matrix Joint Joint ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (controlRun X) :=
  swapJoint_density (resetBoth_density (swapJoint_density hX))

theorem controlRun_basis (b : Qubit) :
    controlRun (basisState b ⊗ₖ basisState 0) = basisState 0 ⊗ₖ basisState 0 := by
  rw [controlRun, swapJoint_basis, resetBoth_basis, swapJoint_basis]

/-- Born probability for the system's computational-basis effect, retaining E. -/
noncomputable def systemProbability (outcome : Qubit) (X : Matrix Joint Joint ℂ) : ℝ :=
  ((basisState outcome ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) * X).trace.re

/-- The two computational-basis effects form a normalized measurement. -/
theorem basisEffects_sum : basisState 0 + basisState 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basisState]

/-- The system's outcome-zero effect is a valid binary POVM on the joint carrier. -/
theorem systemEffect_binary :
    IsBinaryPOVM (basisState 0 ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) := by
  have hsum : (basisState 0 ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) +
      (basisState 1 ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) = 1 := by
    rw [← Matrix.add_kronecker, basisEffects_sum, Matrix.one_kronecker_one]
  refine ⟨(basisState_density 0).1.kronecker Matrix.PosSemidef.one, ?_⟩
  rw [← hsum, add_sub_cancel_left]
  exact (basisState_density 1).1.kronecker Matrix.PosSemidef.one

/-- Computational-basis measurement on a basis preparation is deterministic. -/
theorem systemProbability_basis (outcome a b : Qubit) :
    systemProbability outcome (basisState a ⊗ₖ basisState b) =
      if outcome = a then 1 else 0 := by
  fin_cases outcome <;> fin_cases a <;> fin_cases b <;>
    simp [systemProbability, basisState, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Exact output probabilities of the retained-memory experiment. -/
theorem retainedRun_probability (b outcome : Qubit) :
    systemProbability outcome (retainedRun (basisState b ⊗ₖ basisState 0)) =
      if outcome = b then 1 else 0 := by
  rw [retainedRun_basis, systemProbability_basis]

/-- Resetting both factors eliminates history dependence. -/
theorem controlRun_probability (b outcome : Qubit) :
    systemProbability outcome (controlRun (basisState b ⊗ₖ basisState 0)) =
      if outcome = 0 then 1 else 0 := by
  rw [controlRun_basis, systemProbability_basis]

/-- Partial trace over E, implemented by exchanging factors before `ptrace1`. -/
noncomputable def systemMarginal (X : Matrix Joint Joint ℂ) : Matrix Qubit Qubit ℂ :=
  ptrace1 (swapJoint X)

/-- Both histories have exactly the same controlled-system state at the intervention. -/
theorem postReset_system_same (b : Qubit) :
    systemMarginal (resetSystem (swapJoint (basisState b ⊗ₖ basisState 0))) =
      basisState 0 := by
  rw [swapJoint_basis, resetSystem_basis, systemMarginal, swapJoint_basis, ptrace1_basis]

/-- No common system-only continuation and common Born effect reproduce both histories.
The exclusion even allows arbitrary continuation maps and effects, hence covers
the narrower class of physical channels and valid binary measurements. -/
theorem no_common_system_model :
    ¬ ∃ (continuation : Matrix Qubit Qubit ℂ → Matrix Qubit Qubit ℂ)
      (effect : Matrix Qubit Qubit ℂ), ∀ b : Qubit,
      (effect * continuation
        (systemMarginal (resetSystem (swapJoint (basisState b ⊗ₖ basisState 0))))).trace.re =
      systemProbability 1 (retainedRun (basisState b ⊗ₖ basisState 0)) := by
  rintro ⟨continuation, effect, h⟩
  have h0 := h 0
  have h1 := h 1
  rw [postReset_system_same, retainedRun_probability] at h0 h1
  norm_num at h0 h1
  linarith

end SKEFTHawking.QuantumNetwork.FiniteMemoryProcess
