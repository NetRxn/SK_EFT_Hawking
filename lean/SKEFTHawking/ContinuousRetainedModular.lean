import SKEFTHawking.RetainedGibbsModular
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Strong time continuity of the actual finite Gibbs modular unitary and its retained sector. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace
namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation
open QuantumNetwork GibbsObservable DiagonalLindblad FiniteGibbsClock
variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

/-- Matrix conjugation is continuous along any continuous coefficient path. -/
theorem conjugate_continuous_coefficient (H X : Matrix n n ℂ) {c : ℝ → ℂ}
    (hc : Continuous c) : Continuous (fun s => conjugate H (c s) X) := by
  have hcExp : Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) :=
    continuous_iff_continuousAt.mpr fun A => (NormedSpace.exp_analytic (𝕂 := ℂ) A).continuousAt
  have hexp : Continuous (expCoeff H) := hcExp.comp (continuous_id.smul continuous_const)
  exact ((hexp.comp hc).mul continuous_const).mul (hexp.comp hc.neg)

variable [Nonempty n]

/-- The original finite modular flow is continuous in real time at each observable. -/
theorem modular_time_continuous {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (β : ℝ) (X : Matrix n n ℂ) : Continuous (fun s => modular hH β s X) := by
  simp only [modular_conjugate]
  exact conjugate_continuous_coefficient H X ((continuous_const.mul Complex.continuous_ofReal).mul
    continuous_const)

/-- Strong time continuity on the full faithful reconstructed Gibbs space. -/
theorem quotientModular_time_continuous {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (β : ℝ) (z : GibbsSpace H hH β) : Continuous (fun s => Clock.quotientModular hH β s z) := by
  obtain ⟨X, rfl⟩ := observable_surjective (gibbs_posDef hH β).posSemidef z
  simp only [Clock.quotientModular_observable]
  exact (observableLinear (gibbs_posDef hH β).posSemidef).continuous_of_finiteDimensional.comp
    (modular_time_continuous hH β X)

/-- The inherited modular group is strongly continuous on the retained sector. -/
theorem retainedModular_time_continuous (ell : κ → n → ℝ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hfixed : H ∈ fixedAlgebra ell) (β : ℝ)
    (z : retainedGibbsSpace ell hH hfixed β) :
    Continuous (fun s => retainedModular ell hH hfixed β s z) :=
  (quotientModular_time_continuous hH β z.1).subtype_mk _

private def threeLevelEnergies : Fin 3 → ℂ := ![0, 1, 0]

private def threeLevelDiagonal : Matrix (Fin 3) (Fin 3) ℂ := diagonal threeLevelEnergies

private theorem threeLevelDiagonal_hermitian : threeLevelDiagonal.IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;> simp [threeLevelDiagonal, threeLevelEnergies]

private theorem threeLevelDiagonal_fixed : threeLevelDiagonal ∈ fixedAlgebra duplicateJumps := by
  change blockExpectation duplicateJumps threeLevelDiagonal = threeLevelDiagonal
  ext i j
  rw [expectation_entry]
  by_cases hij : i = j
  · subst j
    simp
  · simp [threeLevelDiagonal, diagonal_apply_ne _ hij]

private def withinBlock : Matrix (Fin 3) (Fin 3) ℂ := Matrix.single 0 1 1
private def betweenBlocks : Matrix (Fin 3) (Fin 3) ℂ := Matrix.single 0 2 1

private theorem withinBlock_modular_flip :
    modular threeLevelDiagonal_hermitian 1 Real.pi withinBlock = -withinBlock := by
  rw [modular_conjugate]
  ext i j
  simp only [threeLevelDiagonal, diagonal_conjugate_entry]
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 1
    · subst j
      have hphase : ((Complex.I * (Real.pi : ℂ)) * (-(1 : ℝ) : ℂ)) *
          (threeLevelEnergies 0 - threeLevelEnergies 1) = (Real.pi : ℂ) * Complex.I := by
        norm_num [threeLevelEnergies]
        ring
      rw [hphase, Complex.exp_pi_mul_I]
      simp [withinBlock, Matrix.single]
    · simp [withinBlock, Matrix.single, Ne.symm hj]
  · simp [withinBlock, Matrix.single, Ne.symm hi]

/-- Equal signatures on two of three levels give a proper retained sector with a nontrivial
modular motion. The inter-block coherence witnesses properness in the faithful space. -/
theorem proper_retained_modular_nontrivial :
    let S := retainedGibbsSpace duplicateJumps threeLevelDiagonal_hermitian threeLevelDiagonal_fixed 1
    S ≠ ⊤ ∧ ∃ z : S,
      retainedModular duplicateJumps threeLevelDiagonal_hermitian threeLevelDiagonal_fixed 1 Real.pi z ≠ z := by
  dsimp only
  let hρ := gibbs_posDef threeLevelDiagonal_hermitian 1
  constructor
  · intro htop
    have hm : observable hρ.posSemidef betweenBlocks ∈
        retainedGibbsSpace duplicateJumps threeLevelDiagonal_hermitian threeLevelDiagonal_fixed 1 := by
      rw [htop]
      trivial
    have hY := (observable_mem_retainedGibbsSpace duplicateJumps threeLevelDiagonal_hermitian
      threeLevelDiagonal_fixed 1 betweenBlocks).mp hm
    have hneq : blockClass duplicateJumps 0 ≠ blockClass duplicateJumps 2 := by
      intro he
      have h := (blockClass_eq_iff duplicateJumps 0 2).mp he 0
      norm_num [duplicateJumps, show (0 : Fin 3) ≠ 2 by decide] at h
    have hz := fixed_entry_zero duplicateJumps betweenBlocks hY 0 2 hneq
    norm_num [betweenBlocks, Matrix.single] at hz
  · have hX : withinBlock ∈ fixedAlgebra duplicateJumps :=
      (blockKraus_stationary_iff _ _).mp duplicate_channel_fixed
    let z : retainedGibbsSpace duplicateJumps threeLevelDiagonal_hermitian threeLevelDiagonal_fixed 1 :=
      ⟨observable hρ.posSemidef withinBlock, (observable_mem_retainedGibbsSpace duplicateJumps
        threeLevelDiagonal_hermitian threeLevelDiagonal_fixed 1 withinBlock).mpr hX⟩
    refine ⟨z, ?_⟩
    intro he
    have h := congrArg Subtype.val he
    change Clock.quotientModular threeLevelDiagonal_hermitian 1 Real.pi
      (observable hρ.posSemidef withinBlock) = observable hρ.posSemidef withinBlock at h
    rw [Clock.quotientModular_observable, withinBlock_modular_flip] at h
    have hM := observable_injective hρ h
    have h01 := congrArg (fun X : Matrix (Fin 3) (Fin 3) ℂ => X 0 1) hM
    norm_num [withinBlock, Matrix.single] at h01

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation
