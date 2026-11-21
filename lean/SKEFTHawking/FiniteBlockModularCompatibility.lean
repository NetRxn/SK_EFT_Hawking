import SKEFTHawking.FiniteBlockConditionalExpectation

/-! Compatibility of the signature-block expectation with finite Gibbs modular flow. -/

noncomputable section
open Matrix
namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation

open DiagonalLindblad QuantumNetwork
open QuantumNetwork.FiniteGibbsClock

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

/-- The finite-dimensional fixed algebra is closed in the matrix norm. -/
theorem fixedAlgebra_isClosed (ell : κ → n → ℝ) :
    IsClosed (fixedAlgebra ell : Set (Matrix n n ℂ)) :=
  (fixedAlgebra ell).toSubmodule.closed_of_finiteDimensional

/-- A block-preserving generator has block-preserving exponentials. -/
theorem expCoeff_mem_fixedAlgebra (ell : κ → n → ℝ) (A : Matrix n n ℂ)
    (hA : A ∈ fixedAlgebra ell) (c : ℂ) :
    expCoeff A c ∈ fixedAlgebra ell :=
  NormedSpace.exp_mem (R := ℂ) (fixedAlgebra_isClosed ell)
    ((fixedAlgebra ell).toSubmodule.smul_mem c hA)

/-- The bimodule law makes expectation commute with conjugation by the
exponentials of any generator in the fixed algebra. -/
theorem expectation_conjugate_of_mem (ell : κ → n → ℝ) (A : Matrix n n ℂ)
    (hA : A ∈ fixedAlgebra ell) (c : ℂ) (X : Matrix n n ℂ) :
    blockExpectation ell (conjugate A c X) = conjugate A c (blockExpectation ell X) := by
  unfold conjugate
  exact expectation_bimodule ell _ X _ (expCoeff_mem_fixedAlgebra ell A hA c)
    (expCoeff_mem_fixedAlgebra ell A hA (-c))

/-- An arbitrary block-preserving Hermitian Hamiltonian gives compatible
faithful Gibbs modular flow on the original matrix algebra. -/
theorem expectation_modular_of_mem [Nonempty n] (ell : κ → n → ℝ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hfixed : H ∈ fixedAlgebra ell) (β s : ℝ) (X : Matrix n n ℂ) :
    blockExpectation ell (modular hH β s X) = modular hH β s (blockExpectation ell X) := by
  rw [modular_conjugate, modular_conjugate]
  exact expectation_conjugate_of_mem ell H hfixed _ X

/-- Diagonal conjugation respects the same matrix-entry support as the
signature-block expectation. -/
theorem expectation_diagonal_conjugate (ell : κ → n → ℝ) (e : n → ℂ)
    (c : ℂ) (X : Matrix n n ℂ) :
    blockExpectation ell (conjugate (diagonal e) c X) =
      conjugate (diagonal e) c (blockExpectation ell X) := by
  ext i j
  rw [expectation_entry, diagonal_conjugate_entry, diagonal_conjugate_entry, expectation_entry]
  split <;> simp_all

/-- The actual faithful Gibbs modular flow commutes with the signature
expectation for a diagonal Hermitian Hamiltonian. -/
theorem expectation_diagonal_modular [Nonempty n] (ell : κ → n → ℝ)
    (e : n → ℂ) (hH : (diagonal e).IsHermitian) (β s : ℝ) (X : Matrix n n ℂ) :
    blockExpectation ell (modular hH β s X) = modular hH β s (blockExpectation ell X) := by
  rw [modular_conjugate, modular_conjugate]
  exact expectation_diagonal_conjugate ell e _ X

/-- Modular flow preserves membership in the fixed algebra in both directions. -/
theorem modular_mem_fixedAlgebra_iff [Nonempty n] (ell : κ → n → ℝ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hfixed : H ∈ fixedAlgebra ell) (β s : ℝ) (X : Matrix n n ℂ) :
    modular hH β s X ∈ fixedAlgebra ell ↔ X ∈ fixedAlgebra ell := by
  change blockExpectation ell (modular hH β s X) = modular hH β s X ↔
    blockExpectation ell X = X
  rw [expectation_modular_of_mem ell hH hfixed]
  constructor
  · intro h
    simpa only [modular_inverse] using congrArg (modular hH β (-s)) h
  · exact congrArg (modular hH β s)

/-- Equal jump signatures can preserve a coherence whose Gibbs modular
phase is nontrivial because the two energies differ. -/
theorem equal_signature_modular_flip :
    E01 ∈ fixedAlgebra (fun (_ : Fin 1) (_ : Fin 2) => 0) ∧
      modular (twoLevel_hermitian 1) 1 Real.pi E01 = -E01 ∧ -E01 ≠ E01 := by
  refine ⟨?_, ?_, ?_⟩
  · change blockExpectation (fun (_ : Fin 1) (_ : Fin 2) => 0) E01 = E01
    ext i j
    rw [expectation_entry, if_pos ((blockClass_eq_iff _ i j).2 (fun _ => rfl))]
  · simpa using twoLevel_sign_flip (Δ := 1) (β := 1) zero_lt_one zero_lt_one
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    norm_num [E01, Matrix.single] at h01

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation
