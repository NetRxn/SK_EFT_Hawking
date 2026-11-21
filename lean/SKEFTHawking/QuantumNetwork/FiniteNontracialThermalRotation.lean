import SKEFTHawking.QuantumNetwork.FiniteGibbsClock

/-! The two-level matrix phase rotation shared by the thermal channel and clock hand. -/
noncomputable section

namespace SKEFTHawking.QuantumNetwork.FiniteNontracialThermalPhase
open Matrix
open scoped Matrix.Norms.L2Operator

abbrev Q := Fin 2
abbrev MatQ := Matrix Q Q ℂ

/-- The phase unitary is a genuine matrix exponential, with explicit diagonal entries. -/
def V (θ : ℝ) : MatQ := FiniteGibbsClock.expCoeff (FiniteGibbsClock.twoLevel 1) (-Complex.I * θ)
theorem V_diagonal (θ : ℝ) :
    V θ = Matrix.diagonal (![1, Complex.exp (-Complex.I * θ)] : Q → ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [V, FiniteGibbsClock.expCoeff, FiniteGibbsClock.twoLevel,
      ← Matrix.diagonal_smul, Matrix.exp_diagonal, ← Complex.exp_eq_exp_ℂ]
theorem V_adjoint (θ : ℝ) : (V θ)ᴴ = V (-θ) := by
  rw [V, FiniteGibbsClock.expCoeff_adjoint (FiniteGibbsClock.twoLevel_hermitian 1)]
  simp [V]
theorem V_mul_neg (θ : ℝ) : V θ * V (-θ) = 1 := by
  convert FiniteGibbsClock.expCoeff_cancel (FiniteGibbsClock.twoLevel 1) (-Complex.I * θ) using 1
  simp [V]
theorem V_unitary (θ : ℝ) : V θ ∈ Matrix.unitaryGroup Q ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change V θ * (V θ)ᴴ = 1
  rw [V_adjoint, V_mul_neg]

/-- Forward state conjugation. Its observable dual uses the negative phase. -/
def C (θ : ℝ) (X : MatQ) : MatQ :=
  FiniteGibbsClock.conjugate (FiniteGibbsClock.twoLevel 1) (-Complex.I * θ) X

theorem C_entry (θ : ℝ) (X : MatQ) (i j : Q) :
    C θ X i j =
      Complex.exp ((-Complex.I * θ) *
        ((![0,1] : Q → ℂ) i - (![0,1] : Q → ℂ) j)) * X i j := by
  exact FiniteGibbsClock.diagonal_conjugate_entry _ _ X i j

theorem C_diagonal (θ : ℝ) (d : Q → ℂ) : C θ (Matrix.diagonal d) = Matrix.diagonal d := by
  ext i j
  by_cases h : i=j
  · subst j; simp [C_entry]
  · simp [C_entry, h]

end SKEFTHawking.QuantumNetwork.FiniteNontracialThermalPhase
