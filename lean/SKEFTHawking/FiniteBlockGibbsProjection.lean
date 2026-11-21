import SKEFTHawking.FiniteBlockModularCompatibility

/-! Orthogonal projection for Gibbs weights supported on the signature blocks. -/

noncomputable section
open Matrix
open scoped ComplexOrder InnerProductSpace
namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation
open QuantumNetwork GibbsObservable DiagonalLindblad FiniteGibbsClock
variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

omit [DecidableEq n] in
/-- Signature pinching preserves the matrix trace. -/
theorem expectation_trace (ell : κ → n → ℝ) (X : Matrix n n ℂ) :
    (blockExpectation ell X).trace = X.trace := by
  simp [Matrix.trace, expectation_entry]

/-- The stationary matrices of the block Kraus channel are precisely its fixed algebra. -/
theorem blockKraus_stationary_iff (ell : κ → n → ℝ) (ρ : Matrix n n ℂ) :
    krausMap (blockKraus ell) ρ = ρ ↔ ρ ∈ fixedAlgebra ell := by
  rw [blockKraus_action]
  rfl

omit [DecidableEq n] in
/-- Detailed balance follows from the bimodule law for any fixed weight. -/
theorem expectation_weighted_symmetry_of_mem (ell : κ → n → ℝ) (ρ : Matrix n n ℂ)
    (hρ : blockExpectation ell ρ = ρ) (X Y : Matrix n n ℂ) :
    (Y * ρ * (blockExpectation ell X)ᴴ).trace =
      (blockExpectation ell Y * ρ * Xᴴ).trace := by
  have hX : blockExpectation ell (blockExpectation ell X)ᴴ = (blockExpectation ell X)ᴴ := by
    rw [expectation_star, blockExpectation_idempotent]
  have hY : blockExpectation ell (blockExpectation ell Y * ρ) = blockExpectation ell Y * ρ := by
    rw [expectation_mul_right ell _ _ hρ, blockExpectation_idempotent]
  calc
    _ = (blockExpectation ell (Y * ρ * (blockExpectation ell X)ᴴ)).trace :=
      (expectation_trace ell _).symm
    _ = (blockExpectation ell Y * ρ * (blockExpectation ell X)ᴴ).trace := by
      rw [expectation_mul_right ell _ _ hX, expectation_mul_right ell _ _ hρ]
    _ = (blockExpectation ell (blockExpectation ell Y * ρ * Xᴴ)).trace := by
      rw [expectation_mul_left ell _ _ hY, expectation_star]
    _ = _ := expectation_trace ell _

theorem blockKraus_detailedBalance_of_mem (ell : κ → n → ℝ) (ρ : Matrix n n ℂ)
    (hρ : ρ ∈ fixedAlgebra ell) : Channel.DetailedBalance ρ (blockKraus ell) := by
  intro X Y
  rw [blockKraus_heisenberg, blockKraus_heisenberg]
  exact expectation_weighted_symmetry_of_mem ell ρ hρ X Y

/-- The normalized Gibbs state of a block-preserving Hamiltonian is a fixed weight. -/
theorem gibbs_mem_fixedAlgebra (ell : κ → n → ℝ) {H : Matrix n n ℂ}
    (hfixed : H ∈ fixedAlgebra ell) (β : ℝ) : gibbs H β ∈ fixedAlgebra ell := by
  unfold gibbs boltzmann
  have real_smul (r : ℝ) (A : Matrix n n ℂ) : r • A = (r : ℂ) • A := by
    ext i j
    simp [Complex.real_smul]
  rw [real_smul, real_smul]
  exact (fixedAlgebra ell).toSubmodule.smul_mem _ (expCoeff_mem_fixedAlgebra ell H hfixed _)

/-- Descend the existing block Kraus channel to the quotient at a fixed positive weight. -/
def fixedWeightProjection (ell : κ → n → ℝ) {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hfixed : ρ ∈ fixedAlgebra ell) :=
  Channel.quotientChannel hρ (blockKraus ell) (blockKraus_channel ell)
    ((blockKraus_stationary_iff ell ρ).2 hfixed)

theorem fixedWeightProjection_observable (ell : κ → n → ℝ) {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hfixed : ρ ∈ fixedAlgebra ell) (X : Matrix n n ℂ) :
    fixedWeightProjection ell hρ hfixed (observable hρ X) = observable hρ (blockExpectation ell X) := by
  rw [fixedWeightProjection, Channel.quotientChannel_observable, blockKraus_heisenberg]

theorem fixedWeightProjection_idempotent (ell : κ → n → ℝ) {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hfixed : ρ ∈ fixedAlgebra ell)
    (z : Space (gram ρ) (gram_posSemidef hρ)) :
    fixedWeightProjection ell hρ hfixed (fixedWeightProjection ell hρ hfixed z) =
      fixedWeightProjection ell hρ hfixed z := by
  obtain ⟨X, rfl⟩ := observable_surjective hρ z
  rw [fixedWeightProjection_observable, fixedWeightProjection_observable, blockExpectation_idempotent]

theorem fixedWeightProjection_symmetric (ell : κ → n → ℝ) {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hfixed : ρ ∈ fixedAlgebra ell) :
    (fixedWeightProjection ell hρ hfixed).IsSymmetric :=
  Channel.quotientChannel_symmetric _ _ _ _ (blockKraus_detailedBalance_of_mem ell ρ hfixed)

theorem fixedWeightProjection_positive (ell : κ → n → ℝ) {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hfixed : ρ ∈ fixedAlgebra ell) :
    (fixedWeightProjection ell hρ hfixed).IsPositive := by
  have hsymm := fixedWeightProjection_symmetric ell hρ hfixed
  refine ⟨hsymm, ?_⟩
  intro z
  let P := fixedWeightProjection ell hρ hfixed
  have h := hsymm (P z) z
  change ⟪P (P z), z⟫_ℂ = ⟪P z, P z⟫_ℂ at h
  have hIdem : P (P z) = P z := fixedWeightProjection_idempotent ell hρ hfixed z
  rw [hIdem] at h
  change 0 ≤ (⟪P z, z⟫_ℂ).re
  rw [h]
  exact inner_self_nonneg (𝕜 := ℂ) (x := P z)

/-- The block channel acts as an orthogonal projection in the actual faithful Gibbs space. -/
theorem gibbsBlockProjection [Nonempty n] (ell : κ → n → ℝ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hfixed : H ∈ fixedAlgebra ell) (β : ℝ) :
    let P := fixedWeightProjection ell (gibbs_posDef hH β).posSemidef
      (gibbs_mem_fixedAlgebra ell hfixed β)
    P.IsPositive ∧ ∀ z, P (P z) = P z :=
  ⟨fixedWeightProjection_positive _ _ _, fixedWeightProjection_idempotent _ _ _⟩

/-- The actual Gibbs-space modular unitary commutes with its orthogonal block projection. -/
theorem gibbsBlockProjection_modular [Nonempty n] (ell : κ → n → ℝ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hfixed : H ∈ fixedAlgebra ell) (β s : ℝ)
    (z : Space (gram (gibbs H β)) (gram_posSemidef (gibbs_posDef hH β).posSemidef)) :
    let P := fixedWeightProjection ell (gibbs_posDef hH β).posSemidef
      (gibbs_mem_fixedAlgebra ell hfixed β)
    P (Clock.quotientModular hH β s z) = Clock.quotientModular hH β s (P z) := by
  dsimp only
  obtain ⟨X, rfl⟩ := observable_surjective (gibbs_posDef hH β).posSemidef z
  rw [Clock.quotientModular_observable, fixedWeightProjection_observable,
    fixedWeightProjection_observable, Clock.quotientModular_observable,
    expectation_modular_of_mem ell hH hfixed]

private def mixingHamiltonian : Matrix (Fin 3) (Fin 3) ℂ :=
  let X := Matrix.single 0 1 (1 : ℂ)
  X + Xᴴ

private theorem mixingHamiltonian_hermitian : mixingHamiltonian.IsHermitian := by
  change (Matrix.single 0 1 (1 : ℂ) + (Matrix.single 0 1 (1 : ℂ))ᴴ)ᴴ = _
  rw [conjTranspose_add, conjTranspose_conjTranspose]
  exact add_comm _ _

private theorem mixingHamiltonian_mem : mixingHamiltonian ∈ fixedAlgebra duplicateJumps := by
  have hX : (Matrix.single 0 1 (1 : ℂ) : Matrix (Fin 3) (Fin 3) ℂ) ∈
      fixedAlgebra duplicateJumps := (blockKraus_stationary_iff _ _).mp duplicate_channel_fixed
  exact (fixedAlgebra duplicateJumps).add_mem hX (fixedAlgebra_star _ _ hX)

/-- On the Gibbs space of a Hamiltonian which mixes two levels inside one signature block,
the projection retains their coherence and kills a coherence joining distinct signatures. -/
theorem mixingHamiltonian_projection (β : ℝ) :
    let h := gibbs_posDef mixingHamiltonian_hermitian β
    let P := fixedWeightProjection duplicateJumps h.posSemidef
      (gibbs_mem_fixedAlgebra _ mixingHamiltonian_mem β)
    let retained := observable h.posSemidef (Matrix.single 0 1 (1 : ℂ))
    let removed := observable h.posSemidef (Matrix.single 0 2 (1 : ℂ))
    P retained = retained ∧ retained ≠ 0 ∧ P removed = 0 ∧ removed ≠ 0 := by
  dsimp only
  rw [fixedWeightProjection_observable, fixedWeightProjection_observable]
  have h01 : blockExpectation duplicateJumps (Matrix.single 0 1 (1 : ℂ)) =
      Matrix.single 0 1 1 := (blockKraus_stationary_iff _ _).mp duplicate_channel_fixed
  have h02 : blockExpectation duplicateJumps (Matrix.single 0 2 (1 : ℂ)) = 0 := by
    ext i j
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 2
      · subst j
        have hr : rate duplicateJumps 0 2 ≠ 0 := by
          norm_num [rate, duplicateJumps, Fin.sum_univ_one,
            show (0 : Fin 3) ≠ 2 from by decide]
        simp [blockExpectation, hr]
      · simp [blockExpectation, Matrix.single, Ne.symm hj]
    · simp [blockExpectation, Matrix.single, Ne.symm hi]
  rw [h01, h02]
  refine ⟨rfl, ?_, map_zero (observableLinear (gibbs_posDef mixingHamiltonian_hermitian β).posSemidef), ?_⟩
  · rw [ne_eq, observable_eq_zero_iff (gibbs_posDef mixingHamiltonian_hermitian β)]
    intro he
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 1) he
    norm_num [Matrix.single] at h
  · rw [ne_eq, observable_eq_zero_iff (gibbs_posDef mixingHamiltonian_hermitian β)]
    intro he
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 2) he
    norm_num [Matrix.single] at h

/-- At inverse temperature one, the Gibbs weight for the mixing example is genuinely nondiagonal. -/
theorem mixingGibbs_nondiagonal : ¬ ∃ d : Fin 3 → ℂ, gibbs mixingHamiltonian 1 = diagonal d := by
  rintro ⟨d, hd⟩
  let Q : Matrix (Fin 3) (Fin 3) ℂ := diagonal (fun i => if i = 0 then 1 else 0)
  have hc : Commute (gibbs mixingHamiltonian 1) Q := by
    rw [hd]
    dsimp [Q, Commute, SemiconjBy]
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  let hG := (gibbs_posDef mixingHamiltonian_hermitian (1 : ℝ)).posSemidef.isHermitian
  have hl : Commute (matrixLog hG) Q := by
    rw [matrixLog, ← Matrix.IsHermitian.cfc_eq]
    exact hc.cfc_real Real.log
  rw [matrixLog_gibbs mixingHamiltonian_hermitian] at hl
  have hz := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 1) hl.eq
  norm_num [Q, mul_diagonal, diagonal_mul, mixingHamiltonian, Matrix.single,
    Matrix.conjTranspose_apply, Matrix.one_apply] at hz

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation
