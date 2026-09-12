import SKEFTHawking.FiniteDiagonalLindblad

/-! The asymptotic signature-block projection is a stationary Kraus conditional
expectation, with its actual observable algebra and weighted orthogonal descent. -/
noncomputable section
open Matrix
open scoped ComplexOrder InnerProductSpace
namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation
open QuantumNetwork GibbsObservable DiagonalLindblad
variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

/-- Equal jump signatures define the physical blocks. -/
def signatureSetoid (ell : κ → n → ℝ) : Setoid n := Setoid.ker (fun i r => ell r i)

abbrev Blocks (ell : κ → n → ℝ) := Quotient (signatureSetoid ell)

instance blocksFintype (ell : κ → n → ℝ) : Fintype (Blocks ell) := Fintype.ofFinite _
instance blocksDecidableEq (ell : κ → n → ℝ) : DecidableEq (Blocks ell) := Classical.decEq _

/-- The class of a basis vector indexes its orthogonal block projection. -/
def blockClass (ell : κ → n → ℝ) (i : n) : Blocks ell := Quotient.mk _ i

omit [Fintype n] [DecidableEq n] [Fintype κ] in
theorem blockClass_eq_iff (ell : κ → n → ℝ) (i j : n) :
    blockClass ell i = blockClass ell j ↔ ∀ r, ell r i = ell r j := by
  change Quotient.mk _ i = Quotient.mk _ j ↔ _
  rw [Quotient.eq]
  exact funext_iff

omit [Fintype n] [DecidableEq n] in
theorem blockClass_eq_rate (ell : κ → n → ℝ) (i j : n) :
    blockClass ell i = blockClass ell j ↔ rate ell i j = 0 := by
  rw [blockClass_eq_iff, rate_eq_zero_iff]

/-- Diagonal orthogonal projection onto one entire signature block. -/
def blockProjector (ell : κ → n → ℝ) (b : Blocks ell) : Matrix n n ℂ :=
  diagonal (fun i => if blockClass ell i = b then 1 else 0)

omit [Fintype n] [Fintype κ] in
theorem blockProjector_star (ell : κ → n → ℝ) (b : Blocks ell) :
    (blockProjector ell b)ᴴ = blockProjector ell b := by
  ext i j
  by_cases h : i = j <;> simp [blockProjector, Matrix.conjTranspose_apply, h, eq_comm]

omit [Fintype κ] in
theorem blockProjector_mul (ell : κ → n → ℝ) (b c : Blocks ell) :
    blockProjector ell b * blockProjector ell c = if b = c then blockProjector ell b else 0 := by
  ext i j
  simp only [blockProjector, Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j <;> by_cases hb : blockClass ell i = b <;>
    by_cases hc : blockClass ell i = c <;> by_cases hbc : b = c <;>
    simp_all

omit [Fintype κ] in
theorem blockProjector_sum (ell : κ → n → ℝ) : ∑ b : Blocks ell, blockProjector ell b = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [blockProjector, Matrix.sum_apply]
  · simp [blockProjector, Matrix.sum_apply, hij]

/-- Reindex the physical block projectors for the existing finite Kraus API. -/
def blockKraus (ell : κ → n → ℝ) : Fin (Fintype.card (Blocks ell)) → Matrix n n ℂ :=
  fun i => blockProjector ell ((Fintype.equivFin (Blocks ell)).symm i)

omit [Fintype κ] in
theorem blockKraus_channel (ell : κ → n → ℝ) : IsKrausChannel (blockKraus ell) := by
  unfold IsKrausChannel blockKraus
  rw [(Fintype.equivFin (Blocks ell)).symm.sum_comp
    (fun b => (blockProjector ell b)ᴴ * blockProjector ell b)]
  simp only [blockProjector_star, blockProjector_mul, if_true]
  exact blockProjector_sum ell

omit [Fintype κ] in
theorem blockProjector_sandwich (ell : κ → n → ℝ) (b : Blocks ell)
    (X : Matrix n n ℂ) (i j : n) :
    (blockProjector ell b * X * blockProjector ell b) i j =
      if blockClass ell i = b ∧ blockClass ell j = b then X i j else 0 := by
  by_cases hi : blockClass ell i = b <;> by_cases hj : blockClass ell j = b <;>
    simp [blockProjector, Matrix.mul_apply, Matrix.diagonal_apply, hi, hj]

/-- The Kraus sum is the existing asymptotic block expectation. -/
theorem blockKraus_action (ell : κ → n → ℝ) (X : Matrix n n ℂ) :
    krausMap (blockKraus ell) X = blockExpectation ell X := by
  unfold krausMap blockKraus
  rw [(Fintype.equivFin (Blocks ell)).symm.sum_comp
    (fun b => blockProjector ell b * X * (blockProjector ell b)ᴴ)]
  ext i j
  simp only [blockProjector_star, Matrix.sum_apply, blockProjector_sandwich, ite_and]
  simp [blockExpectation]
  simp only [eq_comm (a := blockClass ell j) (b := blockClass ell i), blockClass_eq_rate]

/-- The same Hermitian Kraus operators implement the observable action. -/
theorem blockKraus_heisenberg (ell : κ → n → ℝ) (X : Matrix n n ℂ) :
    Channel.heisenberg (blockKraus ell) X = blockExpectation ell X := by
  rw [← blockKraus_action]
  simp only [Channel.heisenberg, krausMap, blockKraus, blockProjector_star]

omit [Fintype n] [DecidableEq n] in
theorem expectation_entry (ell : κ → n → ℝ) (X : Matrix n n ℂ) (i j : n) :
    blockExpectation ell X i j = if blockClass ell i = blockClass ell j then X i j else 0 := by
  simp only [blockClass_eq_rate]
  rfl

omit [Fintype n] in
theorem expectation_one (ell : κ → n → ℝ) : blockExpectation ell 1 = 1 := by
  ext i j
  by_cases h : i = j <;> simp [blockExpectation, h, Matrix.one_apply]

omit [Fintype n] [DecidableEq n] in
theorem expectation_add (ell : κ → n → ℝ) (X Y : Matrix n n ℂ) :
    blockExpectation ell (X+Y) = blockExpectation ell X + blockExpectation ell Y := by
  ext i j
  by_cases h : rate ell i j = 0 <;> simp [blockExpectation, h]

omit [Fintype n] [DecidableEq n] in
theorem expectation_smul (ell : κ → n → ℝ) (c : ℂ) (X : Matrix n n ℂ) :
    blockExpectation ell (c • X) = c • blockExpectation ell X := by
  ext i j
  by_cases h : rate ell i j = 0 <;> simp [blockExpectation, h]

omit [Fintype n] [DecidableEq n] in
theorem expectation_star (ell : κ → n → ℝ) (X : Matrix n n ℂ) :
    blockExpectation ell Xᴴ = (blockExpectation ell X)ᴴ := by
  ext i j
  simp only [expectation_entry, Matrix.conjTranspose_apply]
  by_cases h : blockClass ell i = blockClass ell j
  · simp only [if_pos h, if_pos h.symm]
  · simp only [if_neg h, if_neg (Ne.symm h), star_zero]

omit [Fintype n] [DecidableEq n] in
theorem fixed_entry_zero (ell : κ → n → ℝ) (A : Matrix n n ℂ)
    (hA : blockExpectation ell A = A) (i j : n) (hij : blockClass ell i ≠ blockClass ell j) :
    A i j = 0 := by
  have h := congrFun (congrFun hA i) j
  simpa [expectation_entry, hij] using h.symm

omit [DecidableEq n] in
/-- The left module law requires the outer factor to belong to the fixed algebra. -/
theorem expectation_mul_left (ell : κ → n → ℝ) (A X : Matrix n n ℂ)
    (hA : blockExpectation ell A = A) :
    blockExpectation ell (A*X) = A * blockExpectation ell X := by
  ext i j
  simp only [expectation_entry, Matrix.mul_apply]
  by_cases hij : blockClass ell i = blockClass ell j
  · simp only [hij, if_true]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : blockClass ell k = blockClass ell j
    · simp [hkj]
    · have hik : blockClass ell i ≠ blockClass ell k := by
        intro he; exact hkj (he.symm.trans hij)
      simp [hkj, fixed_entry_zero ell A hA i k hik]
  · simp only [hij, if_false]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hkj : blockClass ell k = blockClass ell j
    · have hik : blockClass ell i ≠ blockClass ell k := by
        intro he; exact hij (he.trans hkj)
      simp [hkj, fixed_entry_zero ell A hA i k hik]
    · simp [hkj]

omit [DecidableEq n] in
/-- The right module law follows through the actual adjoint-preserving expectation. -/
theorem expectation_mul_right (ell : κ → n → ℝ) (X B : Matrix n n ℂ)
    (hB : blockExpectation ell B = B) :
    blockExpectation ell (X*B) = blockExpectation ell X * B := by
  have h := expectation_mul_left ell Bᴴ Xᴴ (by rw [expectation_star, hB])
  have hc := congrArg Matrix.conjTranspose h
  simpa only [← Matrix.conjTranspose_mul, expectation_star, Matrix.conjTranspose_conjTranspose] using hc

omit [DecidableEq n] in
/-- Conditional expectation bimodule law, with both outer factors fixed. -/
theorem expectation_bimodule (ell : κ → n → ℝ) (A X B : Matrix n n ℂ)
    (hA : blockExpectation ell A = A) (hB : blockExpectation ell B = B) :
    blockExpectation ell (A*X*B) = A * blockExpectation ell X * B := by
  rw [expectation_mul_right ell _ B hB, expectation_mul_left ell A X hA]

/-- The full fixed range is a unital complex algebra. -/
def fixedAlgebra (ell : κ → n → ℝ) : Subalgebra ℂ (Matrix n n ℂ) where
  carrier := {X | blockExpectation ell X = X}
  zero_mem' := by ext i j; simp [blockExpectation]
  one_mem' := expectation_one ell
  add_mem' := by
    intro X Y hX hY
    change blockExpectation ell (X+Y) = X+Y
    rw [expectation_add, hX, hY]
  mul_mem' := by
    intro X Y hX hY
    change blockExpectation ell (X*Y) = X*Y
    rw [expectation_mul_left ell X Y hX, hY]
  algebraMap_mem' c := by
    change blockExpectation ell ((algebraMap ℂ (Matrix n n ℂ)) c) = _
    rw [Algebra.algebraMap_eq_smul_one]
    rw [expectation_smul, expectation_one]

theorem fixedAlgebra_star (ell : κ → n → ℝ) (X : Matrix n n ℂ) (hX : X ∈ fixedAlgebra ell) :
    Xᴴ ∈ fixedAlgebra ell := by
  change blockExpectation ell Xᴴ = Xᴴ
  rw [expectation_star]
  exact congrArg Matrix.conjTranspose hX

/-- The range statement is about the same expectation used by the dynamics. -/
theorem expectation_range (ell : κ → n → ℝ) (X : Matrix n n ℂ) :
    (∃ Y, blockExpectation ell Y = X) ↔ X ∈ fixedAlgebra ell := by
  constructor
  · rintro ⟨Y, rfl⟩
    exact blockExpectation_idempotent ell Y
  · intro h
    exact ⟨X, h⟩

theorem blockKraus_stationary (ell : κ → n → ℝ) (w : n → ℝ) :
    krausMap (blockKraus ell) (density w) = density w := by
  rw [blockKraus_action]
  ext i j
  by_cases h : i = j <;> simp [blockExpectation, density, h]

theorem expectation_weighted_symmetry (ell : κ → n → ℝ) (w : n → ℝ)
    (X Y : Matrix n n ℂ) :
    (Y * density w * (blockExpectation ell X)ᴴ).trace =
      (blockExpectation ell Y * density w * Xᴴ).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply, density, expectation_entry,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : blockClass ell i = blockClass ell j <;> simp [h]

/-- Concrete detailed balance for the normalized block Kraus family. -/
theorem blockKraus_detailedBalance (ell : κ → n → ℝ) (w : n → ℝ) :
    Channel.DetailedBalance (density w) (blockKraus ell) := by
  intro X Y
  rw [blockKraus_heisenberg, blockKraus_heisenberg]
  exact expectation_weighted_symmetry ell w X Y

/-- The accepted asymptotic projection equals the existing stationary-channel descent. -/
theorem quotientChannel_eq_projection (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 < w i) :
    Channel.quotientChannel (density_posDef w hw).posSemidef (blockKraus ell)
      (blockKraus_channel ell) (blockKraus_stationary ell w) = projection w hw ell := by
  ext z
  obtain ⟨X, rfl⟩ := observable_surjective (density_posDef w hw).posSemidef z
  rw [Channel.quotientChannel_observable, projection_observable, blockKraus_heisenberg]

/-- Weighted symmetry is inherited from the concrete stationary Kraus realization. -/
theorem projection_symmetric (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 < w i) :
    (projection w hw ell).IsSymmetric := by
  rw [← quotientChannel_eq_projection ell w hw]
  exact Channel.quotientChannel_symmetric _ _ _ _ (blockKraus_detailedBalance ell w)

theorem projection_selfAdjoint (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 < w i) :
    IsSelfAdjoint (projection w hw ell) := (projection_symmetric ell w hw).isSelfAdjoint

/-- The projection quadratic form is the squared norm of its retained component. -/
theorem projection_inner (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 < w i)
    (z : WeightedSpace w hw) :
    ⟪projection w hw ell z, z⟫_ℂ = ⟪projection w hw ell z, projection w hw ell z⟫_ℂ := by
  have h := projection_symmetric ell w hw (projection w hw ell z) z
  change ⟪projection w hw ell (projection w hw ell z), z⟫_ℂ =
    ⟪projection w hw ell z, projection w hw ell z⟫_ℂ at h
  rw [projection_idempotent] at h
  exact h

theorem projection_positive (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 < w i) :
    (projection w hw ell).IsPositive := by
  refine ⟨projection_symmetric ell w hw, ?_⟩
  intro z
  change 0 ≤ (⟪projection w hw ell z, z⟫_ℂ).re
  rw [projection_inner]
  exact inner_self_nonneg (𝕜 := ℂ) (x := projection w hw ell z)

/-- Retained observables and removed error are orthogonal in the actual weighted quotient. -/
theorem projection_error_orthogonal (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 < w i)
    (z : WeightedSpace w hw) :
    ⟪projection w hw ell z, z - projection w hw ell z⟫_ℂ = 0 := by
  rw [inner_sub_right, projection_inner, sub_self]

/-- Exact orthogonal error accounting, strengthening the previous contraction bound. -/
theorem projection_pythagoras (ell : κ → n → ℝ) (w : n → ℝ) (hw : ∀ i, 0 < w i)
    (z : WeightedSpace w hw) :
    ‖z‖^2 = ‖projection w hw ell z‖^2 + ‖z - projection w hw ell z‖^2 := by
  have h := norm_add_sq (𝕜 := ℂ) (projection w hw ell z) (z - projection w hw ell z)
  rw [projection_error_orthogonal] at h
  simpa using h

/-- The actual Kraus channel retains the duplicate-signature off-diagonal observable. -/
theorem duplicate_channel_fixed :
    krausMap (blockKraus duplicateJumps) (Matrix.single 0 1 (1 : ℂ)) = Matrix.single 0 1 1 := by
  rw [blockKraus_action]
  exact (propagator_fixed_iff duplicateJumps 1 (by norm_num) _).mp (duplicate_fixed 1)

/-- The faithful quotient retains the same duplicate-signature observable. -/
theorem duplicate_projection_fixed :
    projection threeWeights threeWeights_pos duplicateJumps
      (observable (density_posDef threeWeights threeWeights_pos).posSemidef (Matrix.single 0 1 1)) =
      observable (density_posDef threeWeights threeWeights_pos).posSemidef (Matrix.single 0 1 1) := by
  rw [← quotientChannel_eq_projection, Channel.quotientChannel_observable,
    blockKraus_heisenberg, ← blockKraus_action, duplicate_channel_fixed]

/-- Degenerate signatures retain a strictly nonzero reconstructed off-diagonal component. -/
theorem duplicate_projection_norm_pos :
    0 < ‖projection threeWeights threeWeights_pos duplicateJumps
      (observable (density_posDef threeWeights threeWeights_pos).posSemidef (Matrix.single 0 1 1))‖ := by
  rw [duplicate_projection_fixed]
  exact three_coherence_norm_pos

/-- Unrestricted multiplicativity fails; the fixed-factor conditions in the bimodule law matter. -/
theorem expectation_not_multiplicative :
    blockExpectation duplicateJumps (Matrix.single 0 2 1 * Matrix.single 2 0 1) ≠
      blockExpectation duplicateJumps (Matrix.single 0 2 1) *
        blockExpectation duplicateJumps (Matrix.single 2 0 1) := by
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [blockExpectation, rate, duplicateJumps, Matrix.mul_apply,
    Fin.sum_univ_one, Fin.sum_univ_three,
    show (0 : Fin 3) ≠ 2 from by decide, show (1 : Fin 3) ≠ 2 from by decide] at he

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation
