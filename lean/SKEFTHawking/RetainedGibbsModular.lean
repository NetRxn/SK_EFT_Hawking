import SKEFTHawking.FiniteBlockGibbsProjection

/-! The reconstructed subspace retained by the block projection carries the same modular group. -/
noncomputable section
open Matrix
open scoped ComplexOrder InnerProductSpace
namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation
open QuantumNetwork GibbsObservable DiagonalLindblad FiniteGibbsClock
variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [Nonempty n]

abbrev GibbsSpace (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :=
  Space (gram (gibbs H β)) (gram_posSemidef (gibbs_posDef hH β).posSemidef)

variable (ell : κ → n → ℝ) {H : Matrix n n ℂ} (hH : H.IsHermitian)
  (hfixed : H ∈ fixedAlgebra ell) (β : ℝ)

/-- The existing block projection specialized to the reconstructed faithful Gibbs space. -/
abbrev gibbsProjection : GibbsSpace H hH β →L[ℂ] GibbsSpace H hH β :=
  fixedWeightProjection ell (gibbs_posDef hH β).posSemidef
    (gibbs_mem_fixedAlgebra ell hfixed β)

/-- The retained closed sector is the range of the actual faithful Gibbs projection. -/
def retainedGibbsSpace : Submodule ℂ (GibbsSpace H hH β) :=
  LinearMap.range (gibbsProjection ell hH hfixed β).toLinearMap

theorem mem_retainedGibbsSpace_iff (z : GibbsSpace H hH β) :
    z ∈ retainedGibbsSpace ell hH hfixed β ↔ gibbsProjection ell hH hfixed β z = z := by
  constructor
  · rintro ⟨x, rfl⟩
    exact fixedWeightProjection_idempotent _ _ _ x
  · intro hz
    exact ⟨z, hz⟩

/-- Faithfulness identifies the retained space with the original block observables. -/
theorem observable_mem_retainedGibbsSpace (X : Matrix n n ℂ) :
    observable (gibbs_posDef hH β).posSemidef X ∈ retainedGibbsSpace ell hH hfixed β ↔
      X ∈ fixedAlgebra ell := by
  rw [mem_retainedGibbsSpace_iff]
  change fixedWeightProjection ell _ _ (observable (gibbs_posDef hH β).posSemidef X) =
    observable (gibbs_posDef hH β).posSemidef X ↔ blockExpectation ell X = X
  rw [fixedWeightProjection_observable]
  exact (observable_injective (gibbs_posDef hH β)).eq_iff

theorem retainedGibbsSpace_closed :
    IsClosed (retainedGibbsSpace ell hH hfixed β : Set (GibbsSpace H hH β)) := by
  have he : (retainedGibbsSpace ell hH hfixed β : Set (GibbsSpace H hH β)) =
      {z | gibbsProjection ell hH hfixed β z = z} := by
    ext z
    exact mem_retainedGibbsSpace_iff ell hH hfixed β z
  rw [he]
  exact isClosed_eq (gibbsProjection ell hH hfixed β).continuous continuous_id

theorem quotientModular_mem_retainedGibbsSpace (s : ℝ) {z : GibbsSpace H hH β}
    (hz : z ∈ retainedGibbsSpace ell hH hfixed β) :
    Clock.quotientModular hH β s z ∈ retainedGibbsSpace ell hH hfixed β := by
  rw [mem_retainedGibbsSpace_iff] at hz ⊢
  rw [gibbsBlockProjection_modular ell hH hfixed β s z, hz]

/-- The original modular unitary restricted to the retained sector, with negative time as inverse. -/
def retainedModular (s : ℝ) : retainedGibbsSpace ell hH hfixed β ≃ₗᵢ[ℂ]
    retainedGibbsSpace ell hH hfixed β where
  toFun z := ⟨Clock.quotientModular hH β s z.1,
    quotientModular_mem_retainedGibbsSpace ell hH hfixed β s z.2⟩
  invFun z := ⟨Clock.quotientModular hH β (-s) z.1,
    quotientModular_mem_retainedGibbsSpace ell hH hfixed β (-s) z.2⟩
  left_inv z := Subtype.ext (Clock.quotientModular_inverse hH β s z.1)
  right_inv z := Subtype.ext (by simpa only [neg_neg] using
    Clock.quotientModular_inverse hH β (-s) z.1)
  map_add' z w := Subtype.ext ((Clock.quotientModular hH β s).map_add z.1 w.1)
  map_smul' c z := Subtype.ext ((Clock.quotientModular hH β s).map_smul c z.1)
  norm_map' z := (Clock.quotientModular hH β s).norm_map z.1

theorem retainedModular_zero (z : retainedGibbsSpace ell hH hfixed β) :
    retainedModular ell hH hfixed β 0 z = z :=
  Subtype.ext (Clock.quotientModular_zero hH β z.1)

theorem retainedModular_group (s t : ℝ) (z : retainedGibbsSpace ell hH hfixed β) :
    retainedModular ell hH hfixed β (s+t) z =
      retainedModular ell hH hfixed β s (retainedModular ell hH hfixed β t z) :=
  Subtype.ext (Clock.quotientModular_group hH β s t z.1)

/-- Projecting from the full Gibbs space yields a vector of the actual retained range. -/
def projectToRetained (z : GibbsSpace H hH β) : retainedGibbsSpace ell hH hfixed β :=
  ⟨gibbsProjection ell hH hfixed β z, ⟨z, rfl⟩⟩

theorem projectToRetained_modular (s : ℝ) (z : GibbsSpace H hH β) :
    projectToRetained ell hH hfixed β (Clock.quotientModular hH β s z) =
      retainedModular ell hH hfixed β s (projectToRetained ell hH hfixed β z) :=
  Subtype.ext (gibbsBlockProjection_modular ell hH hfixed β s z)

private def twoLevelSignatures : Fin 1 → Fin 2 → ℝ := fun _ _ => 0

private theorem twoLevel_generator_fixed : twoLevel 1 ∈ fixedAlgebra twoLevelSignatures := by
  change blockExpectation twoLevelSignatures (twoLevel 1) = twoLevel 1
  ext i j
  rw [expectation_entry, if_pos ((blockClass_eq_iff _ i j).2 (fun _ => rfl))]

/-- The retained unitary genuinely changes a vector at modular time π. -/
theorem retainedModular_flip_nontrivial :
    ∃ z : retainedGibbsSpace twoLevelSignatures (twoLevel_hermitian 1) twoLevel_generator_fixed 1,
      retainedModular twoLevelSignatures (twoLevel_hermitian 1) twoLevel_generator_fixed 1 Real.pi z ≠ z := by
  let hρ := gibbs_posDef (twoLevel_hermitian 1) 1
  let x := observable hρ.posSemidef E01
  let P := gibbsProjection twoLevelSignatures (twoLevel_hermitian 1) twoLevel_generator_fixed 1
  have hP : P x = x := by
    change fixedWeightProjection _ _ _ (observable hρ.posSemidef E01) = x
    rw [fixedWeightProjection_observable]
    exact congrArg (observable hρ.posSemidef) equal_signature_modular_flip.1
  refine ⟨projectToRetained twoLevelSignatures (twoLevel_hermitian 1) twoLevel_generator_fixed 1 x, ?_⟩
  intro h
  have hval := congrArg Subtype.val h
  change Clock.quotientModular (twoLevel_hermitian 1) 1 Real.pi (P x) = P x at hval
  rw [hP, show x = observable hρ.posSemidef E01 from rfl,
    Clock.quotientModular_observable, equal_signature_modular_flip.2.1] at hval
  exact equal_signature_modular_flip.2.2 (observable_injective hρ hval)

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation
