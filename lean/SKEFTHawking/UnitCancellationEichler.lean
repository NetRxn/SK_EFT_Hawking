/-
# `⟨1⟩`-cancellation: the Eichler assembly

`UnitBlockCancellation.UnitCancellation` reduces the K8b interior brick to ONE statement, and
`EichlerTransvection.exists_isometry_map_of_perp_hyp` discharges **STEP 2** of Eichler's criterion
(the three-transvection chain). This module builds the ASSEMBLY between them: everything that turns
STEP 2 plus a STEP-1 normalisation into `UnitCancellation`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.UnitBlockCancellation

namespace SKEFTHawking

open Matrix Module QuadraticForm

/-! ### Extracting `A ≅ B` from a unit-vector-fixing isometry

If `Φ` conjugates `⟨1⟩ ⊕ A` to `⟨1⟩ ⊕ B` *and fixes the adjoined generator*, then `Φ` is itself
block-diagonal `⟨1⟩ ⊕ P`, and `Pᵀ A P = B`. This is the exit gate of the whole route: the entire
remaining problem is producing such a `Φ`.
-/

/-- The adjoined `⟨1⟩` generator, as a vector of `Fin m → ℤ` under the reindexing `e`. -/
def unitGen {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) : Fin m → ℤ :=
  Pi.single (e (Sum.inl 0)) 1

/-- The Gram matrix of `⟨1⟩ ⊕ A` in the reindexing `e`, evaluated on the adjoined generator's row. -/
theorem unitExtend_row {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) (A : Matrix (Fin n) (Fin n) ℤ)
    (l : Fin m) :
    (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) (e (Sum.inl 0)) l = unitGen e l := by
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, unitGen]
  rcases hl : e.symm l with j | j
  · have : l = e (Sum.inl 0) := by
      have := congrArg e hl
      rwa [Equiv.apply_symm_apply, Subsingleton.elim j 0] at this
    subst this
    simp
  · have : l ≠ e (Sum.inl 0) := by
      intro hcon
      rw [hcon, Equiv.symm_apply_apply] at hl
      simp at hl
    simp [this, Matrix.fromBlocks_apply₁₂]

/-- The adjoined generator's COLUMN of the Gram matrix of `⟨1⟩ ⊕ A`. -/
theorem unitExtend_col {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m) (A : Matrix (Fin n) (Fin n) ℤ)
    (i : Fin m) :
    (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) i (e (Sum.inl 0)) = unitGen e i := by
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, unitGen]
  rcases hi : e.symm i with j | j
  · have : i = e (Sum.inl 0) := by
      have := congrArg e hi
      rwa [Equiv.apply_symm_apply, Subsingleton.elim j 0] at this
    subst this
    simp
  · have : i ≠ e (Sum.inl 0) := by
      intro hcon
      rw [hcon, Equiv.symm_apply_apply] at hi
      simp at hi
    simp [this, Matrix.fromBlocks_apply₂₁]

/-- `⟨1⟩ ⊕ A` fixes the adjoined generator: `G *ᵥ w = w`. -/
theorem unitExtend_mulVec_gen {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) *ᵥ unitGen e = unitGen e := by
  funext i
  have : ((Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) *ᵥ unitGen e) i
      = (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) i (e (Sum.inl 0)) := by
    rw [unitGen]; simp
  rw [this]
  exact unitExtend_col e A i

/-- **Exit gate.** An isometry `⟨1⟩ ⊕ A → ⟨1⟩ ⊕ B` that FIXES the adjoined generator is block
diagonal, and its residual block realises `IntCongr A B`. -/
theorem intCongr_of_unitFixing {n m : ℕ} (e : Fin 1 ⊕ Fin n ≃ Fin m)
    (A B : Matrix (Fin n) (Fin n) ℤ) (Φ : Matrix (Fin m) (Fin m) ℤ) (hdet : IsUnit Φ.det)
    (hfix : Φ *ᵥ unitGen e = unitGen e)
    (hconj : Φᵀ * (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) * Φ
      = Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 B)) :
    IntCongr A B := by
  classical
  -- the column of `Φ` at the generator's index is the generator
  have hcolΦ : ∀ i, Φ i (e (Sum.inl 0)) = unitGen e i := by
    intro i
    have h := congrFun hfix i
    rw [unitGen] at h ⊢
    simpa using h
  -- the ROW of `Φ` at the generator's index is the generator too
  have hrowΦ : ∀ j, Φ (e (Sum.inl 0)) j = unitGen e j := by
    have h1 : (Φᵀ * (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 A)) * Φ) *ᵥ unitGen e
        = unitGen e := by
      rw [hconj]; exact unitExtend_mulVec_gen e B
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix, unitExtend_mulVec_gen e A] at h1
    intro j
    have h := congrFun h1 j
    rw [unitGen] at h ⊢
    simpa using h
  set Ψ : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℤ := Φ.submatrix e e with hΨ
  set P : Matrix (Fin n) (Fin n) ℤ := Ψ.toBlocks₂₂ with hP
  -- `Ψ` is block diagonal
  have hblock : Ψ = Matrix.fromBlocks !![1] 0 0 P := by
    ext a b
    match a, b with
    | Sum.inl i, Sum.inl j =>
      have hi : i = 0 := Subsingleton.elim i 0
      have hj : j = 0 := Subsingleton.elim j 0
      subst hi; subst hj
      rw [hΨ, Matrix.submatrix_apply, hcolΦ, unitGen]
      simp
    | Sum.inl i, Sum.inr j =>
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [hΨ, Matrix.submatrix_apply, hrowΦ, unitGen, Pi.single_apply]
      have : e (Sum.inr j) ≠ e (Sum.inl 0) := by
        intro hcon; simp at hcon
      simp [this]
    | Sum.inr i, Sum.inl j =>
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      rw [hΨ, Matrix.submatrix_apply, hcolΦ, unitGen, Pi.single_apply]
      have : e (Sum.inr i) ≠ e (Sum.inl 0) := by
        intro hcon; simp at hcon
      simp [this]
    | Sum.inr i, Sum.inr j => simp [hP, Matrix.toBlocks₂₂]
  -- transport the conjugation identity down to `Fin 1 ⊕ Fin n`
  have hGsub : ∀ C : Matrix (Fin n) (Fin n) ℤ,
      (Matrix.reindex e e (Matrix.fromBlocks !![1] 0 0 C)).submatrix e e
        = Matrix.fromBlocks !![1] 0 0 C := by
    intro C; rw [Matrix.reindex_apply, Matrix.submatrix_submatrix]; simp
  have hsub : Ψᵀ * (Matrix.fromBlocks !![1] 0 0 A) * Ψ = Matrix.fromBlocks !![1] 0 0 B := by
    rw [hΨ, Matrix.transpose_submatrix, ← hGsub A, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hconj, hGsub B]
  -- block-diagonal conjugation acts blockwise
  have hone : (!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) = 1 := by
    ext i j; fin_cases i; fin_cases j; simp
  have hexp : Ψᵀ * (Matrix.fromBlocks !![1] 0 0 A) * Ψ
      = Matrix.fromBlocks !![1] 0 0 (Pᵀ * A * P) := by
    rw [hblock, Matrix.fromBlocks_transpose, hone]
    simp [Matrix.fromBlocks_multiply]
  refine ⟨P, ?_, ?_⟩
  · have h1 : Ψ.det = Φ.det := Matrix.det_submatrix_equiv_self e Φ
    have h2 : Ψ.det = P.det := by
      rw [hblock, Matrix.det_fromBlocks_zero₂₁, hone]
      simp
    rw [← h2, h1]; exact hdet
  · have := hexp.symm.trans hsub
    have h3 := congrArg Matrix.toBlocks₂₂ this
    simpa [Matrix.toBlocks_fromBlocks₂₂] using h3

end SKEFTHawking
