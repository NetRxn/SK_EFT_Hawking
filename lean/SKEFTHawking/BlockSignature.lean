/-
Phase 5q.B: signature additivity over block-diagonal matrices (`σ(A ⊕ B) = σ(A) + σ(B)`).

This connects the abstract `QuadraticMap.prod` additivity engine (`SignatureAdditivity.lean`) to the
*concrete* block-diagonal matrix `Matrix.fromBlocks A 0 0 B`. It is the calculus step that, applied
repeatedly, computes the signature of the classification normal form `E₈^a ⊕ (−E₈)^b ⊕ H^c` as
`8a − 8b + 0 = 8(a − b)`, manifestly `≡ 0 mod 8` — the conclusion of van der Blij.

The chain:
* `fromBlocks_tQM_elim` — on a `Sum.elim` input the block-diagonal form splits: `Q_{A⊕B}(x ⊕ y) = Q_A(x) +
  Q_B(y)` (the off-diagonal zero blocks kill the cross terms).
* `fromBlocksEquivProd` — hence the block-diagonal form is `IsometryEquiv` to the product form
  `Q_A.prod Q_B`, via the canonical `(Fin na ⊕ Fin nb → ℝ) ≃ₗ (Fin na → ℝ) × (Fin nb → ℝ)`.
* `sigPos_fromBlocks`/`sigNeg_fromBlocks` — combine with `Equivalent.sigPos_eq` (Sylvester) and the
  nondegenerate `prod` additivity to get `sigPos (A ⊕ B) = sigPos A + sigPos B` (and `sigNeg`), for
  nondegenerate `A, B` (radical `= ⊥`; satisfied by all unimodular generators).

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.SignatureAdditivity

namespace SKEFTHawking

open Matrix QuadraticMap QuadraticForm

/-- **Nondegeneracy ⟹ radical `= ⊥`** for a symmetric real matrix form. The radical equals the kernel of
the polar bilinear form (`radical_eq_ker_polarBilin`, valid since `2` is invertible over ℝ); for symmetric
`M` the polar is `2·(x ⬝ᵥ M y)`, whose kernel is `⊥` exactly when `M` is nondegenerate. Supplies the
`radical = ⊥` hypotheses of the additivity theorems for the (unimodular, hence nondegenerate) generators
`E₈`, `−E₈`, `H`. -/
theorem nondeg_radical_eq_bot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hsym : Mᵀ = M) (hnd : M.Nondegenerate) : M.toQuadraticMap'.radical = ⊥ := by
  rw [QuadraticMap.radical_eq_ker_polarBilin, LinearMap.ker_eq_bot']
  intro x hx
  apply (Matrix.nondegenerate_def.mp hnd).1
  intro w
  have hpw : (QuadraticMap.polarBilin M.toQuadraticMap') x w = 0 := by rw [hx]; rfl
  have hform : (QuadraticMap.polarBilin M.toQuadraticMap') x w
      = x ⬝ᵥ M.mulVec w + w ⬝ᵥ M.mulVec x := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Matrix.toQuadraticMap',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]; ring
  have hcomm : w ⬝ᵥ M *ᵥ x = x ⬝ᵥ M *ᵥ w := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]
  rw [hform, hcomm] at hpw
  linarith [hpw]

/-- On a `Sum.elim` input, the block-diagonal quadratic form splits as the sum of the block forms (the
zero off-diagonal blocks annihilate the cross terms). -/
theorem fromBlocks_tQM_elim {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℝ)
    (B : Matrix (Fin nb) (Fin nb) ℝ) (x : Fin na → ℝ) (y : Fin nb → ℝ) :
    (Matrix.fromBlocks A 0 0 B).toQuadraticMap' (Sum.elim x y)
      = A.toQuadraticMap' x + B.toQuadraticMap' y := by
  simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rfl

/-- The block-diagonal form `Q_{A⊕B}` is isometric to the product form `Q_A.prod Q_B`, via the canonical
linear equivalence `(Fin na ⊕ Fin nb → ℝ) ≃ₗ (Fin na → ℝ) × (Fin nb → ℝ)`. -/
noncomputable def fromBlocksEquivProd {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℝ)
    (B : Matrix (Fin nb) (Fin nb) ℝ) :
    (Matrix.fromBlocks A 0 0 B).toQuadraticMap'.IsometryEquiv
      (A.toQuadraticMap'.prod B.toQuadraticMap') where
  toLinearEquiv := LinearEquiv.sumArrowLequivProdArrow (Fin na) (Fin nb) ℝ ℝ
  map_app' m := by
    have hm : m = Sum.elim (m ∘ Sum.inl) (m ∘ Sum.inr) := by ext i; cases i <;> rfl
    rw [QuadraticMap.prod_apply]
    conv_rhs => rw [hm]
    rw [fromBlocks_tQM_elim]
    rfl

/-- **Positive-inertia additivity over block-diagonal:** `sigPos (A ⊕ B) = sigPos A + sigPos B` for
nondegenerate blocks. -/
theorem sigPos_fromBlocks {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℝ)
    (B : Matrix (Fin nb) (Fin nb) ℝ)
    (hA : A.toQuadraticMap'.radical = ⊥) (hB : B.toQuadraticMap'.radical = ⊥) :
    sigPos (Matrix.fromBlocks A 0 0 B).toQuadraticMap'
      = sigPos A.toQuadraticMap' + sigPos B.toQuadraticMap' := by
  rw [QuadraticMap.Equivalent.sigPos_eq ⟨fromBlocksEquivProd A B⟩, sigPos_prod_of_nondeg _ _ hA hB]

/-- **Negative-inertia additivity over block-diagonal:** `sigNeg (A ⊕ B) = sigNeg A + sigNeg B` for
nondegenerate blocks. -/
theorem sigNeg_fromBlocks {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℝ)
    (B : Matrix (Fin nb) (Fin nb) ℝ)
    (hA : A.toQuadraticMap'.radical = ⊥) (hB : B.toQuadraticMap'.radical = ⊥) :
    sigNeg (Matrix.fromBlocks A 0 0 B).toQuadraticMap'
      = sigNeg A.toQuadraticMap' + sigNeg B.toQuadraticMap' := by
  rw [QuadraticMap.Equivalent.sigNeg_eq ⟨fromBlocksEquivProd A B⟩, sigNeg_prod_of_nondeg _ _ hA hB]

end SKEFTHawking
