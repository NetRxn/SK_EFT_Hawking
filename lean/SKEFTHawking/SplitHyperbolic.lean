/-
Phase 5q.B: the hyperbolic-plane split-off at the matrix level — the Gram of `M` in the combined basis
`hypFullBasis` is block-diagonal `H ⊕ M'`.

This is the heart of the inductive split-off-H step ([E2]): given a primitive isotropic vector of an even
unimodular form `M`, the combined basis `{v, w'} ∪ (basis of K^⊥)` (`hypFullBasis`) puts `M` into the form
`H ⊕ M'`, where `H` is the hyperbolic plane and `M' = residGram` is the residual even-symmetric form on the
orthogonal complement. The block structure is exactly `hypPerpBasis_ortho` (off-diagonal vanishes) plus the
`hv0/hvw/hw0` values (the `K`-block is `H`).

`gramB_eq` is the kernel-pure block identity. The remaining step to `latticeSig M = latticeSigOf residGram`
is the change-of-basis congruence (the matrix of `hypFullBasis` is unimodular, so `latticeSig_congr`
applies), tracked as the next brick in `docs/roadmaps/Phase5qB_LabNotebook.md`.

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.LatticePrimitive
import SKEFTHawking.LatticeSignatureCongr
import SKEFTHawking.LatticeSigBlock
import SKEFTHawking.GeneratorNondeg
import SKEFTHawking.BlockSignature

namespace SKEFTHawking

open Matrix Module

/-- **The Gram of `M` in the combined basis is block-diagonal `H ⊕ M'`.** Off-diagonal blocks vanish
because the `K^⊥`-basis is `M`-orthogonal to `v, w'` (`hypPerpBasis_ortho`); the `K`-block is the
hyperbolic plane `H` (from `vᵀMv = 0`, `vᵀMw' = w'ᵀMv = 1`, `w'ᵀMw' = 0`); the `K^⊥`-block is `residGram`. -/
theorem gramB_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v w' : Fin n → ℤ)
    (hsymm : Mᵀ = M) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w' = 1) (hw0 : w' ⬝ᵥ M *ᵥ w' = 0)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) :
    Matrix.of (fun s t => (hypFullBasis M v w' hsymm hv0 hvw hw0 hfr s : Fin n → ℤ) ⬝ᵥ
        M *ᵥ (hypFullBasis M v w' hsymm hv0 hvw hw0 hfr t : Fin n → ℤ))
      = Matrix.fromBlocks Hyp 0 0 (residGram M v w' hfr) := by
  have hwv : w' ⬝ᵥ M *ᵥ v = 1 := by
    rw [show w' ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ w' from by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]]; exact hvw
  ext s t
  rcases s with k | i <;> rcases t with l | j
  · rw [Matrix.of_apply, hypFullBasis_inl, hypFullBasis_inl, Matrix.fromBlocks_apply₁₁]
    fin_cases k <;> fin_cases l <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Hyp,
        Matrix.of_apply] <;> first | exact hv0 | exact hvw | exact hwv | exact hw0
  · rw [Matrix.of_apply, hypFullBasis_inl, hypFullBasis_inr, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply]
    fin_cases k <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · exact (hypPerpBasis_ortho M v w' hfr j).1
    · exact (hypPerpBasis_ortho M v w' hfr j).2
  · rw [Matrix.of_apply, hypFullBasis_inr, hypFullBasis_inl, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
    rw [show (hypPerpBasis M v w' hfr i : Fin n → ℤ) ⬝ᵥ M *ᵥ (![v, w'] l)
        = (![v, w'] l) ⬝ᵥ M *ᵥ (hypPerpBasis M v w' hfr i : Fin n → ℤ) from by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]]
    fin_cases l <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · exact (hypPerpBasis_ortho M v w' hfr i).1
    · exact (hypPerpBasis_ortho M v w' hfr i).2
  · rw [Matrix.of_apply, hypFullBasis_inr, hypFullBasis_inr, Matrix.fromBlocks_apply₂₂]
    rfl

/-- **Split-off-H at the signature level (the [E2] inductive step):** for an even unimodular form `M` with
a primitive isotropic vector packaged as a hyperbolic pair `{v, w'}` (Gram `H`), the signature equals that
of the residual form on the orthogonal complement: `latticeSig M = latticeSigOf (residGram …)`. The proof
forms the unimodular change of basis `P` from `hypFullBasis` (`P.det` a unit since it is a basis matrix),
shows `Pᵀ M P = reindex (H ⊕ M')` (`gramB_eq`), and reads off via `latticeSig_congr` (Sylvester) +
`latticeSigOf_fromBlocks` (`σ(H ⊕ M') = σ(H) + σ(M') = 0 + σ(M')`, with `M'` nondegenerate because
`det M' = ±det M = ±1`) + reindex-invariance. Iterating this peels every hyperbolic plane off an indefinite
even unimodular form, reducing van der Blij to the definite base case. -/
theorem latticeSig_split {n : ℕ} (hn2 : 2 ≤ n) (M : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : Mᵀ = M) (hunim : IsUnimodular M)
    (v w' : Fin n → ℤ) (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w' = 1) (hw0 : w' ⬝ᵥ M *ᵥ w' = 0)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) :
    latticeSig M = latticeSigOf (residGram M v w' hfr) := by
  classical
  set B := hypFullBasis M v w' hsymm hv0 hvw hw0 hfr with hB
  let e : Fin 2 ⊕ Fin (n - 2) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  set B' := B.reindex e with hB'
  set P := (Pi.basisFun ℤ (Fin n)).toMatrix ⇑B' with hP
  have hP_entry : ∀ k l, P k l = (B' l) k := fun k l => by
    rw [hP, Basis.toMatrix_apply, Pi.basisFun_repr]
  have hPunit : IsUnit P.det := by
    have h1 : P.det * (B'.toMatrix ⇑(Pi.basisFun ℤ (Fin n))).det = 1 := by
      rw [hP, ← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ h1
  have hPMP : Pᵀ * M * P
      = Matrix.reindex e e (Matrix.of (fun s t => (B s : Fin n → ℤ) ⬝ᵥ M *ᵥ (B t : Fin n → ℤ))) := by
    ext i j
    have hlhs : (Pᵀ * M * P) i j = (B' i) ⬝ᵥ M *ᵥ (B' j) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hP_entry, Matrix.mulVec, dotProduct]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [hlhs, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, hB',
      Basis.reindex_apply, Basis.reindex_apply]
  have hgram := gramB_eq M v w' hsymm hv0 hvw hw0 hfr
  have hdetM : M.det ≠ 0 := by rcases hunim with h | h <;> rw [h] <;> norm_num
  have hPMP_det_ne : (Pᵀ * M * P).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hPunit.ne_zero hdetM) hPunit.ne_zero
  have hdetRG : (residGram M v w' hfr).det ≠ 0 := by
    have hkey : (Pᵀ * M * P).det = -(residGram M v w' hfr).det := by
      rw [hPMP, hgram, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
        show Hyp.det = -1 from by decide]; ring
    rw [hkey] at hPMP_det_ne; simpa using hPMP_det_ne
  have hRG : ((residGram M v w' hfr).map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ := by
    apply nondeg_radical_eq_bot
    · rw [← Matrix.transpose_map, residGram_symm M hsymm]
    · exact cast_nondegenerate _ hdetRG
  rw [← latticeSig_congr M P hPunit, hPMP, hgram, ← latticeSigOf_fin, latticeSigOf_reindex,
    latticeSigOf_fromBlocks Hyp (residGram M v w' hfr) hyp_radical hRG,
    show latticeSigOf Hyp = 0 from by rw [latticeSigOf_fin, hyp_latticeSig]]
  ring

/-- **`det (residGram) = − det M`.** The hyperbolic block contributes `det H = −1`, and the change of basis
is unimodular, so the residual determinant is exactly `−det M`. -/
theorem residGram_det {n : ℕ} (hn2 : 2 ≤ n) (M : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : Mᵀ = M) (v w' : Fin n → ℤ)
    (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w' = 1) (hw0 : w' ⬝ᵥ M *ᵥ w' = 0)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) :
    (residGram M v w' hfr).det = - M.det := by
  classical
  set B := hypFullBasis M v w' hsymm hv0 hvw hw0 hfr with hB
  let e : Fin 2 ⊕ Fin (n - 2) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  set B' := B.reindex e with hB'
  set P := (Pi.basisFun ℤ (Fin n)).toMatrix ⇑B' with hP
  have hP_entry : ∀ k l, P k l = (B' l) k := fun k l => by
    rw [hP, Basis.toMatrix_apply, Pi.basisFun_repr]
  have hPunit : IsUnit P.det := by
    have h1 : P.det * (B'.toMatrix ⇑(Pi.basisFun ℤ (Fin n))).det = 1 := by
      rw [hP, ← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ h1
  have hPMP : Pᵀ * M * P
      = Matrix.reindex e e (Matrix.of (fun s t => (B s : Fin n → ℤ) ⬝ᵥ M *ᵥ (B t : Fin n → ℤ))) := by
    ext i j
    have hlhs : (Pᵀ * M * P) i j = (B' i) ⬝ᵥ M *ᵥ (B' j) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hP_entry, Matrix.mulVec, dotProduct]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [hlhs, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, hB',
      Basis.reindex_apply, Basis.reindex_apply]
  have hgram := gramB_eq M v w' hsymm hv0 hvw hw0 hfr
  have hdet1 : (Pᵀ * M * P).det = (P.det) ^ 2 * M.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
  have hdet2 : (Pᵀ * M * P).det = -(residGram M v w' hfr).det := by
    rw [hPMP, hgram, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
      show Hyp.det = -1 from by decide]; ring
  have hP2 : (P.det) ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hPunit with h | h <;> rw [h] <;> ring
  rw [hdet1, hP2, one_mul] at hdet2
  linarith [hdet2]

/-- **The residual form `M'` is even unimodular** — the induction invariant for the split-off-H recursion:
`M'` is symmetric (`residGram_symm`), even (`residGram_even`), and unimodular (`det M' = −det M = ∓1`). -/
theorem residGram_evenUnimodular {n : ℕ} (hn2 : 2 ≤ n) (M : Matrix (Fin n) (Fin n) ℤ)
    (h_eu : IsEvenUnimodular M) (v w' : Fin n → ℤ)
    (hv0 : v ⬝ᵥ M *ᵥ v = 0) (hvw : v ⬝ᵥ M *ᵥ w' = 1) (hw0 : w' ⬝ᵥ M *ᵥ w' = 0)
    (hfr : Module.finrank ℤ (hypPerp M v w') = n - 2) :
    IsEvenUnimodular (residGram M v w' hfr) := by
  obtain ⟨hsym, hunim, heven⟩ := h_eu
  refine ⟨residGram_symm M hsym v w' hfr, ?_, residGram_even M hsym heven v w' hfr⟩
  rw [IsUnimodular, residGram_det hn2 M hsym v w' hv0 hvw hw0 hfr]
  rcases hunim with h | h <;> rw [h] <;> [right; left] <;> ring

end SKEFTHawking
