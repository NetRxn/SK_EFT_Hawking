/-
Phase 5q.B: `latticeSig` on arbitrary finite index, block additivity, and reindex-invariance.

`latticeSig` (in `LatticeSignature.lean`) is hard-wired to `Fin n`, but the classification normal form
`E₈^a ⊕ (−E₈)^b ⊕ H^c` is naturally built by *block sums* (a `Sum`-indexed `Matrix.fromBlocks`). This module
generalises the signature to any finite index (`latticeSigOf`), proves it agrees with `latticeSig` on `Fin n`,
is additive over `fromBlocks`, and is invariant under reindexing. Together these turn the block-diagonal
normal form into `σ = 8a − 8b + 0 = 8(a − b)` — the conclusion of van der Blij — with no index bookkeeping
left over.

* `latticeSigOf` — `sigPos − sigNeg` of the cast form, for any `[Fintype ι] [DecidableEq ι]`.
* `latticeSigOf_fin` — agrees with `latticeSig` on `Fin n` (by `rfl`).
* `latticeSigOf_fromBlocks` — `σ(A ⊕ B) = σ(A) + σ(B)` for nondegenerate blocks (via `BlockSignature`).
* `reindexFormEquiv`/`latticeSigOf_reindex` — `σ` is unchanged by relabelling the index (`Matrix.reindex`).

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.LatticeSignature
import SKEFTHawking.BlockSignature

namespace SKEFTHawking

open Matrix QuadraticMap QuadraticForm

/-- The **signature** of an integer symmetric form on an arbitrary finite index type — the same
`sigPos − sigNeg` of the real-cast form as `latticeSig`, but not tied to `Fin n`. -/
noncomputable def latticeSigOf {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) : ℤ :=
  (sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ)
    - (sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ)

/-- On `Fin n`, `latticeSigOf` is exactly `latticeSig`. -/
theorem latticeSigOf_fin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    latticeSigOf M = latticeSig M := rfl

/-- **Block-diagonal additivity for `latticeSigOf`:** `σ(A ⊕ B) = σ(A) + σ(B)` for nondegenerate blocks. -/
theorem latticeSigOf_fromBlocks {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ)
    (hA : (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (hB : (B.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥) :
    latticeSigOf (Matrix.fromBlocks A 0 0 B) = latticeSigOf A + latticeSigOf B := by
  have hmap : (Matrix.fromBlocks A 0 0 B).map (Int.cast : ℤ → ℝ)
      = Matrix.fromBlocks (A.map Int.cast) 0 0 (B.map Int.cast) := by
    rw [Matrix.fromBlocks_map]; simp
  unfold latticeSigOf
  rw [hmap, sigPos_fromBlocks _ _ hA hB, sigNeg_fromBlocks _ _ hA hB]
  push_cast; ring

/-- Relabelling the index by `e : ι ≃ ι'` gives an isometric real form (precomposition by `e`). -/
noncomputable def reindexFormEquiv {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι ≃ ι') (M : Matrix ι ι ℝ) :
    (Matrix.reindex e e M).toQuadraticMap'.IsometryEquiv M.toQuadraticMap' where
  toLinearEquiv := LinearEquiv.funCongrLeft ℝ ℝ e
  map_app' x := by
    show M.toQuadraticMap' (x ∘ e) = (Matrix.reindex e e M).toQuadraticMap' x
    simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    rw [dotProduct, dotProduct, ← Equiv.sum_comp e]
    simp

/-- **`latticeSigOf` is reindex-invariant:** relabelling the index leaves the signature unchanged. -/
theorem latticeSigOf_reindex {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι ≃ ι') (M : Matrix ι ι ℤ) :
    latticeSigOf (Matrix.reindex e e M) = latticeSigOf M := by
  have hmap : (Matrix.reindex e e M).map (Int.cast : ℤ → ℝ)
      = Matrix.reindex e e (M.map (Int.cast : ℤ → ℝ)) := by
    ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have hequiv : QuadraticMap.Equivalent
      (Matrix.reindex e e (M.map (Int.cast : ℤ → ℝ))).toQuadraticMap'
      (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' := ⟨reindexFormEquiv e _⟩
  unfold latticeSigOf
  rw [hmap, hequiv.sigPos_eq, hequiv.sigNeg_eq]

end SKEFTHawking
