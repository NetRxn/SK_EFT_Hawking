/-
Phase 5q.B: nondegeneracy of the classification generators `E₈`, `−E₈`, `H`.

The block-additivity theorems (`BlockSignature.sigPos_fromBlocks`/`sigNeg_fromBlocks`) require each block's
real form to be nondegenerate (`radical = ⊥`). This capstone discharges that hypothesis for the three
generators of the classification of even unimodular lattices, so that the signature of any normal form
`E₈^a ⊕ (−E₈)^b ⊕ H^c` is computable by repeated block additivity. (Every unimodular form is nondegenerate —
`det = ±1 ≠ 0` — so this is automatic; we record it concretely for the generators.)

* `cast_nondegenerate` — a general bridge: an integer matrix with `det ≠ 0` casts to a nondegenerate real
  matrix.
* `e8r_radical` — `E₈` is nondegenerate, via positive-definiteness (`e8r_posDef`).
* `negE8_radical` — `−E₈`, via `det(−E₈) = det(E₈) = ±1 ≠ 0` (rank 8 even) and symmetry.
* `hyp_radical` — `H`, via `det H = −1 ≠ 0` and symmetry (the indefinite case, where the positive-definite
  route does not apply — handled by the general `nondeg_radical_eq_bot`).

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.E8Signature
import SKEFTHawking.LatticeSignatureCongr
import SKEFTHawking.BlockSignature

namespace SKEFTHawking

open Matrix QuadraticMap QuadraticForm

/-- An integer matrix with nonzero determinant casts to a nondegenerate real matrix. -/
theorem cast_nondegenerate {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (h : M.det ≠ 0) :
    (M.map (Int.cast : ℤ → ℝ)).Nondegenerate := by
  rw [Matrix.nondegenerate_iff_det_ne_zero, ← Int.cast_det]
  exact_mod_cast h

/-- **`E₈` is nondegenerate** (`radical = ⊥`), via positive-definiteness. -/
theorem e8r_radical : E8r.toQuadraticMap'.radical = ⊥ :=
  posDef_radical_eq_bot _ e8r_posDef.toQuadraticForm'

/-- **`−E₈` is nondegenerate** (`radical = ⊥`): `det(−E₈) = (−1)^8 · det(E₈) = ±1 ≠ 0`. -/
theorem negE8_radical : ((-E8lit).map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ := by
  apply nondeg_radical_eq_bot
  · rw [← Matrix.transpose_map, Matrix.transpose_neg, e8lit_symm]
  · refine cast_nondegenerate (-E8lit) ?_
    rw [Matrix.det_neg]
    rcases e8lit_unimodular with h | h <;> simp [h]

/-- **`H` is nondegenerate** (`radical = ⊥`): `det H = −1 ≠ 0`. The indefinite generator, where the
positive-definite route does not apply. -/
theorem hyp_radical : (Hyp.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥ := by
  apply nondeg_radical_eq_bot
  · rw [← Matrix.transpose_map, hyp_symm]
  · exact cast_nondegenerate Hyp (by rw [show Hyp.det = -1 from by decide]; norm_num)

end SKEFTHawking
