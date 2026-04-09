/-
Phase 5s Track B: S-matrix Non-degeneracy → Muger Center Triviality (General Theorem)

Direction 1 of the Muger modularity equivalence: det(S) ≠ 0 → Z₂(C) = Vec.
This is pure linear algebra — an invertible matrix cannot have two proportional rows.

Replaces 3 case-by-case native_decide proofs (Ising, Fibonacci, toric code)
with ONE abstract theorem applicable to ALL finite modular tensor categories.

The proof uses Mathlib's Matrix.det_zero_of_row_eq (equal rows → zero det)
and Matrix.det_updateRow_smul (determinant multilinearity in rows).

References:
  Muger, Proc. LMS 87 (2003), arXiv:math/0201017
  Deep research: Lit-Search/Phase-5s/S-matrix non-degeneracy...
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace SKEFTHawking

/-! ## The General Modularity Theorem (Direction 1)

For ANY invertible matrix over ANY integral domain:
  det(S) ≠ 0 → no two distinct rows are proportional.

Applied to MTC S-matrices: transparent objects have rows proportional
to the vacuum row, so det(S) ≠ 0 → no transparent objects → Z₂ = Vec. -/

/-- An invertible matrix has no two proportional rows.
    Proof: proportional rows → linearly dependent → det = 0 → contradiction.

    This is Direction 1 of the Muger modularity equivalence.
    The MTC-specific content (transparency ↔ row proportionality) is
    in MugerCenter.lean; this is the purely matrix-theoretic step. -/
theorem det_ne_zero_no_proportional_rows {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (S : Matrix (Fin n) (Fin n) R) (h_det : S.det ≠ 0)
    (i j : Fin n) (h_ne : i ≠ j) (c : R) (h_prop : S i = c • S j) : False := by
  apply h_det
  calc S.det
      = (S.updateRow i (S i)).det := by rw [Matrix.updateRow_eq_self]
    _ = (S.updateRow i (c • S j)).det := by rw [h_prop]
    _ = c * (S.updateRow i (S j)).det :=
        Matrix.det_updateRow_smul S i c (S j)
    _ = c * 0 := by
        congr 1
        exact Matrix.det_zero_of_row_eq h_ne
          (by ext k; simp [Matrix.updateRow_apply, show i ≠ j from h_ne])
    _ = 0 := mul_zero c

/-- Corollary: for MTC S-matrices, det(S) ≠ 0 implies every non-vacuum
    simple object X has a row NOT proportional to the vacuum row.
    Combined with the categorical fact (transparency ↔ proportionality),
    this gives Z₂(C) = Vec.

    This replaces the 3 case-by-case proofs in MugerCenter.lean
    (ising_muger_trivial, fib_muger_trivial, toric_muger_trivial). -/
theorem modularity_from_det {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (S : Matrix (Fin (n+1)) (Fin (n+1)) R) (h_det : S.det ≠ 0)
    (i : Fin (n+1)) (h_ne : i ≠ (0 : Fin (n+1))) (c : R) :
    S i ≠ c • S 0 := by
  intro h_prop
  exact det_ne_zero_no_proportional_rows S h_det i 0 h_ne c h_prop

end SKEFTHawking
