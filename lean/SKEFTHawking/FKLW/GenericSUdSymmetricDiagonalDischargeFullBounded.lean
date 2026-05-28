/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Full diagonal discharge WITH norm bound (bounded Session 31)

Strengthens Session 31's `symmetric_balanced_commutator_diagonal_real_full`
(arbitrary traceless real diagonal H, no partial-sums hypothesis) to ALSO
return explicit linftyOp norm bounds on F, G:

  `‖F‖ ≤ ∑_p √(θ·(b'_p).re/2)` and `‖G‖ ≤ ∑_p √(θ·(b'_p).re/2)`

where `b'_p = partialSumCoeff (a_sorted coerced) p` and
`a_sorted = a ∘ Tuple.sort (-a)` is the eigenvalue-sorted version.

## Composition chain

Session 31's proof, with two changes:

  1. At the discharge step (Step 6), apply Session 77's BOUNDED discharge
     `symmetric_balanced_commutator_diagonal_nonneg_partials_bounded` (instead
     of Session 24), obtaining F', G' AND `‖F'‖, ‖G'‖ ≤ ∑_p √(θ·(b'_p).re/2)`.
  2. The conjugation `F = P.val · F' · star P.val` (with `P = permMatrixAsUnitary σ⁻¹`)
     preserves the linftyOp norm by Session 78's
     `permMatrixAsUnitary_conj_linftyOpNorm_eq`, so `‖F‖ = ‖F'‖ ≤ ∑_p √(θ·(b'_p).re/2)`.

This exposes the F/G-norm bound for the eigenvalue-sort path — the bridge
needed to compose the full diagonal discharge with the super-quad bound's
F_inner norm ingredient.

## Substantive content shipped

  * `symmetric_balanced_commutator_diagonal_real_full_bounded` — Session 31's
    full diagonal discharge + `‖F‖, ‖G‖ ≤ ∑_p √(θ·(sorted partial sum).re/2)`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — bounded full diagonal
discharge (F_inner norm bound bridge through eigenvalue sort).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSymmetricDischargeBounded
import SKEFTHawking.FKLW.GenericSUdDecreasingSortPartialSums
import SKEFTHawking.FKLW.GenericSUdUnitaryConjugationInvariance
import SKEFTHawking.FKLW.GenericSUdPermutationConjugation
import SKEFTHawking.FKLW.GenericSUdPermutationDiagonal
import SKEFTHawking.FKLW.GenericSUdPartialSumBridge
import SKEFTHawking.FKLW.GenericSUdRangeFilterBridge
import SKEFTHawking.FKLW.GenericSUdPermConjNormPreserve

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **BOUNDED FULL DIAGONAL DISCHARGE of S.3 d≥3 PROPER**: for ARBITRARY
traceless real `a : Fin (n + 2) → ℝ` (no partial-sums hypothesis), there exist
Hermitian-traceless F, G satisfying

  `F · G − G · F = -((θ : ℂ) · Complex.I) • Matrix.diagonal (a coerced to ℂ)`

for any θ ∈ [0, 1], AND with explicit linftyOp norm bounds

  `‖F‖ ≤ ∑_p √(θ·(b'_p).re/2)` and `‖G‖ ≤ ∑_p √(θ·(b'_p).re/2)`

where `b'_p = partialSumCoeff (a_sorted coerced) p` for the eigenvalue-sorted
`a_sorted = a ∘ Tuple.sort (-a)`.

Proof: Session 31's eigenvalue-sort conjugation, threading Session 77's
BOUNDED discharge at the sorted diagonal and Session 78's permMatrix-conjugation
norm preservation to carry the norm bound through the conjugation. -/
theorem symmetric_balanced_commutator_diagonal_real_full_bounded {n : ℕ}
    (a : Fin (n + 2) → ℝ)
    (h_tr_real : (∑ k, a k) = 0)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) •
        Matrix.diagonal (fun k => (a k : ℂ)) ∧
      ‖F‖ ≤ ∑ p : Fin (n + 1),
        Real.sqrt (θ * (partialSumCoeff
          (fun k => (a ((Tuple.sort (fun i => -(a i))) k) : ℂ)) p).re / 2) ∧
      ‖G‖ ≤ ∑ p : Fin (n + 1),
        Real.sqrt (θ * (partialSumCoeff
          (fun k => (a ((Tuple.sort (fun i => -(a i))) k) : ℂ)) p).re / 2) := by
  -- Step 1: Define sort permutation σ.
  set σ : Equiv.Perm (Fin (n + 2)) := Tuple.sort (fun i => -(a i)) with hσ_def
  -- Step 2: a_sorted = a ∘ σ is non-increasing.
  set a_sorted : Fin (n + 2) → ℝ := fun k => a (σ k) with ha_sorted_def
  have h_mono : Monotone ((fun i => -(a i)) ∘ σ) := Tuple.monotone_sort _
  have h_dec : ∀ i j : Fin (n + 2), i ≤ j → a_sorted j ≤ a_sorted i := by
    intro i j hij
    have h_neg : -(a (σ i)) ≤ -(a (σ j)) := h_mono hij
    linarith
  -- Step 3: Traceless preserved.
  have h_tr_sorted_real : (∑ k, a_sorted k) = 0 := by
    show (∑ k, a (σ k)) = 0
    rw [Fintype.sum_equiv σ _ _ (fun _ => rfl)]
    exact h_tr_real
  have h_tr_sorted_complex : (∑ k, (a_sorted k : ℂ)) = 0 := by
    rw [show (∑ k, (a_sorted k : ℂ)) = ((∑ k, a_sorted k : ℝ) : ℂ) from by push_cast; rfl]
    rw [h_tr_sorted_real]
    simp
  -- Step 4: Real partial sums of a_sorted are ≥ 0 (by S25).
  have h_nn_real_full : ∀ k : Fin (n + 2),
      0 ≤ ∑ j ∈ (Finset.univ : Finset (Fin (n + 2))).filter (· ≤ k), a_sorted j :=
    partial_sums_nonneg_of_decreasing_traceless a_sorted h_dec h_tr_sorted_real
  have h_nn_real : ∀ p : Fin (n + 1),
      0 ≤ ∑ j ∈ (Finset.univ : Finset (Fin (n + 2))).filter (· ≤ p.castSucc), a_sorted j :=
    fun p => h_nn_real_full p.castSucc
  -- Step 5: Convert to partialSumCoeff form via S29 + S30.
  have h_nn_pSC : ∀ p : Fin (n + 1),
      0 ≤ (partialSumCoeff (fun k => (a_sorted k : ℂ)) p).re := by
    intro p
    rw [partialSumCoeff_real_re_eq_finset_range_real_sum a_sorted p]
    rw [sum_range_eq_sum_filter_le_castSucc a_sorted p]
    exact h_nn_real p
  have h_im_pSC : ∀ p : Fin (n + 1),
      (partialSumCoeff (fun k => (a_sorted k : ℂ)) p).im = 0 :=
    fun p => partialSumCoeff_real_im_zero a_sorted p
  -- Step 6: Apply S77 (BOUNDED discharge) to a_sorted.
  obtain ⟨F', G', hF'_herm, hG'_herm, hF'_tr, hG'_tr, hcomm', hF'_bound, hG'_bound⟩ :=
    symmetric_balanced_commutator_diagonal_nonneg_partials_bounded
      a_sorted h_tr_sorted_complex h_nn_pSC h_im_pSC θ hθ_nn hθ_le_one
  -- Step 7: Permutation matrix P = permMatrix σ⁻¹.
  let P := permMatrixAsUnitary (σ⁻¹ : Equiv.Perm (Fin (n + 2)))
  -- Step 8: Define F = P.val · F' · star P.val, G similar.
  refine ⟨P.val * F' * star P.val, P.val * G' * star P.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- F Hermitian (by S26)
  · exact unitary_group_conjugation_isHermitian P F' hF'_herm
  -- G Hermitian
  · exact unitary_group_conjugation_isHermitian P G' hG'_herm
  -- F traceless
  · exact unitary_group_conjugation_traceless P F' hF'_tr
  -- G traceless
  · exact unitary_group_conjugation_traceless P G' hG'_tr
  -- Commutator identity: F · G − G · F = -iθ · diag(a)
  · have h_smul_comm := unitary_group_conjugation_smul_commutator_invariance
      P F' G' (Matrix.diagonal (fun k => (a_sorted k : ℂ)))
      (-((θ : ℂ) * Complex.I)) hcomm'
    rw [h_smul_comm]
    congr 1
    show Equiv.Perm.permMatrix ℂ σ⁻¹ * Matrix.diagonal (fun k => (a_sorted k : ℂ)) *
         star (Equiv.Perm.permMatrix ℂ σ⁻¹) = Matrix.diagonal (fun k => (a k : ℂ))
    rw [star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    rw [permMatrix_mul_diagonal_mul_permMatrix_inv σ⁻¹
        (fun k => (a_sorted k : ℂ))]
    congr 1
    funext k
    show (a_sorted (σ⁻¹ k) : ℂ) = (a k : ℂ)
    show (a (σ (σ⁻¹ k)) : ℂ) = (a k : ℂ)
    have : σ (σ⁻¹ k) = k := by simp
    rw [this]
  -- ‖F‖ bound: ‖P.val · F' · star P.val‖ = ‖F'‖ (S78) ≤ bound (S77)
  · show ‖(permMatrixAsUnitary σ⁻¹).val * F' * star (permMatrixAsUnitary σ⁻¹).val‖ ≤ _
    rw [permMatrixAsUnitary_conj_linftyOpNorm_eq σ⁻¹ F']
    exact hF'_bound
  -- ‖G‖ bound: same via S78 + S77
  · show ‖(permMatrixAsUnitary σ⁻¹).val * G' * star (permMatrixAsUnitary σ⁻¹).val‖ ≤ _
    rw [permMatrixAsUnitary_conj_linftyOpNorm_eq σ⁻¹ G']
    exact hG'_bound

end SKEFTHawking.FKLW.GenericSUd
