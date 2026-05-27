/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Symmetric balanced commutator ∃-discharge for ANY diagonal real H

For ARBITRARY traceless `a : Fin (n + 2) → ℝ` (no partial-sums hypothesis),
there exist Hermitian-traceless F, G ∈ Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ
such that

  F · G − G · F = -((θ : ℂ) · Complex.I) • Matrix.diagonal (a coerced to ℂ)

for any θ ∈ [0, 1].

This is the **FULL DIAGONAL CASE of S.3 d≥3 PROPER**, lifting Session 24's
discharge (restricted to non-negative partial sums) to ARBITRARY traceless
real diagonal H via eigenvalue sort + permutation matrix conjugation.

## Composition chain

1. σ := Tuple.sort (fun i => -(a i)) — sort a descendingly
2. a_sorted := a ∘ σ — non-increasing real (by Tuple.monotone_sort)
3. ∑ a_sorted = ∑ a = 0 — sum preserved under permutation
4. By S25: real partial sums of a_sorted are ≥ 0
5. By S29 + S30: `(partialSumCoeff (a_sorted ·: ℂ) p).re ≥ 0` AND `.im = 0`
6. By S24: ∃ F', G' for diag(a_sorted ·: ℂ)
7. P := permMatrixAsUnitary σ⁻¹ (S27: unitary)
8. F := P.val · F' · star P.val, G similar (S26: Hermitian + traceless preserved)
9. F · G − G · F = -iθ · (P.val · diag(a_sorted) · star P.val)
10. By S28: P.val · diag(a_sorted) · star P.val = diag(a)
    (since star P.val = permMatrix σ, conjugation gives diag(a_sorted ∘ σ⁻¹) = diag(a))

## Substantive content shipped

  * `symmetric_balanced_commutator_diagonal_real_full` — the FULL DIAGONAL CASE
    discharge of S.3 d≥3 PROPER.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 d≥3 PROPER (final assembly
for diagonal case; spectral theorem lift to arbitrary Hermitian follows).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSymmetricDischarge
import SKEFTHawking.FKLW.GenericSUdDecreasingSortPartialSums
import SKEFTHawking.FKLW.GenericSUdUnitaryConjugationInvariance
import SKEFTHawking.FKLW.GenericSUdPermutationConjugation
import SKEFTHawking.FKLW.GenericSUdPermutationDiagonal
import SKEFTHawking.FKLW.GenericSUdPartialSumBridge
import SKEFTHawking.FKLW.GenericSUdRangeFilterBridge

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Helper: real coerced sum equals zero -/

/-- **Permutation preserves real sum**: `∑ k, (a (σ k) : ℂ) = ∑ k, (a k : ℂ)`. -/
theorem sum_coerce_perm_eq {n : ℕ} (a : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    (∑ k, (a (σ k) : ℂ)) = ∑ k, (a k : ℂ) := by
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

/-! ## 2. MAIN THEOREM: full diagonal discharge for ANY traceless real H

For arbitrary traceless `a : Fin (n + 2) → ℝ`, the symmetric balanced
commutator equation `F · G − G · F = -iθ · diag(a)` is dischargeable
with Hermitian-traceless F, G. -/

/-- **FULL DIAGONAL DISCHARGE of S.3 d≥3 PROPER**: for ARBITRARY traceless
real `a : Fin (n + 2) → ℝ` (no partial-sums hypothesis), there exist
Hermitian-traceless F, G satisfying

  `F · G − G · F = -((θ : ℂ) · Complex.I) • Matrix.diagonal (a coerced to ℂ)`

for any θ ∈ [0, 1].

Proof: sort eigenvalues decreasingly (σ = Tuple.sort (-a)), apply Session 24's
discharge to the sorted version (which has non-negative partial sums by S25
+ S29 + S30 bridging), then conjugate by permMatrix σ⁻¹ (unitary by S27) to
recover the discharge for the original diagonal via S26 + S28. -/
theorem symmetric_balanced_commutator_diagonal_real_full {n : ℕ}
    (a : Fin (n + 2) → ℝ)
    (h_tr_real : (∑ k, a k) = 0)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) •
        Matrix.diagonal (fun k => (a k : ℂ)) := by
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
  -- Step 6: Apply S24 to a_sorted.
  obtain ⟨F', G', hF'_herm, hG'_herm, hF'_tr, hG'_tr, hcomm'⟩ :=
    symmetric_balanced_commutator_diagonal_nonneg_partials
      a_sorted h_tr_sorted_complex h_nn_pSC h_im_pSC θ hθ_nn hθ_le_one
  -- Step 7: Permutation matrix P = permMatrix σ⁻¹.
  let P := permMatrixAsUnitary (σ⁻¹ : Equiv.Perm (Fin (n + 2)))
  -- Step 8: Define F = P.val · F' · star P.val, G similar.
  refine ⟨P.val * F' * star P.val, P.val * G' * star P.val, ?_, ?_, ?_, ?_, ?_⟩
  -- F Hermitian (by S26)
  · exact unitary_group_conjugation_isHermitian P F' hF'_herm
  -- G Hermitian
  · exact unitary_group_conjugation_isHermitian P G' hG'_herm
  -- F traceless
  · exact unitary_group_conjugation_traceless P F' hF'_tr
  -- G traceless
  · exact unitary_group_conjugation_traceless P G' hG'_tr
  -- Commutator identity: F · G − G · F = -iθ · diag(a)
  · -- Apply S26 with scaled commutator
    have h_smul_comm := unitary_group_conjugation_smul_commutator_invariance
      P F' G' (Matrix.diagonal (fun k => (a_sorted k : ℂ)))
      (-((θ : ℂ) * Complex.I)) hcomm'
    rw [h_smul_comm]
    -- Goal: -(θ · i) • (P.val · diag(a_sorted) · star P.val) = -(θ · i) • diag(a)
    congr 1
    -- Need: P.val · diag(a_sorted) · star P.val = diag(a)
    -- P.val = permMatrix σ⁻¹, star P.val = permMatrix σ (via S27's _star)
    show Equiv.Perm.permMatrix ℂ σ⁻¹ * Matrix.diagonal (fun k => (a_sorted k : ℂ)) *
         star (Equiv.Perm.permMatrix ℂ σ⁻¹) = Matrix.diagonal (fun k => (a k : ℂ))
    rw [star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    -- Goal: permMatrix σ⁻¹ · diag(a_sorted) · permMatrix (σ⁻¹)⁻¹ = diag(a)
    -- By S28 with τ = σ⁻¹: permMatrix σ⁻¹ · diag(a_sorted) · permMatrix (σ⁻¹)⁻¹
    --                     = diag(a_sorted ∘ σ⁻¹) = diag(a ∘ σ ∘ σ⁻¹) = diag(a)
    rw [permMatrix_mul_diagonal_mul_permMatrix_inv σ⁻¹
        (fun k => (a_sorted k : ℂ))]
    congr 1
    funext k
    -- Goal: ((fun k => (a_sorted k : ℂ)) ∘ σ⁻¹) k = (a k : ℂ)
    show (a_sorted (σ⁻¹ k) : ℂ) = (a k : ℂ)
    show (a (σ (σ⁻¹ k)) : ℂ) = (a k : ℂ)
    have : σ (σ⁻¹ k) = k := by simp
    rw [this]

end SKEFTHawking.FKLW.GenericSUd
