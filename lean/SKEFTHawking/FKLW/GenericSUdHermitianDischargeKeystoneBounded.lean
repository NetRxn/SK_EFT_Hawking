/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Concrete `K_F·√(θ/2)` bounded Hermitian keystone

Composes Session 80's explicit-∑√ bounded Hermitian discharge with the
spectral partial-sum analysis (Gershgorin eigenvalue bound + partial-sum
bound + γ-sum decomposition) to give the **concrete** linftyOp norm bound

  `‖F‖ ≤ (n+2)²·(n+1)·√(n+2) · √(θ/2)`  (and mirror for G)

for any Hermitian-traceless `H` with `‖H‖ ≤ 1` and `θ ∈ [0, 1]`. This is the
exact `K_F·√(θ/2)` shape needed by `DnStepFG_sud_F_norm_bound_predicate`
(with `K_F = (n+2)²·(n+1)·√(n+2)`).

## Bound derivation

For the eigenvalues `a = h_herm.eigenvalues` (sorted descending via
`Tuple.sort (-a)`):
  * Gershgorin (Session 73): `|a k| ≤ ‖H‖ ≤ 1`.
  * Each sorted partial sum `b'_p ≤ (n+2)·1 = (n+2)` (Session 74, ≤ card·max).
  * Sorted partial sums are non-negative (Session 25, non-increasing traceless).
  * γ-sum bound (Session 72): `∑_p √(θ·b'_p/2) ≤ √(θ/2)·(n+1)·√(n+2)`.
  * Session 80: `‖F‖ ≤ (n+2)²·∑_p √(θ·b'_p/2) ≤ (n+2)²·√(θ/2)·(n+1)·√(n+2)`.

## Substantive content shipped

  * `sorted_nonneg_sqrt_sum_le` — for non-increasing traceless `c` with
    `|c k| ≤ 1`, `∑_p √(θ·(partialSumCoeff c p).re/2) ≤ √(θ/2)·(n+1)·√(n+2)`.
  * `symmetric_balanced_commutator_hermitian_unconditional_bounded` — the
    keystone with concrete `K_F·√(θ/2)` linftyOp bound.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — concrete K_F·√(θ/2)
bounded keystone (discharges DnStepFG_sud_F_norm_bound_predicate's bound shape).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeBoundedExplicit
import SKEFTHawking.FKLW.GenericSUdDecreasingSortPartialSums
import SKEFTHawking.FKLW.GenericSUdPartialSumBridge
import SKEFTHawking.FKLW.GenericSUdRangeFilterBridge
import SKEFTHawking.FKLW.GenericSUdGammaSumDecomp
import SKEFTHawking.FKLW.GenericSUdEigenvalueLinftyBound

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Generic ∑√ bound for a non-increasing traceless bounded sequence -/

/-- **∑√ bound for a non-increasing traceless bounded sequence**: for
`c : Fin (n+2) → ℝ` non-increasing, traceless, with `|c k| ≤ 1`,

  `∑_p √(θ·(partialSumCoeff (c coerced) p).re/2) ≤ √(θ/2)·((n+1)·√(n+2))`.

Composes Session 25 (non-increasing-traceless partial sums ≥ 0), Session 74
(partial sum ≤ card·max), and Session 72 (`gamma_sum_bound`). -/
lemma sorted_nonneg_sqrt_sum_le {n : ℕ} (c : Fin (n + 2) → ℝ)
    (h_dec : ∀ i j : Fin (n + 2), i ≤ j → c j ≤ c i)
    (h_tr : (∑ k, c k) = 0) (h_abs : ∀ k, |c k| ≤ 1)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∑ p : Fin (n + 1), Real.sqrt (θ *
      (partialSumCoeff (fun k => (c k : ℂ)) p).re / 2))
    ≤ Real.sqrt (θ / 2) * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)) := by
  -- partial sums are non-negative
  have h_nn_full : ∀ k : Fin (n + 2),
      0 ≤ ∑ j ∈ (Finset.univ : Finset (Fin (n + 2))).filter (· ≤ k), c j :=
    partial_sums_nonneg_of_decreasing_traceless c h_dec h_tr
  -- partialSumCoeff real part = filtered finset sum
  have hb_eq : ∀ p : Fin (n + 1),
      (partialSumCoeff (fun k => (c k : ℂ)) p).re =
      ∑ j ∈ (Finset.univ : Finset (Fin (n + 2))).filter (· ≤ p.castSucc), c j := by
    intro p
    rw [partialSumCoeff_real_re_eq_finset_range_real_sum c p,
        sum_range_eq_sum_filter_le_castSucc c p]
  -- non-negativity of b_p
  have hb_nn : ∀ p ∈ (Finset.univ : Finset (Fin (n + 1))),
      0 ≤ (partialSumCoeff (fun k => (c k : ℂ)) p).re := by
    intro p _
    rw [hb_eq p]
    exact h_nn_full p.castSucc
  -- upper bound b_p ≤ n + 2
  have hb_le : ∀ p ∈ (Finset.univ : Finset (Fin (n + 1))),
      (partialSumCoeff (fun k => (c k : ℂ)) p).re ≤ ((n : ℝ) + 2) := by
    intro p _
    rw [hb_eq p]
    calc ∑ j ∈ (Finset.univ : Finset (Fin (n + 2))).filter (· ≤ p.castSucc), c j
        ≤ (((Finset.univ : Finset (Fin (n + 2))).filter (· ≤ p.castSucc)).card : ℝ) * 1 :=
          partial_sum_le_card_mul_of_abs _ c 1 (fun j _ => h_abs j)
      _ ≤ ((n : ℝ) + 2) := by
          rw [mul_one]
          have h_le : ((Finset.univ : Finset (Fin (n + 2))).filter (· ≤ p.castSucc)).card
              ≤ n + 2 := by
            calc ((Finset.univ : Finset (Fin (n + 2))).filter (· ≤ p.castSucc)).card
                ≤ (Finset.univ : Finset (Fin (n + 2))).card := Finset.card_filter_le _ _
              _ = n + 2 := by rw [Finset.card_univ, Fintype.card_fin]
          calc (((Finset.univ : Finset (Fin (n + 2))).filter (· ≤ p.castSucc)).card : ℝ)
              ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast h_le
            _ = (n : ℝ) + 2 := by push_cast; ring
  -- apply gamma_sum_bound
  have h := gamma_sum_bound (Finset.univ : Finset (Fin (n + 1))) θ
      (fun p => (partialSumCoeff (fun k => (c k : ℂ)) p).re) ((n : ℝ) + 2) hθ hb_nn hb_le
  rw [Finset.card_univ, Fintype.card_fin,
      show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 from by push_cast; ring] at h
  exact h

/-! ## 2. Concrete K_F·√(θ/2) bounded keystone -/

/-- **Concrete bounded Hermitian keystone**: for ANY Hermitian-traceless `H`
with `‖H‖ ≤ 1` and `θ ∈ [0, 1]`, there exist Hermitian-traceless F, G with

  `F · G − G · F = -((θ : ℂ) · Complex.I) • H`

AND concrete linftyOp norm bounds

  `‖F‖ ≤ (n+2)²·(n+1)·√(n+2) · √(θ/2)`  (and mirror for G).

This is the `K_F·√(θ/2)` form (with `K_F = (n+2)²·(n+1)·√(n+2)`) consumed by
`DnStepFG_sud_F_norm_bound_predicate`. Composes Session 80 (explicit-∑√ bound)
with the spectral partial-sum analysis: Gershgorin (Session 73) bounds the
eigenvalues by `‖H‖ ≤ 1`, then `sorted_nonneg_sqrt_sum_le` bounds the ∑√. -/
theorem symmetric_balanced_commutator_hermitian_unconditional_bounded {n : ℕ}
    (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (h_herm : H.IsHermitian) (h_tr : H.trace = 0) (h_norm : ‖H‖ ≤ 1)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H ∧
      ‖F‖ ≤ ((n + 2 : ℕ) : ℝ)^2 * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)) *
        Real.sqrt (θ / 2) ∧
      ‖G‖ ≤ ((n + 2 : ℕ) : ℝ)^2 * (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)) *
        Real.sqrt (θ / 2) := by
  -- Spectral decomposition (mirror of the unbounded keystone).
  have h_spec : H = h_herm.eigenvectorUnitary.val *
      Matrix.diagonal (fun k => ((h_herm.eigenvalues k : ℝ) : ℂ)) *
      star h_herm.eigenvectorUnitary.val := by
    have h_st := h_herm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h_st
    convert h_st
  -- Eigenvalues sum to zero.
  have h_tr_real : (∑ k, h_herm.eigenvalues k) = 0 := by
    have h_diag_tr : (Matrix.diagonal (fun k => ((h_herm.eigenvalues k : ℝ) : ℂ))).trace = 0 := by
      have h_inv : (Matrix.diagonal (fun k => ((h_herm.eigenvalues k : ℝ) : ℂ))).trace =
          (h_herm.eigenvectorUnitary.val *
            Matrix.diagonal (fun k => ((h_herm.eigenvalues k : ℝ) : ℂ)) *
            star h_herm.eigenvectorUnitary.val).trace := by
        rw [unitary_group_conjugation_trace_invariance h_herm.eigenvectorUnitary]
      rw [h_inv, ← h_spec]
      exact h_tr
    have h_tr_sum : (∑ k, ((h_herm.eigenvalues k : ℝ) : ℂ)) = 0 := by
      rw [Matrix.trace_diagonal] at h_diag_tr
      exact h_diag_tr
    exact (real_sum_coerce_eq_zero_iff h_herm.eigenvalues).mp h_tr_sum
  -- Apply Session 80's explicit-∑√ bounded discharge.
  obtain ⟨F, G, hF_herm, hG_herm, hF_tr, hG_tr, hcomm, hF_bound, hG_bound⟩ :=
    symmetric_balanced_commutator_hermitian_via_spectral_bounded_explicit H h_tr
      h_herm.eigenvectorUnitary h_herm.eigenvalues h_spec θ hθ_nn hθ_le_one
  -- Abbreviate eigenvalues + sort permutation; fold into hF_bound, hG_bound.
  set a : Fin (n + 2) → ℝ := h_herm.eigenvalues with ha_def
  set σ : Equiv.Perm (Fin (n + 2)) := Tuple.sort (fun i => -(a i)) with hσ_def
  -- Properties of the sorted eigenvalues c = a ∘ σ.
  have h_mono : Monotone ((fun i => -(a i)) ∘ σ) := Tuple.monotone_sort _
  have h_dec : ∀ i j : Fin (n + 2), i ≤ j → a (σ j) ≤ a (σ i) := by
    intro i j hij
    have h_neg := h_mono hij
    simp only [Function.comp_apply] at h_neg
    linarith
  have h_tr_c : (∑ k, a (σ k)) = 0 := by
    rw [Fintype.sum_equiv σ _ _ (fun _ => rfl)]
    exact h_tr_real
  have h_abs_a : ∀ k, |a k| ≤ 1 := by
    intro k
    rw [ha_def]
    exact le_trans (isHermitian_eigenvalue_abs_le_linftyOpNorm h_herm k) h_norm
  have h_abs_c : ∀ k, |a (σ k)| ≤ 1 := fun k => h_abs_a (σ k)
  -- ∑√ bound for the sorted eigenvalues.
  have h_inner := sorted_nonneg_sqrt_sum_le (fun k => a (σ k)) h_dec h_tr_c h_abs_c θ hθ_nn
  -- Assemble.
  refine ⟨F, G, hF_herm, hG_herm, hF_tr, hG_tr, hcomm, ?_, ?_⟩
  · refine le_trans hF_bound (le_trans (mul_le_mul_of_nonneg_left h_inner (by positivity))
      (le_of_eq ?_))
    ring
  · refine le_trans hG_bound (le_trans (mul_le_mul_of_nonneg_left h_inner (by positivity))
      (le_of_eq ?_))
    ring

end SKEFTHawking.FKLW.GenericSUd
