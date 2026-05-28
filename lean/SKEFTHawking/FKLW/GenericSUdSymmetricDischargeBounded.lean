/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Symmetric diagonal discharge WITH norm bound (re-thread)

Strengthens Session 24's `symmetric_balanced_commutator_diagonal_nonneg_partials`
to ALSO return the explicit linftyOp norm bound on F, G:

  `‖F‖ ≤ ∑_p √(θ·(b_p).re/2)` and `‖G‖ ≤ ∑_p √(θ·(b_p).re/2)`

where `b_p = partialSumCoeff (a coerced) p`. Since Session 24's witnesses
are the EXPLICIT sums `F = ∑_p γ_p·σ_y(p.castSucc, p.succ)` (and σ_x for G),
the norm bound follows directly from Session 70's
`sigmaYBlock_sum_linftyOpNorm_le`.

This is the re-thread that exposes the inner-witness norm bound for the
super-quad bound F/G-norm ingredient (the missing assembly piece).

## Substantive content shipped

  * `symmetric_balanced_commutator_diagonal_nonneg_partials_bounded` —
    Session 24's discharge + `‖F‖, ‖G‖ ≤ ∑_p √(θ·(b_p).re/2)`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — bounded diagonal discharge
(F_inner norm bound re-thread).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSymmetricDischarge
import SKEFTHawking.FKLW.GenericSUdSigmaYSumNormBound

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Bounded symmetric diagonal discharge** — Session 24's discharge plus
explicit linftyOp norm bounds on F, G.

For traceless `a : Fin (n+2) → ℝ` with non-negative real partial sums and
zero imaginary parts, `∃ F G` Hermitian-traceless with the balanced
commutator identity AND
  `‖F‖ ≤ ∑_p √(θ·(partialSumCoeff (a coerced) p).re / 2)`
  `‖G‖ ≤ ∑_p √(θ·(partialSumCoeff (a coerced) p).re / 2)`.

The witnesses are the explicit `F = ∑_p γ_p·σ_y(p.castSucc, p.succ)`
(Session 24), so the norm bound is Session 70's `sigmaYBlock_sum_linftyOpNorm_le`. -/
theorem symmetric_balanced_commutator_diagonal_nonneg_partials_bounded {n : ℕ}
    (a : Fin (n + 2) → ℝ)
    (h_tr : (∑ k : Fin (n + 2), (a k : ℂ)) = 0)
    (h_nn : ∀ p : Fin (n + 1),
      0 ≤ (partialSumCoeff (fun k => (a k : ℂ)) p).re)
    (h_im : ∀ p : Fin (n + 1),
      (partialSumCoeff (fun k => (a k : ℂ)) p).im = 0)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) •
        Matrix.diagonal (fun k => (a k : ℂ)) ∧
      ‖F‖ ≤ ∑ p : Fin (n + 1),
        Real.sqrt (θ * (partialSumCoeff (fun k => (a k : ℂ)) p).re / 2) ∧
      ‖G‖ ≤ ∑ p : Fin (n + 1),
        Real.sqrt (θ * (partialSumCoeff (fun k => (a k : ℂ)) p).re / 2) := by
  set b : Fin (n + 1) → ℂ := fun p => partialSumCoeff (fun k => (a k : ℂ)) p with hb_def
  set γ_real : Fin (n + 1) → ℝ := fun p => Real.sqrt (θ * (b p).re / 2) with hγr_def
  -- Index maps for the σ-block sums.
  have h_ne : ∀ p ∈ (Finset.univ : Finset (Fin (n + 1))),
      (p.castSucc : Fin (n + 2)) ≠ p.succ := by
    intro p _
    exact ne_of_lt Fin.castSucc_lt_succ
  -- Get Session 24's discharge for the commutator + Hermitian + trace conjuncts.
  obtain ⟨F, G, hF_herm, hG_herm, hF_tr, hG_tr, hcomm⟩ :=
    symmetric_balanced_commutator_diagonal_nonneg_partials a h_tr h_nn h_im θ hθ_nn hθ_le_one
  -- The witnesses F, G from Session 24 are NOT exposed here. Instead, re-build
  -- the explicit witnesses and show they coincide via the same construction.
  -- We use the explicit form directly: F_explicit = ∑ γ_real p • σ_y(...).
  refine ⟨∑ p : Fin (n + 1), ((γ_real p : ℂ)) •
            sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ,
          ∑ p : Fin (n + 1), ((γ_real p : ℂ)) •
            sigmaXBlock (p.castSucc : Fin (n + 2)) p.succ,
          sigmaY_sum_isHermitian γ_real, sigmaX_sum_isHermitian γ_real,
          sigmaY_sum_trace_zero (fun p => (γ_real p : ℂ)),
          sigmaX_sum_trace_zero (fun p => (γ_real p : ℂ)), ?_, ?_, ?_⟩
  · -- Commutator identity: re-derive via Session 23 (same as Session 24's proof).
    have h_γ_sq : ∀ p, ((γ_real p : ℂ))^2 = (θ : ℂ) * b p / 2 := by
      intro p
      have h_nn_p : 0 ≤ (b p).re := h_nn p
      have h_θ_b_nn : 0 ≤ θ * (b p).re / 2 := by
        have h_θ_b : 0 ≤ θ * (b p).re := mul_nonneg hθ_nn h_nn_p
        linarith
      show ((Real.sqrt (θ * (b p).re / 2) : ℝ) : ℂ)^2 = (θ : ℂ) * b p / 2
      rw [show ((Real.sqrt (θ * (b p).re / 2) : ℝ) : ℂ)^2 =
          ((Real.sqrt (θ * (b p).re / 2))^2 : ℝ) from by push_cast; ring]
      rw [Real.sq_sqrt h_θ_b_nn]
      have h_b_real : b p = ((b p).re : ℂ) := by
        apply Complex.ext
        · rw [Complex.ofReal_re]
        · rw [Complex.ofReal_im]; exact h_im p
      rw [h_b_real]
      simp [Complex.ofReal_re]
    exact symmetric_F_G_eq_neg_iθ_diagonal (fun k => (a k : ℂ)) h_tr (θ : ℂ)
      (fun p => (γ_real p : ℂ)) h_γ_sq
  · -- ‖F‖ bound via Session 70.
    have h := sigmaYBlock_sum_linftyOpNorm_le (Finset.univ : Finset (Fin (n + 1)))
      γ_real (fun p => (p.castSucc : Fin (n + 2))) (fun p => p.succ) h_ne
    refine le_trans h (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro p _
    rw [hγr_def]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  · -- ‖G‖ bound via Session 70 (σ_x).
    have h := sigmaXBlock_sum_linftyOpNorm_le (Finset.univ : Finset (Fin (n + 1)))
      γ_real (fun p => (p.castSucc : Fin (n + 2))) (fun p => p.succ) h_ne
    refine le_trans h (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro p _
    rw [hγr_def]
    exact abs_of_nonneg (Real.sqrt_nonneg _)

end SKEFTHawking.FKLW.GenericSUd
