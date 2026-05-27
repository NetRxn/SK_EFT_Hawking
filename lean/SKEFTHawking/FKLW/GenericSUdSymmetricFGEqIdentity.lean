/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Symmetric F·G − G·F = -iθ · diag(a) identity

For SYMMETRIC F = Σ_p γ_p · σ_y(p.castSucc, p.succ),
G = Σ_p γ_p · σ_x(p.castSucc, p.succ) with `γ_p² = θ · b_p / 2` and
`b_p := partialSumCoeff a p`:

  F · G − G · F = -(θ · i) • Matrix.diagonal a

provided `a : Fin (n + 2) → ℂ` is traceless (`∑ a = 0`).

**This is the algebraic core of the symmetric F=αG balanced commutator
construction at SU(d).** Composes:
  - Session 22: `F · G − G · F = Σ_p γ_p² · [σ_y(p), σ_x(p)]`
  - Session 11: `[σ_y(p), σ_x(p)] = -2i · σ_z(p)`
  - Session 15: `Matrix.diagonal a = Σ_p b_p · σ_z(p)` (for traceless a)

Chaining gives the −iθ · diag(a) identity.

## Substantive content shipped

  * `symmetric_F_G_eq_neg_iθ_diagonal` — the main algebraic identity.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (full algebraic
combination for symmetric F=αG construction).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock
import SKEFTHawking.FKLW.GenericSUdDiagonalDecomp
import SKEFTHawking.FKLW.GenericSUdSymmetricCommFGreduction

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The algebraic identity F · G − G · F = -iθ · diag(a)

Composes the three substrate pieces (S22 + S11 + S15) via direct
substitution and scalar arithmetic. -/

/-- **Helper**: `(p.castSucc : Fin (n + 2)) ≠ p.succ` for any `p : Fin (n + 1)`. -/
private lemma castSucc_ne_succ {n : ℕ} (p : Fin (n + 1)) :
    (p.castSucc : Fin (n + 2)) ≠ p.succ := by
  intro h
  have := congr_arg Fin.val h
  simp [Fin.coe_castSucc, Fin.val_succ] at this

/-- **Symmetric F · G − G · F identity (intermediate form, generic `b`)**:
For arbitrary `γ : Fin (n + 1) → ℂ` and `b : Fin (n + 1) → ℂ` satisfying
`γ p ² = θ · b p / 2`,

  `F · G − G · F = -(θ · i) • Σ_p b_p · σ_z(p.castSucc, p.succ)`

(independent of `a` — `a` enters only when `b_p = partialSumCoeff a p`
in the next theorem). -/
theorem symmetric_F_G_comm_eq_neg_iθ_sum_sigmaZ {n : ℕ}
    (θ : ℂ) (γ : Fin (n + 1) → ℂ) (b : Fin (n + 1) → ℂ)
    (h_γ_sq : ∀ p, (γ p)^2 = θ * b p / 2) :
    (∑ p : Fin (n + 1), γ p • sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ) *
      (∑ q : Fin (n + 1), γ q • sigmaXBlock q.castSucc q.succ) -
    (∑ q : Fin (n + 1), γ q • sigmaXBlock q.castSucc q.succ) *
      (∑ p : Fin (n + 1), γ p • sigmaYBlock p.castSucc p.succ) =
    -(θ * Complex.I) •
      ∑ p : Fin (n + 1), b p •
        sigmaZBlock (p.castSucc : Fin (n + 2)) p.succ := by
  -- Step 1: apply S22 to reduce LHS to Σ_p γ_p² · [σ_y(p), σ_x(p)]
  rw [symmetric_F_G_comm_eq_same_pair_sum γ]
  -- Step 2: substitute [σ_y(p), σ_x(p)] = -2i · σ_z(p) (Session 11) +
  --         use γ_p² = θ·b_p/2 hypothesis
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  -- Goal: (γ p * γ p) • [σ_y(p), σ_x(p)] = -(θ · i) • (b p • σ_z(p))
  rw [sigmaY_sigmaX_commutator (castSucc_ne_succ p)]
  -- Goal: (γ p * γ p) • ((-2 · i) • σ_z(p)) = -(θ · i) • (b p • σ_z(p))
  rw [smul_smul, smul_smul]
  -- Goal: (γ p * γ p * (-2 · i)) • σ_z(p) = (-(θ · i) * b p) • σ_z(p)
  congr 1
  -- Goal: γ p * γ p * (-2 · i) = -(θ · i) * b p
  -- Use γ p * γ p = (γ p)^2 = θ * b p / 2.
  have h_sq : γ p * γ p = θ * b p / 2 := by rw [← sq]; exact h_γ_sq p
  rw [h_sq]
  ring

/-- **MAIN ALGEBRAIC IDENTITY** — symmetric F · G − G · F = -iθ · diag(a):

For SYMMETRIC F = Σ_p γ_p · σ_y(p), G = Σ_p γ_p · σ_x(p) with
`γ p ² = θ · (partialSumCoeff a p) / 2` and `a` traceless,

  `F · G − G · F = -(θ · i) • Matrix.diagonal a`

This is the algebraic heart of the symmetric F=αG balanced commutator
construction at SU(d): for the right choice of γ_p (proportional to
square-root of partial sums of a), the commutator equals -iθ · diag(a). -/
theorem symmetric_F_G_eq_neg_iθ_diagonal {n : ℕ}
    (a : Fin (n + 2) → ℂ) (h_tr : ∑ k, a k = 0)
    (θ : ℂ) (γ : Fin (n + 1) → ℂ)
    (h_γ_sq : ∀ p, (γ p)^2 = θ * (partialSumCoeff a p) / 2) :
    (∑ p : Fin (n + 1), γ p • sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ) *
      (∑ q : Fin (n + 1), γ q • sigmaXBlock q.castSucc q.succ) -
    (∑ q : Fin (n + 1), γ q • sigmaXBlock q.castSucc q.succ) *
      (∑ p : Fin (n + 1), γ p • sigmaYBlock p.castSucc p.succ) =
    -(θ * Complex.I) • Matrix.diagonal a := by
  rw [symmetric_F_G_comm_eq_neg_iθ_sum_sigmaZ θ γ (partialSumCoeff a) h_γ_sq]
  -- Goal: -(θ · i) • Σ_p (partialSumCoeff a p) • σ_z(p) = -(θ · i) • diag(a)
  rw [← diagonal_traceless_eq_sum_sigmaZ_pattern a h_tr]

end SKEFTHawking.FKLW.GenericSUd
