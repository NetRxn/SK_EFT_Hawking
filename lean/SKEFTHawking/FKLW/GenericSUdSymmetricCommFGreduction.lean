/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Symmetric F·G − G·F = Σ γ_p² · [σ_y(p), σ_x(p)]

For SYMMETRIC `F := ∑_p γ_p · σ_y(p.castSucc, p.succ)` and
`G := ∑_p γ_p · σ_x(p.castSucc, p.succ)` (SAME coefficient γ_p in F and G),
the commutator reduces to ONLY the same-pair (diagonal) contributions:

  `F · G − G · F = Σ_p (γ_p)² · [σ_y(p.castSucc, p.succ), σ_x(p.castSucc, p.succ)]`

This is the **double-sum reduction theorem** — the key step in the
Aharonov-Arad balanced commutator construction at SU(d). The off-diagonal
cross-terms `(p ≠ q)` vanish via Session 19's pair-swap cancellation
lifted to γ-weighted form (Session 20) and combined with Session 21's
generic antisymmetric off-diag sum vanishing.

## Substantive content shipped

  * `symmetric_F_G_comm_eq_same_pair_sum` — the main double-sum reduction.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (symmetric F=αG
commutator reduction; combines S19 + S20 + S21).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock
import SKEFTHawking.FKLW.GenericSUdSigmaPairSwap
import SKEFTHawking.FKLW.GenericSUdSymmetricCommReduction
import SKEFTHawking.FKLW.GenericSUdAntisymOffDiag

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Double-sum expansion of F · G − G · F

For F = Σ_p γ_p · σ_y(p) and G = Σ_q γ_q · σ_x(q):

  F · G = Σ_p Σ_q (γ_p · γ_q) • (σ_y(p) · σ_x(q))
  G · F = Σ_p Σ_q (γ_p · γ_q) • (σ_x(q) · σ_y(p))   [after Fubini-renaming]

Hence:

  F · G − G · F = Σ_p Σ_q (γ_p · γ_q) • (σ_y(p) · σ_x(q) − σ_x(q) · σ_y(p))
                = Σ_p Σ_q (γ_p · γ_q) • [σ_y(p), σ_x(q)]    (defining notation)

This expansion uses `Finset.sum_mul_sum` + smul/mul distribution + Matrix
ring structure. -/

/-- **Double-sum expansion of `F · G − G · F`**. -/
theorem symmetric_F_G_comm_double_sum {n : ℕ} (γ : Fin (n + 1) → ℂ) :
    (∑ p : Fin (n + 1), γ p • sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ) *
      (∑ q : Fin (n + 1), γ q • sigmaXBlock q.castSucc q.succ) -
    (∑ q : Fin (n + 1), γ q • sigmaXBlock q.castSucc q.succ) *
      (∑ p : Fin (n + 1), γ p • sigmaYBlock p.castSucc p.succ) =
    ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), (γ p * γ q) •
      (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ *
         sigmaXBlock q.castSucc q.succ -
       sigmaXBlock q.castSucc q.succ *
         sigmaYBlock p.castSucc p.succ) := by
  -- Helper: expand F · G as double sum.
  have h_FG : (∑ p : Fin (n + 1), γ p • sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ) *
              (∑ q : Fin (n + 1), γ q • sigmaXBlock q.castSucc q.succ) =
              ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), (γ p * γ q) •
                (sigmaYBlock p.castSucc p.succ * sigmaXBlock q.castSucc q.succ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  -- Helper: expand G · F as double sum (with index labels matching after Fubini).
  have h_GF : (∑ q : Fin (n + 1), γ q • sigmaXBlock (q.castSucc : Fin (n + 2)) q.succ) *
              (∑ p : Fin (n + 1), γ p • sigmaYBlock p.castSucc p.succ) =
              ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), (γ p * γ q) •
                (sigmaXBlock q.castSucc q.succ * sigmaYBlock p.castSucc p.succ) := by
    rw [Finset.sum_mul]
    -- After Finset.sum_mul: ∑_q (γ_q • σ_x(q)) * (∑_p ...)
    -- We need ∑_p ∑_q (γ_p γ_q) • (σ_x(q) σ_y(p)). Use sum_comm to swap outer index.
    rw [show (∑ q : Fin (n + 1),
          (γ q • sigmaXBlock (q.castSucc : Fin (n + 2)) q.succ) *
          ∑ p : Fin (n + 1), γ p • sigmaYBlock p.castSucc p.succ) =
        ∑ q : Fin (n + 1), ∑ p : Fin (n + 1), (γ p * γ q) •
          (sigmaXBlock q.castSucc q.succ * sigmaYBlock p.castSucc p.succ) from by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm (γ q) (γ p)]]
    rw [Finset.sum_comm]
  -- Subtract and combine.
  rw [h_FG, h_GF]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [← smul_sub]

/-! ## 2. The symmetric F · G − G · F reduction

Applying Session 21 (`sum_antisymmetric_off_diag_eq_zero`) with the
γ-weighted commutator `f p q := (γ_p γ_q) • [σ_y(p), σ_x(q)]` —
the antisymmetric hypothesis `f p q + f q p = 0` for `p ≠ q` holds
by Session 19 / Session 20 (`gamma_weighted_cross_pair_swap_cancel`). -/

/-- **MAIN REDUCTION THEOREM**: For SYMMETRIC F = Σ_p γ_p · σ_y(p), G = Σ_p γ_p · σ_x(p),

  `F · G − G · F = Σ_p (γ_p)² · [σ_y(p), σ_x(p)]`

via off-diagonal cross-term cancellation (Sessions 19 + 20 + 21). -/
theorem symmetric_F_G_comm_eq_same_pair_sum {n : ℕ} (γ : Fin (n + 1) → ℂ) :
    (∑ p : Fin (n + 1), γ p • sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ) *
      (∑ q : Fin (n + 1), γ q • sigmaXBlock q.castSucc q.succ) -
    (∑ q : Fin (n + 1), γ q • sigmaXBlock q.castSucc q.succ) *
      (∑ p : Fin (n + 1), γ p • sigmaYBlock p.castSucc p.succ) =
    ∑ p : Fin (n + 1), (γ p * γ p) •
      (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ *
         sigmaXBlock p.castSucc p.succ -
       sigmaXBlock p.castSucc p.succ *
         sigmaYBlock p.castSucc p.succ) := by
  rw [symmetric_F_G_comm_double_sum γ]
  -- Goal: ∑_p ∑_q f p q = ∑_p f p p
  -- where f p q := (γ_p γ_q) • (σ_y(p) σ_x(q) - σ_x(q) σ_y(p))
  -- Split into diagonal + off-diagonal via Finset.add_sum_erase.
  set f : Fin (n + 1) → Fin (n + 1) → Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
    fun p q => (γ p * γ q) •
      (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ * sigmaXBlock q.castSucc q.succ -
       sigmaXBlock q.castSucc q.succ * sigmaYBlock p.castSucc p.succ)
    with f_def
  show (∑ p, ∑ q, f p q) = ∑ p, f p p
  have h_split : (∑ p, ∑ q, f p q) =
      (∑ p, f p p) + ∑ p, ∑ q ∈ (Finset.univ : Finset (Fin (n + 1))).erase p, f p q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ p)).symm
  rw [h_split]
  -- Show the off-diagonal sum is 0 via Session 21 + Session 20.
  have h_offdiag : (∑ p, ∑ q ∈ (Finset.univ : Finset (Fin (n + 1))).erase p, f p q) = 0 := by
    apply sum_antisymmetric_off_diag_eq_zero
    intro p q h_pq
    -- Show f p q + f q p = 0 by S20.
    rw [f_def]
    exact gamma_weighted_cross_pair_swap_cancel' γ h_pq
  rw [h_offdiag, add_zero]

end SKEFTHawking.FKLW.GenericSUd
