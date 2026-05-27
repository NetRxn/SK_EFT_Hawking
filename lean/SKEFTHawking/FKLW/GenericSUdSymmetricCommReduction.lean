/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — γ-weighted cross-term pair-swap cancellation

For SYMMETRIC F = Σ_p γ_p · σ_y(p.castSucc, p.succ) and
G = Σ_p γ_p · σ_x(p.castSucc, p.succ) (SAME coefficient γ_p in F and G),
the γ-weighted commutator cross-terms cancel pairwise:

  `(γ_p γ_q) • [σ_y(p), σ_x(q)] + (γ_q γ_p) • [σ_y(q), σ_x(p)] = 0`

for any distinct `p ≠ q ∈ Fin (n + 1)`.

This is the **γ-weighted lift** of Session 19's pair-swap cancellation,
prepared for direct use in the double-sum reduction `F · G − G · F =
Σ_p γ_p² · [σ_y(p), σ_x(p)]` (Session 21).

## Substantive content shipped

  * `gamma_weighted_cross_pair_swap_cancel` — the γ-weighted pair-swap.
  * `gamma_weighted_same_pair_sum` — the γ-weighted same-pair sum
    (preparing for combination in Session 21).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (γ-weighted lift
of cross-term cancellation for symmetric F=αG construction).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock
import SKEFTHawking.FKLW.GenericSUdSigmaPairSwap

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. γ-weighted pair-swap cancellation

Lifting Session 19's `sigmaY_sigmaX_pair_swap_cancel` to a γ-weighted
form, factoring out the scalar coefficient `γ_p γ_q`. -/

/-- **γ-weighted cross-term pair-swap cancellation**: for distinct
`p ≠ q ∈ Fin (n + 1)` and any γ : Fin (n + 1) → ℂ,

  `(γ_p γ_q) • [σ_y(p), σ_x(q)] + (γ_p γ_q) • [σ_y(q), σ_x(p)] = 0`

Direct lift of Session 19 (`sigmaY_sigmaX_pair_swap_cancel`) using
scalar mult linearity. -/
theorem gamma_weighted_cross_pair_swap_cancel {n : ℕ} (γ : Fin (n + 1) → ℂ)
    {p q : Fin (n + 1)} (h_pq : p ≠ q) :
    (γ p * γ q) • (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ *
                    sigmaXBlock q.castSucc q.succ -
                  sigmaXBlock q.castSucc q.succ *
                    sigmaYBlock p.castSucc p.succ)
    + (γ p * γ q) • (sigmaYBlock q.castSucc q.succ *
                      sigmaXBlock p.castSucc p.succ -
                    sigmaXBlock p.castSucc p.succ *
                      sigmaYBlock q.castSucc q.succ) = 0 := by
  rw [← smul_add]
  rw [sigmaY_sigmaX_pair_swap_cancel h_pq]
  simp

/-- **γ-weighted pair-swap, swap form**: explicitly with `(γ_q * γ_p)`
on the second term (uses commutativity of complex multiplication). -/
theorem gamma_weighted_cross_pair_swap_cancel' {n : ℕ} (γ : Fin (n + 1) → ℂ)
    {p q : Fin (n + 1)} (h_pq : p ≠ q) :
    (γ p * γ q) • (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ *
                    sigmaXBlock q.castSucc q.succ -
                  sigmaXBlock q.castSucc q.succ *
                    sigmaYBlock p.castSucc p.succ)
    + (γ q * γ p) • (sigmaYBlock q.castSucc q.succ *
                      sigmaXBlock p.castSucc p.succ -
                    sigmaXBlock p.castSucc p.succ *
                      sigmaYBlock q.castSucc q.succ) = 0 := by
  rw [show γ q * γ p = γ p * γ q from mul_comm _ _]
  exact gamma_weighted_cross_pair_swap_cancel γ h_pq

/-! ## 2. Same-pair γ-weighted formula

For p : Fin (n + 1), the same-pair γ-weighted contribution is
`γ_p² · [σ_y(p), σ_x(p)] = γ_p² · (-2i · σ_z(p))`. -/

/-- **Same-pair γ-weighted commutator** at SU(d):
`(γ_p · γ_p) • [σ_y(p), σ_x(p)] = γ_p² · (-2i · σ_z(p))`. -/
theorem gamma_weighted_same_pair_eq {n : ℕ} (γ : Fin (n + 1) → ℂ)
    (p : Fin (n + 1)) :
    (γ p * γ p) • (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ *
                    sigmaXBlock p.castSucc p.succ -
                  sigmaXBlock p.castSucc p.succ *
                    sigmaYBlock p.castSucc p.succ) =
      ((γ p)^2 * (-2 * Complex.I)) • sigmaZBlock p.castSucc p.succ := by
  have h_ne : (p.castSucc : Fin (n + 2)) ≠ p.succ := by
    intro h
    have := congr_arg Fin.val h
    simp [Fin.coe_castSucc, Fin.val_succ] at this
  rw [sigmaY_sigmaX_commutator h_ne]
  -- (γ p * γ p) • ((-2 * Complex.I) • σ_z) = ((γ p)^2 * (-2 * Complex.I)) • σ_z
  rw [smul_smul]
  congr 1
  ring

/-! ## 3. Same-pair scaled by θ·b_p (substituting α_p² = θ·b_p/2)

When `γ_p² = θ · b_p / 2`, the same-pair contribution simplifies to
`-i·θ·b_p · σ_z(p)`. This is the form that feeds into the diagonal
decomposition lemma (Session 15) for the final `-iθ·H` form. -/

/-- **Same-pair contribution with α_p² = θ·b_p/2**: at the chosen
coefficient, the same-pair commutator equals `−i·θ·b_p · σ_z(p)`. -/
theorem same_pair_at_target_coeff {n : ℕ} (b : Fin (n + 1) → ℂ)
    (p : Fin (n + 1)) (θ : ℂ) :
    ((θ * b p / 2) * (-2 * Complex.I)) • sigmaZBlock (p.castSucc : Fin (n + 2)) p.succ =
      (-(θ * Complex.I * b p)) • sigmaZBlock p.castSucc p.succ := by
  congr 1
  ring

end SKEFTHawking.FKLW.GenericSUd
