/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — γ-sum algebraic decomposition

For the symmetric F=αG construction, `γ_p = √(θ·b_p/2)` (with `b_p ≥ 0`
the non-negative partial sums). The inner-witness norm bound
`‖F_inner‖ ≤ ∑_p |γ_p|` (Session 70/71) factors as:

  `∑_p |γ_p| = ∑_p √(θ·b_p/2) = √(θ/2) · ∑_p √(b_p)`

This module ships that algebraic decomposition + the consequent bound
`∑_p √(b_p) ≤ (card s) · √(B)` when each `b_p ≤ B`, giving
`∑_p |γ_p| ≤ √(θ/2) · (card s) · √(B)` — i.e., `K_inner = (card s)·√B`.

## Substantive content shipped

  * `sqrt_theta_b_div_two_eq` — `√(θ·b/2) = √(θ/2)·√b` for θ, b ≥ 0
  * `sum_sqrt_theta_b_div_two_eq` — `∑_p √(θ·b_p/2) = √(θ/2)·∑_p √b_p`
  * `sum_sqrt_le_card_mul_sqrt` — `∑_p √(b_p) ≤ (card s)·√B` when b_p ≤ B
  * `gamma_sum_bound` — `∑_p √(θ·b_p/2) ≤ √(θ/2)·(card s)·√B`

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — γ-sum decomposition
(F_inner norm bound, K_inner = (card s)·√B).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

/-- `√(θ·b/2) = √(θ/2)·√b` for θ, b ≥ 0. -/
lemma sqrt_theta_b_div_two_eq {θ b : ℝ} (hθ : 0 ≤ θ) (hb : 0 ≤ b) :
    Real.sqrt (θ * b / 2) = Real.sqrt (θ / 2) * Real.sqrt b := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  ring

/-- `∑_p √(θ·b_p/2) = √(θ/2)·∑_p √b_p` for θ ≥ 0 and b_p ≥ 0. -/
lemma sum_sqrt_theta_b_div_two_eq {ι : Type*} (s : Finset ι) (θ : ℝ)
    (b : ι → ℝ) (hθ : 0 ≤ θ) (hb : ∀ p ∈ s, 0 ≤ b p) :
    ∑ p ∈ s, Real.sqrt (θ * b p / 2) =
      Real.sqrt (θ / 2) * ∑ p ∈ s, Real.sqrt (b p) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact sqrt_theta_b_div_two_eq hθ (hb p hp)

/-- `∑_p √(b_p) ≤ (card s)·√B` when each `b_p ≤ B` (and `0 ≤ b_p`). -/
lemma sum_sqrt_le_card_mul_sqrt {ι : Type*} (s : Finset ι)
    (b : ι → ℝ) (B : ℝ) (hb_nn : ∀ p ∈ s, 0 ≤ b p) (hb_le : ∀ p ∈ s, b p ≤ B) :
    ∑ p ∈ s, Real.sqrt (b p) ≤ (s.card : ℝ) * Real.sqrt B := by
  calc ∑ p ∈ s, Real.sqrt (b p)
      ≤ ∑ _p ∈ s, Real.sqrt B := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.sqrt_le_sqrt (hb_le p hp)
    _ = (s.card : ℝ) * Real.sqrt B := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **γ-sum bound**: `∑_p √(θ·b_p/2) ≤ √(θ/2)·(card s)·√B`. -/
lemma gamma_sum_bound {ι : Type*} (s : Finset ι) (θ : ℝ)
    (b : ι → ℝ) (B : ℝ) (hθ : 0 ≤ θ)
    (hb_nn : ∀ p ∈ s, 0 ≤ b p) (hb_le : ∀ p ∈ s, b p ≤ B) :
    ∑ p ∈ s, Real.sqrt (θ * b p / 2) ≤
      Real.sqrt (θ / 2) * ((s.card : ℝ) * Real.sqrt B) := by
  rw [sum_sqrt_theta_b_div_two_eq s θ b hθ hb_nn]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact sum_sqrt_le_card_mul_sqrt s b B hb_nn hb_le

end SKEFTHawking.FKLW.GenericSUd
