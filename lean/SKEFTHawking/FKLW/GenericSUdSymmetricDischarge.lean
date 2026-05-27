/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Symmetric F=αG discharge (Hermitian/trace conjuncts)

For diagonal traceless `H = diag(a)` (a : Fin (n + 2) → ℝ, ∑ a = 0) with
all partial sums non-negative, the symmetric F=γσ_y, G=γσ_x construction
yields F, G ∈ Matrix (Fin (n+2)) (Fin (n+2)) ℂ that are:

  - Hermitian (both)
  - Traceless (both)
  - Satisfying [F, G] = -iθ · diag(a)

with γ_p := √(θ · b_p / 2) ∈ ℝ (well-defined since b_p ≥ 0).

This is the **packaged existence theorem** that combines Session 23's
algebraic identity (the F·G − G·F = -iθ · diag(a) calculation) with
explicit Hermitian + trace conjuncts.

## Substantive content shipped

  * `sigmaY_sum_isHermitian` — Hermiticity of `∑ γ_p · σ_y(p)` (real γ_p)
  * `sigmaX_sum_isHermitian` — Hermiticity of `∑ γ_p · σ_x(p)`
  * `sigmaY_sum_trace_zero` / `sigmaX_sum_trace_zero` — tracelessness
  * `symmetric_balanced_commutator_diagonal_nonneg_partials` — MAIN discharge

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (symmetric
discharge packaging — combines S23 algebraic identity with Hermitian/trace
conjuncts via real-coefficient lifting).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock
import SKEFTHawking.FKLW.GenericSUdDiagonalDecomp
import SKEFTHawking.FKLW.GenericSUdSymmetricFGEqIdentity

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Hermiticity of real-scaled σ-block sums

For γ : Fin (n + 1) → ℝ (real coefficients), the sum
`∑_p γ_p · σ_y(p.castSucc, p.succ)` is Hermitian. -/

/-- **`castSucc ≠ succ`** for any `p : Fin (n + 1)`. -/
private lemma castSucc_ne_succ_pub {n : ℕ} (p : Fin (n + 1)) :
    (p.castSucc : Fin (n + 2)) ≠ p.succ := by
  intro h
  have := congr_arg Fin.val h
  simp [Fin.coe_castSucc, Fin.val_succ] at this

/-- **`∑_p γ_p · σ_y(p)` is Hermitian** for real γ. -/
theorem sigmaY_sum_isHermitian {n : ℕ} (γ : Fin (n + 1) → ℝ) :
    (∑ p : Fin (n + 1), (γ p : ℂ) •
       sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ).IsHermitian := by
  show (∑ p, (γ p : ℂ) • sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ).conjTranspose =
       ∑ p, (γ p : ℂ) • sigmaYBlock p.castSucc p.succ
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.conjTranspose_smul]
  rw [show star ((γ p : ℝ) : ℂ) = ((γ p : ℝ) : ℂ) from by
    rw [Complex.star_def, Complex.conj_ofReal]]
  rw [show (sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ).conjTranspose =
        sigmaYBlock p.castSucc p.succ from sigmaYBlock_isHermitian (castSucc_ne_succ_pub p)]

/-- **`∑_p γ_p · σ_x(p)` is Hermitian** for real γ. -/
theorem sigmaX_sum_isHermitian {n : ℕ} (γ : Fin (n + 1) → ℝ) :
    (∑ p : Fin (n + 1), (γ p : ℂ) •
       sigmaXBlock (p.castSucc : Fin (n + 2)) p.succ).IsHermitian := by
  show (∑ p, (γ p : ℂ) • sigmaXBlock (p.castSucc : Fin (n + 2)) p.succ).conjTranspose =
       ∑ p, (γ p : ℂ) • sigmaXBlock p.castSucc p.succ
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.conjTranspose_smul]
  rw [show star ((γ p : ℝ) : ℂ) = ((γ p : ℝ) : ℂ) from by
    rw [Complex.star_def, Complex.conj_ofReal]]
  rw [show (sigmaXBlock (p.castSucc : Fin (n + 2)) p.succ).conjTranspose =
        sigmaXBlock p.castSucc p.succ from sigmaXBlock_isHermitian (castSucc_ne_succ_pub p)]

/-! ## 2. Tracelessness of σ-block sums

Each `σ_y(p)`, `σ_x(p)` has trace 0; scalar mult + sum preserve this. -/

/-- **`(∑_p γ_p · σ_y(p)).trace = 0`** for any γ. -/
theorem sigmaY_sum_trace_zero {n : ℕ} (γ : Fin (n + 1) → ℂ) :
    (∑ p : Fin (n + 1), γ p •
       sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ).trace = 0 := by
  rw [Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro p _
  rw [Matrix.trace_smul, sigmaYBlock_trace (castSucc_ne_succ_pub p), smul_zero]

/-- **`(∑_p γ_p · σ_x(p)).trace = 0`** for any γ. -/
theorem sigmaX_sum_trace_zero {n : ℕ} (γ : Fin (n + 1) → ℂ) :
    (∑ p : Fin (n + 1), γ p •
       sigmaXBlock (p.castSucc : Fin (n + 2)) p.succ).trace = 0 := by
  rw [Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro p _
  rw [Matrix.trace_smul, sigmaXBlock_trace (castSucc_ne_succ_pub p), smul_zero]

/-! ## 3. MAIN symmetric F=αG balanced commutator discharge

For real-valued diagonal traceless `a : Fin (n + 2) → ℝ` with all partial
sums non-negative, the symmetric F=γσ_y, G=γσ_x construction discharges
the balanced commutator equation `[F, G] = -iθ · diag(a)` with
Hermitian + traceless F, G. -/

/-- **MAIN discharge**: For real-valued diagonal `a : Fin (n + 2) → ℝ`
that is traceless (∑ a = 0) AND has all partial sums non-negative,
there exist Hermitian-traceless F, G satisfying

  `F · G − G · F = -((θ : ℂ) · Complex.I) • Matrix.diagonal (coerce a to ℂ)`

for any θ ∈ [0, 1].

Witness: `F = ∑_p √(θ b_p/2) · σ_y(p)`, `G = ∑_p √(θ b_p/2) · σ_x(p)`
where `b_p` is the p-th partial sum of `a`. Proof composes Session 23's
algebraic identity + sections §1, §2 of this module. -/
theorem symmetric_balanced_commutator_diagonal_nonneg_partials {n : ℕ}
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
        Matrix.diagonal (fun k => (a k : ℂ)) := by
  -- Define γ_real : Fin (n + 1) → ℝ via real square root.
  set b : Fin (n + 1) → ℂ := fun p => partialSumCoeff (fun k => (a k : ℂ)) p with hb_def
  set γ_real : Fin (n + 1) → ℝ := fun p => Real.sqrt (θ * (b p).re / 2)
  set γ : Fin (n + 1) → ℂ := fun p => (γ_real p : ℂ) with hγ_def
  -- Set F, G.
  set F : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
    ∑ p : Fin (n + 1), γ p • sigmaYBlock (p.castSucc : Fin (n + 2)) p.succ with hF_def
  set G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
    ∑ p : Fin (n + 1), γ p • sigmaXBlock (p.castSucc : Fin (n + 2)) p.succ with hG_def
  refine ⟨F, G, ?_, ?_, ?_, ?_, ?_⟩
  · -- F Hermitian
    exact sigmaY_sum_isHermitian γ_real
  · -- G Hermitian
    exact sigmaX_sum_isHermitian γ_real
  · -- F.trace = 0
    exact sigmaY_sum_trace_zero γ
  · -- G.trace = 0
    exact sigmaX_sum_trace_zero γ
  · -- F * G - G * F = -iθ · diag(a) — apply Session 23's identity.
    -- Key: γ p ^ 2 = θ · b p / 2 in ℂ.
    have h_γ_sq : ∀ p, (γ p)^2 = (θ : ℂ) * b p / 2 := by
      intro p
      have h_nn_p : 0 ≤ (b p).re := h_nn p
      have h_θ_b_nn : 0 ≤ θ * (b p).re / 2 := by
        have h_θ_b : 0 ≤ θ * (b p).re := mul_nonneg hθ_nn h_nn_p
        linarith
      -- γ p = (Real.sqrt (θ · (b p).re / 2) : ℂ).
      -- γ p ^ 2 = ((Real.sqrt _)^2 : ℂ) = ((θ · (b p).re / 2 : ℝ) : ℂ).
      show ((Real.sqrt (θ * (b p).re / 2) : ℝ) : ℂ)^2 = (θ : ℂ) * b p / 2
      rw [show ((Real.sqrt (θ * (b p).re / 2) : ℝ) : ℂ)^2 =
          ((Real.sqrt (θ * (b p).re / 2))^2 : ℝ) from by push_cast; ring]
      rw [Real.sq_sqrt h_θ_b_nn]
      -- Goal: ((θ * (b p).re / 2 : ℝ) : ℂ) = (θ : ℂ) * b p / 2
      -- b p is real (im = 0 by h_im), so b p = (b p).re : ℂ.
      have h_b_real : b p = ((b p).re : ℂ) := by
        apply Complex.ext
        · rw [Complex.ofReal_re]
        · rw [Complex.ofReal_im]; exact h_im p
      rw [h_b_real]
      simp [Complex.ofReal_re, Complex.ofReal_im]
    exact symmetric_F_G_eq_neg_iθ_diagonal (fun k => (a k : ℂ)) h_tr (θ : ℂ) γ h_γ_sq

end SKEFTHawking.FKLW.GenericSUd
