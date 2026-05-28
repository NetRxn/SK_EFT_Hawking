/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Super-quad bound SUBSTRATE for SU(d) recursion discharge

Lift of the SU(2) super-quad bound substrate lemmas from Phase 6t/6u
(`SolovayKitaevPathA.lean`, `GenericSolovayKitaevRecursionDischarge.lean`)
to SU(d). Provides the per-step substrate lemmas needed for the
super-quad bound discharge `SkApproxCSuperQuadraticBound_generic_sud`
(Session 44 predicate).

## Substantive content shipped

  * `residual_norm_le_d_mul` — SU(d) analog of SU(2)'s
    `residual_norm_le_sqrt_two_mul`: for `V, U ∈ ↥SU(d)`, the residual
    `Δ = V⁻¹ * U` satisfies `‖Δ - 1‖ ≤ d · ‖V - U‖`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — super-quad bound
substrate lift (1st of ~10 substrate lemmas per Explore-agent intel).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdNormBridgeUnitaryConjugation
import SKEFTHawking.FKLW.GenericSUdMatrixLogLipschitzExplicit

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## Residual norm bound at SU(d) -/

/-- **Residual norm bound at SU(d)**.

For `V, U ∈ ↥SU(d)` (d ≥ 1), the residual `Δ := V⁻¹ * U` satisfies
`‖Δ.val - 1‖_linftyOp ≤ d · ‖V.val - U.val‖_linftyOp`.

SU(d) analog of SU(2)'s `residual_norm_le_sqrt_two_mul` (which used
the SU(2)-specific `‖V⁻¹‖ ≤ √2` bound). The SU(d) version uses
`linftyOpNorm_unitary_le` (Session 36 substrate) giving `‖V⁻¹‖ ≤ d`.

Proof: `V⁻¹·U - 1 = V⁻¹·(U - V)`, then sub-multiplicativity of linftyOp
norm + `‖V⁻¹‖ ≤ d` + norm symmetry. -/
lemma residual_norm_le_d_mul {d : ℕ} [Nonempty (Fin d)]
    (V U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    ‖((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) - (1 : Matrix (Fin d) (Fin d) ℂ)‖ ≤
      (d : ℝ) *
        ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖ := by
  -- Unfold subtype-level mul.
  have h_mul_val : ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
                    Matrix (Fin d) (Fin d) ℂ) =
                   (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val *
                   U.val := rfl
  rw [h_mul_val]
  -- V⁻¹.val ∈ unitaryGroup via special ⊆ unitary.
  have h_V_inv_unitary : (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val ∈
      Matrix.unitaryGroup (Fin d) ℂ := by
    exact Matrix.specialUnitaryGroup_le_unitaryGroup (V⁻¹).property
  -- ‖V⁻¹.val‖ ≤ d.
  have h_V_inv_norm : ‖(V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val‖ ≤
      (d : ℝ) :=
    linftyOpNorm_unitary_le ⟨_, h_V_inv_unitary⟩
  -- V⁻¹.val * V.val = 1.
  have h_inv_left : (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val * V.val
      = 1 := by
    have h := inv_mul_cancel V
    have h_eq : ((V⁻¹ * V : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
                Matrix (Fin d) (Fin d) ℂ) =
              (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val * V.val := rfl
    rw [← h_eq, h]; rfl
  -- Factor: V⁻¹·U - 1 = V⁻¹·(U - V).
  have h_factor : (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val * U.val -
                    (1 : Matrix (Fin d) (Fin d) ℂ) =
                  (V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val *
                    (U.val - V.val) := by
    rw [Matrix.mul_sub, h_inv_left]
  rw [h_factor]
  -- Submultiplicativity + norm bound.
  have h_sub_mul := norm_mul_le
    ((V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val) (U.val - V.val)
  have h_norm_sub_sym : ‖U.val - V.val‖ = ‖V.val - U.val‖ := norm_sub_rev _ _
  calc ‖(V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val * (U.val - V.val)‖
      ≤ ‖(V⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val‖ * ‖U.val - V.val‖ :=
        h_sub_mul
    _ ≤ (d : ℝ) * ‖U.val - V.val‖ := by
        gcongr
    _ = (d : ℝ) * ‖V.val - U.val‖ := by rw [h_norm_sub_sym]

/-! ## H norm bound at SU(d) (using matrixLog Lipschitz K=2) -/

/-- **H norm bound at SU(d)** via matrixLog Lipschitz K=2.

For `Δ : Matrix (Fin d) (Fin d) ℂ` in the matrixLog-Lipschitz neighborhood
of 1 (radius δ from Session 41's `matrixLog_lipschitz_K_two_near_one`),
the matrix `H := (-Complex.I) • matrixLog d Δ` has linftyOp norm at most
`2 · ‖Δ - 1‖`.

SU(d) analog of SU(2)'s `H_norm_le_four_norm_sub_one` (Phase 6t
SolovayKitaevPathA). The SU(d) constant is K=2 (Session 41) vs SU(2)'s
K=4 (loose) or K=π (tight); the analog uses `matrixLog_lipschitz_K_two_near_one`. -/
lemma H_norm_le_two_norm_sub_one_sud (d : ℕ) :
    ∃ δ > (0 : ℝ), ∀ Δ : Matrix (Fin d) (Fin d) ℂ,
      ‖Δ - 1‖ < δ →
      ‖((-Complex.I) • matrixLog d Δ : Matrix (Fin d) (Fin d) ℂ)‖ ≤
        2 * ‖Δ - 1‖ := by
  obtain ⟨δ, hδ_pos, h_lipschitz⟩ := matrixLog_lipschitz_K_two_near_one d
  refine ⟨δ, hδ_pos, ?_⟩
  intro Δ h_small
  -- ‖(-i) • matrixLog Δ‖ = ‖-i‖ · ‖matrixLog Δ‖ = 1 · ‖matrixLog Δ‖
  rw [norm_smul]
  have h_norm_neg_I : ‖(-Complex.I)‖ = 1 := by
    rw [norm_neg, Complex.norm_I]
  rw [h_norm_neg_I, one_mul]
  exact h_lipschitz Δ h_small

/-! ## Composite H-norm-from-V-diff bound at SU(d) -/

/-- **Composite H-norm bound from V-diff at SU(d)**: combines
`residual_norm_le_d_mul` (Session 60) with `H_norm_le_two_norm_sub_one_sud`
(Session 61) into a single substrate lemma.

For `V, U ∈ ↥SU(d)` with `d · ‖V - U‖ < δ` (the matrixLog Lipschitz
neighborhood radius from Session 41), the matrix
`H := (-i) • matrixLog d (V⁻¹·U)` has linftyOp norm at most
`2·d · ‖V - U‖`.

SU(d) analog of SU(2)'s `H_norm_bound_from_V_diff` (Phase 6t). Captures
Steps 2-4 of the super-quad DN chain in a single substrate lemma. -/
lemma H_norm_bound_from_V_diff_sud {d : ℕ} [Nonempty (Fin d)] :
    ∃ δ > (0 : ℝ),
    ∀ (V U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)),
      (d : ℝ) * ‖(V : Matrix (Fin d) (Fin d) ℂ) -
        (U : Matrix (Fin d) (Fin d) ℂ)‖ < δ →
      ‖((-Complex.I) • matrixLog d
          ((V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)).val) :
          Matrix (Fin d) (Fin d) ℂ)‖ ≤
        2 * (d : ℝ) *
          ‖(V : Matrix (Fin d) (Fin d) ℂ) -
            (U : Matrix (Fin d) (Fin d) ℂ)‖ := by
  obtain ⟨δ, hδ_pos, h_H_bound⟩ := H_norm_le_two_norm_sub_one_sud d
  refine ⟨δ, hδ_pos, ?_⟩
  intro V U h_small
  -- Apply Step 2 (residual_norm_le_d_mul)
  have h_residual := residual_norm_le_d_mul V U
  -- Δ residual ‖_ - 1‖ ≤ d · ‖V - U‖
  set Δ := (V⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) with hΔ_def
  have h_residual_lt :
      ‖(Δ : Matrix (Fin d) (Fin d) ℂ) - (1 : Matrix (Fin d) (Fin d) ℂ)‖ < δ :=
    lt_of_le_of_lt h_residual h_small
  -- Apply Step 4 (H_norm_le_two_norm_sub_one_sud)
  have h_H := h_H_bound Δ.val h_residual_lt
  -- Chain: ‖H‖ ≤ 2·‖Δ - 1‖ ≤ 2·(d·‖V - U‖) = 2d·‖V - U‖
  calc ‖((-Complex.I) • matrixLog d Δ.val : Matrix (Fin d) (Fin d) ℂ)‖
      ≤ 2 * ‖(Δ : Matrix (Fin d) (Fin d) ℂ) -
              (1 : Matrix (Fin d) (Fin d) ℂ)‖ := h_H
    _ ≤ 2 * ((d : ℝ) *
            ‖(V : Matrix (Fin d) (Fin d) ℂ) -
              (U : Matrix (Fin d) (Fin d) ℂ)‖) := by gcongr
    _ = 2 * (d : ℝ) *
        ‖(V : Matrix (Fin d) (Fin d) ℂ) -
          (U : Matrix (Fin d) (Fin d) ℂ)‖ := by ring

/-! ## SU(d) calibration constants (K_compose_sud + ε₀_sud) -/

/-- **The SU(d) full SK per-step composition constant** — d-dependent
analog of SU(2)'s `K_compose = 1024`.

SU(2) K_compose aggregates cubic remainder + stability + margin. For
SU(d), each component scales with d (polynomial growth from the loose
norm bounds). Use `K_compose_sud d := 1024 * d^4` as a loose-but-explicit
upper bound (the d^4 factor absorbs the (n+2)² norm-bridge constant
squared, providing margin for the cubic+stability composition). -/
noncomputable def K_compose_sud (d : ℕ) : ℝ := 1024 * (d : ℝ)^4

/-- `K_compose_sud d > 0` for d ≥ 1. -/
lemma K_compose_sud_pos {d : ℕ} (hd : 1 ≤ d) : 0 < K_compose_sud d := by
  unfold K_compose_sud
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- **The SU(d) SK base-case threshold** — d-dependent analog of SU(2)'s
`ε₀ = 1/(8 · K_compose²)`. Chosen so `K_compose_sud(d)² · 2·ε₀_sud(d) = 1/4`,
the Dawson-Nielsen super-quadratic convergence condition at SU(d). -/
noncomputable def ε₀_sud (d : ℕ) : ℝ := 1 / (8 * K_compose_sud d ^ 2)

/-- `ε₀_sud d > 0` for d ≥ 1. -/
lemma ε₀_sud_pos {d : ℕ} (hd : 1 ≤ d) : 0 < ε₀_sud d := by
  unfold ε₀_sud
  have h_K_pos := K_compose_sud_pos hd
  positivity

/-- **Calibration identity at SU(d)**: `K_compose_sud(d)² · 2·ε₀_sud(d) = 1/4`. -/
lemma K_compose_sud_sq_times_two_ε₀_sud {d : ℕ} (hd : 1 ≤ d) :
    K_compose_sud d ^ 2 * (2 * ε₀_sud d) = 1 / 4 := by
  unfold ε₀_sud
  have h_K_pos := K_compose_sud_pos hd
  have h_K_sq_pos : 0 < K_compose_sud d ^ 2 := by positivity
  have h_K_sq_ne : K_compose_sud d ^ 2 ≠ 0 := ne_of_gt h_K_sq_pos
  field_simp
  ring

/-- **Calibration inequality at SU(d)**: `K_compose_sud(d)² · 2·ε₀_sud(d) ≤ 1/4`
(used by Session 48's `skLevel_polylog_sud_spec_holds` calibration hypothesis). -/
lemma K_compose_sud_calibration_le {d : ℕ} (hd : 1 ≤ d) :
    K_compose_sud d ^ 2 * (2 * ε₀_sud d) ≤ 1 / 4 := by
  rw [K_compose_sud_sq_times_two_ε₀_sud hd]

/-- **K_compose_sud d ≥ 1024** (for d ≥ 1). -/
lemma K_compose_sud_ge_1024 {d : ℕ} (hd : 1 ≤ d) :
    1024 ≤ K_compose_sud d := by
  unfold K_compose_sud
  have hd_ge_1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h_pow : (1 : ℝ) ≤ (d : ℝ)^4 := by
    have : (1 : ℝ)^4 ≤ (d : ℝ)^4 := pow_le_pow_left₀ (by norm_num) hd_ge_1 4
    simpa using this
  nlinarith

end SKEFTHawking.FKLW.GenericSUd
