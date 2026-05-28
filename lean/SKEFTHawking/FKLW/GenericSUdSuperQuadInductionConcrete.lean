/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — concrete-radius super-quad induction substrate (re-point R4)

The first bricks of the super-quad induction re-pointed onto the concrete-radius SK
recursion `skApproxC_generic_sud_concrete` (S133). These mirror the IFT-log induction
substrate (`GenericSUdSuperQuadInduction.lean`, S89–S102) with `skApproxC_generic_sud` →
`skApproxC_generic_sud_concrete` and `dnStepFG_sud` → `dnStepFG_sud_concrete`:

  * the **base case** (level-0 error ≤ `ε_seq … 0 = 2·ε₀`) is log-agnostic — depends only on
    the base finder — so it is a verbatim copy;
  * the **polynomial F/G-norm bounds** (`‖F‖, ‖G‖ ≤ (n+2)⁴·√(θ/2)`) compose the concrete
    F/G-norm bound (S131, `≤ K_F·√(θ/2)`) with `K_F ≤ (n+2)⁴` (S90) — `θ = ‖(-i)·mLog(Δ−1)‖`.

These feed the concrete single-step super-quad bound (the remaining inductive-step brick),
whose regime ingredients (θ-bound S120, exp-delta S130, cubic S132) are all available on the
named calibration ball with no `Δ ∈ target` hypothesis.

## Substantive content shipped

  * `skApproxC_generic_sud_concrete_zero_error_bound` — base-case error bound.
  * `dnStepFG_sud_concrete_F_norm_le_poly` / `_G_norm_le_poly` — `(n+2)⁴·√(θ/2)` form.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Re-point sub-brick breakdown (R0–R4)" — R4: concrete super-quad
induction substrate (base case + polynomial norm bounds).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkApproxCConcrete
import SKEFTHawking.FKLW.GenericSUdDnStepFGFromLogNormBound
import SKEFTHawking.FKLW.GenericSUdDnStepFGConcreteCubic
import SKEFTHawking.FKLW.GenericSUdSuperQuadInduction

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix
open SKEFTHawking.FKLW.GroupCommutator

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Concrete recursion base-case error bound**: the level-0 concrete approximation is within
`ε_seq K (2·ε₀) 0 = 2·ε₀` of the target. Log-agnostic (depends only on the base finder);
verbatim concrete counterpart of `skApproxC_generic_sud_zero_error_bound` (S89). -/
lemma skApproxC_generic_sud_concrete_zero_error_bound {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (K ε₀ : ℝ)
    (h_baseFinder : BaseFinder_approximates_within_sud gs baseFinder (2 * ε₀))
    (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
    ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred 0 U) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K (2 * ε₀) 0 := by
  rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_zero, skApproxC_generic_sud_concrete_zero]
  exact (h_baseFinder U).le

/-- **Concrete polynomial F-norm bound**: `‖(dnStepFG_sud_concrete V_n U).F‖ ≤ (n+2)⁴·√(θ/2)`
with `θ = ‖(-i)·matrixMercatorLog ((V_n⁻¹U).val − 1)‖`. Composes the concrete F-norm bound
(S131, `≤ K_F·√(θ/2)`) with `K_F ≤ (n+2)⁴` (S90). Concrete counterpart of
`dnStepFG_sud_F_norm_le_poly`. -/
lemma dnStepFG_sud_concrete_F_norm_le_poly {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    ‖(dnStepFG_sud_concrete V_n U).F‖ ≤ ((n : ℝ) + 2) ^ 4 *
      Real.sqrt (‖((-Complex.I) • matrixMercatorLog
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ / 2) := by
  refine le_trans (dnStepFG_sud_concrete_F_norm_le V_n U) ?_
  exact mul_le_mul_of_nonneg_right (dnStepFG_sud_K_F_le n) (Real.sqrt_nonneg _)

/-- **Concrete polynomial G-norm bound** (mirror of F). -/
lemma dnStepFG_sud_concrete_G_norm_le_poly {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    ‖(dnStepFG_sud_concrete V_n U).G‖ ≤ ((n : ℝ) + 2) ^ 4 *
      Real.sqrt (‖((-Complex.I) • matrixMercatorLog
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ / 2) := by
  refine le_trans (dnStepFG_sud_concrete_G_norm_le V_n U) ?_
  exact mul_le_mul_of_nonneg_right (dnStepFG_sud_K_F_le n) (Real.sqrt_nonneg _)

/-- **Concrete F-norm in √ε form**: given the concrete θ-bound
`‖(-i)·matrixMercatorLog(Δ−1)‖ ≤ 2(n+2)·ε`, `‖(dnStepFG_sud_concrete V_n U).F‖ ≤ (n+2)^5·√ε`.
Concrete counterpart of `dnStepFG_sud_F_norm_le_sqrt_eps` (S100): composes the concrete poly
norm `(n+2)^4·√(θ/2)` with `√(θ/2) ≤ (n+2)·√ε` (the `√(n+2) ≤ n+2` step). The `hδ_le` input
shape required by the (concrete) super-quad numeric chain. The θ-bound hypothesis is itself
dischargeable on the calibration ball from `regime_thetabound_concrete` (S120) + the IH. -/
lemma dnStepFG_sud_concrete_F_norm_le_sqrt_eps {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) (ε : ℝ)
    (h_theta_le : ‖((-Complex.I) • matrixMercatorLog
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 2 * ((n : ℝ) + 2) * ε) :
    ‖(dnStepFG_sud_concrete V_n U).F‖ ≤ ((n : ℝ) + 2) ^ 5 * Real.sqrt ε := by
  have hd_ge_one : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  refine le_trans (dnStepFG_sud_concrete_F_norm_le_poly V_n U) ?_
  set θ := ‖((-Complex.I) • matrixMercatorLog
    ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ with hθ_def
  have h_sqrt_d_le : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 2 by linarith),
      Real.sqrt_nonneg ((n : ℝ) + 2), sq_nonneg (Real.sqrt ((n : ℝ) + 2) - 1)]
  have h_sqrt_half : Real.sqrt (θ / 2) ≤ ((n : ℝ) + 2) * Real.sqrt ε := by
    calc Real.sqrt (θ / 2)
        ≤ Real.sqrt (((n : ℝ) + 2) * ε) := Real.sqrt_le_sqrt (by linarith [h_theta_le])
      _ = Real.sqrt ((n : ℝ) + 2) * Real.sqrt ε := Real.sqrt_mul (by linarith) ε
      _ ≤ ((n : ℝ) + 2) * Real.sqrt ε :=
          mul_le_mul_of_nonneg_right h_sqrt_d_le (Real.sqrt_nonneg ε)
  calc ((n : ℝ) + 2) ^ 4 * Real.sqrt (θ / 2)
      ≤ ((n : ℝ) + 2) ^ 4 * (((n : ℝ) + 2) * Real.sqrt ε) :=
        mul_le_mul_of_nonneg_left h_sqrt_half (by positivity)
    _ = ((n : ℝ) + 2) ^ 5 * Real.sqrt ε := by ring

/-- **Concrete G-norm in √ε form** (mirror of F). -/
lemma dnStepFG_sud_concrete_G_norm_le_sqrt_eps {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) (ε : ℝ)
    (h_theta_le : ‖((-Complex.I) • matrixMercatorLog
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 2 * ((n : ℝ) + 2) * ε) :
    ‖(dnStepFG_sud_concrete V_n U).G‖ ≤ ((n : ℝ) + 2) ^ 5 * Real.sqrt ε := by
  have hd_ge_one : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  refine le_trans (dnStepFG_sud_concrete_G_norm_le_poly V_n U) ?_
  set θ := ‖((-Complex.I) • matrixMercatorLog
    ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val - 1) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ with hθ_def
  have h_sqrt_d_le : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 2 by linarith),
      Real.sqrt_nonneg ((n : ℝ) + 2), sq_nonneg (Real.sqrt ((n : ℝ) + 2) - 1)]
  have h_sqrt_half : Real.sqrt (θ / 2) ≤ ((n : ℝ) + 2) * Real.sqrt ε := by
    calc Real.sqrt (θ / 2)
        ≤ Real.sqrt (((n : ℝ) + 2) * ε) := Real.sqrt_le_sqrt (by linarith [h_theta_le])
      _ = Real.sqrt ((n : ℝ) + 2) * Real.sqrt ε := Real.sqrt_mul (by linarith) ε
      _ ≤ ((n : ℝ) + 2) * Real.sqrt ε :=
          mul_le_mul_of_nonneg_right h_sqrt_d_le (Real.sqrt_nonneg ε)
  calc ((n : ℝ) + 2) ^ 4 * Real.sqrt (θ / 2)
      ≤ ((n : ℝ) + 2) ^ 4 * (((n : ℝ) + 2) * Real.sqrt ε) :=
        mul_le_mul_of_nonneg_left h_sqrt_half (by positivity)
    _ = ((n : ℝ) + 2) ^ 5 * Real.sqrt ε := by ring

/-- **Concrete cubic term through V_n**: `‖ρ(V_n)·gC(A_F, A_G) − U‖ ≤ (n+2)·320·δ³` for the
concrete DN step, on the named calibration ball `(n+2)²·‖V_n − U‖ ≤ 1/8`. Concrete counterpart
of `cubic_term_through_Vn` (S93), with the existential `h_regime3` + `Δ ∈ target` hypotheses
ELIMINATED. Since `ρ(V_n)·Δ = U` (`Vn_mul_residual_eq_U`), `ρ(V_n)·gC − U = ρ(V_n)·(gC − Δ)`,
bounded by `‖ρ(V_n)‖·320·δ³ ≤ (n+2)·320·δ³` (M-bound `SUd_val_linftyOpNorm_le` + the concrete
cubic remainder S132). The "term 2" of the concrete inductive-step telescoping. -/
lemma cubic_term_through_Vn_concrete {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    (hVU : ((n : ℝ) + 2) ^ 2 *
        ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
          (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 / 8)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (hF_norm : ‖(dnStepFG_sud_concrete V_n U).F‖ ≤ δ)
    (hG_norm : ‖(dnStepFG_sud_concrete V_n U).G‖ ≤ δ) :
    ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) *
        groupCommutator
          ((expIsud n (dnStepFG_sud_concrete V_n U).F (dnStepFG_sud_concrete V_n U).hF_herm
              (dnStepFG_sud_concrete V_n U).hF_tr :
              ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
              Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
          ((expIsud n (dnStepFG_sud_concrete V_n U).G (dnStepFG_sud_concrete V_n U).hG_herm
              (dnStepFG_sud_concrete V_n U).hG_tr :
              ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
              Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
        (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤
      ((n : ℝ) + 2) * (320 * δ ^ 3) := by
  have h_cubic := dnStepFG_sud_concrete_gC_minus_Delta_norm_le_cubic V_n U hVU
    δ hδ_nn hδ_le_one hF_norm hG_norm
  set gC := groupCommutator
    ((expIsud n (dnStepFG_sud_concrete V_n U).F (dnStepFG_sud_concrete V_n U).hF_herm
        (dnStepFG_sud_concrete V_n U).hF_tr : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    ((expIsud n (dnStepFG_sud_concrete V_n U).G (dnStepFG_sud_concrete V_n U).hG_herm
        (dnStepFG_sud_concrete V_n U).hG_tr : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) with hgC_def
  rw [← Vn_mul_residual_eq_U V_n U, ← Matrix.mul_sub]
  calc ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) *
          (gC - ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ))‖
      ≤ ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ *
          ‖gC - ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ := Matrix.linfty_opNorm_mul _ _
    _ ≤ ((n : ℝ) + 2) * (320 * δ ^ 3) := by
        have h_M : ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ ((n : ℝ) + 2) := by
          have := SUd_val_linftyOpNorm_le V_n
          simpa using this
        have h_gC_nn : (0 : ℝ) ≤ ‖gC - ((V_n⁻¹ * U :
            ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ := norm_nonneg _
        exact mul_le_mul h_M h_cubic h_gC_nn (by positivity)

/-! ## Concrete inductive-step telescoping (S92 + S95 analogs) -/

/-- **Concrete recursion ρ_hom-unfolding**: `ρ(sk_{n+1}^concrete U) = ρ(V_n)·gC(ρ(sk_n A_F),
ρ(sk_n A_G))` at the matrix level. Log-agnostic structural lemma (S92 analog): unfolds the
concrete recursion's `succ` shape via the S87 ρ_hom MonoidHom abstractions. -/
lemma skApproxC_generic_sud_concrete_succ_rho_val {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
    let V_n_word := skApproxC_generic_sud_concrete gs baseFinder h_det_pred n U
    let data := dnStepFG_sud_concrete (gs.ρ_hom V_n_word) U
    let A_F := expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr
    let A_G := expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr
    ((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred (n + 1) U) :
        ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) =
      ((gs.ρ_hom V_n_word : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) *
      groupCommutator
        ((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n A_F) :
            ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
            Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
        ((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n A_G) :
            ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
            Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) := by
  intro V_n_word data A_F A_G
  rw [skApproxC_generic_sud_concrete_succ]
  rw [ρ_hom_sud_mul_val, ρ_hom_sud_groupCommutator_val]

/-- **Concrete single-step error combine (telescoping assembly)**: `‖ρ(sk_{n+1}^concrete U) − U‖
≤ Cstab + Ccubic`, given the stability term (`‖ρ(V_n)·gC(ρ(sk A_F),ρ(sk A_G)) − ρ(V_n)·gC(A_F,A_G)‖
≤ Cstab`) and the cubic term (`‖ρ(V_n)·gC(A_F,A_G) − U‖ ≤ Ccubic`). Concrete counterpart of
`skApproxC_sud_succ_error_le_combine` (S95): unfolds the recursion via the concrete
`succ_rho_val` and applies the triangle inequality through the common midpoint
`ρ(V_n)·gC(A_F,A_G)`. -/
lemma skApproxC_sud_succ_error_le_combine_concrete {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ))
    (Cstab Ccubic : ℝ)
    (h_stab_term :
      let V_n_word := skApproxC_generic_sud_concrete gs baseFinder h_det_pred n U
      let data := dnStepFG_sud_concrete (gs.ρ_hom V_n_word) U
      let A_F := expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr
      let A_G := expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr
      ‖((gs.ρ_hom V_n_word : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) *
          groupCommutator
            ((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n A_F) :
                ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
                Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
            ((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n A_G) :
                ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
                Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        ((gs.ρ_hom V_n_word : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
            Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) *
          groupCommutator
            ((A_F : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
                Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
            ((A_G : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
                Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ Cstab)
    (h_cubic_term :
      let V_n_word := skApproxC_generic_sud_concrete gs baseFinder h_det_pred n U
      let data := dnStepFG_sud_concrete (gs.ρ_hom V_n_word) U
      let A_F := expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr
      let A_G := expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr
      ‖((gs.ρ_hom V_n_word : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) *
          groupCommutator
            ((A_F : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
                Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
            ((A_G : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
                Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ Ccubic) :
    ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred (n + 1) U) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ Cstab + Ccubic := by
  simp only at h_stab_term h_cubic_term
  have htri : ∀ (a b c : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) (X Y : ℝ),
      ‖a - b‖ ≤ X → ‖b - c‖ ≤ Y → ‖a - c‖ ≤ X + Y := by
    intro a b c X Y hab hbc
    calc ‖a - c‖ = ‖(a - b) + (b - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖a - b‖ + ‖b - c‖ := norm_add_le _ _
      _ ≤ X + Y := add_le_add hab hbc
  rw [skApproxC_generic_sud_concrete_succ_rho_val gs baseFinder h_det_pred n U]
  exact htri _ _ _ _ _ h_stab_term h_cubic_term

/-! ## Concrete single-step valid-branch super-quad bound (S101 analog) -/

/-- **Concrete single-step super-quad bound (valid branch)**: given the level-n IH
(`∀ U', ‖ρ(sk_n^concrete U') − U'‖ ≤ ε`), the concrete θ-bound on the residual, the named
calibration bound `(m+2)²·‖V_n − U‖ ≤ 1/8`, and `(m+2)^5·√ε ≤ 1`, `ε ≤ 2·ε₀_sud`, the
level-(n+1) error contracts super-quadratically:

  `‖ρ(sk_{n+1}^concrete U) − U‖ ≤ K_compose_sud(m+2) · ε^(3/2)`.

Concrete counterpart of `skApproxC_sud_succ_super_quad_valid` (S101), with the existential
`h_regime3` + `Δ ∈ target` hypotheses ELIMINATED — the cubic term uses the concrete
`cubic_term_through_Vn_concrete` (S136) under the named calibration bound. Composes the
concrete √ε-norm (S135), the concrete cubic term (S136), the concrete error-combine (S137),
and the **log-agnostic** stability term (S96) + numeric chain (S99) + near-identity bounds
(S85), all reused as-is. -/
lemma skApproxC_sud_succ_super_quad_valid_concrete {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ))
    (ε : ℝ) (hε_nn : 0 ≤ ε) (hε_le : ε ≤ 2 * ε₀_sud (m + 2))
    (h_delta_le_one : ((m : ℝ) + 2) ^ 5 * Real.sqrt ε ≤ 1)
    (h_theta_le : ‖((-Complex.I) • matrixMercatorLog
        (((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n U))⁻¹ * U :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)).val - 1) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ 2 * ((m : ℝ) + 2) * ε)
    (hVU : ((m : ℝ) + 2) ^ 2 *
        ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n U) :
            ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
            Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
          (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ 1 / 8)
    (h_IH : ∀ U' : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ),
        ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n U') :
            ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
            Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
          (U' : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ ε) :
    ‖((gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred (n + 1) U) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤
      K_compose_sud (m + 2) * ε ^ (3 / 2 : ℝ) := by
  haveI : Nonempty (Fin (m + 2)) := ⟨0⟩
  set V_n := gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n U) with hV_n_def
  set data := dnStepFG_sud_concrete V_n U with hdata_def
  set δ_lie := ((m : ℝ) + 2) ^ 5 * Real.sqrt ε with hδ_def
  have hδ_nn : 0 ≤ δ_lie := by rw [hδ_def]; positivity
  set η := δ_lie * Real.exp δ_lie with hη_def
  have hη_nn : 0 ≤ η := by rw [hη_def]; positivity
  have hF_norm : ‖data.F‖ ≤ δ_lie := dnStepFG_sud_concrete_F_norm_le_sqrt_eps V_n U ε h_theta_le
  have hG_norm : ‖data.G‖ ≤ δ_lie := dnStepFG_sud_concrete_G_norm_le_sqrt_eps V_n U ε h_theta_le
  have h_A_G_near :
      ‖((expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) - 1‖ ≤ η :=
    expIsud_norm_sub_one_le data.G data.hG_herm data.hG_tr δ_lie hδ_nn hG_norm
  have h_A_F_inv_near :
      ‖((expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)⁻¹ - 1‖ ≤ η :=
    expIsud_inv_norm_sub_one_le data.F data.hF_herm data.hF_tr δ_lie hδ_nn hF_norm
  have h_stab := stability_term_through_Vn V_n
    (expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr)
    (expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr)
    (gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n
      (expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr)))
    (gs.ρ_hom (skApproxC_generic_sud_concrete gs baseFinder h_det_pred n
      (expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr)))
    η ε hη_nn hε_nn h_A_G_near h_A_F_inv_near
    (h_IH (expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr))
    (h_IH (expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr))
  rw [show ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 from by push_cast; ring] at h_stab
  have h_cubic := cubic_term_through_Vn_concrete V_n U hVU δ_lie hδ_nn h_delta_le_one
    hF_norm hG_norm
  have h_combine := skApproxC_sud_succ_error_le_combine_concrete gs baseFinder h_det_pred n U
    _ _ h_stab h_cubic
  have hη_le : η ≤ 3 * δ_lie := by rw [hη_def]; exact eta_le_three_delta δ_lie hδ_nn h_delta_le_one
  have h_chain := super_quad_numeric_chain (m := m) ε δ_lie η hε_nn hδ_nn
    (le_of_eq hδ_def) hη_le hε_le
  exact le_trans h_combine h_chain

end SKEFTHawking.FKLW.GenericSUd
