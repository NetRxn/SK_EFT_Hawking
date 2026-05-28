/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Super-quad main induction (assembly)

The (B) ingredient: discharge of `SkApproxCSuperQuadraticBound_generic_sud`
(Session 44 predicate) — the SU(d) analog of SU(2)'s
`SkApproxCSuperQuadraticBound_generic_holds`
(`GenericSolovayKitaevRecursionDischarge.lean` lines 468-1181).

This module assembles the recursion induction from the per-step ingredients
shipped in Sessions 79-88:
  * F/G-norm bound (Session 82, `dnStepFG_sud_F_norm_le`)
  * commutator identity + invalid-zero (Session 83)
  * exp(-[F,G]) = Δ (Session 84)
  * expIsud near-identity norm bounds (Session 85)
  * group-commutator cubic remainder (Session 86, `≤ 320·δ³`)
  * ρ_hom MonoidHom abstractions (Session 87)
  * `groupCommutator_stability_nearIdentity` (already dimension-generic)
  * ε_seq monotonicity + the bumped `K_compose_sud = 1024·d^16` calibration
    (Session 88)

The induction proceeds in stages (shipped incrementally):
  1. **Base case** (this module): level-0 error ≤ `ε_seq K (2·ε₀) 0 = 2·ε₀`.
  2. Regime lemmas (θ ≤ 1, δ_lie ≤ 1 from `ε_n ≤ 2·ε₀_sud`).
  3. `valid_branch_K_chain_le_K_compose_sud_numeric` (the numeric K-chain).
  4. Inductive step (valid + invalid branches).
  5. The full induction `SkApproxCSuperQuadraticBound_generic_sud_holds`.

## Substantive content shipped (this session)

  * `skApproxC_generic_sud_zero_error_bound` — base case of the induction.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — super-quad main induction
assembly (the (B) ingredient; base case).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkApproxC
import SKEFTHawking.FKLW.GenericSUdDnStepFGNormBound
import SKEFTHawking.FKLW.GenericSUdDnStepFGCubic
import SKEFTHawking.FKLW.GenericSUdRhomAbstraction
import SKEFTHawking.FKLW.GroupCommutator
import SKEFTHawking.FKLW.GroupCommutatorNearIdentity
import SKEFTHawking.FKLW.EpsilonSeq

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix
open SKEFTHawking.FKLW.GroupCommutator

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## Numeric-chain prep: polynomial bound on the F/G-norm constant K_F -/

/-- `0 ≤ dnStepFG_sud_K_F n`. -/
lemma dnStepFG_sud_K_F_nonneg (n : ℕ) : 0 ≤ dnStepFG_sud_K_F n := by
  unfold dnStepFG_sud_K_F
  positivity

/-- **Polynomial bound on K_F**: `dnStepFG_sud_K_F n = (n+2)²·(n+1)·√(n+2) ≤ (n+2)⁴`.

Tames the awkward `√(n+2)` factor to a clean polynomial d-power for the
super-quad numeric chain: `(n+1)·√(n+2) ≤ (n+2)·(n+2) = (n+2)²` (since
`n+1 ≤ n+2` and `√(n+2) ≤ n+2`), so `K_F ≤ (n+2)²·(n+2)² = (n+2)⁴`. -/
lemma dnStepFG_sud_K_F_le (n : ℕ) : dnStepFG_sud_K_F n ≤ ((n : ℝ) + 2)^4 := by
  unfold dnStepFG_sud_K_F
  have h_cast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [h_cast]
  have h_sqrt_le : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ) + 2 by positivity)
    have hs_nn := Real.sqrt_nonneg ((n:ℝ) + 2)
    nlinarith [hs, hs_nn, sq_nonneg (Real.sqrt ((n:ℝ) + 2) - 1),
      (by positivity : (0:ℝ) ≤ (n:ℝ))]
  rw [show ((n:ℝ) + 2)^4 = ((n:ℝ) + 2)^2 * (((n:ℝ) + 2) * ((n:ℝ) + 2)) from by ring]
  gcongr
  norm_num

/-- **Base case of the super-quad induction**: the level-0 approximation
`skApproxC_generic_sud … 0 U = baseFinder U` is within
`ε_seq K (2·ε₀) 0 = 2·ε₀` of `U`, given the base finder's ε₀-net property.

SU(d) analog of SU(2)'s `skApproxC_generic_zero_error_bound`. -/
lemma skApproxC_generic_sud_zero_error_bound {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (K ε₀ : ℝ)
    (h_baseFinder : BaseFinder_approximates_within_sud gs baseFinder (2 * ε₀))
    (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
    ‖((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred 0 U) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K (2 * ε₀) 0 := by
  rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_zero, skApproxC_generic_sud_zero]
  exact (h_baseFinder U).le

/-! ## Stability M-bound + polynomial F/G-norm bounds (inductive-step prep) -/

/-- **The stability M-bound**: every `SU(d)` element has linftyOp norm `≤ d`.

This is the uniform `M = d` bound the `groupCommutator_stability_nearIdentity`
step needs on all eight operands `‖g'‖, ‖h'‖, ‖g⁻¹‖, ‖h⁻¹‖, ‖g'⁻¹‖, ‖h'⁻¹‖`
(each a `ρ_hom`-image or its inverse, hence an `SU(d)` element). SU(d) analog
of SU(2)'s `SU2_linftyOpNorm_le_sqrt_two` (which uses the tighter `√2`). -/
lemma SUd_val_linftyOpNorm_le {d : ℕ} [Nonempty (Fin d)]
    (x : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    ‖(x : Matrix (Fin d) (Fin d) ℂ)‖ ≤ (d : ℝ) :=
  linftyOpNorm_unitary_le ⟨_, Matrix.specialUnitaryGroup_le_unitaryGroup x.property⟩

/-- **Polynomial F-norm bound**: `‖(dnStepFG_sud V_n U).F‖ ≤ (n+2)⁴·√(θ/2)`
(clean d-power form, composing S82's `K_F·√(θ/2)` with S90's `K_F ≤ (n+2)⁴`). -/
lemma dnStepFG_sud_F_norm_le_poly {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    let Δ := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    let H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
      ((-Complex.I) : ℂ) • matrixLog (n + 2) Δ.val
    let θ : ℝ := ‖H‖
    ‖(dnStepFG_sud V_n U).F‖ ≤ ((n : ℝ) + 2)^4 * Real.sqrt (θ / 2) := by
  intro Δ H θ
  refine le_trans (dnStepFG_sud_F_norm_le V_n U) ?_
  exact mul_le_mul_of_nonneg_right (dnStepFG_sud_K_F_le n) (Real.sqrt_nonneg _)

/-- **Polynomial G-norm bound** (mirror of F). -/
lemma dnStepFG_sud_G_norm_le_poly {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
    let Δ := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    let H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
      ((-Complex.I) : ℂ) • matrixLog (n + 2) Δ.val
    let θ : ℝ := ‖H‖
    ‖(dnStepFG_sud V_n U).G‖ ≤ ((n : ℝ) + 2)^4 * Real.sqrt (θ / 2) := by
  intro Δ H θ
  refine le_trans (dnStepFG_sud_G_norm_le V_n U) ?_
  exact mul_le_mul_of_nonneg_right (dnStepFG_sud_K_F_le n) (Real.sqrt_nonneg _)

/-! ## Composition identity (inductive-step structural core) -/

/-- **Composition identity**: the level-(n+1) recursion output, mapped through
`ρ_hom` to the matrix level, equals `ρ(V_n) · groupCommutator(ρ(sk_n A_F), ρ(sk_n A_G))`.

This is the structural heart of the inductive step: it exposes the recursion's
`V_{n+1} = V_n · gC(...)` shape so the telescoping `‖V_{n+1} − U‖ = ‖V_n·(gC − Δ)‖`
can proceed. SU(d) analog of the SU(2) `h_skApproxC_succ_val`; composes
`skApproxC_generic_sud_succ` with the S87 ρ_hom MonoidHom abstractions
`ρ_hom_sud_mul_val` + `ρ_hom_sud_groupCommutator_val`. -/
lemma skApproxC_generic_sud_succ_rho_val {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
    let V_n_word := skApproxC_generic_sud gs baseFinder h_det_pred n U
    let data := dnStepFG_sud (gs.ρ_hom V_n_word) U
    let A_F := expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr
    let A_G := expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr
    ((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred (n + 1) U) :
        ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) =
      ((gs.ρ_hom V_n_word : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) *
      groupCommutator
        ((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n A_F) :
            ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
            Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
        ((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n A_G) :
            ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
            Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) := by
  intro V_n_word data A_F A_G
  rw [skApproxC_generic_sud_succ]
  rw [ρ_hom_sud_mul_val, ρ_hom_sud_groupCommutator_val]

/-! ## Telescoping term 2: cubic term through V_n -/

/-- **`V_n · Δ = U` at the matrix level**: for `Δ := V_n⁻¹·U`, `V_n.val · Δ.val = U.val`. -/
lemma Vn_mul_residual_eq_U {d : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    (V_n : Matrix (Fin d) (Fin d) ℂ) *
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ) =
      (U : Matrix (Fin d) (Fin d) ℂ) := by
  have h_grp : V_n * (V_n⁻¹ * U) = U := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  calc (V_n : Matrix (Fin d) (Fin d) ℂ) *
        ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ)
      = ((V_n * (V_n⁻¹ * U) : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ) := rfl
    _ = (U : Matrix (Fin d) (Fin d) ℂ) := by rw [h_grp]

/-- **Cubic term through V_n**: `‖ρ(V_n)·gC(A_F, A_G) − U‖ ≤ (n+2)·320·δ³`.

The "term 2" of the inductive-step telescoping: since `ρ(V_n)·Δ = U`, we have
`ρ(V_n)·gC(A_F,A_G) − U = ρ(V_n)·(gC(A_F,A_G) − Δ)`, bounded by `‖ρ(V_n)‖·320·δ³ ≤ (n+2)·320·δ³`
(M-bound S91 + cubic remainder S86). Carries the valid-regime + target hypotheses. -/
lemma cubic_term_through_Vn {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ))
    (h_valid : 0 < ‖((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ∧
        ‖((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 1 ∧
        (((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)).IsHermitian ∧
        (((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)).trace = 0)
    (h_target : (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val ∈
        (expAmbientPartialHomeo (n + 2)).target)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (hF_norm : ‖(dnStepFG_sud V_n U).F‖ ≤ δ)
    (hG_norm : ‖(dnStepFG_sud V_n U).G‖ ≤ δ) :
    ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) *
        groupCommutator
          ((expIsud n (dnStepFG_sud V_n U).F (dnStepFG_sud V_n U).hF_herm
              (dnStepFG_sud V_n U).hF_tr : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
              Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
          ((expIsud n (dnStepFG_sud V_n U).G (dnStepFG_sud V_n U).hG_herm
              (dnStepFG_sud V_n U).hG_tr : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
              Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) -
        (U : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤
      ((n : ℝ) + 2) * (320 * δ ^ 3) := by
  have h_cubic := dnStepFG_sud_gC_minus_Delta_norm_le_cubic V_n U h_valid h_target
    δ hδ_nn hδ_le_one hF_norm hG_norm
  set gC := groupCommutator
    ((expIsud n (dnStepFG_sud V_n U).F (dnStepFG_sud V_n U).hF_herm
        (dnStepFG_sud V_n U).hF_tr : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    ((expIsud n (dnStepFG_sud V_n U).G (dnStepFG_sud V_n U).hG_herm
        (dnStepFG_sud V_n U).hG_tr : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) with hgC_def
  -- Rewrite U = V_n · Δ, factor, submultiplicativity, M-bound × cubic.
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
        have h_cubic_nn : (0 : ℝ) ≤ 320 * δ ^ 3 := by positivity
        have h_gC_nn : (0 : ℝ) ≤ ‖gC - ((V_n⁻¹ * U :
            ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
            Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ := norm_nonneg _
        have h_Mn : (0 : ℝ) ≤ ((n : ℝ) + 2) := by positivity
        calc ‖(V_n : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ *
              ‖gC - ((V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) :
                Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖
            ≤ ((n : ℝ) + 2) * (320 * δ ^ 3) :=
              mul_le_mul h_M h_cubic h_gC_nn h_Mn

/-! ## Telescoping term 1: stability term -/

/-- **SU(d) stability-term wrapper**: instantiates the dimension-generic
`groupCommutator_stability_nearIdentity` at `M = d`, supplying the SU(d)
M-bounds (`SUd_val_linftyOpNorm_le` + inverse via `SUd_subtype_inv_val_eq_matrix_inv`)
and the det-unit hypotheses (`det = 1` for `SU(d)` elements) internally.

For `SU(d)` elements `A_F, A_G` (base points) and `ρA_F, ρA_G` (their
ε-perturbations) with near-identity radius `η` (on `‖A_G − 1‖, ‖A_F⁻¹ − 1‖`)
and perturbation `ε` (on `‖ρA_F − A_F‖, ‖ρA_G − A_G‖`),

  `‖gC(ρA_F, ρA_G) − gC(A_F, A_G)‖ ≤ 2·(d² + d⁴)·ε·η + (d⁴ + d⁶)·ε²`.

In the SK recursion `η = O(δ_lie)` and `ε = ε_n`, giving the `O(ε_n^{3/2})`
super-quadratic stability shrinkage. -/
lemma stability_term_bound {d : ℕ} [Nonempty (Fin d)]
    (A_F A_G ρA_F ρA_G : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (η ε : ℝ) (hη_nn : 0 ≤ η) (hε_nn : 0 ≤ ε)
    (h_A_G_near : ‖(A_G : Matrix (Fin d) (Fin d) ℂ) - 1‖ ≤ η)
    (h_A_F_inv_near : ‖(A_F : Matrix (Fin d) (Fin d) ℂ)⁻¹ - 1‖ ≤ η)
    (h_F_diff : ‖(ρA_F : Matrix (Fin d) (Fin d) ℂ) -
        (A_F : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ε)
    (h_G_diff : ‖(ρA_G : Matrix (Fin d) (Fin d) ℂ) -
        (A_G : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ε) :
    ‖groupCommutator (ρA_F : Matrix (Fin d) (Fin d) ℂ) (ρA_G : Matrix (Fin d) (Fin d) ℂ) -
        groupCommutator (A_F : Matrix (Fin d) (Fin d) ℂ)
          (A_G : Matrix (Fin d) (Fin d) ℂ)‖ ≤
      2 * ((d : ℝ)^2 + (d : ℝ)^4) * ε * η + ((d : ℝ)^4 + (d : ℝ)^6) * ε^2 := by
  have h_det : ∀ x : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
      IsUnit (x : Matrix (Fin d) (Fin d) ℂ).det := by
    intro x
    have h_mem := x.property
    rw [Matrix.mem_specialUnitaryGroup_iff] at h_mem
    rw [h_mem.2]
    exact isUnit_one
  have h_inv_M : ∀ x : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
      ‖(x : Matrix (Fin d) (Fin d) ℂ)⁻¹‖ ≤ (d : ℝ) := by
    intro x
    rw [← SUd_subtype_inv_val_eq_matrix_inv x]
    exact SUd_val_linftyOpNorm_le x⁻¹
  exact GroupCommutatorNearIdentity.groupCommutator_stability_nearIdentity
    (A_F : Matrix (Fin d) (Fin d) ℂ) (A_G : Matrix (Fin d) (Fin d) ℂ)
    (ρA_F : Matrix (Fin d) (Fin d) ℂ) (ρA_G : Matrix (Fin d) (Fin d) ℂ)
    η ε (d : ℝ) hη_nn hε_nn (by positivity)
    (SUd_val_linftyOpNorm_le ρA_F) (SUd_val_linftyOpNorm_le ρA_G)
    (h_inv_M A_F) (h_inv_M A_G) (h_inv_M ρA_F) (h_inv_M ρA_G)
    h_A_G_near h_A_F_inv_near h_F_diff h_G_diff
    (h_det A_F) (h_det ρA_F) (h_det A_G) (h_det ρA_G)

end SKEFTHawking.FKLW.GenericSUd
