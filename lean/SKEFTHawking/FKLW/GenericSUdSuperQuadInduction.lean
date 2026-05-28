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

/-- **Stability term through V_n** (`Cstab = d·stability`): for `SU(d)` element
`V_n`, `‖ρ(V_n)·gC(ρA_F,ρA_G) − ρ(V_n)·gC(A_F,A_G)‖ ≤ d·(2(d²+d⁴)·ε·η + (d⁴+d⁶)·ε²)`.
Factors as `ρ(V_n)·(gC(ρA_F,ρA_G) − gC(A_F,A_G))`, then M-bound (S91) × `stability_term_bound`. -/
lemma stability_term_through_Vn {d : ℕ} [Nonempty (Fin d)]
    (V_n A_F A_G ρA_F ρA_G : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (η ε : ℝ) (hη_nn : 0 ≤ η) (hε_nn : 0 ≤ ε)
    (h_A_G_near : ‖(A_G : Matrix (Fin d) (Fin d) ℂ) - 1‖ ≤ η)
    (h_A_F_inv_near : ‖(A_F : Matrix (Fin d) (Fin d) ℂ)⁻¹ - 1‖ ≤ η)
    (h_F_diff : ‖(ρA_F : Matrix (Fin d) (Fin d) ℂ) -
        (A_F : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ε)
    (h_G_diff : ‖(ρA_G : Matrix (Fin d) (Fin d) ℂ) -
        (A_G : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ε) :
    ‖(V_n : Matrix (Fin d) (Fin d) ℂ) *
        groupCommutator (ρA_F : Matrix (Fin d) (Fin d) ℂ) (ρA_G : Matrix (Fin d) (Fin d) ℂ) -
        (V_n : Matrix (Fin d) (Fin d) ℂ) *
        groupCommutator (A_F : Matrix (Fin d) (Fin d) ℂ)
          (A_G : Matrix (Fin d) (Fin d) ℂ)‖ ≤
      (d : ℝ) * (2 * ((d : ℝ)^2 + (d : ℝ)^4) * ε * η + ((d : ℝ)^4 + (d : ℝ)^6) * ε^2) := by
  rw [← Matrix.mul_sub]
  have h_stab := stability_term_bound A_F A_G ρA_F ρA_G η ε hη_nn hε_nn
    h_A_G_near h_A_F_inv_near h_F_diff h_G_diff
  have h_stab_nn : (0 : ℝ) ≤ 2 * ((d : ℝ)^2 + (d : ℝ)^4) * ε * η +
      ((d : ℝ)^4 + (d : ℝ)^6) * ε^2 := by positivity
  calc ‖(V_n : Matrix (Fin d) (Fin d) ℂ) *
        (groupCommutator (ρA_F : Matrix (Fin d) (Fin d) ℂ)
            (ρA_G : Matrix (Fin d) (Fin d) ℂ) -
          groupCommutator (A_F : Matrix (Fin d) (Fin d) ℂ)
            (A_G : Matrix (Fin d) (Fin d) ℂ))‖
      ≤ ‖(V_n : Matrix (Fin d) (Fin d) ℂ)‖ *
          ‖groupCommutator (ρA_F : Matrix (Fin d) (Fin d) ℂ)
              (ρA_G : Matrix (Fin d) (Fin d) ℂ) -
            groupCommutator (A_F : Matrix (Fin d) (Fin d) ℂ)
              (A_G : Matrix (Fin d) (Fin d) ℂ)‖ := Matrix.linfty_opNorm_mul _ _
    _ ≤ (d : ℝ) * (2 * ((d : ℝ)^2 + (d : ℝ)^4) * ε * η + ((d : ℝ)^4 + (d : ℝ)^6) * ε^2) :=
        mul_le_mul (SUd_val_linftyOpNorm_le V_n) h_stab (norm_nonneg _) (by positivity)

/-! ## Regime brick: δ_lie = ‖F‖ ≤ (m+2)^5·√ε from the θ-bound -/

/-- **F-norm in √ε form**: given `θ = ‖(-i)·matrixLog Δ‖ ≤ 2·(n+2)·ε`,
`‖(dnStepFG_sud V_n U).F‖ ≤ (n+2)^5·√ε`. Composes S91's `(n+2)^4·√(θ/2)`
with `√(θ/2) ≤ √((n+2)ε) ≤ (n+2)·√ε` (the `√(n+2) ≤ n+2` step). This is the
`hδ_le` input shape required by the super-quad numeric chain. -/
lemma dnStepFG_sud_F_norm_le_sqrt_eps {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) (ε : ℝ)
    (h_theta_le : ‖((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 2 * ((n : ℝ) + 2) * ε) :
    ‖(dnStepFG_sud V_n U).F‖ ≤ ((n : ℝ) + 2) ^ 5 * Real.sqrt ε := by
  have hd_ge_one : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  refine le_trans (dnStepFG_sud_F_norm_le_poly V_n U) ?_
  set θ := ‖((-Complex.I) • matrixLog (n + 2)
    (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
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

/-- **G-norm in √ε form** (mirror of F). -/
lemma dnStepFG_sud_G_norm_le_sqrt_eps {n : ℕ}
    (V_n U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)) (ε : ℝ)
    (h_theta_le : ‖((-Complex.I) • matrixLog (n + 2)
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
        Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)‖ ≤ 2 * ((n : ℝ) + 2) * ε) :
    ‖(dnStepFG_sud V_n U).G‖ ≤ ((n : ℝ) + 2) ^ 5 * Real.sqrt ε := by
  have hd_ge_one : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  refine le_trans (dnStepFG_sud_G_norm_le_poly V_n U) ?_
  set θ := ‖((-Complex.I) • matrixLog (n + 2)
    (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin (n + 2)) ℂ)).val :
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

/-! ## Numeric chain prep: rpow ^(3/2) conversions -/

/-- `ε^(3/2) = (√ε)³` for `ε ≥ 0`. The bridge from the recursion's `ε_seq`
super-quadratic `^(3/2 : ℝ)` rpow exponent to the nat-power arithmetic of the
telescoping bounds (everything reduces to powers of `s = √ε`). -/
lemma rpow_three_halves_eq_sqrt_cube (ε : ℝ) (hε_nn : 0 ≤ ε) :
    ε ^ (3 / 2 : ℝ) = (Real.sqrt ε) ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (ε ^ (1 / 2 : ℝ)) 3, ← Real.rpow_mul hε_nn]
  norm_num

/-- **Cubic term in ε^(3/2) form**: `δ_lie³ ≤ (m+2)^15 · ε^(3/2)` from
`δ_lie ≤ (m+2)^5·√ε`. (Then `(m+2)·320·δ_lie³ ≤ 320·(m+2)^16·ε^(3/2)`.) -/
lemma cubic_le_rpow {m : ℕ} (ε δ_lie : ℝ) (hε_nn : 0 ≤ ε) (hδ_nn : 0 ≤ δ_lie)
    (hδ_le : δ_lie ≤ ((m : ℝ) + 2) ^ 5 * Real.sqrt ε) :
    δ_lie ^ 3 ≤ ((m : ℝ) + 2) ^ 15 * ε ^ (3 / 2 : ℝ) := by
  rw [rpow_three_halves_eq_sqrt_cube ε hε_nn]
  calc δ_lie ^ 3 ≤ (((m : ℝ) + 2) ^ 5 * Real.sqrt ε) ^ 3 := by gcongr
    _ = ((m : ℝ) + 2) ^ 15 * (Real.sqrt ε) ^ 3 := by ring

/-- **`ε·η` term in ε^(3/2) form**: `ε·η ≤ 3·(m+2)^5 · ε^(3/2)` from
`η ≤ 3·δ_lie ≤ 3·(m+2)^5·√ε` and `ε = (√ε)²`. -/
lemma eps_eta_le_rpow {m : ℕ} (ε δ_lie η : ℝ) (hε_nn : 0 ≤ ε)
    (hδ_le : δ_lie ≤ ((m : ℝ) + 2) ^ 5 * Real.sqrt ε)
    (hη_le : η ≤ 3 * δ_lie) :
    ε * η ≤ 3 * ((m : ℝ) + 2) ^ 5 * ε ^ (3 / 2 : ℝ) := by
  have h_s_nn : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have h_s_sq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε_nn
  have hη_le' : η ≤ 3 * (((m : ℝ) + 2) ^ 5 * Real.sqrt ε) := le_trans hη_le (by linarith)
  rw [rpow_three_halves_eq_sqrt_cube ε hε_nn]
  calc ε * η
      ≤ ε * (3 * (((m : ℝ) + 2) ^ 5 * Real.sqrt ε)) :=
        mul_le_mul_of_nonneg_left hη_le' hε_nn
    _ = 3 * ((m : ℝ) + 2) ^ 5 * (Real.sqrt ε ^ 2 * Real.sqrt ε) := by rw [h_s_sq]; ring
    _ = 3 * ((m : ℝ) + 2) ^ 5 * (Real.sqrt ε) ^ 3 := by ring

/-- **`ε²` term in ε^(3/2) form**: `ε² ≤ √(2·ε₀_sud(m+2)) · ε^(3/2)` from
`ε ≤ 2·ε₀_sud(m+2)`. Since `√(2·ε₀_sud) = 1/(2·K_compose_sud)` is tiny, this
makes the `ε²` (super-cubic) stability term negligible vs the `ε^(3/2)` budget. -/
lemma eps_sq_le_rpow {m : ℕ} (ε : ℝ) (hε_nn : 0 ≤ ε)
    (hε_le : ε ≤ 2 * ε₀_sud (m + 2)) :
    ε ^ 2 ≤ Real.sqrt (2 * ε₀_sud (m + 2)) * ε ^ (3 / 2 : ℝ) := by
  have h_s_sq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε_nn
  have h_s_le : Real.sqrt ε ≤ Real.sqrt (2 * ε₀_sud (m + 2)) := Real.sqrt_le_sqrt hε_le
  have h_s3_nn : (0 : ℝ) ≤ (Real.sqrt ε) ^ 3 := by positivity
  rw [rpow_three_halves_eq_sqrt_cube ε hε_nn]
  have h_eq : ε ^ 2 = (Real.sqrt ε) ^ 3 * Real.sqrt ε := by
    have h4 : (Real.sqrt ε) ^ 4 = ε ^ 2 := by
      rw [show (Real.sqrt ε) ^ 4 = ((Real.sqrt ε) ^ 2) ^ 2 from by ring, h_s_sq]
    calc ε ^ 2 = (Real.sqrt ε) ^ 4 := h4.symm
      _ = (Real.sqrt ε) ^ 3 * Real.sqrt ε := by ring
  rw [h_eq]
  calc (Real.sqrt ε) ^ 3 * Real.sqrt ε
      ≤ (Real.sqrt ε) ^ 3 * Real.sqrt (2 * ε₀_sud (m + 2)) :=
        mul_le_mul_of_nonneg_left h_s_le h_s3_nn
    _ = Real.sqrt (2 * ε₀_sud (m + 2)) * (Real.sqrt ε) ^ 3 := by ring

/-- **Super-quad numeric chain**: the assembled per-step constant is `≤ K_compose_sud·ε^(3/2)`.

`(m+2)·[2((m+2)²+(m+2)⁴)·ε·η + ((m+2)⁴+(m+2)⁶)·ε²] + (m+2)·320·δ_lie³ ≤ K_compose_sud(m+2)·ε^(3/2)`
given `δ_lie ≤ (m+2)^5·√ε`, `η ≤ 3·δ_lie`, `ε ≤ 2·ε₀_sud(m+2)`. Each term reduces to
a `d^k·ε^(3/2)` multiple (S97/S98), summing to `≤ (12+2+320)·d^16·ε^(3/2) = 334·d^16·ε^(3/2)
≤ 1024·d^16·ε^(3/2) = K_compose_sud·ε^(3/2)`. -/
lemma super_quad_numeric_chain {m : ℕ} (ε δ_lie η : ℝ)
    (hε_nn : 0 ≤ ε) (hδ_nn : 0 ≤ δ_lie)
    (hδ_le : δ_lie ≤ ((m : ℝ) + 2) ^ 5 * Real.sqrt ε)
    (hη_le : η ≤ 3 * δ_lie)
    (hε_le : ε ≤ 2 * ε₀_sud (m + 2)) :
    ((m : ℝ) + 2) * (2 * (((m : ℝ) + 2) ^ 2 + ((m : ℝ) + 2) ^ 4) * ε * η +
        (((m : ℝ) + 2) ^ 4 + ((m : ℝ) + 2) ^ 6) * ε ^ 2) +
        ((m : ℝ) + 2) * (320 * δ_lie ^ 3) ≤
      K_compose_sud (m + 2) * ε ^ (3 / 2 : ℝ) := by
  have hd_ge_one : (1 : ℝ) ≤ (m : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith
  have hd_nn : (0 : ℝ) ≤ (m : ℝ) + 2 := by linarith
  set P := ε ^ (3 / 2 : ℝ) with hP_def
  have hP_nn : 0 ≤ P := Real.rpow_nonneg hε_nn _
  have h_cubic := cubic_le_rpow ε δ_lie hε_nn hδ_nn hδ_le
  have h_eta := eps_eta_le_rpow ε δ_lie η hε_nn hδ_le hη_le
  have h_sq0 := eps_sq_le_rpow ε hε_nn hε_le
  -- √(2·ε₀_sud) ≤ 1
  have h_two_ε₀_le_one : 2 * ε₀_sud (m + 2) ≤ 1 := by
    have h_cal := K_compose_sud_sq_times_two_ε₀_sud (d := m + 2) (by omega)
    have hK := K_compose_sud_ge_1024 (d := m + 2) (by omega)
    nlinarith [h_cal, hK, ε₀_sud_pos (d := m + 2) (by omega),
      K_compose_sud_pos (d := m + 2) (by omega)]
  have h_sqrt_le_one : Real.sqrt (2 * ε₀_sud (m + 2)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt h_two_ε₀_le_one
  have h_sq : ε ^ 2 ≤ P := by
    refine le_trans h_sq0 ?_
    have := mul_le_mul_of_nonneg_right h_sqrt_le_one hP_nn
    simpa using this
  -- power monotonicity
  have hp8 : ((m : ℝ) + 2) ^ 8 ≤ ((m : ℝ) + 2) ^ 16 := pow_le_pow_right₀ hd_ge_one (by norm_num)
  have hp10 : ((m : ℝ) + 2) ^ 10 ≤ ((m : ℝ) + 2) ^ 16 := pow_le_pow_right₀ hd_ge_one (by norm_num)
  have hp5 : ((m : ℝ) + 2) ^ 5 ≤ ((m : ℝ) + 2) ^ 16 := pow_le_pow_right₀ hd_ge_one (by norm_num)
  have hp7 : ((m : ℝ) + 2) ^ 7 ≤ ((m : ℝ) + 2) ^ 16 := pow_le_pow_right₀ hd_ge_one (by norm_num)
  -- term 1: d·(2(d²+d⁴)·ε·η) ≤ 12·d^16·P
  have hT1 : ((m : ℝ) + 2) * (2 * (((m : ℝ) + 2) ^ 2 + ((m : ℝ) + 2) ^ 4) * ε * η) ≤
      12 * ((m : ℝ) + 2) ^ 16 * P := by
    have hcoef_nn : (0 : ℝ) ≤ 2 * (((m : ℝ) + 2) ^ 2 + ((m : ℝ) + 2) ^ 4) * ((m : ℝ) + 2) := by
      positivity
    calc ((m : ℝ) + 2) * (2 * (((m : ℝ) + 2) ^ 2 + ((m : ℝ) + 2) ^ 4) * ε * η)
        = (2 * (((m : ℝ) + 2) ^ 2 + ((m : ℝ) + 2) ^ 4) * ((m : ℝ) + 2)) * (ε * η) := by ring
      _ ≤ (2 * (((m : ℝ) + 2) ^ 2 + ((m : ℝ) + 2) ^ 4) * ((m : ℝ) + 2)) *
            (3 * ((m : ℝ) + 2) ^ 5 * P) := mul_le_mul_of_nonneg_left h_eta hcoef_nn
      _ = (6 * ((m : ℝ) + 2) ^ 8 + 6 * ((m : ℝ) + 2) ^ 10) * P := by ring
      _ ≤ 12 * ((m : ℝ) + 2) ^ 16 * P := by
          nlinarith [mul_le_mul_of_nonneg_right hp8 hP_nn,
            mul_le_mul_of_nonneg_right hp10 hP_nn]
  -- term 2: d·((d⁴+d⁶)·ε²) ≤ 2·d^16·P
  have hT2 : ((m : ℝ) + 2) * ((((m : ℝ) + 2) ^ 4 + ((m : ℝ) + 2) ^ 6) * ε ^ 2) ≤
      2 * ((m : ℝ) + 2) ^ 16 * P := by
    have hcoef_nn : (0 : ℝ) ≤ (((m : ℝ) + 2) ^ 4 + ((m : ℝ) + 2) ^ 6) * ((m : ℝ) + 2) := by
      positivity
    calc ((m : ℝ) + 2) * ((((m : ℝ) + 2) ^ 4 + ((m : ℝ) + 2) ^ 6) * ε ^ 2)
        = ((((m : ℝ) + 2) ^ 4 + ((m : ℝ) + 2) ^ 6) * ((m : ℝ) + 2)) * ε ^ 2 := by ring
      _ ≤ ((((m : ℝ) + 2) ^ 4 + ((m : ℝ) + 2) ^ 6) * ((m : ℝ) + 2)) * P :=
          mul_le_mul_of_nonneg_left h_sq hcoef_nn
      _ = (((m : ℝ) + 2) ^ 5 + ((m : ℝ) + 2) ^ 7) * P := by ring
      _ ≤ 2 * ((m : ℝ) + 2) ^ 16 * P := by
          nlinarith [mul_le_mul_of_nonneg_right hp5 hP_nn,
            mul_le_mul_of_nonneg_right hp7 hP_nn]
  -- term 3: d·(320·δ³) ≤ 320·d^16·P
  have hT3 : ((m : ℝ) + 2) * (320 * δ_lie ^ 3) ≤ 320 * ((m : ℝ) + 2) ^ 16 * P := by
    calc ((m : ℝ) + 2) * (320 * δ_lie ^ 3)
        = 320 * ((m : ℝ) + 2) * δ_lie ^ 3 := by ring
      _ ≤ 320 * ((m : ℝ) + 2) * (((m : ℝ) + 2) ^ 15 * P) := by
          have hc : (0 : ℝ) ≤ 320 * ((m : ℝ) + 2) := by positivity
          exact mul_le_mul_of_nonneg_left h_cubic hc
      _ = 320 * ((m : ℝ) + 2) ^ 16 * P := by ring
  -- assemble
  rw [show K_compose_sud (m + 2) = 1024 * ((m : ℝ) + 2) ^ 16 from by
    unfold K_compose_sud; push_cast; ring]
  have h_dP_nn : (0 : ℝ) ≤ ((m : ℝ) + 2) ^ 16 * P := by positivity
  calc ((m : ℝ) + 2) * (2 * (((m : ℝ) + 2) ^ 2 + ((m : ℝ) + 2) ^ 4) * ε * η +
          (((m : ℝ) + 2) ^ 4 + ((m : ℝ) + 2) ^ 6) * ε ^ 2) +
          ((m : ℝ) + 2) * (320 * δ_lie ^ 3)
      = ((m : ℝ) + 2) * (2 * (((m : ℝ) + 2) ^ 2 + ((m : ℝ) + 2) ^ 4) * ε * η) +
          ((m : ℝ) + 2) * ((((m : ℝ) + 2) ^ 4 + ((m : ℝ) + 2) ^ 6) * ε ^ 2) +
          ((m : ℝ) + 2) * (320 * δ_lie ^ 3) := by ring
    _ ≤ 12 * ((m : ℝ) + 2) ^ 16 * P + 2 * ((m : ℝ) + 2) ^ 16 * P +
          320 * ((m : ℝ) + 2) ^ 16 * P := by linarith [hT1, hT2, hT3]
    _ = 334 * ((m : ℝ) + 2) ^ 16 * P := by ring
    _ ≤ 1024 * ((m : ℝ) + 2) ^ 16 * P := by nlinarith [h_dP_nn]

/-! ## Combine: single-step error from the two telescoping terms -/

/-- **Single-step error combine**: given the stability term bound `Cstab` on
`‖ρ(V_n)·gC(ρsk A_F, ρsk A_G) − ρ(V_n)·gC(A_F, A_G)‖` and the cubic term bound
`Ccubic` on `‖ρ(V_n)·gC(A_F, A_G) − U‖`, the level-(n+1) error is `≤ Cstab + Ccubic`.

Composes the composition identity (S92) with the triangle inequality
`a − U = (a − b) + (b − U)`. This is the structural combine; the actual
`Cstab = d·stability` (S91 M-bound + S94) and `Ccubic = d·320δ³` (S93) plug in,
and the numeric chain then bounds `Cstab + Ccubic ≤ K_compose_sud·ε_n^{3/2}`. -/
lemma skApproxC_sud_succ_error_le_combine {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (n : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ))
    (Cstab Ccubic : ℝ)
    (h_stab_term :
      let V_n_word := skApproxC_generic_sud gs baseFinder h_det_pred n U
      let data := dnStepFG_sud (gs.ρ_hom V_n_word) U
      let A_F := expIsud_of_det_predicate h_det_pred data.F data.hF_herm data.hF_tr
      let A_G := expIsud_of_det_predicate h_det_pred data.G data.hG_herm data.hG_tr
      ‖((gs.ρ_hom V_n_word : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) *
          groupCommutator
            ((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n A_F) :
                ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
                Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
            ((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n A_G) :
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
      let V_n_word := skApproxC_generic_sud gs baseFinder h_det_pred n U
      let data := dnStepFG_sud (gs.ρ_hom V_n_word) U
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
    ‖((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred (n + 1) U) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤ Cstab + Ccubic := by
  simp only at h_stab_term h_cubic_term
  rw [skApproxC_generic_sud_succ_rho_val gs baseFinder h_det_pred n U]
  set a := ((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U) :
      ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) *
    groupCommutator
      ((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n
          (expIsud_of_det_predicate h_det_pred
            (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).F
            (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).hF_herm
            (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).hF_tr)) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
      ((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n
          (expIsud_of_det_predicate h_det_pred
            (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).G
            (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).hG_herm
            (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).hG_tr)) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) with ha_def
  set b := ((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U) :
      ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) *
    groupCommutator
      ((expIsud_of_det_predicate h_det_pred
          (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).F
          (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).hF_herm
          (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).hF_tr :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
      ((expIsud_of_det_predicate h_det_pred
          (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).G
          (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).hG_herm
          (dnStepFG_sud (gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred n U)) U).hG_tr :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
          Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) with hb_def
  calc ‖a - (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖
      = ‖(a - b) + (b - (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖a - b‖ + ‖b - (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ := norm_add_le _ _
    _ ≤ Cstab + Ccubic := add_le_add h_stab_term h_cubic_term

end SKEFTHawking.FKLW.GenericSUd
