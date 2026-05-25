/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Wave 4b — Generic Solovay-Kitaev super-quadratic discharge

The alphabet-agnostic substantive port of Phase 6t Path A Option C's
`SkApproxCSuperQuadraticBound_holds` (≈800 LoC kernel-only induction)
to the generic `GeneratingSet` framework. Given any `gs : GeneratingSet`
and any base-case finder `baseFinder : ↥SU(2) → gs.W` satisfying the
`(2 * ε₀)`-approximation property, the generic recursion
`skApproxC_generic gs baseFinder` satisfies the super-quadratic shrinkage
bound at `K_compose = 1024`.

## Headline theorems

  * `SkApproxCSuperQuadraticBound_generic_holds` — UNCONDITIONAL discharge
    (hypothesizing only `BaseFinder_approximates_within gs baseFinder (2·ε₀)`).
    Mirrors Phase 6t's `SkApproxCSuperQuadraticBound_holds` structure
    via induction on the recursion depth, with the Fibonacci-specific
    `ρ_Fib_SU2_*` multiplicativity lemmas replaced by the generic
    `MonoidHom.map_mul` / `MonoidHom.map_inv` of `gs.ρ_hom`.

  * `solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional`
    — UNCONDITIONAL bundled-strict generic headline, composing the
    discharge with Wave 6's conditional `*_tight` headline.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected — proof decomposed via small
  `have` sub-lemmas mirroring the Phase 6t structure.
- **#15** (no new axioms): respected — zero new project-local axioms.
- **Strengthening discipline**: the generic discharge takes the
  `BaseFinder_approximates_within` hypothesis (load-bearing — without
  it, the level-0 base case is not bounded by `2 * ε₀`). The headline
  is non-trivial (composing the substantive cubic + stability cascade
  on the abstract `gs.ρ_hom`).

-/

import SKEFTHawking.FKLW.GenericSolovayKitaevRecursion
import SKEFTHawking.FKLW.GenericSolovayKitaevQuantitative

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SU2BalancedCommutator
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound
  SKEFTHawking.FKLW.OneParameterSubgroupSU2
  SKEFTHawking.FKLW.SolovayKitaevPathA

/-! ## 1. Alphabet-agnostic substrate lemmas

Ports of Phase 6t's `dnStepFG_*` lemmas (typed on `FibonacciBraidWord`) to
the alphabet-agnostic `dnStepFG_su2 V_n U` form. Each port is a direct
substitution: the original lemmas operate on `ρ_Fib_SU2 V_n_braid` as a
SU(2) value, so the alphabet-agnostic versions take `V_n : ↥SU(2)`
directly. Bodies are structurally identical.
-/

/-- **Alphabet-agnostic dnStepFG F-norm bound**. -/
lemma dnStepFG_su2_F_norm_le_sqrt_theta_half
    (V_n : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    let Δ := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    let θ := ‖((-Complex.I) • Y_h Δ.val : Matrix (Fin 2) (Fin 2) ℂ)‖
    ‖(dnStepFG_su2 V_n U).F‖ ≤ Real.sqrt (θ / 2) := by
  simp only [dnStepFG_su2]
  split_ifs with h_valid
  · set Δ_local := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    set H_local : Matrix (Fin 2) (Fin 2) ℂ :=
      ((-Complex.I) : ℂ) • Y_h Δ_local.val
    set θ_local : ℝ := ‖H_local‖
    have h_ex_spec :=
      (balanced_commutator_general_axis_lie_traceless
        (((1 / θ_local : ℝ) : ℂ) • H_local)
        (IsHermitian_real_smul (neg_I_smul_Y_h_isHermitian Δ_local.property)
          (1 / θ_local))
        (smul_trace_zero (neg_I_smul_Y_h_trace_zero Δ_local.property) _)
        (norm_normalize h_valid.1)
        θ_local h_valid.1.le h_valid.2).choose_spec.choose_spec
    exact h_ex_spec.2.2.2.2.1
  · show ‖(0 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ _
    rw [norm_zero]
    exact Real.sqrt_nonneg _

/-- **Alphabet-agnostic dnStepFG G-norm bound**. -/
lemma dnStepFG_su2_G_norm_le_sqrt_theta_half
    (V_n : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    let Δ := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    let θ := ‖((-Complex.I) • Y_h Δ.val : Matrix (Fin 2) (Fin 2) ℂ)‖
    ‖(dnStepFG_su2 V_n U).G‖ ≤ Real.sqrt (θ / 2) := by
  simp only [dnStepFG_su2]
  split_ifs with h_valid
  · set Δ_local := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    set H_local : Matrix (Fin 2) (Fin 2) ℂ :=
      ((-Complex.I) : ℂ) • Y_h Δ_local.val
    set θ_local : ℝ := ‖H_local‖
    have h_ex_spec :=
      (balanced_commutator_general_axis_lie_traceless
        (((1 / θ_local : ℝ) : ℂ) • H_local)
        (IsHermitian_real_smul (neg_I_smul_Y_h_isHermitian Δ_local.property)
          (1 / θ_local))
        (smul_trace_zero (neg_I_smul_Y_h_trace_zero Δ_local.property) _)
        (norm_normalize h_valid.1)
        θ_local h_valid.1.le h_valid.2).choose_spec.choose_spec
    exact h_ex_spec.2.2.2.2.2.1
  · show ‖(0 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ _
    rw [norm_zero]
    exact Real.sqrt_nonneg _

/-- **Alphabet-agnostic dnStepFG commutator identity (valid branch)**. -/
lemma dnStepFG_su2_commutator_identity_valid
    (V_n : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_valid : 0 < ‖((-Complex.I) • Y_h
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ∧
        ‖((-Complex.I) • Y_h
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1) :
    let data := dnStepFG_su2 V_n U
    let Δ := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    data.F * data.G - data.G * data.F = -Y_h Δ.val := by
  simp only [dnStepFG_su2]
  set Δ_local := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
  set H_local : Matrix (Fin 2) (Fin 2) ℂ :=
    ((-Complex.I) : ℂ) • Y_h Δ_local.val
  set θ_local : ℝ := ‖H_local‖
  rw [dif_pos h_valid]
  set ex_data := balanced_commutator_general_axis_lie_traceless
      (((1 / θ_local : ℝ) : ℂ) • H_local)
      (IsHermitian_real_smul (neg_I_smul_Y_h_isHermitian Δ_local.property)
        (1 / θ_local))
      (smul_trace_zero (neg_I_smul_Y_h_trace_zero Δ_local.property) _)
      (norm_normalize h_valid.1)
      θ_local h_valid.1.le h_valid.2 with hex_def
  have h_comm_eq : ex_data.choose * ex_data.choose_spec.choose -
                   ex_data.choose_spec.choose * ex_data.choose =
                   -(((θ_local : ℂ) * Complex.I)) •
                     (((1 / θ_local : ℝ) : ℂ) • H_local) :=
    ex_data.choose_spec.choose_spec.2.2.2.2.2.2
  have h_theta_pos : (0 : ℝ) < θ_local := h_valid.1
  have h_theta_ne : (θ_local : ℂ) ≠ 0 := by
    have : (θ_local : ℝ) ≠ 0 := ne_of_gt h_theta_pos
    exact_mod_cast this
  have h_scalar : -((θ_local : ℂ) * Complex.I) * (((1 / θ_local : ℝ) : ℂ)) =
                  -Complex.I := by
    have h_div : ((1 / θ_local : ℝ) : ℂ) = ((θ_local : ℂ))⁻¹ := by
      push_cast
      rw [one_div]
    rw [h_div]
    field_simp
  rw [h_comm_eq, smul_smul, h_scalar]
  show -Complex.I • ((-Complex.I : ℂ) • Y_h Δ_local.val) = -Y_h Δ_local.val
  rw [smul_smul]
  ring_nf
  simp [Complex.I_sq]

/-- **Alphabet-agnostic dnStepFG exp(-[F,G]) = Δ identity**. -/
lemma dnStepFG_su2_exp_neg_comm_eq_Delta
    (V_n : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_valid : 0 < ‖((-Complex.I) • Y_h
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ∧
        ‖((-Complex.I) • Y_h
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1)
    (h_ne_neg_two : (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val.trace.re ≠ -2) :
    let data := dnStepFG_su2 V_n U
    let Δ := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    NormedSpace.exp (-(data.F * data.G - data.G * data.F)) = Δ.val := by
  dsimp only
  set Δ := (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) with hΔ_def
  have h_comm := dnStepFG_su2_commutator_identity_valid V_n U h_valid
  dsimp only at h_comm
  have h_neg_comm : -((dnStepFG_su2 V_n U).F * (dnStepFG_su2 V_n U).G -
                       (dnStepFG_su2 V_n U).G * (dnStepFG_su2 V_n U).F) =
                    Y_h Δ.val := by
    have h1 : -((dnStepFG_su2 V_n U).F * (dnStepFG_su2 V_n U).G -
              (dnStepFG_su2 V_n U).G * (dnStepFG_su2 V_n U).F) =
           -(-Y_h Δ.val) := by rw [h_comm]
    rw [h1]
    exact neg_neg _
  rw [h_neg_comm]
  have h_expAmbient :=
    SU2_expAmbient_Y_h_eq Δ.property h_ne_neg_two
  show NormedSpace.exp (Y_h Δ.val) = Δ.val
  rw [show NormedSpace.exp (Y_h Δ.val) =
      SU2MatrixExp.expAmbient (Y_h Δ.val) from rfl]
  exact h_expAmbient

/-- **Alphabet-agnostic dnStepFG DN cubic composition bound (valid branch)**. -/
lemma dnStepFG_su2_gC_minus_Delta_norm_le_cubic
    (V_n : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_valid : 0 < ‖((-Complex.I) • Y_h
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ∧
        ‖((-Complex.I) • Y_h
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1)
    (h_ne_neg_two : (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val.trace.re ≠ -2)
    (δ : ℝ) (hδ_nn : 0 ≤ δ) (hδ_le_one : δ ≤ 1)
    (hF_norm : ‖(dnStepFG_su2 V_n U).F‖ ≤ δ)
    (hG_norm : ‖(dnStepFG_su2 V_n U).G‖ ≤ δ) :
    ‖SKEFTHawking.FKLW.GroupCommutator.groupCommutator
        ((expIsu2 (dnStepFG_su2 V_n U).F (dnStepFG_su2 V_n U).hF_herm
                  (dnStepFG_su2 V_n U).hF_tr :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ)
        ((expIsu2 (dnStepFG_su2 V_n U).G (dnStepFG_su2 V_n U).hG_herm
                  (dnStepFG_su2 V_n U).hG_tr :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) -
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val‖ ≤ 320 * δ ^ 3 := by
  rw [expIsu2_val, expIsu2_val]
  have h_bch := SKEFTHawking.FKLW.GroupCommutator.groupCommutator_lie_bracket_cubic_remainder
                  δ hδ_nn hδ_le_one (dnStepFG_su2 V_n U).F (dnStepFG_su2 V_n U).G
                  hF_norm hG_norm
  have h_exp_eq_Δ := dnStepFG_su2_exp_neg_comm_eq_Delta V_n U h_valid h_ne_neg_two
  dsimp only at h_exp_eq_Δ
  rw [show SU2MatrixExp.expAmbient (Complex.I • (dnStepFG_su2 V_n U).F) =
      NormedSpace.exp (Complex.I • (dnStepFG_su2 V_n U).F) from rfl]
  rw [show SU2MatrixExp.expAmbient (Complex.I • (dnStepFG_su2 V_n U).G) =
      NormedSpace.exp (Complex.I • (dnStepFG_su2 V_n U).G) from rfl]
  rw [← h_exp_eq_Δ]
  exact h_bch

/-- **Alphabet-agnostic dnStepFG invalid branch gives F = G = 0**. -/
lemma dnStepFG_su2_invalid_F_zero
    (V_n : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_invalid : ¬(0 < ‖((-Complex.I) • Y_h
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ∧
        ‖((-Complex.I) • Y_h
        (V_n⁻¹ * U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1)) :
    (dnStepFG_su2 V_n U).F = 0 ∧ (dnStepFG_su2 V_n U).G = 0 := by
  simp only [dnStepFG_su2]
  rw [dif_neg h_invalid]
  exact ⟨rfl, rfl⟩

/-! ## 2. Generic multiplicativity lemmas

Alphabet-agnostic ports of `ρ_Fib_SU2_mul_val`, `ρ_Fib_SU2_inv_val`,
`ρ_Fib_SU2_groupCommutator_val`. These are direct consequences of
`gs.ρ_hom` being a `MonoidHom` plus the SU(2) subtype mult/inv. -/

/-- **`gs.ρ_hom` multiplicativity at the matrix level**. -/
lemma ρ_hom_mul_val (gs : GeneratingSet) (a b : gs.W) :
    ((gs.ρ_hom (a * b) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      ((gs.ρ_hom a : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) *
      ((gs.ρ_hom b : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [map_mul]
  rfl

/-- **`gs.ρ_hom` inverse at the matrix level**. -/
lemma ρ_hom_inv_val (gs : GeneratingSet) (a : gs.W) :
    ((gs.ρ_hom a⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      ((gs.ρ_hom a : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
  rw [map_inv]
  exact SU2_subtype_inv_val_eq_matrix_inv _

/-- **`gs.ρ_hom` of group commutator at the matrix level**. -/
lemma ρ_hom_groupCommutator_val (gs : GeneratingSet) (a b : gs.W) :
    ((gs.ρ_hom (a * b * a⁻¹ * b⁻¹) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      SKEFTHawking.FKLW.GroupCommutator.groupCommutator
        ((gs.ρ_hom a : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ)
        ((gs.ρ_hom b : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold SKEFTHawking.FKLW.GroupCommutator.groupCommutator
  rw [ρ_hom_mul_val, ρ_hom_mul_val, ρ_hom_mul_val,
      ρ_hom_inv_val, ρ_hom_inv_val]

/-! ## 3. Numerical K-bound lemma (re-export of Phase 6t's private lemma)

The Phase 6t file's `valid_branch_K_chain_le_K_compose_numeric` is `private`,
so we re-prove it here at the top level. Identical proof body; the only
purpose of this lemma is to keep the main induction inside the heartbeat
budget by avoiding monolithic inlined numerical reasoning. -/

/-- **K_proof ≤ K_compose numerical bound** (top-level re-export of the
Phase 6t private lemma). Identical proof body, public so the generic
discharge below can reference it without inlining ~190 LoC of numerical
reasoning into the main induction body. -/
lemma valid_branch_K_chain_le_K_compose_numeric_generic :
    Real.sqrt 2 *
      (12 * Real.sqrt 2 * Real.exp 1 *
        ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) +
       12 * Real.sqrt (2 * ε₀)) +
    Real.sqrt 2 * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) ≤
    K_compose := by
  rw [show K_compose = 1024 from rfl]
  have h_sqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h_e_pos : 0 < Real.exp 1 := Real.exp_pos _
  have h_e_nn : (0 : ℝ) ≤ Real.exp 1 := h_e_pos.le
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_nn : (0 : ℝ) ≤ Real.pi := h_pi_pos.le
  have h_C0_nn : (0 : ℝ) ≤ (Real.pi / 4) * Real.sqrt 2 := by positivity
  have h_sqrt2_le : Real.sqrt 2 ≤ 3/2 := by
    rw [show (3/2 : ℝ) = Real.sqrt ((3/2)^2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt; norm_num
  have h_e_le : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_C0_le : (Real.pi / 4) * Real.sqrt 2 ≤ 6/5 := by
    have h_pi_4_lt : Real.pi / 4 < 3.15 / 4 := by linarith
    calc (Real.pi / 4) * Real.sqrt 2
        ≤ (3.15 / 4) * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_right h_pi_4_lt.le h_sqrt2_nn
      _ ≤ (3.15 / 4) * (3/2) :=
          mul_le_mul_of_nonneg_left h_sqrt2_le (by norm_num)
      _ = 189 / 160 := by norm_num
      _ ≤ 6/5 := by norm_num
  have h_six_five_half_le : ((6/5 : ℝ)) ^ (1 / 2 : ℝ) ≤ 6/5 := by
    have h_chain : (6/5 : ℝ) ^ (1 / 2 : ℝ) ≤ (6/5 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6/5)
        (by norm_num : (1/2 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at h_chain
  have h_C0_half_le : ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) ≤ 6/5 := by
    have h_step : ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) ≤
                    (6/5 : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow h_C0_nn h_C0_le (by norm_num)
    linarith
  have h_six_five_pos : (0 : ℝ) < 6/5 := by norm_num
  have h_C0_three_halves_le : ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) ≤ 36/25 := by
    have h_step1 : ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) ≤
                    (6/5 : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow h_C0_nn h_C0_le (by norm_num)
    have h_split : (6/5 : ℝ) ^ (3 / 2 : ℝ) =
                    (6/5 : ℝ) * (6/5 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 from by norm_num,
          Real.rpow_add h_six_five_pos, Real.rpow_one]
    have h_step2 : (6/5 : ℝ) * (6/5 : ℝ) ^ (1 / 2 : ℝ) ≤ (6/5 : ℝ) * (6/5 : ℝ) :=
      mul_le_mul_of_nonneg_left h_six_five_half_le (by norm_num)
    have h_eq : (6/5 : ℝ) * (6/5 : ℝ) = 36/25 := by norm_num
    linarith
  have h_sqrt_2ε₀_le : Real.sqrt (2 * ε₀) ≤ 1 / 2048 := by
    rw [show (2 * ε₀ : ℝ) = 1 / 4194304 from two_ε₀_value]
    rw [show (1 / 4194304 : ℝ) = (1 / 2048 : ℝ) ^ 2 from by norm_num]
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2048)]
  have h_rpow_half_nn : (0 : ℝ) ≤ ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg h_C0_nn _
  have h_rpow_three_halves_nn : (0 : ℝ) ≤ ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg h_C0_nn _
  have h_K_stab1_le :
      12 * Real.sqrt 2 * Real.exp 1 *
        ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) ≤ 324 / 5 := by
    calc 12 * Real.sqrt 2 * Real.exp 1 *
            ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ)
        ≤ 12 * (3/2) * Real.exp 1 *
            ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ h_rpow_half_nn
          apply mul_le_mul_of_nonneg_right _ h_e_nn
          exact mul_le_mul_of_nonneg_left h_sqrt2_le (by norm_num)
      _ ≤ 12 * (3/2) * 3 *
            ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ h_rpow_half_nn
          apply mul_le_mul_of_nonneg_left h_e_le
          norm_num
      _ ≤ 12 * (3/2) * 3 * (6/5) := by
          apply mul_le_mul_of_nonneg_left h_C0_half_le
          norm_num
      _ = 324 / 5 := by norm_num
  have h_K_stab2_le : 12 * Real.sqrt (2 * ε₀) ≤ 3 / 512 := by
    have h_step : 12 * Real.sqrt (2 * ε₀) ≤ 12 * (1/2048) :=
      mul_le_mul_of_nonneg_left h_sqrt_2ε₀_le (by norm_num)
    linarith
  have h_K_cubic_le :
      Real.sqrt 2 * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) ≤
        17280 / 25 := by
    calc Real.sqrt 2 * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ)
        ≤ (3/2) * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ h_rpow_three_halves_nn
          exact mul_le_mul_of_nonneg_right h_sqrt2_le (by norm_num)
      _ ≤ (3/2) * 320 * (36/25) := by
          apply mul_le_mul_of_nonneg_left h_C0_three_halves_le
          norm_num
      _ = 17280 / 25 := by norm_num
  have h_sum_le : (12 * Real.sqrt 2 * Real.exp 1 *
                   ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) +
                  12 * Real.sqrt (2 * ε₀)) ≤ 324/5 + 3/512 :=
    add_le_add h_K_stab1_le h_K_stab2_le
  have h_sqrt2_mul_sum_le :
      Real.sqrt 2 *
        (12 * Real.sqrt 2 * Real.exp 1 *
          ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) +
         12 * Real.sqrt (2 * ε₀)) ≤
      (3/2) * (324/5 + 3/512) := by
    calc Real.sqrt 2 *
          (12 * Real.sqrt 2 * Real.exp 1 *
            ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) +
           12 * Real.sqrt (2 * ε₀))
        ≤ Real.sqrt 2 * (324/5 + 3/512) :=
          mul_le_mul_of_nonneg_left h_sum_le h_sqrt2_nn
      _ ≤ (3/2) * (324/5 + 3/512) :=
          mul_le_mul_of_nonneg_right h_sqrt2_le (by norm_num : (0:ℝ) ≤ 324/5 + 3/512)
  calc Real.sqrt 2 *
        (12 * Real.sqrt 2 * Real.exp 1 *
          ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) +
         12 * Real.sqrt (2 * ε₀)) +
       Real.sqrt 2 * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ)
      ≤ (3/2) * (324/5 + 3/512) + 17280 / 25 :=
        add_le_add h_sqrt2_mul_sum_le h_K_cubic_le
    _ ≤ 1024 := by norm_num

/-! ## 4. Generic level-0 base case bound

Given `BaseFinder_approximates_within gs baseFinder (2 * ε₀)`, the
level-0 generic recursion satisfies `‖ρ_hom (baseFinder U) - U‖ ≤ 2·ε₀`,
which is the `ε_seq K (2 * ε₀) 0 = 2 * ε₀` headline. -/

/-- **Generic level-0 error bound**. -/
lemma skApproxC_generic_zero_error_bound
    (gs : GeneratingSet) (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → gs.W)
    (h_baseFinder : BaseFinder_approximates_within gs baseFinder (2 * ε₀))
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖((gs.ρ_hom (skApproxC_generic gs baseFinder 0 U) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K_compose (2 * ε₀) 0 := by
  rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_zero]
  rw [skApproxC_generic_zero]
  exact (h_baseFinder U).le

/-! ## 5. **HEADLINE — Generic super-quadratic discharge**

The substantive port of Phase 6t Path A Option C's
`SkApproxCSuperQuadraticBound_holds` to the generic substrate. Same
induction-on-n shape, with Fibonacci-specific `ρ_Fib_SU2_*` lemmas
replaced by the alphabet-agnostic `ρ_hom_*` and `dnStepFG_su2_*`
lemmas above.
-/

/-- **HEADLINE — Generic super-quadratic discharge (Phase 6u Wave 4b)**.

For any `GeneratingSet gs` and any base finder satisfying
`BaseFinder_approximates_within gs baseFinder (2 * ε₀)`, the generic
constructive Dawson-Nielsen Solovay-Kitaev recursion `skApproxC_generic`
achieves super-quadratic error convergence at the calibrated rate
`K_compose = 1024` for all levels `n` and targets `U ∈ SU(2)`.

Proof structure mirrors Phase 6t's `SkApproxCSuperQuadraticBound_holds`:
induction on `n`, valid/invalid branch case-split at the dnStepFG level,
substantive composition of the cubic + stability + V_n linftyOp factors
in the valid branch, and the identity-collapse in the invalid branch.

Pipeline invariants #10 (no maxHeartbeats), #15 (no new axioms),
strengthening discipline (non-trivial, load-bearing): all respected. -/
theorem SkApproxCSuperQuadraticBound_generic_holds
    (gs : GeneratingSet)
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → gs.W)
    (h_baseFinder : BaseFinder_approximates_within gs baseFinder (2 * ε₀)) :
    SkApproxCSuperQuadraticBound_generic K_compose gs baseFinder := by
  intro n
  induction n with
  | zero =>
    intro U
    exact skApproxC_generic_zero_error_bound gs baseFinder h_baseFinder U
  | succ m ih =>
    intro U
    rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_succ]
    set ε_n : ℝ :=
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K_compose (2 * ε₀) m with hε_n_def
    have h_ε_n_le_2ε₀ : ε_n ≤ 2 * ε₀ := ε_seq_K_compose_two_ε₀_le_two_ε₀ m
    have h_ε_n_nn : 0 ≤ ε_n :=
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq_nonneg K_compose (2 * ε₀)
        K_compose_pos two_ε₀_pos m
    have h_V_n_bound :
        ‖((gs.ρ_hom (skApproxC_generic gs baseFinder m U) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) -
          (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε_n := ih U
    set V_n_word : gs.W := skApproxC_generic gs baseFinder m U with hV_n_word_def
    set V_n_SU2 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
      gs.ρ_hom V_n_word with hV_n_SU2_def
    set Δ_SU2 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
      V_n_SU2⁻¹ * U with hΔ_SU2_def
    set H : Matrix (Fin 2) (Fin 2) ℂ :=
      ((-Complex.I) : ℂ) • Y_h Δ_SU2.val with hH_def
    set θ : ℝ := ‖H‖ with hθ_def
    have h_sqrt2_eps_lt : Real.sqrt 2 * ε_n < 1 / 4 :=
      sqrt_two_mul_eps_lt_one_quarter ε_n h_ε_n_nn h_ε_n_le_2ε₀
    have h_half_pi_eps_le : (Real.pi / 2) * Real.sqrt 2 * ε_n ≤ 1 :=
      half_pi_sqrt_two_mul_eps_le_one ε_n h_ε_n_nn h_ε_n_le_2ε₀
    have h_Δ_norm_le : ‖(Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤
                        Real.sqrt 2 * ε_n := by
      calc ‖(Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) - 1‖
          ≤ Real.sqrt 2 *
              ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) -
                (U : Matrix (Fin 2) (Fin 2) ℂ)‖ :=
            residual_norm_le_sqrt_two_mul V_n_SU2 U
        _ ≤ Real.sqrt 2 * ε_n := by
            exact mul_le_mul_of_nonneg_left h_V_n_bound (Real.sqrt_nonneg _)
    have h_Δ_norm_lt : ‖(Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < 1/4 :=
      lt_of_le_of_lt h_Δ_norm_le h_sqrt2_eps_lt
    have h_θ_le : θ ≤ (Real.pi / 2) * Real.sqrt 2 * ε_n := by
      have h_H_bound :
          ‖((-Complex.I) • Y_h
              ((V_n_SU2⁻¹ * U :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val) :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
            (Real.pi / 2) * Real.sqrt 2 *
              ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) -
                (U : Matrix (Fin 2) (Fin 2) ℂ)‖ :=
        H_norm_bound_from_V_diff_half_pi V_n_SU2 U
          (lt_of_le_of_lt (mul_le_mul_of_nonneg_left h_V_n_bound
            (Real.sqrt_nonneg _)) h_sqrt2_eps_lt)
      have h_θ_eq_H : θ = ‖((-Complex.I) • Y_h
                            ((V_n_SU2⁻¹ * U :
                                ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val) :
                            Matrix (Fin 2) (Fin 2) ℂ)‖ := rfl
      rw [h_θ_eq_H]
      calc ‖((-Complex.I) • Y_h
              ((V_n_SU2⁻¹ * U :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val) :
              Matrix (Fin 2) (Fin 2) ℂ)‖
          ≤ (Real.pi / 2) * Real.sqrt 2 *
              ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) -
                (U : Matrix (Fin 2) (Fin 2) ℂ)‖ := h_H_bound
        _ ≤ (Real.pi / 2) * Real.sqrt 2 * ε_n := by
            have h_nn : (0 : ℝ) ≤ (Real.pi / 2) * Real.sqrt 2 := by positivity
            exact mul_le_mul_of_nonneg_left h_V_n_bound h_nn
    have h_θ_le_one : θ ≤ 1 := le_trans h_θ_le h_half_pi_eps_le
    have h_θ_nn : 0 ≤ θ := norm_nonneg _
    by_cases h_θ_pos : 0 < θ
    · -- VALID branch
      have h_valid : 0 < θ ∧ θ ≤ 1 := ⟨h_θ_pos, h_θ_le_one⟩
      set δ_lie : ℝ := Real.sqrt (θ / 2) with hδ_lie_def
      have h_δ_lie_nn : 0 ≤ δ_lie := Real.sqrt_nonneg _
      have h_θ_div_two_nn : (0 : ℝ) ≤ θ / 2 := by linarith
      have h_δ_lie_sq : δ_lie ^ 2 = θ / 2 := Real.sq_sqrt h_θ_div_two_nn
      have h_δ_lie_le_one : δ_lie ≤ 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by linarith)
      have h_F_norm : ‖(dnStepFG_su2 V_n_SU2 U).F‖ ≤ δ_lie :=
        dnStepFG_su2_F_norm_le_sqrt_theta_half V_n_SU2 U
      have h_G_norm : ‖(dnStepFG_su2 V_n_SU2 U).G‖ ≤ δ_lie :=
        dnStepFG_su2_G_norm_le_sqrt_theta_half V_n_SU2 U
      have h_trace_ne :
          (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ).trace.re ≠ -2 :=
        SU2_trace_re_ne_neg_two_of_norm_sub_one_lt_quarter
          Δ_SU2.property h_Δ_norm_lt
      set A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
        expIsu2 (dnStepFG_su2 V_n_SU2 U).F
          (dnStepFG_su2 V_n_SU2 U).hF_herm (dnStepFG_su2 V_n_SU2 U).hF_tr
        with hA_F_def
      set A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
        expIsu2 (dnStepFG_su2 V_n_SU2 U).G
          (dnStepFG_su2 V_n_SU2 U).hG_herm (dnStepFG_su2 V_n_SU2 U).hG_tr
        with hA_G_def
      have h_cubic :
          ‖SKEFTHawking.FKLW.GroupCommutator.groupCommutator
              ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ)
              ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ) -
            ((Δ_SU2 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 320 * δ_lie ^ 3 :=
        dnStepFG_su2_gC_minus_Delta_norm_le_cubic V_n_SU2 U h_valid h_trace_ne
          δ_lie h_δ_lie_nn h_δ_lie_le_one h_F_norm h_G_norm
      have h_A_F_near_one :
          ‖((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δ_lie * Real.exp δ_lie :=
        expIsu2_norm_sub_one_le _
          (dnStepFG_su2 V_n_SU2 U).hF_herm (dnStepFG_su2 V_n_SU2 U).hF_tr
          δ_lie h_F_norm
      have h_A_G_near_one :
          ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δ_lie * Real.exp δ_lie :=
        expIsu2_norm_sub_one_le _
          (dnStepFG_su2 V_n_SU2 U).hG_herm (dnStepFG_su2 V_n_SU2 U).hG_tr
          δ_lie h_G_norm
      have h_A_F_inv_near_one :
          ‖((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹ - 1‖ ≤
            Real.sqrt 2 * (δ_lie * Real.exp δ_lie) :=
        expIsu2_inv_norm_sub_one_le _
          (dnStepFG_su2 V_n_SU2 U).hF_herm (dnStepFG_su2 V_n_SU2 U).hF_tr
          δ_lie h_F_norm
      have h_A_G_inv_near_one :
          ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹ - 1‖ ≤
            Real.sqrt 2 * (δ_lie * Real.exp δ_lie) :=
        expIsu2_inv_norm_sub_one_le _
          (dnStepFG_su2 V_n_SU2 U).hG_herm (dnStepFG_su2 V_n_SU2 U).hG_tr
          δ_lie h_G_norm
      have h_IH_F :
          ‖((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε_n := ih A_F
      have h_IH_G :
          ‖((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε_n := ih A_G
      have h_sqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      have h_V_n_M : ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 :=
        SU2_linftyOpNorm_le_sqrt_two V_n_SU2.property
      have h_ρA_F_M :
          ‖((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 :=
        SU2_linftyOpNorm_le_sqrt_two
          (gs.ρ_hom (skApproxC_generic gs baseFinder m A_F)).property
      have h_ρA_G_M :
          ‖((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 :=
        SU2_linftyOpNorm_le_sqrt_two
          (gs.ρ_hom (skApproxC_generic gs baseFinder m A_G)).property
      have h_A_F_M :
          ‖((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 :=
        SU2_linftyOpNorm_le_sqrt_two A_F.property
      have h_A_G_M :
          ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt 2 :=
        SU2_linftyOpNorm_le_sqrt_two A_G.property
      have h_A_F_inv_M :
          ‖((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹‖ ≤ Real.sqrt 2 := by
        rw [← SU2_subtype_inv_val_eq_matrix_inv A_F]
        exact SU2_linftyOpNorm_le_sqrt_two (A_F⁻¹).property
      have h_A_G_inv_M :
          ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹‖ ≤ Real.sqrt 2 := by
        rw [← SU2_subtype_inv_val_eq_matrix_inv A_G]
        exact SU2_linftyOpNorm_le_sqrt_two (A_G⁻¹).property
      have h_ρA_F_inv_M :
          ‖((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹‖ ≤ Real.sqrt 2 := by
        rw [← SU2_subtype_inv_val_eq_matrix_inv
              (gs.ρ_hom (skApproxC_generic gs baseFinder m A_F))]
        exact SU2_linftyOpNorm_le_sqrt_two
          (gs.ρ_hom (skApproxC_generic gs baseFinder m A_F))⁻¹.property
      have h_ρA_G_inv_M :
          ‖((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹‖ ≤ Real.sqrt 2 := by
        rw [← SU2_subtype_inv_val_eq_matrix_inv
              (gs.ρ_hom (skApproxC_generic gs baseFinder m A_G))]
        exact SU2_linftyOpNorm_le_sqrt_two
          (gs.ρ_hom (skApproxC_generic gs baseFinder m A_G))⁻¹.property
      have h_A_F_det : IsUnit (A_F : Matrix (Fin 2) (Fin 2) ℂ).det :=
        SU2_val_det_isUnit A_F
      have h_A_G_det : IsUnit (A_G : Matrix (Fin 2) (Fin 2) ℂ).det :=
        SU2_val_det_isUnit A_G
      have h_ρA_F_det :
          IsUnit ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ).det :=
        SU2_val_det_isUnit _
      have h_ρA_G_det :
          IsUnit ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ).det :=
        SU2_val_det_isUnit _
      set η : ℝ := Real.sqrt 2 * (δ_lie * Real.exp δ_lie) with hη_def
      have h_δ_lie_exp_nn : (0 : ℝ) ≤ δ_lie * Real.exp δ_lie :=
        mul_nonneg h_δ_lie_nn (Real.exp_pos _).le
      have h_η_nn : (0 : ℝ) ≤ η :=
        mul_nonneg h_sqrt2_nn h_δ_lie_exp_nn
      have h_h_near_id_η :
          ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ η := by
        calc ‖((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ) - 1‖
            ≤ δ_lie * Real.exp δ_lie := h_A_G_near_one
          _ ≤ Real.sqrt 2 * (δ_lie * Real.exp δ_lie) := by
              have h_one_le_sqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
                rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
                exact Real.sqrt_le_sqrt (by norm_num)
              nlinarith
      have h_g_inv_near_id_η :
          ‖((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)⁻¹ - 1‖ ≤ η := h_A_F_inv_near_one
      have h_g_diff_ε :
          ‖((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε_n := h_IH_F
      have h_h_diff_ε :
          ‖((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε_n := h_IH_G
      have h_stability :
          ‖SKEFTHawking.FKLW.GroupCommutator.groupCommutator
              ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ)
              ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ) -
            SKEFTHawking.FKLW.GroupCommutator.groupCommutator
              ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ)
              ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
            2 * (Real.sqrt 2 ^ 2 + Real.sqrt 2 ^ 4) * ε_n * η +
            (Real.sqrt 2 ^ 4 + Real.sqrt 2 ^ 6) * ε_n ^ 2 :=
        SKEFTHawking.FKLW.GroupCommutatorNearIdentity.groupCommutator_stability_nearIdentity
          (A_F : Matrix (Fin 2) (Fin 2) ℂ)
          (A_G : Matrix (Fin 2) (Fin 2) ℂ)
          ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)
          ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)
          η ε_n (Real.sqrt 2)
          h_η_nn h_ε_n_nn h_sqrt2_nn
          h_ρA_F_M h_ρA_G_M
          h_A_F_inv_M h_A_G_inv_M
          h_ρA_F_inv_M h_ρA_G_inv_M
          h_h_near_id_η h_g_inv_near_id_η
          h_g_diff_ε h_h_diff_ε
          h_A_F_det h_ρA_F_det h_A_G_det h_ρA_G_det
      -- ρ_hom (skApproxC_generic gs baseFinder (m+1) U) = V_n_SU2.val * gC(ρA_F.val, ρA_G.val)
      have h_skApproxC_succ_val :
          ((gs.ρ_hom (skApproxC_generic gs baseFinder (m + 1) U) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) =
            (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
            SKEFTHawking.FKLW.GroupCommutator.groupCommutator
              ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ)
              ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [skApproxC_generic_succ]
        show ((gs.ρ_hom (V_n_word * (skApproxC_generic gs baseFinder m A_F *
                  skApproxC_generic gs baseFinder m A_G *
                  (skApproxC_generic gs baseFinder m A_F)⁻¹ *
                  (skApproxC_generic gs baseFinder m A_G)⁻¹)) :
                ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ) = _
        rw [ρ_hom_mul_val, ρ_hom_groupCommutator_val]
      have h_V_n_Δ_eq_U :
          (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
            (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) =
            (U : Matrix (Fin 2) (Fin 2) ℂ) := by
        have h_mul_def : V_n_SU2 * Δ_SU2 = V_n_SU2 * (V_n_SU2⁻¹ * U) := by
          rw [hΔ_SU2_def]
        have h_simp : V_n_SU2 * Δ_SU2 = U := by
          rw [h_mul_def]
          rw [← mul_assoc, mul_inv_cancel, one_mul]
        have h_val : ((V_n_SU2 * Δ_SU2 :
                          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                       Matrix (Fin 2) (Fin 2) ℂ) =
                     (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
                     (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) := rfl
        rw [← h_val, h_simp]
      have h_term2 :
          ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
            (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
            Real.sqrt 2 * (320 * δ_lie ^ 3) := by
        rw [← h_V_n_Δ_eq_U]
        rw [show (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ) =
              (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              (SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ)) from by noncomm_ring]
        calc ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              (SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ))‖
            ≤ ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ)‖ *
              ‖SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (Δ_SU2 : Matrix (Fin 2) (Fin 2) ℂ)‖ := norm_mul_le _ _
          _ ≤ Real.sqrt 2 * (320 * δ_lie ^ 3) := by
              have h_cubic_nn : (0 : ℝ) ≤ 320 * δ_lie ^ 3 := by positivity
              exact mul_le_mul h_V_n_M h_cubic (norm_nonneg _) h_sqrt2_nn
      set stab_bound : ℝ :=
        2 * (Real.sqrt 2 ^ 2 + Real.sqrt 2 ^ 4) * ε_n * η +
        (Real.sqrt 2 ^ 4 + Real.sqrt 2 ^ 6) * ε_n ^ 2 with hstab_def
      have h_term1 :
          ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
            (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
            Real.sqrt 2 * stab_bound := by
        rw [show (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) =
              (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              (SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)) from by noncomm_ring]
        calc ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              (SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ))‖
            ≤ ‖(V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ)‖ *
              ‖SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)‖ := norm_mul_le _ _
          _ ≤ Real.sqrt 2 * stab_bound := by
              have h_stab_nn : (0 : ℝ) ≤ stab_bound := by
                rw [hstab_def]
                positivity
              exact mul_le_mul h_V_n_M h_stability (norm_nonneg _) h_sqrt2_nn
      have h_combined_norm :
          ‖((gs.ρ_hom (skApproxC_generic gs baseFinder (m + 1) U) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
            Real.sqrt 2 * stab_bound + Real.sqrt 2 * (320 * δ_lie ^ 3) := by
        rw [h_skApproxC_succ_val]
        have h_decomp :
            (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (U : Matrix (Fin 2) (Fin 2) ℂ) =
            ((V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_F) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((gs.ρ_hom (skApproxC_generic gs baseFinder m A_G) :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)) +
            ((V_n_SU2 : Matrix (Fin 2) (Fin 2) ℂ) *
              SKEFTHawking.FKLW.GroupCommutator.groupCommutator
                ((A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ)
                ((A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
              (U : Matrix (Fin 2) (Fin 2) ℂ)) := by noncomm_ring
        rw [h_decomp]
        exact le_trans (norm_add_le _ _) (add_le_add h_term1 h_term2)
      -- Now the numerical chain. Mirrors Phase 6t's substantive proof.
      have h_δ_lie_sq_le : δ_lie ^ 2 ≤ (Real.pi / 4) * Real.sqrt 2 * ε_n := by
        rw [h_δ_lie_sq]
        linarith [h_θ_le]
      have h_C_cubic_nn : (0 : ℝ) ≤ (Real.pi / 4) * Real.sqrt 2 := by positivity
      have h_δ_lie_pow3_le :
          δ_lie ^ 3 ≤ ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) *
                      ε_n ^ (3 / 2 : ℝ) := by
        have h_sq_nn : (0 : ℝ) ≤ δ_lie ^ 2 := sq_nonneg _
        have h_eq1 : δ_lie ^ 3 = (δ_lie ^ 2) ^ (3 / 2 : ℝ) := by
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 from by norm_num,
              Real.rpow_add_of_nonneg h_sq_nn (by norm_num) (by norm_num),
              Real.rpow_one, ← Real.sqrt_eq_rpow,
              Real.sqrt_sq h_δ_lie_nn]
          ring
        rw [h_eq1]
        have h_step : (δ_lie ^ 2) ^ (3 / 2 : ℝ) ≤
                      ((Real.pi / 4) * Real.sqrt 2 * ε_n) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (sq_nonneg _) h_δ_lie_sq_le (by norm_num)
        calc (δ_lie ^ 2) ^ (3 / 2 : ℝ)
            ≤ ((Real.pi / 4) * Real.sqrt 2 * ε_n) ^ (3 / 2 : ℝ) := h_step
          _ = ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) *
              ε_n ^ (3 / 2 : ℝ) := by
              rw [Real.mul_rpow (by positivity) h_ε_n_nn]
      have h_exp_le_e : Real.exp δ_lie ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr h_δ_lie_le_one
      have h_e_nn : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos _).le
      have h_η_le : η ≤ Real.sqrt 2 * (δ_lie * Real.exp 1) := by
        rw [hη_def]
        have h_δ_exp_le : δ_lie * Real.exp δ_lie ≤ δ_lie * Real.exp 1 :=
          mul_le_mul_of_nonneg_left h_exp_le_e h_δ_lie_nn
        exact mul_le_mul_of_nonneg_left h_δ_exp_le h_sqrt2_nn
      have h_δ_lie_le_rpow :
          δ_lie ≤ ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) *
                  ε_n ^ (1 / 2 : ℝ) := by
        rw [← Real.mul_rpow h_C_cubic_nn h_ε_n_nn]
        rw [← Real.sqrt_eq_rpow]
        rw [show δ_lie = Real.sqrt (δ_lie ^ 2) from (Real.sqrt_sq h_δ_lie_nn).symm]
        exact Real.sqrt_le_sqrt h_δ_lie_sq_le
      have h_ε_n_sq_le :
          ε_n ^ 2 ≤ Real.sqrt (2 * ε₀) * ε_n ^ (3 / 2 : ℝ) := by
        have h_split : ε_n ^ 2 = ε_n ^ (3 / 2 : ℝ) * ε_n ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast ε_n 2]
          rw [show ((2 : ℕ) : ℝ) = 3 / 2 + 1 / 2 from by norm_num]
          exact Real.rpow_add_of_nonneg h_ε_n_nn (by norm_num) (by norm_num)
        rw [h_split]
        have h_ε_n_rpow_nn : (0 : ℝ) ≤ ε_n ^ (3 / 2 : ℝ) := Real.rpow_nonneg h_ε_n_nn _
        have h_ε_n_half_le : ε_n ^ (1 / 2 : ℝ) ≤ Real.sqrt (2 * ε₀) := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow h_ε_n_nn h_ε_n_le_2ε₀ (by norm_num)
        calc ε_n ^ (3 / 2 : ℝ) * ε_n ^ (1 / 2 : ℝ)
            ≤ ε_n ^ (3 / 2 : ℝ) * Real.sqrt (2 * ε₀) :=
              mul_le_mul_of_nonneg_left h_ε_n_half_le h_ε_n_rpow_nn
          _ = Real.sqrt (2 * ε₀) * ε_n ^ (3 / 2 : ℝ) := by ring
      have h_sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      have h_sqrt2_pow4 : Real.sqrt 2 ^ 4 = 4 := by
        have h_eq : Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
        rw [h_eq, h_sqrt2_sq]
        norm_num
      have h_sqrt2_pow6 : Real.sqrt 2 ^ 6 = 8 := by
        have h_eq : Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by ring
        rw [h_eq, h_sqrt2_sq]
        norm_num
      have h_stab_simplified :
          stab_bound = 12 * ε_n * η + 12 * ε_n ^ 2 := by
        rw [hstab_def, h_sqrt2_sq, h_sqrt2_pow4, h_sqrt2_pow6]; ring
      set K_stab1 : ℝ := 12 * Real.sqrt 2 * Real.exp 1 *
                          ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ)
        with hKstab1_def
      have h_K_stab1_nn : (0 : ℝ) ≤ K_stab1 := by
        rw [hKstab1_def]
        positivity
      have h_term_η_le :
          12 * ε_n * η ≤ K_stab1 * ε_n ^ (3 / 2 : ℝ) := by
        have h_ε_n_eq : ε_n * ε_n ^ (1 / 2 : ℝ) = ε_n ^ (3 / 2 : ℝ) := by
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 from by norm_num,
              Real.rpow_add_of_nonneg h_ε_n_nn (by norm_num : (0:ℝ) ≤ 1)
                (by norm_num : (0:ℝ) ≤ 1/2),
              Real.rpow_one]
        have h_chain :
            12 * ε_n * η ≤
            12 * ε_n * (Real.sqrt 2 * (δ_lie * Real.exp 1)) :=
          mul_le_mul_of_nonneg_left h_η_le (by positivity)
        have h_chain2 :
            12 * ε_n * (Real.sqrt 2 * (δ_lie * Real.exp 1)) ≤
            12 * ε_n * (Real.sqrt 2 *
              ((((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) *
                ε_n ^ (1 / 2 : ℝ)) * Real.exp 1)) := by
          apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_left
            · apply mul_le_mul_of_nonneg_right h_δ_lie_le_rpow h_e_nn
            · exact h_sqrt2_nn
          · positivity
        have h_rearrange :
            12 * ε_n * (Real.sqrt 2 *
              ((((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) *
                ε_n ^ (1 / 2 : ℝ)) * Real.exp 1)) =
            K_stab1 * ε_n ^ (3 / 2 : ℝ) := by
          rw [hKstab1_def]
          rw [show 12 * ε_n * (Real.sqrt 2 *
              ((((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ) *
                ε_n ^ (1 / 2 : ℝ)) * Real.exp 1)) =
              (12 * Real.sqrt 2 * Real.exp 1 *
                ((Real.pi / 4) * Real.sqrt 2) ^ (1 / 2 : ℝ)) *
              (ε_n * ε_n ^ (1 / 2 : ℝ)) from by ring]
          rw [h_ε_n_eq]
        linarith
      set K_stab2 : ℝ := 12 * Real.sqrt (2 * ε₀) with hKstab2_def
      have h_K_stab2_nn : (0 : ℝ) ≤ K_stab2 := by
        rw [hKstab2_def]; positivity
      have h_term_sq_le :
          12 * ε_n ^ 2 ≤ K_stab2 * ε_n ^ (3 / 2 : ℝ) := by
        rw [hKstab2_def]
        have h_step : 12 * ε_n ^ 2 ≤ 12 * (Real.sqrt (2 * ε₀) * ε_n ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h_ε_n_sq_le (by norm_num : (0:ℝ) ≤ 12)
        linarith
      have h_stab_bound_le :
          stab_bound ≤ (K_stab1 + K_stab2) * ε_n ^ (3 / 2 : ℝ) := by
        rw [h_stab_simplified, add_mul]
        exact add_le_add h_term_η_le h_term_sq_le
      set K_cubic : ℝ := Real.sqrt 2 * 320 *
                          ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ)
        with hKcubic_def
      have h_K_cubic_nn : (0 : ℝ) ≤ K_cubic := by
        rw [hKcubic_def]; positivity
      have h_cubic_le :
          Real.sqrt 2 * (320 * δ_lie ^ 3) ≤ K_cubic * ε_n ^ (3 / 2 : ℝ) := by
        rw [hKcubic_def]
        have h_320_nn : (0 : ℝ) ≤ 320 := by norm_num
        have h_step :
            320 * δ_lie ^ 3 ≤ 320 * (((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) *
                              ε_n ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h_δ_lie_pow3_le h_320_nn
        calc Real.sqrt 2 * (320 * δ_lie ^ 3)
            ≤ Real.sqrt 2 * (320 * (((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) *
                              ε_n ^ (3 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left h_step h_sqrt2_nn
          _ = Real.sqrt 2 * 320 * ((Real.pi / 4) * Real.sqrt 2) ^ (3 / 2 : ℝ) *
              ε_n ^ (3 / 2 : ℝ) := by ring
      have h_sqrt2_stab_le :
          Real.sqrt 2 * stab_bound ≤
            Real.sqrt 2 * (K_stab1 + K_stab2) * ε_n ^ (3 / 2 : ℝ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h_stab_bound_le h_sqrt2_nn
      have h_total_le :
          Real.sqrt 2 * stab_bound + Real.sqrt 2 * (320 * δ_lie ^ 3) ≤
            (Real.sqrt 2 * (K_stab1 + K_stab2) + K_cubic) *
            ε_n ^ (3 / 2 : ℝ) := by
        rw [add_mul]
        exact add_le_add h_sqrt2_stab_le h_cubic_le
      -- K_proof ≤ K_compose: extracted to top-level lemma to keep this
      -- induction body within the heartbeat budget.
      have h_K_proof_le_K_compose :
          Real.sqrt 2 * (K_stab1 + K_stab2) + K_cubic ≤ K_compose := by
        rw [hKstab1_def, hKstab2_def, hKcubic_def]
        exact valid_branch_K_chain_le_K_compose_numeric_generic
      calc ‖((gs.ρ_hom (skApproxC_generic gs baseFinder (m + 1) U) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            (U : Matrix (Fin 2) (Fin 2) ℂ)‖
          ≤ Real.sqrt 2 * stab_bound + Real.sqrt 2 * (320 * δ_lie ^ 3) :=
            h_combined_norm
        _ ≤ (Real.sqrt 2 * (K_stab1 + K_stab2) + K_cubic) *
            ε_n ^ (3 / 2 : ℝ) := h_total_le
        _ ≤ K_compose * ε_n ^ (3 / 2 : ℝ) := by
            have h_rpow_nn : (0 : ℝ) ≤ ε_n ^ (3 / 2 : ℝ) :=
              Real.rpow_nonneg h_ε_n_nn _
            exact mul_le_mul_of_nonneg_right h_K_proof_le_K_compose h_rpow_nn
    · -- INVALID branch: θ = 0 forces V_n = U exactly.
      have h_θ_le_zero : θ ≤ 0 := not_lt.mp h_θ_pos
      have h_θ_zero : θ = 0 := le_antisymm h_θ_le_zero h_θ_nn
      have h_invalid_check :
          ¬(0 < ‖((-Complex.I) • Y_h
              (V_n_SU2⁻¹ * U :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ∧
              ‖((-Complex.I) • Y_h
              (V_n_SU2⁻¹ * U :
                  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
              Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 1) := by
        intro ⟨h_pos, _⟩
        exact h_θ_pos h_pos
      have h_FG_zero : (dnStepFG_su2 V_n_SU2 U).F = 0 ∧
                        (dnStepFG_su2 V_n_SU2 U).G = 0 :=
        dnStepFG_su2_invalid_F_zero V_n_SU2 U h_invalid_check
      set A_F : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
        expIsu2 (dnStepFG_su2 V_n_SU2 U).F
          (dnStepFG_su2 V_n_SU2 U).hF_herm (dnStepFG_su2 V_n_SU2 U).hF_tr
        with hA_F_def
      set A_G : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
        expIsu2 (dnStepFG_su2 V_n_SU2 U).G
          (dnStepFG_su2 V_n_SU2 U).hG_herm (dnStepFG_su2 V_n_SU2 U).hG_tr
        with hA_G_def
      have h_A_F_eq_A_G : A_F = A_G := by
        apply Subtype.ext
        rw [hA_F_def, hA_G_def, expIsu2_val, expIsu2_val, h_FG_zero.1, h_FG_zero.2]
      have h_skA_eq : skApproxC_generic gs baseFinder m A_F =
                       skApproxC_generic gs baseFinder m A_G := by
        rw [h_A_F_eq_A_G]
      have h_skApproxC_succ_eq : skApproxC_generic gs baseFinder (m + 1) U = V_n_word := by
        rw [skApproxC_generic_succ]
        show V_n_word * (skApproxC_generic gs baseFinder m A_F *
              skApproxC_generic gs baseFinder m A_G *
              (skApproxC_generic gs baseFinder m A_F)⁻¹ *
              (skApproxC_generic gs baseFinder m A_G)⁻¹) = V_n_word
        rw [h_skA_eq]
        group
      have h_ρ_eq : (gs.ρ_hom (skApproxC_generic gs baseFinder (m + 1) U) :
                      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) = V_n_SU2 := by
        rw [h_skApproxC_succ_eq]
      have h_H_zero : H = 0 := by
        have h_norm_zero : ‖H‖ = 0 := h_θ_zero
        exact norm_eq_zero.mp h_norm_zero
      have h_neg_I_ne : ((-Complex.I) : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
      have h_Y_h_zero : Y_h Δ_SU2.val = 0 := by
        have h_unfold : H = ((-Complex.I) : ℂ) • Y_h Δ_SU2.val := rfl
        rw [h_unfold] at h_H_zero
        rcases smul_eq_zero.mp h_H_zero with hh | hh
        · exact absurd hh h_neg_I_ne
        · exact hh
      have h_Δ_val_eq_one : Δ_SU2.val = 1 :=
        Y_h_eq_zero_in_regime_implies_eq_one Δ_SU2.property h_Δ_norm_lt h_Y_h_zero
      have h_Δ_SU2_eq_one : Δ_SU2 = 1 := Subtype.ext h_Δ_val_eq_one
      have h_eq_in_SU2 : V_n_SU2⁻¹ * U = 1 := h_Δ_SU2_eq_one
      have h_U_eq_V_n : U = V_n_SU2 := by
        calc U = 1 * U := (one_mul _).symm
          _ = V_n_SU2 * V_n_SU2⁻¹ * U := by rw [mul_inv_cancel]
          _ = V_n_SU2 * (V_n_SU2⁻¹ * U) := mul_assoc _ _ _
          _ = V_n_SU2 * 1 := by rw [h_eq_in_SU2]
          _ = V_n_SU2 := mul_one _
      have h_lhs_zero :
          ‖((gs.ρ_hom (skApproxC_generic gs baseFinder (m + 1) U) :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) -
            (U : Matrix (Fin 2) (Fin 2) ℂ)‖ = 0 := by
        rw [h_ρ_eq, h_U_eq_V_n]
        simp
      have h_rhs_nn : (0 : ℝ) ≤ K_compose * ε_n ^ (3 / 2 : ℝ) := by
        have h_K_nn : (0 : ℝ) ≤ K_compose := K_compose_pos.le
        have h_rpow_nn : (0 : ℝ) ≤ ε_n ^ (3 / 2 : ℝ) := Real.rpow_nonneg h_ε_n_nn _
        exact mul_nonneg h_K_nn h_rpow_nn
      rw [h_lhs_zero]
      exact h_rhs_nn

/-! ## 6. UNCONDITIONAL bundled-strict generic headline (Bonus task)

Composes the generic discharge above with Wave 6's conditional bundled
headline to produce the UNCONDITIONAL alphabet-independent canonical
quantitative Solovay-Kitaev statement, parametric over `gs` and any base
finder satisfying the (2·ε₀)-approximation property. -/

/-- **UNCONDITIONAL bundled-strict generic headline**.

For any `GeneratingSet gs`, any base finder `baseFinder` satisfying
`BaseFinder_approximates_within gs baseFinder (2 * ε₀)`, any target
`U ∈ SU(2)`, and any precision `ε ∈ (0, ε₀]`, the generic constructive
Dawson-Nielsen Solovay-Kitaev compiler achieves BOTH:

  - **Error**: `‖gs.ρ_hom (compile U ε) - U‖ ≤ ε`
  - **Length**: polylog `O(log(1/ε)^skLengthExponent)` word length

at the SAME algorithmic compile level `skLevel_polylog ε`. This is the
**alphabet-independent canonical quantitative Solovay-Kitaev statement**
discharged UNCONDITIONALLY (modulo only the base-finder approximation
property `h_baseFinder`, which is the standard ε₀-net hypothesis).

Closes Phase 6u Wave 4b: the substantive generic discharge
(`SkApproxCSuperQuadraticBound_generic_holds`) composed with Wave 6's
bundled conditional headline. -/
theorem solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight_unconditional
    (gs : GeneratingSet)
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → gs.W)
    (h_baseFinder : BaseFinder_approximates_within gs baseFinder (2 * ε₀))
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((gs.ρ_hom
            (solovayKitaev_compile_strict_constructive_generic gs baseFinder U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent :=
  solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight
    gs baseFinder
    (SkApproxCSuperQuadraticBound_generic_holds gs baseFinder h_baseFinder)
    U ε hε_pos hε_le

end SKEFTHawking.FKLW.GenericSU2
