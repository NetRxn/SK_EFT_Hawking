/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Track T-S.2 — Clifford+T v4-witness discharge (conditional on AccPt 1)

Discharges `cliffordT_v4_witness_tracked` CONDITIONAL on `AccPt 1
(Filter.principal (H_of_G cliffordTGeneratingSet : Set _))`. Direct
transcription of Phase 5 Step 13's `H_Fib_v4_witness_unconditional`
template (lines 5274-5366 of `OneParameterSubgroupSU2.lean`), with
substitutions:

  - `H_Fib`                                       → `H_of_G cliffordTGeneratingSet`
  - `σ_Fib_1_SU`, `σ_Fib_2_SU`                    → `H_SU`, `T_SU`
  - `σ_Fib_1_SU_mat`, `σ_Fib_2_SU_mat`            → `H_SU_mat`, `T_SU_mat`
  - `σ_Fib_1_SU_mem_H_Fib`, `σ_Fib_2_SU_mem_H_Fib` → `H_SU_mem_H_of_G_cliffordT`, `T_SU_mem_H_of_G_cliffordT`
  - `exists_σ_Fib_SU_mat_not_commute_not_anticommute` → `exists_cliffordT_generator_not_commute_not_anticommute`
  - `H_Fib_accPt_one_unconditional`               → `h_accPt` (taken as hypothesis)

## Headline

  * `cliffordT_v4_witness_from_accPt` — given `AccPt 1`, discharges
    `cliffordT_v4_witness_tracked`.

The unconditional version `cliffordT_v4_witness_discharged` (composing
with `cliffordT_accPt_one_unconditional` from the in-flight Niven-based
infinite-order proof) will land in `CliffordTV4WitnessUnconditional.lean`
once that substrate ships.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
- **Strengthening discipline**: substantive composition; no rfl-discharges
  on load-bearing claims.

-/

import SKEFTHawking.FKLW.CliffordTClosureDenseWitness
import SKEFTHawking.FKLW.CliffordTGeneratorCaseAnalysis
import SKEFTHawking.FKLW.OneParameterSubgroupSU2

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix
open SKEFTHawking.FKLW
open SKEFTHawking.FKLW.SU2LieAlgebra
open SKEFTHawking.FKLW.SU2MatrixExp
open SKEFTHawking.FKLW.OneParameterSubgroupSU2

/-! ## Conditional v4-witness discharge

Takes `AccPt 1` as hypothesis; once shipped, discharges
`cliffordT_v4_witness_tracked` via the standard Phase-5-Step-13
substrate (`vonNeumann_assemble_explicit_X_unconditional` +
`ts_Ad_LI_of_not_commute_anticommute` + `expAmbient_unitary_conj`)
composed with the Clifford+T case-analysis headline. -/

/-- **Conditional Clifford+T v4-witness discharge** (from AccPt 1). -/
theorem cliffordT_v4_witness_from_accPt
    (h_accPt : AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (Filter.principal (H_of_G cliffordTGeneratingSet :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))) :
    cliffordT_v4_witness_tracked := by
  -- Step 1: extract X₁ ∈ ts \ {0} with all-t identity via vonNeumann.
  obtain ⟨X₁, hX₁_ts, hX₁_ne, h_all_t_X₁⟩ :=
    vonNeumann_assemble_explicit_X_unconditional
      (H_of_G cliffordTGeneratingSet) (H_of_G_isClosed _) h_accPt
  -- Step 2: pick g ∈ {H_SU_mat, T_SU_mat} not commuting / anti-commuting with X₁.
  obtain ⟨g_mat, hg_choice, hg_nc, hg_na⟩ :=
    exists_cliffordT_generator_not_commute_not_anticommute hX₁_ts hX₁_ne
  -- Step 3: case-split on g.
  rcases hg_choice with hg_eq_H | hg_eq_T
  · -- g_mat = H_SU_mat. Use g := H_SU.
    set g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := H_SU with hg_def
    have hg_val : (g : Matrix (Fin 2) (Fin 2) ℂ) = g_mat := by
      rw [hg_def, hg_eq_H]; rfl
    have hg_in_H : g ∈ H_of_G cliffordTGeneratingSet :=
      H_SU_mem_H_of_G_cliffordT
    have hg_unitary : g.val ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      Matrix.specialUnitaryGroup_le_unitaryGroup g.property
    set X₂ : Matrix (Fin 2) (Fin 2) ℂ := g.val * X₁ * star g.val with hX₂_def
    have hX₂_ts : X₂ ∈ tracelessSkewHermitian (Fin 2) :=
      SU2LieAlgebra.tracelessSkewHermitian_unitary_conj hX₁_ts hg_unitary
    have hg_nc_val : g.val * X₁ ≠ X₁ * g.val := by rw [hg_val]; exact hg_nc
    have hg_na_val : g.val * X₁ ≠ -(X₁ * g.val) := by rw [hg_val]; exact hg_na
    have h_LI : ∀ a b : ℝ, (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0 :=
      ts_Ad_LI_of_not_commute_anticommute hX₁_ts hX₁_ne hg_unitary hg_nc_val hg_na_val
    refine ⟨X₁, X₂, hX₁_ts, hX₂_ts, h_all_t_X₁, ?_, h_LI⟩
    intro t
    obtain ⟨M₁, hM₁_inH, hM₁_val⟩ := h_all_t_X₁ t
    refine ⟨g * M₁ * g⁻¹, ?_, ?_⟩
    · -- g * M₁ * g⁻¹ ∈ H_of_G cliffordTGeneratingSet (mul/inv closure)
      exact (H_of_G cliffordTGeneratingSet).mul_mem
        ((H_of_G cliffordTGeneratingSet).mul_mem hg_in_H hM₁_inH)
        ((H_of_G cliffordTGeneratingSet).inv_mem hg_in_H)
    · -- M.val = expAmbient((t:ℂ)•X₂) via Ad-exp
      have h_mul_val : (g * M₁ * g⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val
          = g.val * M₁.val * (g⁻¹).val := rfl
      rw [h_mul_val, hM₁_val]
      have h_inv_val : (g⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val
          = star g.val := by
        rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
      rw [h_inv_val]
      rw [← expAmbient_unitary_conj hg_unitary]
      congr 1
      rw [hX₂_def]
      rw [show g.val * (((t : ℝ) : ℂ) • X₁) * star g.val
            = ((t : ℝ) : ℂ) • (g.val * X₁ * star g.val) from by
        rw [mul_smul_comm, smul_mul_assoc]]
  · -- g_mat = T_SU_mat. Use g := T_SU.
    set g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := T_SU with hg_def
    have hg_val : (g : Matrix (Fin 2) (Fin 2) ℂ) = g_mat := by
      rw [hg_def, hg_eq_T]; rfl
    have hg_in_H : g ∈ H_of_G cliffordTGeneratingSet :=
      T_SU_mem_H_of_G_cliffordT
    have hg_unitary : g.val ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      Matrix.specialUnitaryGroup_le_unitaryGroup g.property
    set X₂ : Matrix (Fin 2) (Fin 2) ℂ := g.val * X₁ * star g.val with hX₂_def
    have hX₂_ts : X₂ ∈ tracelessSkewHermitian (Fin 2) :=
      SU2LieAlgebra.tracelessSkewHermitian_unitary_conj hX₁_ts hg_unitary
    have hg_nc_val : g.val * X₁ ≠ X₁ * g.val := by rw [hg_val]; exact hg_nc
    have hg_na_val : g.val * X₁ ≠ -(X₁ * g.val) := by rw [hg_val]; exact hg_na
    have h_LI : ∀ a b : ℝ, (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0 :=
      ts_Ad_LI_of_not_commute_anticommute hX₁_ts hX₁_ne hg_unitary hg_nc_val hg_na_val
    refine ⟨X₁, X₂, hX₁_ts, hX₂_ts, h_all_t_X₁, ?_, h_LI⟩
    intro t
    obtain ⟨M₁, hM₁_inH, hM₁_val⟩ := h_all_t_X₁ t
    refine ⟨g * M₁ * g⁻¹, ?_, ?_⟩
    · exact (H_of_G cliffordTGeneratingSet).mul_mem
        ((H_of_G cliffordTGeneratingSet).mul_mem hg_in_H hM₁_inH)
        ((H_of_G cliffordTGeneratingSet).inv_mem hg_in_H)
    · have h_mul_val : (g * M₁ * g⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val
          = g.val * M₁.val * (g⁻¹).val := rfl
      rw [h_mul_val, hM₁_val]
      have h_inv_val : (g⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val
          = star g.val := by
        rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
      rw [h_inv_val]
      rw [← expAmbient_unitary_conj hg_unitary]
      congr 1
      rw [hX₂_def]
      rw [show g.val * (((t : ℝ) : ℂ) • X₁) * star g.val
            = ((t : ℝ) : ℂ) • (g.val * X₁ * star g.val) from by
        rw [mul_smul_comm, smul_mul_assoc]]

end SKEFTHawking.FKLW.GenericSU2
