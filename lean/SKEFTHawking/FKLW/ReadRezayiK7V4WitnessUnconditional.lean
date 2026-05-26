/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-B.5.2 — Unconditional discharge of `rr7_v4_witness_tracked`

Composes `rr7_accPt_one_unconditional` (from
`ReadRezayiK7InfiniteOrder.lean`) with the second-tangent case analysis
(`exists_readRezayiK7_generator_not_commute_not_anticommute` from
`ReadRezayiK7GeneratorCaseAnalysis.lean`) to substantively discharge
`rr7_v4_witness_tracked`.

Mirrors the Clifford+T Phase 6u Track T-S.2 unconditional discharge
(`CliffordTV4WitnessDischarge.lean` + `CliffordTV4WitnessUnconditional.lean`),
with H_SU+T_RR7 replacing H_SU+T_SU.

## Headlines

  * `rr7_v4_witness_from_accPt` — given `AccPt 1`, discharges
    `rr7_v4_witness_tracked` via the Phase-5-Step-13 substrate.

  * `rr7_v4_witness_discharged : rr7_v4_witness_tracked` — composes
    with `rr7_accPt_one_unconditional` (unconditional).

  * `rr7_density_unconditional : IsDenseInSU2_gs readRezayiK7GeneratingSet`.

  * `rr7_H_of_G_eq_top_unconditional : H_of_G readRezayiK7GeneratingSet = ⊤`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.

-/

import SKEFTHawking.FKLW.ReadRezayiK7ClosureDenseWitness
import SKEFTHawking.FKLW.ReadRezayiK7GeneratorCaseAnalysis
import SKEFTHawking.FKLW.ReadRezayiK7InfiniteOrder
import SKEFTHawking.FKLW.OneParameterSubgroupSU2

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix
open SKEFTHawking.FKLW
open SKEFTHawking.FKLW.SU2LieAlgebra
open SKEFTHawking.FKLW.SU2MatrixExp
open SKEFTHawking.FKLW.OneParameterSubgroupSU2

/-! ## Conditional v4-witness discharge from AccPt 1 -/

/-- **Conditional Read-Rezayi SU(2)_7 v4-witness discharge** (from AccPt 1). -/
theorem rr7_v4_witness_from_accPt
    (h_accPt : AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (Filter.principal (H_of_G readRezayiK7GeneratingSet :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))) :
    rr7_v4_witness_tracked := by
  obtain ⟨X₁, hX₁_ts, hX₁_ne, h_all_t_X₁⟩ :=
    vonNeumann_assemble_explicit_X_unconditional
      (H_of_G readRezayiK7GeneratingSet) (H_of_G_isClosed _) h_accPt
  obtain ⟨g_mat, hg_choice, hg_nc, hg_na⟩ :=
    exists_readRezayiK7_generator_not_commute_not_anticommute hX₁_ts hX₁_ne
  rcases hg_choice with hg_eq_H | hg_eq_T
  · -- g_mat = H_SU_mat. Use g := H_SU.
    set g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := H_SU with hg_def
    have hg_val : (g : Matrix (Fin 2) (Fin 2) ℂ) = g_mat := by
      rw [hg_def, hg_eq_H]; rfl
    have hg_in_H : g ∈ H_of_G readRezayiK7GeneratingSet :=
      H_SU_mem_H_of_G_RR7
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
    · exact (H_of_G readRezayiK7GeneratingSet).mul_mem
        ((H_of_G readRezayiK7GeneratingSet).mul_mem hg_in_H hM₁_inH)
        ((H_of_G readRezayiK7GeneratingSet).inv_mem hg_in_H)
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
  · -- g_mat = T_RR7_mat. Use g := T_RR7.
    set g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := T_RR7 with hg_def
    have hg_val : (g : Matrix (Fin 2) (Fin 2) ℂ) = g_mat := by
      rw [hg_def, hg_eq_T]; rfl
    have hg_in_H : g ∈ H_of_G readRezayiK7GeneratingSet :=
      T_RR7_mem_H_of_G_RR7
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
    · exact (H_of_G readRezayiK7GeneratingSet).mul_mem
        ((H_of_G readRezayiK7GeneratingSet).mul_mem hg_in_H hM₁_inH)
        ((H_of_G readRezayiK7GeneratingSet).inv_mem hg_in_H)
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

/-! ## Unconditional discharge -/

/-- **Unconditional `rr7_v4_witness_tracked` discharge**. -/
theorem rr7_v4_witness_discharged : rr7_v4_witness_tracked :=
  rr7_v4_witness_from_accPt rr7_accPt_one_unconditional

/-- **Unconditional SU(2)_7 density**. -/
theorem rr7_density_unconditional : IsDenseInSU2_gs readRezayiK7GeneratingSet :=
  rr7_density_of_tracked rr7_v4_witness_discharged

/-- **Unconditional `H_of_G readRezayiK7GeneratingSet = ⊤`**. -/
theorem rr7_H_of_G_eq_top_unconditional :
    H_of_G readRezayiK7GeneratingSet = ⊤ :=
  rr7_H_of_G_eq_top_of_tracked rr7_v4_witness_discharged

end SKEFTHawking.FKLW.GenericSU2
