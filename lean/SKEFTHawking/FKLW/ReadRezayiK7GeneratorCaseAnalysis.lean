/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-B.5.2 substantive substrate — Read-Rezayi SU(2)_7 generator case analysis

For any `X ∈ 𝔰𝔲(2)` with `X ≠ 0`, at least one of `H_SU`, `T_RR7` is a
unitary that neither commutes nor anti-commutes with `X`. This mirrors
the Phase 6u Track T-S.2 substrate (`CliffordTGeneratorCaseAnalysis.lean`)
at phase `π/18` (level k=7) instead of `π/8`, REUSING the H_SU lemmas
from Clifford+T verbatim (since `σ_5_1 = H_SU` is alphabet-independent).

## Strategy

Same as Clifford+T:
  - **T_RR7's bad set**: `T_RR7 · X = X · T_RR7` iff `X = c · paulI_z`
    for some `c : ℝ`. Anti-commute case is trivial: `T_RR7` NEVER
    anti-commutes with any non-zero `X ∈ ts`.
  - **H_SU's coverage of T_RR7's bad set**: for `X = c · paulI_z` with
    `c ≠ 0`, `H_SU` neither commutes nor anti-commutes — reused from
    Phase 6u (`H_SU_mat_not_commute_paulI_z_real_smul`,
    `H_SU_mat_not_anticommute_paulI_z_real_smul`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.

-/

import SKEFTHawking.FKLW.ReadRezayiK7GeneratingSet
import SKEFTHawking.FKLW.ReadRezayiK7NonCommuting
import SKEFTHawking.FKLW.CliffordTGeneratorCaseAnalysis
import SKEFTHawking.FKLW.SU2LieAlgebra

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix Complex Real
open SKEFTHawking.FKLW
open SKEFTHawking.FKLW.SU2LieAlgebra

/-! ## Sub-lemma 1: T_RR7 never anti-commutes with non-zero ts elements -/
theorem T_RR7_mat_never_anticommute_ts
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (_hX : X ∈ tracelessSkewHermitian (Fin 2))
    (hX_ne : X ≠ 0) :
    T_RR7_mat * X ≠ -(X * T_RR7_mat) := by
  intro h_anticom
  apply hX_ne
  have h_sum_zero : T_RR7_mat * X + X * T_RR7_mat = 0 := by
    rw [h_anticom]; exact neg_add_cancel _
  set α : ℂ := Complex.exp (-(Complex.I * (Real.pi : ℂ) / 18)) with hα_def
  set β : ℂ := Complex.exp (Complex.I * (Real.pi : ℂ) / 18) with hβ_def
  have hα_ne : α ≠ 0 := Complex.exp_ne_zero _
  have hβ_ne : β ≠ 0 := Complex.exp_ne_zero _
  -- α + β = 2·cos(π/18) ≠ 0.
  have hαβ_ne : α + β ≠ 0 := by
    have h_two_cos := Complex.two_cos ((Real.pi / 18 : ℝ) : ℂ)
    have h_eq_β : Complex.exp (((Real.pi / 18 : ℝ) : ℂ) * Complex.I) = β := by
      rw [hβ_def]; congr 1; push_cast; ring
    have h_eq_α : Complex.exp (-((Real.pi / 18 : ℝ) : ℂ) * Complex.I) = α := by
      rw [hα_def]; congr 1; push_cast; ring
    rw [h_eq_β, h_eq_α] at h_two_cos
    have h_sum_eq : α + β = 2 * Complex.cos ((Real.pi / 18 : ℝ) : ℂ) := by
      rw [add_comm, ← h_two_cos]
    rw [h_sum_eq, ← Complex.ofReal_cos]
    have h_cos_pos : (0 : ℝ) < Real.cos (Real.pi / 18) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have h_pi := Real.pi_pos; linarith
      · have h_pi := Real.pi_pos; linarith
    have h_cos_ne : (Real.cos (Real.pi / 18) : ℂ) ≠ 0 := by
      exact_mod_cast h_cos_pos.ne'
    exact mul_ne_zero two_ne_zero h_cos_ne
  have h2α_ne : 2 * α ≠ 0 := mul_ne_zero two_ne_zero hα_ne
  have h2β_ne : 2 * β ≠ 0 := mul_ne_zero two_ne_zero hβ_ne
  have h0eq : (0 : Fin 2) = ⟨0, by decide⟩ := rfl
  have h1eq : (1 : Fin 2) = ⟨1, by decide⟩ := rfl
  have h_T00 : T_RR7_mat ⟨0, by decide⟩ ⟨0, by decide⟩ = α := rfl
  have h_T01 : T_RR7_mat ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := rfl
  have h_T10 : T_RR7_mat ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := rfl
  have h_T11 : T_RR7_mat ⟨1, by decide⟩ ⟨1, by decide⟩ = β := rfl
  have h_X00_zero : X ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by
    have h_entry := congr_fun (congr_fun h_sum_zero ⟨0, by decide⟩) ⟨0, by decide⟩
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
               Matrix.zero_apply] at h_entry
    rw [h0eq, h1eq, h_T00, h_T01, h_T10] at h_entry
    have h_eq : (2 * α) * X ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by
      linear_combination h_entry
    exact (mul_eq_zero.mp h_eq).resolve_left h2α_ne
  have h_X01_zero : X ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
    have h_entry := congr_fun (congr_fun h_sum_zero ⟨0, by decide⟩) ⟨1, by decide⟩
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
               Matrix.zero_apply] at h_entry
    rw [h0eq, h1eq, h_T00, h_T01, h_T11] at h_entry
    have h_eq : (α + β) * X ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
      linear_combination h_entry
    exact (mul_eq_zero.mp h_eq).resolve_left hαβ_ne
  have h_X10_zero : X ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := by
    have h_entry := congr_fun (congr_fun h_sum_zero ⟨1, by decide⟩) ⟨0, by decide⟩
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
               Matrix.zero_apply] at h_entry
    rw [h0eq, h1eq, h_T00, h_T10, h_T11] at h_entry
    have h_eq : (α + β) * X ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := by
      linear_combination h_entry
    exact (mul_eq_zero.mp h_eq).resolve_left hαβ_ne
  have h_X11_zero : X ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := by
    have h_entry := congr_fun (congr_fun h_sum_zero ⟨1, by decide⟩) ⟨1, by decide⟩
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
               Matrix.zero_apply] at h_entry
    rw [h0eq, h1eq, h_T01, h_T10, h_T11] at h_entry
    have h_eq : (2 * β) * X ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := by
      linear_combination h_entry
    exact (mul_eq_zero.mp h_eq).resolve_left h2β_ne
  ext i j
  fin_cases i <;> fin_cases j
  · exact h_X00_zero
  · exact h_X01_zero
  · exact h_X10_zero
  · exact h_X11_zero

/-! ## Sub-lemma 2: T_RR7 commutator characterization -/
theorem T_RR7_mat_commute_ts_iff_paulI_z
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    T_RR7_mat * X = X * T_RR7_mat ↔
    ∃ c : ℝ, X = (c : ℂ) • SU2LieAlgebra.paulI_z := by
  set α : ℂ := Complex.exp (-(Complex.I * (Real.pi : ℂ) / 18)) with hα_def
  set β : ℂ := Complex.exp (Complex.I * (Real.pi : ℂ) / 18) with hβ_def
  have hα_ne : α ≠ 0 := Complex.exp_ne_zero _
  have hβ_ne : β ≠ 0 := Complex.exp_ne_zero _
  have hαβ_distinct : α ≠ β := by
    intro h_eq
    apply exp_I_pi_18_ne_exp_neg_I_pi_18
    rw [hβ_def, hα_def] at h_eq
    exact h_eq.symm
  have hαβ_diff_ne : α - β ≠ 0 := sub_ne_zero.mpr hαβ_distinct
  have hβα_diff_ne : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ_distinct)
  have h0eq : (0 : Fin 2) = ⟨0, by decide⟩ := rfl
  have h1eq : (1 : Fin 2) = ⟨1, by decide⟩ := rfl
  have h_T00 : T_RR7_mat ⟨0, by decide⟩ ⟨0, by decide⟩ = α := rfl
  have h_T01 : T_RR7_mat ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := rfl
  have h_T10 : T_RR7_mat ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := rfl
  have h_T11 : T_RR7_mat ⟨1, by decide⟩ ⟨1, by decide⟩ = β := rfl
  refine ⟨fun h_comm => ?_, ?_⟩
  · have h_diff_zero : T_RR7_mat * X - X * T_RR7_mat = 0 := sub_eq_zero.mpr h_comm
    have h_X01_zero : X ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
      have h_entry := congr_fun (congr_fun h_diff_zero ⟨0, by decide⟩) ⟨1, by decide⟩
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
                 Matrix.zero_apply] at h_entry
      rw [h0eq, h1eq, h_T00, h_T01, h_T11] at h_entry
      have h_eq : (α - β) * X ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
        linear_combination h_entry
      exact (mul_eq_zero.mp h_eq).resolve_left hαβ_diff_ne
    have h_X10_zero : X ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := by
      have h_entry := congr_fun (congr_fun h_diff_zero ⟨1, by decide⟩) ⟨0, by decide⟩
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
                 Matrix.zero_apply] at h_entry
      rw [h0eq, h1eq, h_T00, h_T10, h_T11] at h_entry
      have h_eq : (β - α) * X ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := by
        linear_combination h_entry
      exact (mul_eq_zero.mp h_eq).resolve_left hβα_diff_ne
    obtain ⟨h_re_00, h_11, _h_offdiag⟩ := tracelessSkewHermitian_entries hX
    set c : ℝ := (X ⟨0, by decide⟩ ⟨0, by decide⟩).im with hc_def
    refine ⟨c, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · show X ⟨0, by decide⟩ ⟨0, by decide⟩ =
        ((c : ℂ) • SU2LieAlgebra.paulI_z) ⟨0, by decide⟩ ⟨0, by decide⟩
      have h_pz : (SU2LieAlgebra.paulI_z) ⟨0, by decide⟩ ⟨0, by decide⟩ = Complex.I := by
        simp [SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z, Matrix.smul_apply, smul_eq_mul]
      rw [Matrix.smul_apply, h_pz, smul_eq_mul]
      apply Complex.ext
      · simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
              Complex.ofReal_im]
        exact h_re_00
      · simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
              Complex.ofReal_im, hc_def]
    · show X ⟨0, by decide⟩ ⟨1, by decide⟩ =
        ((c : ℂ) • SU2LieAlgebra.paulI_z) ⟨0, by decide⟩ ⟨1, by decide⟩
      have h_pz : (SU2LieAlgebra.paulI_z) ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
        simp [SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z, Matrix.smul_apply, smul_eq_mul]
      rw [Matrix.smul_apply, h_pz, smul_eq_mul, mul_zero]
      exact h_X01_zero
    · show X ⟨1, by decide⟩ ⟨0, by decide⟩ =
        ((c : ℂ) • SU2LieAlgebra.paulI_z) ⟨1, by decide⟩ ⟨0, by decide⟩
      have h_pz : (SU2LieAlgebra.paulI_z) ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := by
        simp [SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z, Matrix.smul_apply, smul_eq_mul]
      rw [Matrix.smul_apply, h_pz, smul_eq_mul, mul_zero]
      exact h_X10_zero
    · show X ⟨1, by decide⟩ ⟨1, by decide⟩ =
        ((c : ℂ) • SU2LieAlgebra.paulI_z) ⟨1, by decide⟩ ⟨1, by decide⟩
      have h_pz : (SU2LieAlgebra.paulI_z) ⟨1, by decide⟩ ⟨1, by decide⟩ = -Complex.I := by
        simp [SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z, Matrix.smul_apply, smul_eq_mul]
      rw [Matrix.smul_apply, h_pz, smul_eq_mul]
      rw [show X ⟨1, by decide⟩ ⟨1, by decide⟩ = -X ⟨0, by decide⟩ ⟨0, by decide⟩ from h_11]
      apply Complex.ext
      · simp [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
        exact h_re_00
      · simp [Complex.mul_im, Complex.neg_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, hc_def]
  · rintro ⟨c, hc⟩
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T_RR7_mat, SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z,
            Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;>
      ring

/-! ## Composition: case-analysis headline -/

/-- **Phase 6x T-B.5.2 case-analysis headline**: for any `X ∈ ts(Fin 2)`
with `X ≠ 0`, at least one of `H_SU_mat`, `T_RR7_mat` is a unitary that
neither commutes nor anti-commutes with `X`.

Reuses `H_SU_mat_not_commute_paulI_z_real_smul` and
`H_SU_mat_not_anticommute_paulI_z_real_smul` from Phase 6u Track T-S.2
(since `σ_5_1 = H_SU` is level-independent). -/
theorem exists_readRezayiK7_generator_not_commute_not_anticommute
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2))
    (hX_ne : X ≠ 0) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℂ,
      (g = H_SU_mat ∨ g = T_RR7_mat) ∧
      g * X ≠ X * g ∧
      g * X ≠ -(X * g) := by
  by_cases h_comm_T : T_RR7_mat * X = X * T_RR7_mat
  · obtain ⟨c, h_X_eq⟩ := (T_RR7_mat_commute_ts_iff_paulI_z hX).mp h_comm_T
    have h_c_ne : (c : ℂ) ≠ 0 := by
      intro h_c_zero
      apply hX_ne
      rw [h_X_eq, h_c_zero, zero_smul]
    refine ⟨H_SU_mat, Or.inl rfl, ?_, ?_⟩
    · rw [h_X_eq]
      exact H_SU_mat_not_commute_paulI_z_real_smul c h_c_ne
    · rw [h_X_eq]
      exact H_SU_mat_not_anticommute_paulI_z_real_smul c h_c_ne
  · refine ⟨T_RR7_mat, Or.inr rfl, h_comm_T, ?_⟩
    exact T_RR7_mat_never_anticommute_ts hX hX_ne

end SKEFTHawking.FKLW.GenericSU2
