/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Track T-S.2 substantive substrate — Clifford+T generator case analysis

For any `X ∈ 𝔰𝔲(2)` with `X ≠ 0`, at least one of `H_SU`, `T_SU` is a
unitary that neither commutes nor anti-commutes with `X`. This is the
Clifford+T analog of Phase 6t's
`exists_σ_Fib_SU_mat_not_commute_not_anticommute`, and is substrate for
the second-tangent direction in the v4-witness assembly for T-S.2.

## Status (COMPLETE — all four sub-lemmas + composition headline shipped)

All four substantive sub-lemmas and the composition headline are
discharged kernel-only via explicit Pauli-matrix entrywise computation.
This file is imported by `SKEFTHawking.lean` and contributes the
Clifford+T case-analysis substrate to the root build.

## Headline

  * `exists_cliffordT_generator_not_commute_not_anticommute` — for any
    `X ∈ ts (Fin 2)` with `X ≠ 0`, exhibits `g ∈ {H_SU.val, T_SU.val}` with
    `g · X ≠ X · g` and `g · X ≠ -(X · g)`.

## Strategy

The cleanest split (computed via Pauli-matrix decomposition):

  - **T_SU's bad set**: `T_SU.val · X = X · T_SU.val` iff `X = c · paulI_z`
    for some `c : ℝ`. Anti-commute case is trivial: `T_SU.val` NEVER
    anti-commutes with any non-zero `X ∈ ts`.

  - **H_SU's coverage of T_SU's bad set**: for `X = c · paulI_z` with `c ≠ 0`,
    `H_SU.val` neither commutes nor anti-commutes.

Sub-lemmas:
  1. `T_SU_mat_never_anticommute_ts` — explicit entrywise computation
     showing the anti-commutator vanishes only when X = 0.
  2. `T_SU_mat_commute_ts_iff_paulI_z` — centralizer characterization
     via diagonal matrices (forward via α ≠ β; reverse by direct
     entrywise computation on the diagonal product).
  3. `H_SU_mat_not_commute_paulI_z_real_smul` — entry (0,1) computation
     reduces to `c = -c` after multiplication by `√2` and `I² = -1`.
  4. `H_SU_mat_not_anticommute_paulI_z_real_smul` — entry (0,0)
     computation, same shape as sub-lemma 3.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
- **ADR-003** (zero sorry in shipped code): respected (zero sorries).

-/

import SKEFTHawking.FKLW.CliffordTGeneratingSet
import SKEFTHawking.FKLW.CliffordTNonCommuting
import SKEFTHawking.FKLW.SU2LieAlgebra

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix Complex Real
open SKEFTHawking.FKLW
open SKEFTHawking.FKLW.SU2LieAlgebra

/-! ## Sub-lemma 1: T_SU never anti-commutes with non-zero ts elements

Strategy: anti-commutator `T_SU·X + X·T_SU = 0` entrywise gives:
  - (0,0): `2·α·X(0,0) = 0` ⟹ `X(0,0) = 0` (α ≠ 0)
  - (0,1): `(α+β)·X(0,1) = 0` ⟹ `X(0,1) = 0` (α+β = 2·cos(π/8) ≠ 0)
  - (1,0): `(α+β)·X(1,0) = 0` ⟹ `X(1,0) = 0`
  - (1,1): `2·β·X(1,1) = 0` ⟹ `X(1,1) = 0`
Hence X = 0, contradicting X ≠ 0. -/
theorem T_SU_mat_never_anticommute_ts
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (_hX : X ∈ tracelessSkewHermitian (Fin 2))
    (hX_ne : X ≠ 0) :
    T_SU_mat * X ≠ -(X * T_SU_mat) := by
  intro h_anticom
  apply hX_ne
  -- We show X = 0 by showing each entry is 0.
  -- Strategy: from h_anticom : T_SU * X = -(X * T_SU), we get
  --   T_SU * X + X * T_SU = 0
  -- The entry (i, j) of this matrix involves T_SU(i,i)·X(i,j) + X(i,j)·T_SU(j,j)
  -- = (T_SU(i,i) + T_SU(j,j))·X(i,j) (since T_SU is diagonal, off-diagonals are 0).
  -- For all (i,j), the coefficient (T_SU(i,i) + T_SU(j,j)) is non-zero (= 2α, α+β, or 2β),
  -- forcing X(i,j) = 0.
  have h_sum_zero : T_SU_mat * X + X * T_SU_mat = 0 := by
    rw [h_anticom]; exact neg_add_cancel _
  -- Set up scalar names.
  set α : ℂ := Complex.exp (-(Complex.I * (Real.pi : ℂ) / 8)) with hα_def
  set β : ℂ := Complex.exp (Complex.I * (Real.pi : ℂ) / 8) with hβ_def
  have hα_ne : α ≠ 0 := Complex.exp_ne_zero _
  have hβ_ne : β ≠ 0 := Complex.exp_ne_zero _
  -- α + β = 2·cos(π/8) ≠ 0.
  have hαβ_ne : α + β ≠ 0 := by
    -- α + β = exp(-iπ/8) + exp(iπ/8). Use Complex.two_cos:
    -- 2 cos x = exp(x·I) + exp(-x·I). At x = π/8 (cast to ℂ): 2 cos(π/8) = β + α.
    have h_two_cos := Complex.two_cos ((Real.pi / 8 : ℝ) : ℂ)
    -- h_two_cos : 2 * Complex.cos ((π/8 : ℝ) : ℂ)
    --              = exp(((π/8 : ℝ) : ℂ) * Complex.I) + exp(-((π/8 : ℝ) : ℂ) * Complex.I)
    have h_eq_β : Complex.exp (((Real.pi / 8 : ℝ) : ℂ) * Complex.I) = β := by
      rw [hβ_def]; congr 1; push_cast; ring
    have h_eq_α : Complex.exp (-((Real.pi / 8 : ℝ) : ℂ) * Complex.I) = α := by
      rw [hα_def]; congr 1; push_cast; ring
    rw [h_eq_β, h_eq_α] at h_two_cos
    -- h_two_cos : 2 * Complex.cos ((π/8 : ℝ) : ℂ) = β + α.
    have h_sum_eq : α + β = 2 * Complex.cos ((Real.pi / 8 : ℝ) : ℂ) := by
      rw [add_comm, ← h_two_cos]
    rw [h_sum_eq, ← Complex.ofReal_cos]
    -- Goal: 2 * ((Real.cos (π/8) : ℝ) : ℂ) ≠ 0.
    have h_cos_pos : (0 : ℝ) < Real.cos (Real.pi / 8) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have h_pi := Real.pi_pos; linarith
      · have h_pi := Real.pi_pos; linarith
    have h_cos_ne : (Real.cos (Real.pi / 8) : ℂ) ≠ 0 := by
      exact_mod_cast h_cos_pos.ne'
    exact mul_ne_zero two_ne_zero h_cos_ne
  -- 2α ≠ 0, 2β ≠ 0.
  have h2α_ne : 2 * α ≠ 0 := mul_ne_zero two_ne_zero hα_ne
  have h2β_ne : 2 * β ≠ 0 := mul_ne_zero two_ne_zero hβ_ne
  -- Show X = 0 entrywise. We extract each (i,j) entry from h_sum_zero.
  -- For T_SU diagonal, (T_SU·X + X·T_SU)(i,j) = T_SU(i,i)·X(i,j) + X(i,j)·T_SU(j,j).
  -- (0,0): 2α·X(0,0) = 0; (0,1): (α+β)·X(0,1) = 0; (1,0): same; (1,1): 2β·X(1,1) = 0.
  -- Fin 2 literal bridges (simp/Fin.sum_univ_two emits `0`/`1` literal form;
  -- our T_SU lookups use `⟨0/1, by decide⟩` form; these are rfl-equal).
  have h0eq : (0 : Fin 2) = ⟨0, by decide⟩ := rfl
  have h1eq : (1 : Fin 2) = ⟨1, by decide⟩ := rfl
  have h_T00 : T_SU_mat ⟨0, by decide⟩ ⟨0, by decide⟩ = α := rfl
  have h_T01 : T_SU_mat ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := rfl
  have h_T10 : T_SU_mat ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := rfl
  have h_T11 : T_SU_mat ⟨1, by decide⟩ ⟨1, by decide⟩ = β := rfl
  have h_X00_zero : X ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by
    have h_entry := congr_fun (congr_fun h_sum_zero ⟨0, by decide⟩) ⟨0, by decide⟩
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
               Matrix.zero_apply] at h_entry
    rw [h0eq, h1eq, h_T00, h_T01, h_T10] at h_entry
    -- h_entry should now be: α * X(0,0) + 0 * X(1,0) + (X(0,0) * α + X(0,1) * 0) = 0
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
  -- All entries are zero, so X = 0. Use Matrix.ext with Fin.forall_fin_two-style.
  ext i j
  fin_cases i <;> fin_cases j
  · exact h_X00_zero
  · exact h_X01_zero
  · exact h_X10_zero
  · exact h_X11_zero


/-! ## Sub-lemma 2: T_SU commutator characterization

Strategy: commutator `T_SU·X = X·T_SU` entrywise:
  - (0,0): `α·X(0,0) = X(0,0)·α` (always true)
  - (0,1): `α·X(0,1) = X(0,1)·β` ⟹ `X(0,1)·(α-β) = 0`. Since α-β ≠ 0,
    X(0,1) = 0.
  - (1,0): `β·X(1,0) = X(1,0)·α` ⟹ `X(1,0)·(β-α) = 0`. Since β-α ≠ 0,
    X(1,0) = 0.
  - (1,1): `β·X(1,1) = X(1,1)·β` (always true)
So X is diagonal. Combined with X ∈ ts (X(1,1) = -X(0,0) and
X(0,0) purely imaginary), X = i·x·diag(1,-1) = (i·x)·σ_z for some real x,
i.e., X = (real x) • paulI_z. -/
theorem T_SU_mat_commute_ts_iff_paulI_z
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    T_SU_mat * X = X * T_SU_mat ↔
    ∃ c : ℝ, X = (c : ℂ) • SU2LieAlgebra.paulI_z := by
  -- Set up scalar names α, β.
  set α : ℂ := Complex.exp (-(Complex.I * (Real.pi : ℂ) / 8)) with hα_def
  set β : ℂ := Complex.exp (Complex.I * (Real.pi : ℂ) / 8) with hβ_def
  have hα_ne : α ≠ 0 := Complex.exp_ne_zero _
  have hβ_ne : β ≠ 0 := Complex.exp_ne_zero _
  -- α ≠ β: exp(-iπ/8) ≠ exp(iπ/8).
  have hαβ_distinct : α ≠ β := by
    intro h_eq
    -- If α = β, then exp(iπ/4) = exp(iπ/8) / exp(-iπ/8) = β/α = 1.
    -- That contradicts our existing lemma exp_I_pi_8_ne_exp_neg_I_pi_8.
    apply exp_I_pi_8_ne_exp_neg_I_pi_8
    rw [hβ_def, hα_def] at h_eq
    exact h_eq.symm
  have hαβ_diff_ne : α - β ≠ 0 := sub_ne_zero.mpr hαβ_distinct
  have hβα_diff_ne : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ_distinct)
  -- Fin 2 literal bridges.
  have h0eq : (0 : Fin 2) = ⟨0, by decide⟩ := rfl
  have h1eq : (1 : Fin 2) = ⟨1, by decide⟩ := rfl
  have h_T00 : T_SU_mat ⟨0, by decide⟩ ⟨0, by decide⟩ = α := rfl
  have h_T01 : T_SU_mat ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := rfl
  have h_T10 : T_SU_mat ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := rfl
  have h_T11 : T_SU_mat ⟨1, by decide⟩ ⟨1, by decide⟩ = β := rfl
  refine ⟨fun h_comm => ?_, ?_⟩
  · -- Forward: commutativity ⟹ X = c • paulI_z.
    -- Entry-by-entry analysis of T_SU·X - X·T_SU = 0:
    --   (0,0): α·X(0,0) - X(0,0)·α = 0 (trivially)
    --   (0,1): α·X(0,1) - X(0,1)·β = (α-β)·X(0,1) = 0 ⟹ X(0,1) = 0
    --   (1,0): β·X(1,0) - X(1,0)·α = (β-α)·X(1,0) = 0 ⟹ X(1,0) = 0
    --   (1,1): trivially 0
    have h_diff_zero : T_SU_mat * X - X * T_SU_mat = 0 := sub_eq_zero.mpr h_comm
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
    -- Now use the ts-structure: X(0,0) is pure imaginary, X(1,1) = -X(0,0).
    obtain ⟨h_re_00, h_11, _h_offdiag⟩ := tracelessSkewHermitian_entries hX
    -- So X(0,0) = (X(0,0).im : ℂ) * I; let c := X(0,0).im.
    set c : ℝ := (X ⟨0, by decide⟩ ⟨0, by decide⟩).im with hc_def
    refine ⟨c, ?_⟩
    -- Show X = c • paulI_z entrywise.
    ext i j
    fin_cases i <;> fin_cases j
    · -- (0,0): X(0,0) = c • paulI_z(0,0) = c • I = c·I
      show X ⟨0, by decide⟩ ⟨0, by decide⟩ =
        ((c : ℂ) • SU2LieAlgebra.paulI_z) ⟨0, by decide⟩ ⟨0, by decide⟩
      have h_pz : (SU2LieAlgebra.paulI_z) ⟨0, by decide⟩ ⟨0, by decide⟩ = Complex.I := by
        simp [SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z, Matrix.smul_apply, smul_eq_mul]
      rw [Matrix.smul_apply, h_pz, smul_eq_mul]
      -- Goal: X(0,0) = (c : ℂ) * I where c = X(0,0).im, and X(0,0).re = 0.
      have := h_re_00
      -- X(0,0) is pure imaginary
      apply Complex.ext
      · simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
              Complex.ofReal_im]
        exact this
      · simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
              Complex.ofReal_im, hc_def]
    · -- (0,1): X(0,1) = c • paulI_z(0,1) = c • 0 = 0
      show X ⟨0, by decide⟩ ⟨1, by decide⟩ =
        ((c : ℂ) • SU2LieAlgebra.paulI_z) ⟨0, by decide⟩ ⟨1, by decide⟩
      have h_pz : (SU2LieAlgebra.paulI_z) ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
        simp [SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z, Matrix.smul_apply, smul_eq_mul]
      rw [Matrix.smul_apply, h_pz, smul_eq_mul, mul_zero]
      exact h_X01_zero
    · -- (1,0): X(1,0) = c • paulI_z(1,0) = c • 0 = 0
      show X ⟨1, by decide⟩ ⟨0, by decide⟩ =
        ((c : ℂ) • SU2LieAlgebra.paulI_z) ⟨1, by decide⟩ ⟨0, by decide⟩
      have h_pz : (SU2LieAlgebra.paulI_z) ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := by
        simp [SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z, Matrix.smul_apply, smul_eq_mul]
      rw [Matrix.smul_apply, h_pz, smul_eq_mul, mul_zero]
      exact h_X10_zero
    · -- (1,1): X(1,1) = -X(0,0) = -c·I = c • paulI_z(1,1) = c • (-I)
      show X ⟨1, by decide⟩ ⟨1, by decide⟩ =
        ((c : ℂ) • SU2LieAlgebra.paulI_z) ⟨1, by decide⟩ ⟨1, by decide⟩
      have h_pz : (SU2LieAlgebra.paulI_z) ⟨1, by decide⟩ ⟨1, by decide⟩ = -Complex.I := by
        simp [SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z, Matrix.smul_apply, smul_eq_mul]
      rw [Matrix.smul_apply, h_pz, smul_eq_mul]
      -- Goal: X(1,1) = c • (-I) = -(c·I)
      -- X(1,1) = -X(0,0). X(0,0) = c·I. So X(1,1) = -c·I.
      rw [show X ⟨1, by decide⟩ ⟨1, by decide⟩ = -X ⟨0, by decide⟩ ⟨0, by decide⟩ from h_11]
      apply Complex.ext
      · simp [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
        exact h_re_00
      · simp [Complex.mul_im, Complex.neg_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, hc_def]
  · -- Reverse: X = c·paulI_z ⟹ commute.
    rintro ⟨c, hc⟩
    rw [hc]
    -- T_SU * (c • paulI_z) = (c • paulI_z) * T_SU. Both are diagonal.
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T_SU_mat, SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z,
            Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul] <;>
      ring

/-! ## Sub-lemma 3: H_SU doesn't commute with c·paulI_z (c ≠ 0)

Strategy: extract entry (0,1) of the commutator. After `simp` reduction:
LHS = `-(I/√2 · (c·I))`, RHS = `c·I · (I/√2)`. Multiply both sides by
`√2`; using `I² = -1`, LHS·√2 = c and RHS·√2 = -c, so `c = -c`, hence
`2c = 0`, hence `c = 0` (contradiction). -/
theorem H_SU_mat_not_commute_paulI_z_real_smul
    (c : ℝ) (h_ne : (c : ℂ) ≠ 0) :
    H_SU_mat * ((c : ℂ) • SU2LieAlgebra.paulI_z) ≠
      ((c : ℂ) • SU2LieAlgebra.paulI_z) * H_SU_mat := by
  intro h_eq
  -- Extract entry (0,1) and reduce both sides via Complex.I_mul_I.
  have h_at_0_1 := congr_fun (congr_fun h_eq ⟨0, by decide⟩) ⟨1, by decide⟩
  simp [H_SU_mat, SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z,
        Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
    at h_at_0_1
  -- After simp: -(I / √2 * (c * I)) = c * I * (I / √2).
  -- Multiply both sides by √2. Use I * I = -1.
  -- LHS · √2 = -(I * c * I) = -c · (-1) = c.
  -- RHS · √2 = c · I · I = c · (-1) = -c.
  -- So c = -c, hence 2c = 0, hence c = 0.
  have h_sqrt_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h_clear : (c : ℂ) = -(c : ℂ) := by
    have h_mul : (-(Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * ((c : ℂ) * Complex.I))) *
                   ((Real.sqrt 2 : ℝ) : ℂ) =
                 ((c : ℂ) * Complex.I * (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ))) *
                   ((Real.sqrt 2 : ℝ) : ℂ) := by
      rw [h_at_0_1]
    have h_lhs : (-(Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * ((c : ℂ) * Complex.I))) *
                   ((Real.sqrt 2 : ℝ) : ℂ) = (c : ℂ) := by
      field_simp
      linear_combination -Complex.I_sq
    have h_rhs : ((c : ℂ) * Complex.I * (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ))) *
                   ((Real.sqrt 2 : ℝ) : ℂ) = -(c : ℂ) := by
      field_simp
      linear_combination Complex.I_sq
    rw [h_lhs, h_rhs] at h_mul
    exact h_mul
  -- From c = -c: 2c = 0.
  have h_2c_zero : (2 : ℂ) * (c : ℂ) = 0 := by linear_combination h_clear
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h_2c_zero with h_2 | h_c
  · exact absurd h_2 h_two_ne
  · exact h_ne h_c

/-! ## Sub-lemma 4: H_SU doesn't anti-commute with c·paulI_z (c ≠ 0)

Same shape as sub-lemma 3 with anti-commutator at (0,0). -/
theorem H_SU_mat_not_anticommute_paulI_z_real_smul
    (c : ℝ) (h_ne : (c : ℂ) ≠ 0) :
    H_SU_mat * ((c : ℂ) • SU2LieAlgebra.paulI_z) ≠
      -(((c : ℂ) • SU2LieAlgebra.paulI_z) * H_SU_mat) := by
  intro h_eq
  -- Extract entry (0,0) and reduce.
  have h_at_0_0 := congr_fun (congr_fun h_eq ⟨0, by decide⟩) ⟨0, by decide⟩
  simp [H_SU_mat, SU2LieAlgebra.paulI_z, SKEFTHawking.σ_z,
        Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul,
        Matrix.neg_apply]
    at h_at_0_0
  -- After simp: I/√2 * (c·I) = -((c·I) * (I/√2)) (or similar).
  -- LHS = c·I²/√2 = -c/√2.
  -- RHS = -(c·I²/√2) = -(-c/√2) = c/√2.
  -- So -c/√2 = c/√2 ⟹ 2c/√2 = 0 ⟹ c = 0.
  have h_sqrt_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h_clear : (c : ℂ) = -(c : ℂ) := by
    -- Multiply both sides of h_at_0_0 by √2.
    have h_mul : h_at_0_0.symm = h_at_0_0.symm := rfl
    -- We need to reduce. After simp, h_at_0_0 typically has the form
    --   I / ↑√2 * (↑c * I) = -(↑c * I * (I / ↑√2))
    -- Multiply LHS · √2 = -c, RHS · √2 = -(-c) = c.
    -- So -c = c, i.e., c = -c.
    have h_step : (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * ((c : ℂ) * Complex.I)) *
                    ((Real.sqrt 2 : ℝ) : ℂ) =
                  (-((c : ℂ) * Complex.I * (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ)))) *
                    ((Real.sqrt 2 : ℝ) : ℂ) := by
      rw [h_at_0_0]
    have h_lhs : (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) * ((c : ℂ) * Complex.I)) *
                   ((Real.sqrt 2 : ℝ) : ℂ) = -(c : ℂ) := by
      field_simp
      linear_combination Complex.I_sq
    have h_rhs : (-((c : ℂ) * Complex.I * (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ)))) *
                   ((Real.sqrt 2 : ℝ) : ℂ) = (c : ℂ) := by
      field_simp
      linear_combination -Complex.I_sq
    rw [h_lhs, h_rhs] at h_step
    -- h_step : -c = c, so c = -c.
    linear_combination -h_step
  have h_2c_zero : (2 : ℂ) * (c : ℂ) = 0 := by linear_combination h_clear
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  apply h_ne
  rcases mul_eq_zero.mp h_2c_zero with h_2 | h_c
  · exact absurd h_2 h_two_ne
  · exact h_c

/-! ## Composition: case-analysis headline -/

/-- **Phase 6u T-S.2 case-analysis headline**: for any `X ∈ ts(Fin 2)`
with `X ≠ 0`, at least one of `H_SU_mat`, `T_SU_mat` is a unitary that
neither commutes nor anti-commutes with `X`.

By the strategy in §"Strategy" of this file's docstring:
  - If T_SU commutes with X, then X = c·paulI_z (sub-lemma 2), so
    H_SU works (sub-lemmas 3 + 4).
  - Else T_SU doesn't commute (by hypothesis); T_SU doesn't anti-commute
    (sub-lemma 1). T_SU works. -/
theorem exists_cliffordT_generator_not_commute_not_anticommute
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2))
    (hX_ne : X ≠ 0) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℂ,
      (g = H_SU_mat ∨ g = T_SU_mat) ∧
      g * X ≠ X * g ∧
      g * X ≠ -(X * g) := by
  by_cases h_comm_T : T_SU_mat * X = X * T_SU_mat
  · -- T_SU commutes with X → X = c·paulI_z → use H_SU
    obtain ⟨c, h_X_eq⟩ := (T_SU_mat_commute_ts_iff_paulI_z hX).mp h_comm_T
    have h_c_ne : (c : ℂ) ≠ 0 := by
      intro h_c_zero
      apply hX_ne
      rw [h_X_eq, h_c_zero, zero_smul]
    refine ⟨H_SU_mat, Or.inl rfl, ?_, ?_⟩
    · -- H_SU doesn't commute with c·paulI_z
      rw [h_X_eq]
      exact H_SU_mat_not_commute_paulI_z_real_smul c h_c_ne
    · -- H_SU doesn't anti-commute with c·paulI_z
      rw [h_X_eq]
      exact H_SU_mat_not_anticommute_paulI_z_real_smul c h_c_ne
  · -- T_SU doesn't commute → use T_SU (it never anti-commutes with non-zero ts)
    refine ⟨T_SU_mat, Or.inr rfl, h_comm_T, ?_⟩
    exact T_SU_mat_never_anticommute_ts hX hX_ne

end SKEFTHawking.FKLW.GenericSU2
