/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Track T-S.2 substantive substrate — Clifford+T generator case analysis

For any `X ∈ 𝔰𝔲(2)` with `X ≠ 0`, at least one of `H_SU`, `T_SU` is a
unitary that neither commutes nor anti-commutes with `X`. This is the
Clifford+T analog of Phase 6t's
`exists_σ_Fib_SU_mat_not_commute_not_anticommute`, and is substrate for
the second-tangent direction in the v4-witness assembly for T-S.2.

## Status (WORK-IN-PROGRESS — not yet imported by root)

This file is being incrementally developed. It is **NOT** added to
`SKEFTHawking.lean` until all `sorry`s are eliminated. The headline
theorem structure is shipped (the composition pattern); the four
substantive sub-lemmas are tracked as `sorry`-placeholders for explicit
Pauli-matrix entrywise computation.

The proof strategy is documented in detail; each `sorry` corresponds to
a concrete computation that can be filled in via `simp` + `ring` + Pauli
relations.

## Headline

  * `exists_cliffordT_generator_not_commute_not_anticommute` — for any
    `X ∈ ts (Fin 2)` with `X ≠ 0`, exhibits `g ∈ {H_SU.val, T_SU.val}` with
    `g · X ≠ X · g` and `g · X ≠ -(X · g)`.

## Strategy

The cleanest split (computed via Pauli-matrix decomposition):

  - **T_SU's bad set**: `T_SU.val · X = X · T_SU.val` iff `X = c · σ_z`
    for some `c : ℝ`. Anti-commute case is trivial: `T_SU.val` NEVER
    anti-commutes with any non-zero `X ∈ ts`.

  - **H_SU's coverage of T_SU's bad set**: for `X = c · σ_z` with `c ≠ 0`,
    `H_SU.val` neither commutes nor anti-commutes.

Sub-lemmas (TODO):
  1. `T_SU_mat_never_anticommute_ts` (the easiest; ~80 LoC explicit
     entrywise computation showing the anti-commutator vanishes only
     when X = 0).
  2. `T_SU_mat_commute_ts_iff_paulI_z` (~100 LoC; centralizer
     characterization via diagonal matrices).
  3. `H_SU_mat_not_commute_paulI_z_real_smul` (~50 LoC).
  4. `H_SU_mat_not_anticommute_paulI_z_real_smul` (~50 LoC).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected (the `sorry`s are placeholders for
  in-progress substantive proofs, not axioms).
- **ADR-003** (zero sorry in shipped code): file is NOT imported by
  `SKEFTHawking.lean` while `sorry`s remain. This complies with the
  zero-sorry-in-shipped-build invariant.

-/

import SKEFTHawking.FKLW.CliffordTGeneratingSet
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
  have h_T00 : T_SU_mat ⟨0, by decide⟩ ⟨0, by decide⟩ = α := rfl
  have h_T01 : T_SU_mat ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := rfl
  have h_T10 : T_SU_mat ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := rfl
  have h_T11 : T_SU_mat ⟨1, by decide⟩ ⟨1, by decide⟩ = β := rfl
  have h_X00_zero : X ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by
    have h_entry := congr_fun (congr_fun h_sum_zero ⟨0, by decide⟩) ⟨0, by decide⟩
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
               h_T00, h_T01, h_T10, h_T11,
               Matrix.zero_apply, zero_mul, mul_zero, add_zero, zero_add] at h_entry
    -- h_entry : α * X(0,0) + X(0,0) * α = 0
    have h_eq : (2 * α) * X ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by
      linear_combination h_entry
    exact (mul_eq_zero.mp h_eq).resolve_left h2α_ne
  have h_X01_zero : X ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
    have h_entry := congr_fun (congr_fun h_sum_zero ⟨0, by decide⟩) ⟨1, by decide⟩
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
               h_T00, h_T01, h_T10, h_T11,
               Matrix.zero_apply, zero_mul, mul_zero, add_zero, zero_add] at h_entry
    -- h_entry : α * X(0,1) + X(0,1) * β = 0
    have h_eq : (α + β) * X ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
      linear_combination h_entry
    exact (mul_eq_zero.mp h_eq).resolve_left hαβ_ne
  have h_X10_zero : X ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := by
    have h_entry := congr_fun (congr_fun h_sum_zero ⟨1, by decide⟩) ⟨0, by decide⟩
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
               h_T00, h_T01, h_T10, h_T11,
               Matrix.zero_apply, zero_mul, mul_zero, add_zero, zero_add] at h_entry
    have h_eq : (α + β) * X ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := by
      linear_combination h_entry
    exact (mul_eq_zero.mp h_eq).resolve_left hαβ_ne
  have h_X11_zero : X ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := by
    have h_entry := congr_fun (congr_fun h_sum_zero ⟨1, by decide⟩) ⟨1, by decide⟩
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
               h_T00, h_T01, h_T10, h_T11,
               Matrix.zero_apply, zero_mul, mul_zero, add_zero, zero_add] at h_entry
    have h_eq : (2 * β) * X ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := by
      linear_combination h_entry
    exact (mul_eq_zero.mp h_eq).resolve_left h2β_ne
  -- All entries are zero, so X = 0.
  ext i j
  fin_cases i <;> fin_cases j <;>
    · show X _ _ = 0
      first
      | exact h_X00_zero
      | exact h_X01_zero
      | exact h_X10_zero
      | exact h_X11_zero


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
  sorry

/-! ## Sub-lemma 3: H_SU doesn't commute with c·paulI_z (c ≠ 0)

Strategy: H_SU = (i/√2)·!![1, 1; 1, -1], paulI_z = !![i, 0; 0, -i].

H_SU · paulI_z = (i/√2) · !![i·1 + 0, 0 + 1·(-i); i·1 + 0, 0 + (-1)·(-i)]
              = (i/√2) · !![i, -i; i, i]

paulI_z · H_SU = !![i·(i/√2) + 0·(i/√2), i·(i/√2) + 0·(-i/√2);
                    0 + (-i)·(i/√2), 0 + (-i)·(-i/√2)]
              = (i/√2) · !![i, i; -i, i]  (wait let me redo)

Hmm let me just compute directly. The key: H_SU and paulI_z have an
explicit commutator, and that commutator is non-zero (proportional to
σ_x - σ_x = ... actually a non-trivial Pauli). -/
theorem H_SU_mat_not_commute_paulI_z_real_smul
    (c : ℝ) (h_ne : (c : ℂ) ≠ 0) :
    H_SU_mat * ((c : ℂ) • SU2LieAlgebra.paulI_z) ≠
      ((c : ℂ) • SU2LieAlgebra.paulI_z) * H_SU_mat := by
  sorry

/-! ## Sub-lemma 4: H_SU doesn't anti-commute with c·paulI_z (c ≠ 0)

Strategy: similar entrywise computation. The anti-commutator equals
c·(i·√2)·I (a non-zero scalar matrix), so it vanishes iff c = 0. -/
theorem H_SU_mat_not_anticommute_paulI_z_real_smul
    (c : ℝ) (h_ne : (c : ℂ) ≠ 0) :
    H_SU_mat * ((c : ℂ) • SU2LieAlgebra.paulI_z) ≠
      -(((c : ℂ) • SU2LieAlgebra.paulI_z) * H_SU_mat) := by
  sorry

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
