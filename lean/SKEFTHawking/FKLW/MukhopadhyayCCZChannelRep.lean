/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x′ Phase 2 (C) — the channel representation of CCZ has half-integer entries (Theorem 3.8)

For the unconditional Toffoli bound, the one fact `hCCZ` needs about `Ĉ := channelRep CCZ` is that
**every entry is a half-integer** (`2·entry ∈ ℤ`): then each product entry
`(Ĉ · X)_{rs} = (1/2)·(integer combination of X entries)`, so `sde₂` rises by at most one. This is
Mukhopadhyay Theorem 3.8 (`Ĉ_CCZ` entries `∈ {0, ±1, ±1/2}`), packaged as the weaker "half-integer"
statement the `sde₂` bound consumes (no `8`-vs-`56` row count needed).

The tractable route (no `4096`-case bash): the `|111⟩` index is `7 = bitIso8 (1,1,1)`, and `kronK8`
factors entrywise over the three qubits (`kronK8_bitIso8_apply`), so
`(P_r · P_s)₇₇ = ∏ᵢ (σ_{rᵢ} σ_{sᵢ})₁₁` (`kronK8_mul_apply_77`). Since the single-qubit Paulis are
Hermitian, `(σ_b σ_a)₁₁ = conj((σ_a σ_b)₁₁)` (`pauliProd11_conj_swap`). This file ships that
entry-factorization + conjugate-swap foundation; the Gaussian-integer structure, the
`CCZ = 1 − 2|111⟩⟨111|` closed form, and the half-integer headline follow in subsequent increments.

PUBLIC math layer only.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected. Kernel-pure.

-/

import SKEFTHawking.FKLW.MukhopadhyayCCZConjugation
import SKEFTHawking.FKLW.MukhopadhyayChannelRep
import SKEFTHawking.FKLW.CliffordCCZSU8CNOTConj

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix
open SKEFTHawking.FKLW.CliffordCCZSU8
open SKEFTHawking.FKLW.TrappedIonSU4
open SKEFTHawking.FKLW.CliffordCCZ (CCZ_mat)

/-! ## C.1 — entry factorization at the `|111⟩` index `7` -/

/-- **General `kronSU8` bit-entry formula** (the `kronK8_bitIso8_apply` analog for arbitrary factors). -/
theorem kronSU8_bitIso8_apply (A B C : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2 × Fin 2 × Fin 2) :
    kronSU8 A B C (bitIso8 i) (bitIso8 j) = A i.1 j.1 * B i.2.1 j.2.1 * C i.2.2 j.2.2 := by
  unfold kronSU8 kronSU2SU4 kronSU4 bitIso8
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id_eq,
    Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

/-- The `|111⟩` computational-basis index is `bitIso8 (1,1,1) = 7`. -/
theorem bitIso8_one_one_one : bitIso8 (1, 1, 1) = 7 := by decide

/-- **`(P_v)₇₇` factors over qubits**: `(kronK8 v)₇₇ = ∏ᵢ (σ_{vᵢ})₁₁`. -/
theorem kronK8_apply_77 (v : Fin 4 × Fin 4 × Fin 4) :
    kronK8 v 7 7 = pauli4 v.1 1 1 * pauli4 v.2.1 1 1 * pauli4 v.2.2 1 1 := by
  rw [← bitIso8_one_one_one, kronK8_bitIso8_apply]

/-- **`(P_r · P_s)₇₇` factors over qubits**: `= ∏ᵢ (σ_{rᵢ} σ_{sᵢ})₁₁`. -/
theorem kronK8_mul_apply_77 (r s : Fin 4 × Fin 4 × Fin 4) :
    (kronK8 r * kronK8 s) 7 7
      = (pauli4 r.1 * pauli4 s.1) 1 1 * (pauli4 r.2.1 * pauli4 s.2.1) 1 1
          * (pauli4 r.2.2 * pauli4 s.2.2) 1 1 := by
  rw [← bitIso8_one_one_one, kronK8, kronK8, ← kronSU8_mul, kronSU8_bitIso8_apply]

/-! ## C.2 — the per-qubit product entry: conjugate-swap -/

/-- **Hermitian swap**: `(σ_b σ_a)₁₁ = conj((σ_a σ_b)₁₁)` — since the single-qubit Paulis are Hermitian,
`σ_b σ_a = (σ_a σ_b)ᴴ`, and conjugate-transpose conjugates a diagonal entry. -/
theorem pauliProd11_conj_swap (a b : Fin 4) :
    (pauli4 b * pauli4 a) 1 1 = (starRingEnd ℂ) ((pauli4 a * pauli4 b) 1 1) := by
  have h : pauli4 b * pauli4 a = (pauli4 a * pauli4 b)ᴴ := by
    rw [Matrix.conjTranspose_mul, pauli4_hermitian, pauli4_hermitian]
  rw [h, Matrix.conjTranspose_apply, starRingEnd_apply]

/-! ## C.3 — Gaussian-integer structure of the per-qubit entries -/

/-- A complex number is a **Gaussian integer** if it is `m + n·i` with `m, n ∈ ℤ`. -/
def IsGaussianInt (z : ℂ) : Prop := ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * Complex.I

theorem isGaussianInt_zero : IsGaussianInt 0 := ⟨0, 0, by simp⟩
theorem isGaussianInt_one : IsGaussianInt 1 := ⟨1, 0, by simp⟩
theorem isGaussianInt_neg_one : IsGaussianInt (-1) := ⟨-1, 0, by push_cast; ring⟩
theorem isGaussianInt_I : IsGaussianInt Complex.I := ⟨0, 1, by simp⟩
theorem isGaussianInt_neg_I : IsGaussianInt (-Complex.I) := ⟨0, -1, by push_cast; ring⟩

theorem isGaussianInt_add {z w : ℂ} (hz : IsGaussianInt z) (hw : IsGaussianInt w) :
    IsGaussianInt (z + w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a + c, b + d, by push_cast; ring⟩

theorem isGaussianInt_mul {z w : ℂ} (hz : IsGaussianInt z) (hw : IsGaussianInt w) :
    IsGaussianInt (z * w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  refine ⟨a * c - b * d, a * d + b * c, ?_⟩
  push_cast
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩ <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]

/-- The real part of a Gaussian integer is an integer. -/
theorem isGaussianInt_re_int {z : ℂ} (h : IsGaussianInt z) : ∃ k : ℤ, z.re = (k : ℝ) := by
  obtain ⟨m, n, rfl⟩ := h
  exact ⟨m, by simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]⟩

/-- Each single-qubit Pauli matrix entry is a Gaussian integer (`∈ {0, ±1, ±i}`). -/
theorem pauli4_entry_isGaussianInt (a : Fin 4) (i j : Fin 2) : IsGaussianInt (pauli4 a i j) := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp only [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.of_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne, Ne, Matrix.one_apply] <;>
    first
      | exact isGaussianInt_zero
      | exact isGaussianInt_one
      | exact isGaussianInt_neg_one
      | exact isGaussianInt_I
      | exact isGaussianInt_neg_I

/-- The single-qubit product entry `(σ_a σ_b)₁₁` is a Gaussian integer. -/
theorem pauliProd11_isGaussianInt (a b : Fin 4) : IsGaussianInt ((pauli4 a * pauli4 b) 1 1) := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact isGaussianInt_add
    (isGaussianInt_mul (pauli4_entry_isGaussianInt a 1 0) (pauli4_entry_isGaussianInt b 0 1))
    (isGaussianInt_mul (pauli4_entry_isGaussianInt a 1 1) (pauli4_entry_isGaussianInt b 1 1))

/-- **`(P_r · P_s)₇₇` is a Gaussian integer** (product of three per-qubit Gaussian entries). -/
theorem kronK8_mul_77_isGaussianInt (r s : Fin 4 × Fin 4 × Fin 4) :
    IsGaussianInt ((kronK8 r * kronK8 s) 7 7) := by
  rw [kronK8_mul_apply_77]
  exact isGaussianInt_mul
    (isGaussianInt_mul (pauliProd11_isGaussianInt r.1 s.1) (pauliProd11_isGaussianInt r.2.1 s.2.1))
    (pauliProd11_isGaussianInt r.2.2 s.2.2)

/-! ## C.4 — `(P_v)₇₇` is an integer -/

/-- Each single-qubit Pauli `(1,1)` entry is an integer (`∈ {1, 0, -1}`). -/
theorem pauli4_11_int (a : Fin 4) : ∃ k : ℤ, pauli4 a 1 1 = (k : ℂ) := by
  fin_cases a <;>
    simp only [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_fin_one,
      Matrix.empty_val', Matrix.of_apply, Matrix.one_apply_eq]
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨-1, by push_cast; ring⟩

/-- **`(P_v)₇₇` is an integer** (product of three integer single-qubit `(1,1)` entries). -/
theorem kronK8_77_int (v : Fin 4 × Fin 4 × Fin 4) : ∃ k : ℤ, kronK8 v 7 7 = (k : ℂ) := by
  obtain ⟨k1, h1⟩ := pauli4_11_int v.1
  obtain ⟨k2, h2⟩ := pauli4_11_int v.2.1
  obtain ⟨k3, h3⟩ := pauli4_11_int v.2.2
  exact ⟨k1 * k2 * k3, by rw [kronK8_apply_77, h1, h2, h3]; push_cast; ring⟩

/-! ## C.5 — the closed form: `channelRep CCZ r s` is a half-integer -/

/-- An indicator-weighted sum over `Fin 8` collapses to the value at `7`. -/
theorem sum_indicator_collapse (f : Fin 8 → ℂ) :
    (∑ i, (if i = 7 then (1 : ℂ) else 0) * f i) = f 7 := by
  rw [Finset.sum_eq_single (7 : Fin 8)]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb; rw [if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `cczDiag i = 1 − 2·𝟙[i = 7]`. -/
theorem cczDiag_eq (i : Fin 8) : cczDiag i = 1 - 2 * (if i = 7 then (1 : ℂ) else 0) := by
  unfold cczDiag
  by_cases h : i = 7 <;> simp [h] <;> norm_num

/-- `CCZ_mat` is Hermitian (real diagonal). -/
theorem CCZ_mat_conjTranspose : (CCZ_mat)ᴴ = CCZ_mat := by
  rw [CCZ_mat_eq_diagonal, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply, cczDiag]
  split <;> simp

/-- `(P_s · P_r)₇₇ = conj((P_r · P_s)₇₇)` — the conjugate symmetry from Hermiticity. -/
theorem kronK8_mul_77_conj_swap (r s : Fin 4 × Fin 4 × Fin 4) :
    (kronK8 s * kronK8 r) 7 7 = (starRingEnd ℂ) ((kronK8 r * kronK8 s) 7 7) := by
  rw [kronK8_mul_apply_77 s r, kronK8_mul_apply_77 r s, pauliProd11_conj_swap r.1 s.1,
    pauliProd11_conj_swap r.2.1 s.2.1, pauliProd11_conj_swap r.2.2 s.2.2, map_mul, map_mul]

/-- Linearity of the double sum over a `(1, −2, −2, +4)` combination (abstract; avoids `mul_sum`
over-pulling when applied to indicator summands). -/
theorem sum_sum_linear_comb (a b c d : Fin 8 → Fin 8 → ℂ) :
    (∑ i, ∑ j, (a i j - 2 * b i j - 2 * c i j + 4 * d i j))
      = (∑ i, ∑ j, a i j) - 2 * (∑ i, ∑ j, b i j) - 2 * (∑ i, ∑ j, c i j)
          + 4 * (∑ i, ∑ j, d i j) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- **The CCZ channel-rep trace decomposition.** Expanding `CCZ = 1 − 2|111⟩⟨111|` entrywise gives the
trace as `8·𝟙[r=s] − 2(P_r P_s)₇₇ − 2(P_s P_r)₇₇ + 4(P_r)₇₇(P_s)₇₇`. -/
theorem trace_kronK8_CCZ_conj (r s : Fin 4 × Fin 4 × Fin 4) :
    (kronK8 r * (CCZ_mat * kronK8 s * CCZ_mat)).trace
      = 8 * (if r = s then 1 else 0) - 2 * (kronK8 r * kronK8 s) 7 7
        - 2 * (kronK8 s * kronK8 r) 7 7 + 4 * (kronK8 r 7 7 * kronK8 s 7 7) := by
  have hLHS : (kronK8 r * (CCZ_mat * kronK8 s * CCZ_mat)).trace
      = ∑ i, ∑ j, kronK8 r i j * cczDiag j * cczDiag i * kronK8 s j i := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CCZ_mat_conj_apply]; ring
  -- the four indicator double-sum identities (value = double sum)
  have e8 : (∑ i, ∑ j, kronK8 r i j * kronK8 s j i) = 8 * (if r = s then 1 else 0) := by
    have h : (∑ i, ∑ j, kronK8 r i j * kronK8 s j i) = (kronK8 r * kronK8 s).trace := by
      rw [Matrix.trace]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Matrix.diag_apply,
        Matrix.mul_apply]
    rw [h, kronK8_mul_trace]; by_cases h : r = s <;> simp [h]
  have ez : (∑ i, ∑ j, (if i = 7 then (1 : ℂ) else 0) * (kronK8 r i j * kronK8 s j i))
      = (kronK8 r * kronK8 s) 7 7 := by
    have hin : ∀ i, (∑ j, (if i = 7 then (1 : ℂ) else 0) * (kronK8 r i j * kronK8 s j i))
        = (if i = 7 then (1 : ℂ) else 0) * ∑ j, kronK8 r i j * kronK8 s j i :=
      fun i => by rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => hin i,
      sum_indicator_collapse fun i => ∑ j, kronK8 r i j * kronK8 s j i, Matrix.mul_apply]
  have ez' : (∑ i, ∑ j, (if j = 7 then (1 : ℂ) else 0) * (kronK8 r i j * kronK8 s j i))
      = (kronK8 s * kronK8 r) 7 7 := by
    rw [Finset.sum_congr rfl fun i _ =>
      sum_indicator_collapse fun j => kronK8 r i j * kronK8 s j i, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have eg : (∑ i, ∑ j, (if i = 7 then (1 : ℂ) else 0)
        * ((if j = 7 then (1 : ℂ) else 0) * (kronK8 r i j * kronK8 s j i)))
      = kronK8 r 7 7 * kronK8 s 7 7 := by
    have hin : ∀ i, (∑ j, (if i = 7 then (1 : ℂ) else 0)
          * ((if j = 7 then (1 : ℂ) else 0) * (kronK8 r i j * kronK8 s j i)))
        = (if i = 7 then (1 : ℂ) else 0) * (kronK8 r i 7 * kronK8 s 7 i) :=
      fun i => by rw [← Finset.mul_sum, sum_indicator_collapse fun j => kronK8 r i j * kronK8 s j i]
    rw [Finset.sum_congr rfl fun i _ => hin i,
      sum_indicator_collapse fun i => kronK8 r i 7 * kronK8 s 7 i]
  rw [hLHS,
    show (∑ i, ∑ j, kronK8 r i j * cczDiag j * cczDiag i * kronK8 s j i)
        = ∑ i, ∑ j, (kronK8 r i j * kronK8 s j i
          - 2 * ((if i = 7 then (1 : ℂ) else 0) * (kronK8 r i j * kronK8 s j i))
          - 2 * ((if j = 7 then (1 : ℂ) else 0) * (kronK8 r i j * kronK8 s j i))
          + 4 * ((if i = 7 then (1 : ℂ) else 0)
              * ((if j = 7 then (1 : ℂ) else 0) * (kronK8 r i j * kronK8 s j i))))
      from Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [cczDiag_eq i, cczDiag_eq j]; ring,
    sum_sum_linear_comb (fun i j => kronK8 r i j * kronK8 s j i)
      (fun i j => (if i = 7 then (1 : ℂ) else 0) * (kronK8 r i j * kronK8 s j i))
      (fun i j => (if j = 7 then (1 : ℂ) else 0) * (kronK8 r i j * kronK8 s j i))
      (fun i j => (if i = 7 then (1 : ℂ) else 0)
        * ((if j = 7 then (1 : ℂ) else 0) * (kronK8 r i j * kronK8 s j i))),
    e8, ez, ez', eg]

/-- **Theorem 3.8 (the form `hCCZ` needs): `channelRep CCZ` has half-integer entries.** Every entry of
`Ĉ_CCZ` is `(integer)/2`. -/
theorem channelRep_CCZ_isHalfInt (r s : Fin 4 × Fin 4 × Fin 4) :
    ∃ a : ℤ, channelRep CCZ_mat r s = (a : ℂ) / 2 := by
  obtain ⟨m, hm⟩ := isGaussianInt_re_int (kronK8_mul_77_isGaussianInt r s)
  obtain ⟨gr, hgr⟩ := kronK8_77_int r
  obtain ⟨gs, hgs⟩ := kronK8_77_int s
  refine ⟨2 * (if r = s then 1 else 0) - m + gr * gs, ?_⟩
  have htr : channelRep CCZ_mat r s = (8⁻¹ : ℂ) *
      (kronK8 r * (CCZ_mat * kronK8 s * CCZ_mat)).trace := by
    rw [channelRep_eq_trace, CCZ_mat_conjTranspose]
  rw [htr, trace_kronK8_CCZ_conj, kronK8_mul_77_conj_swap r s]
  -- z + conj z = 2·Re z = 2m, so conj z = 2m − z
  have hconj : (kronK8 r * kronK8 s) 7 7 + (starRingEnd ℂ) ((kronK8 r * kronK8 s) 7 7)
      = 2 * (m : ℂ) := by
    rw [Complex.add_conj, hm]; push_cast; ring
  have hcz : (starRingEnd ℂ) ((kronK8 r * kronK8 s) 7 7)
      = 2 * (m : ℂ) - (kronK8 r * kronK8 s) 7 7 :=
    eq_sub_of_add_eq (by rw [add_comm]; exact hconj)
  rw [hgr, hgs, hcz]
  push_cast
  ring

end SKEFTHawking.FKLW.MukhopadhyayCCZ
