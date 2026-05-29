/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4f.2a — single-qubit Clifford generator conjugation values

The single-qubit conjugation action of the Clifford generators on the Paulis, in the form needed for the
tensor tableau lifts (`gen · σ_a · gen⁻¹ = sign • σ_{φ(a)}`). This module ships the **Hadamard** value:

  `litHadamard · σ_a · litHadamard = hSign a · σ_{hLabel a}`

(`litHadamard` is Hermitian and an involution, so `litHadamard⁻¹ = litHadamard`). The label map `hLabel`
(`X ↔ Z`, `I, Y` fixed) matches `CliffordCCZSU8LabelTransitivity.hLabel`; the sign `hSign` is `−1` only on
`Y` (`H σ_y H = −σ_y`). The companion S-gate and CNOT conjugation values follow in subsequent increments,
and tensor up (via `kronSU8_mul`) to the 3-qubit generator tableau lifts driving the W-transport.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4f.2a (single-qubit generator conjugation — Hadamard). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8LiteralSeed
import SKEFTHawking.FKLW.CliffordCCZSU8LiteralGeneratingSet
import SKEFTHawking.FKLW.CliffordCCZSU8LabelTransitivity
import SKEFTHawking.FKLW.CliffordCCZSU8SeedNotFiniteOrder

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4 SKEFTHawking.FKLW.CliffordCCZ
  SKEFTHawking.FKLW.GenericSU2

/-- The Hadamard-conjugation sign on the Paulis: `+1` on `I, X, Z`; `−1` on `Y` (`H σ_y H = −σ_y`). -/
noncomputable def hSign : Fin 4 → ℂ := ![1, 1, -1, 1]

/-- **Single-qubit Hadamard conjugation value**: `H · σ_a · H = (±1) · σ_{hLabel a}` with `hLabel`
swapping `X ↔ Z` (and `H σ_y H = −σ_y`). Proof: factor the two `1/√2` scalars (`(1/√2)² = 1/2`) out of
`litHadamard = (1/√2)·!![1,1;1,-1]`, then the residual `(1/2)·(M σ_a M)` is a rational-entry 2×2
computation closed entrywise by `ring`. -/
theorem litHadamard_conj_pauli4 (a : Fin 4) :
    litHadamard * pauli4 a * litHadamard = hSign a • pauli4 (hLabel a) := by
  have hhalf : (1 / Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2 : ℂ) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  unfold litHadamard
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hhalf]
  fin_cases a <;>
    · simp only [hSign, hLabel]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.smul_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

/-! ## 2. The S-gate conjugation value -/

/-- `exp(iπ/2) = i`. -/
theorem expIpiHalf : Complex.exp (Complex.I * (Real.pi : ℂ) / 2) = Complex.I := by
  rw [show Complex.I * (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `exp(-iπ/2) = -i`. -/
theorem expNIpiHalf : Complex.exp (-(Complex.I * (Real.pi : ℂ) / 2)) = -Complex.I := by
  rw [Complex.exp_neg, expIpiHalf]; simp [Complex.inv_I]

/-- The S-conjugation sign on the Paulis: `+1` on `I, X, Z`; `−1` on `Y` (`S σ_y S† = −σ_x`). -/
noncomputable def sSign : Fin 4 → ℂ := ![1, 1, -1, 1]

/-- **Single-qubit S-gate conjugation value**: `S · σ_a · S† = (±1) · σ_{sLabel a}` with `sLabel`
swapping `X ↔ Y` (and `S σ_y S† = −σ_x`). The inverse of the unitary `S_SU_mat = diag(e^{−iπ/4}, e^{iπ/4})`
is its conjugate transpose `star S_SU_mat`. Proof: set the two phases as atoms `α = e^{−iπ/4}`,
`β = e^{iπ/4}` with `α² = −i`, `β² = i`, `αβ = 1`, and `conj α = β`; the `star` is `!![β,0;0,α]`; then the
entrywise 2×2 computation closes by `ring_nf` + the atom identities. -/
theorem S_SU_mat_conj_pauli4 (a : Fin 4) :
    S_SU_mat * pauli4 a * star S_SU_mat = sSign a • pauli4 (sLabel a) := by
  rw [show S_SU_mat = !![Complex.exp (-(Complex.I * (Real.pi : ℂ) / 4)), 0;
        0, Complex.exp (Complex.I * (Real.pi : ℂ) / 4)] from rfl]
  set α := Complex.exp (-(Complex.I * (Real.pi : ℂ) / 4)) with hα
  set β := Complex.exp (Complex.I * (Real.pi : ℂ) / 4) with hβ
  have hconjm : (starRingEnd ℂ) α = β := by
    rw [hα, ← Complex.exp_conj]; congr 1
    simp only [map_neg, map_div₀, map_mul, Complex.conj_I, map_ofNat, Complex.conj_ofReal]; ring
  have hconjp : (starRingEnd ℂ) β = α := by
    rw [hβ, ← Complex.exp_conj]; congr 1
    simp only [map_div₀, map_mul, Complex.conj_I, map_ofNat, Complex.conj_ofReal]; ring
  have hαα : α ^ 2 = -Complex.I := by
    rw [sq, hα, ← Complex.exp_add,
      show -(Complex.I * (Real.pi : ℂ) / 4) + -(Complex.I * (Real.pi : ℂ) / 4)
        = -(Complex.I * (Real.pi : ℂ) / 2) by ring, expNIpiHalf]
  have hββ : β ^ 2 = Complex.I := by
    rw [sq, hβ, ← Complex.exp_add,
      show Complex.I * (Real.pi : ℂ) / 4 + Complex.I * (Real.pi : ℂ) / 4
        = Complex.I * (Real.pi : ℂ) / 2 by ring, expIpiHalf]
  have hαβ : α * β = 1 := by rw [hα, hβ, ← Complex.exp_add]; simp
  have hβα : β * α = 1 := by rw [hα, hβ, ← Complex.exp_add]; simp
  have hstar : star (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℂ) = !![β, 0; 0, α] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.star_apply, hconjm, hconjp]
  rw [hstar]
  fin_cases a <;>
    · simp only [sSign, sLabel]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.mul_apply,
          Fin.sum_univ_two, Matrix.smul_apply] <;>
        (ring_nf; simp [hαα, hββ, hαβ, hβα])

/-! ## 3. Single-qubit conjugation in the `SU(2)`-subtype inverse form

The factor-conjugation lemmas `qubit{1,2,3}Embed_conj` rotate the qubit-`i` factor by `C.val · A ·
C.val⁻¹` (matrix inverse). This section re-expresses the H/S conjugation values in that `(·)⁻¹` form so the
3-qubit generator lifts compose directly. For unitary `C ∈ SU(2)`, `C.val⁻¹` is `star C.val`. -/

/-- `litHadamard` is an involution: `litHadamard · litHadamard = 1`. -/
theorem litHadamard_sq : litHadamard * litHadamard = 1 := by
  have hhalf : (1 / Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2 : ℂ) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  unfold litHadamard
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hhalf]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> ring

/-- The matrix inverse of the SU(2) Hadamard: `(H_SU.val)⁻¹ = (−i)·litHadamard`. -/
theorem H_SU_val_inv : (SKEFTHawking.FKLW.GenericSU2.H_SU.val)⁻¹ = (-Complex.I) • litHadamard := by
  apply Matrix.inv_eq_right_inv
  rw [H_SU_val_eq_smul_litHadamard, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, litHadamard_sq,
    show Complex.I * (-Complex.I) = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_smul]

/-- **Hadamard conjugation (subtype-inverse form)**: `H_SU.val · σ_a · (H_SU.val)⁻¹ = hSign a · σ_{hLabel a}`. -/
theorem H_SU_conj_pauli4 (a : Fin 4) :
    SKEFTHawking.FKLW.GenericSU2.H_SU.val * pauli4 a * (SKEFTHawking.FKLW.GenericSU2.H_SU.val)⁻¹
      = hSign a • pauli4 (hLabel a) := by
  rw [H_SU_val_inv, H_SU_val_eq_smul_litHadamard, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, litHadamard_conj_pauli4, smul_smul]
  congr 1
  simp [Complex.I_mul_I, mul_neg]

/-- **S-gate conjugation (subtype-inverse form)**: `S_SU.val · σ_a · (S_SU.val)⁻¹ = sSign a · σ_{sLabel a}`. -/
theorem S_SU_conj_pauli4 (a : Fin 4) :
    S_SU.val * pauli4 a * (S_SU.val)⁻¹ = sSign a • pauli4 (sLabel a) := by
  have hinv : (S_SU.val)⁻¹ = star S_SU.val := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp S_SU.2).1)
  rw [hinv]
  show S_SU_mat * pauli4 a * star S_SU_mat = _
  exact S_SU_mat_conj_pauli4 a

end SKEFTHawking.FKLW.CliffordCCZSU8
