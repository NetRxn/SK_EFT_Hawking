/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 39) — the SU(2) Euler decomposition into Λ-phases and H

Every `U ∈ SU(2)` factors, **up to a global phase**, as `Λ(φ₁)·H·Λ(φ₂)·H·Λ(φ₃)` — the ZXZ Euler
decomposition expressed in the gates the KMM pipeline approximates exactly: `Λ(φ) = diag(1, e^{iφ})`
(the z-rotation target of `kmm_z_rotation_word`) and the Hadamard (exactly realizable). The global
phase is unavoidable: only `ωʲ` global phases are exactly Clifford+T-realizable, and approximation up
to global phase is the standard (projective) notion in the synthesis literature (KMM, RS, SK).

Mechanism: `H·Λ(φ)·H = e^{iφ/2}·Rx(φ)` and `Λ(φ) = e^{iφ/2}·Rz(φ)`, so the product sweeps
`Rz·Rx·Rz` — all of `SU(2)` — with the accumulated half-angle phases absorbed into `c`. The angles:
`φ₂ = 2·arccos |a|` (so `cos(φ₂/2) = |a|`, `sin(φ₂/2) = |b|`), `φ₁, φ₃` from `arg a ∓ arg b ∓ π/2`,
with the degenerate columns (`b = 0`, `a = 0`) split off.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.ComplexEmbeddingMatrix
import SKEFTHawking.FKLW.RossSelinger.CompileApprox
import Mathlib.LinearAlgebra.UnitaryGroup

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

open Complex

/-- The z-rotation phase gate `Λ(φ) = diag(1, e^{iφ})` — the target the KMM word approximates. -/
noncomputable def lamC (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp ((φ : ℂ) * Complex.I)]

/-- The complex Hadamard — definitionally the embedding of the exact gate
(`toComplexMat_gateMatrix_H`). -/
noncomputable def hC : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.sqrt 2)⁻¹ : ℂ), (Real.sqrt 2)⁻¹; (Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹]

/-! ### Half-angle exponential identities -/

theorem one_add_exp (θ : ℝ) :
    1 + Complex.exp ((θ : ℂ) * Complex.I)
      = 2 * Real.cos (θ / 2) * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
  have hcos : (2 : ℂ) * (Real.cos (θ / 2) : ℂ)
      = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
        + Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_cos, Complex.cos]
    ring
  rw [hcos, add_mul, ← Complex.exp_add, ← Complex.exp_add,
    show ((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I
      from by push_cast; ring,
    show -((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I = 0 from by ring,
    Complex.exp_zero]
  ring

theorem one_sub_exp (θ : ℝ) :
    1 - Complex.exp ((θ : ℂ) * Complex.I)
      = -2 * Complex.I * Real.sin (θ / 2) * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
  have hsin : (-2 : ℂ) * Complex.I * (Real.sin (θ / 2) : ℂ)
      = Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_sin, Complex.sin,
      show (-2 : ℂ) * Complex.I * ((Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) * Complex.I / 2)
        = (Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) * (-(Complex.I * Complex.I)) from by
        ring,
      Complex.I_mul_I]
    ring
  rw [show (-2 : ℂ) * Complex.I * (Real.sin (θ / 2) : ℂ)
        * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
      = ((-2 : ℂ) * Complex.I * (Real.sin (θ / 2) : ℂ))
        * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) from by ring,
    hsin, sub_mul, ← Complex.exp_add, ← Complex.exp_add,
    show -((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I = 0 from by ring,
    show ((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I
      from by push_cast; ring,
    Complex.exp_zero]

/-! ### The Euler 5-product -/

/-- The Euler word target: `Λ(φ₁)·H·Λ(φ₂)·H·Λ(φ₃)` (right-associated, matching word
interpretations). -/
noncomputable def eulerProd (φ₁ φ₂ φ₃ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  lamC φ₁ * (hC * (lamC φ₂ * (hC * lamC φ₃)))

/-- The closed form of the Euler product: with `eⱼ = e^{iφⱼ}`,
`½·[[1+e₂, (1−e₂)e₃], [e₁(1−e₂), e₁e₃(1+e₂)]]`. -/
theorem eulerProd_eq (φ₁ φ₂ φ₃ : ℝ) :
    eulerProd φ₁ φ₂ φ₃ =
      (1 / 2 : ℂ) • !![1 + Complex.exp ((φ₂ : ℂ) * Complex.I),
          (1 - Complex.exp ((φ₂ : ℂ) * Complex.I)) * Complex.exp ((φ₃ : ℂ) * Complex.I);
        Complex.exp ((φ₁ : ℂ) * Complex.I) * (1 - Complex.exp ((φ₂ : ℂ) * Complex.I)),
          Complex.exp ((φ₁ : ℂ) * Complex.I) * Complex.exp ((φ₃ : ℂ) * Complex.I)
            * (1 + Complex.exp ((φ₂ : ℂ) * Complex.I))] := by
  have hs : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerProd, lamC, hC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    first
      | linear_combination (1 + Complex.exp ((φ₂ : ℂ) * Complex.I)) * hs
      | linear_combination
          (1 - Complex.exp ((φ₂ : ℂ) * Complex.I)) * Complex.exp ((φ₃ : ℂ) * Complex.I) * hs
      | linear_combination
          Complex.exp ((φ₁ : ℂ) * Complex.I) * (1 - Complex.exp ((φ₂ : ℂ) * Complex.I)) * hs
      | linear_combination Complex.exp ((φ₁ : ℂ) * Complex.I)
          * Complex.exp ((φ₃ : ℂ) * Complex.I) * (1 + Complex.exp ((φ₂ : ℂ) * Complex.I)) * hs

/-! ### The SU(2) decomposition -/

/-- Column normalization of `SU(2)`: `|U₀₀|² + |U₁₀|² = 1`. -/
theorem su2_col_norm (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Complex.normSq ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
      + Complex.normSq ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = 1 := by
  obtain ⟨hunit, _⟩ := Matrix.mem_specialUnitaryGroup_iff.mp U.2
  have hstar : star (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hunit
  have h00 := congrFun (congrFun hstar 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, RCLike.star_def,
    Matrix.one_apply_eq] at h00
  rw [mul_comm ((starRingEnd ℂ) _) _, mul_comm ((starRingEnd ℂ) _) _, Complex.mul_conj,
    Complex.mul_conj] at h00
  exact_mod_cast h00

/-- The conjugate in polar form: `conj z = ‖z‖·e^{−i·arg z}`. -/
theorem conj_polar (z : ℂ) :
    (starRingEnd ℂ) z = (‖z‖ : ℂ) * Complex.exp (-(Complex.arg z : ℂ) * Complex.I) := by
  nth_rewrite 1 [show z = (‖z‖ : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) from
    (Complex.norm_mul_exp_arg_mul_I z).symm]
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  ring_nf

/-- **The SU(2) Euler decomposition (up to global phase)**: every `U ∈ SU(2)` is a unit scalar
times `Λ(φ₁)·H·Λ(φ₂)·H·Λ(φ₃)` — the form the KMM pipeline approximates gate-by-gate (the global
phase is unavoidable: only `ωʲ` global phases are exactly Clifford+T-realizable; approximation up
to global phase is the standard projective notion). -/
theorem su2_euler_decomposition (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ∃ (φ₁ φ₂ φ₃ : ℝ) (c : ℂ), ‖c‖ = 1 ∧
      (U : Matrix (Fin 2) (Fin 2) ℂ) = c • eulerProd φ₁ φ₂ φ₃ := by
  obtain ⟨h01, h11⟩ := su2_entry_structure U
  have hnorm := su2_col_norm U
  set a := (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 with ha
  set b := (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 with hb
  have hf2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  have hext : ∀ (φ₁ φ₂ φ₃ : ℝ) (c : ℂ),
      c * ((1 + Complex.exp ((φ₂ : ℂ) * Complex.I)) / 2) = a →
      c * ((1 - Complex.exp ((φ₂ : ℂ) * Complex.I)) * Complex.exp ((φ₃ : ℂ) * Complex.I) / 2)
        = -(starRingEnd ℂ) b →
      c * (Complex.exp ((φ₁ : ℂ) * Complex.I)
        * (1 - Complex.exp ((φ₂ : ℂ) * Complex.I)) / 2) = b →
      c * (Complex.exp ((φ₁ : ℂ) * Complex.I) * Complex.exp ((φ₃ : ℂ) * Complex.I)
        * (1 + Complex.exp ((φ₂ : ℂ) * Complex.I)) / 2) = (starRingEnd ℂ) a →
      (U : Matrix (Fin 2) (Fin 2) ℂ) = c • eulerProd φ₁ φ₂ φ₃ := by
    intro φ₁ φ₂ φ₃ c e00 e01 e10 e11
    rw [eulerProd_eq]
    refine Matrix.ext fun i j => ?_
    rcases hf2 i with hi | hi <;> rcases hf2 j with hj | hj <;> subst hi <;> subst hj
    · show a = c * ((1 / 2 : ℂ) * (1 + Complex.exp ((φ₂ : ℂ) * Complex.I)))
      linear_combination -e00
    · show (U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = c * ((1 / 2 : ℂ)
        * ((1 - Complex.exp ((φ₂ : ℂ) * Complex.I)) * Complex.exp ((φ₃ : ℂ) * Complex.I)))
      rw [h01]
      linear_combination -e01
    · show b = c * ((1 / 2 : ℂ) * (Complex.exp ((φ₁ : ℂ) * Complex.I)
        * (1 - Complex.exp ((φ₂ : ℂ) * Complex.I))))
      linear_combination -e10
    · show (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = c * ((1 / 2 : ℂ)
        * (Complex.exp ((φ₁ : ℂ) * Complex.I) * Complex.exp ((φ₃ : ℂ) * Complex.I)
          * (1 + Complex.exp ((φ₂ : ℂ) * Complex.I))))
      rw [h11]
      linear_combination -e11
  have hzero : ((0 : ℝ) : ℂ) * Complex.I = 0 := by norm_num
  by_cases hb0 : b = 0
  · -- diagonal: U = diag(a, ā), ‖a‖ = 1
    have hna : ‖a‖ = 1 := by
      have h1 : Complex.normSq a = 1 := by
        rw [hb0] at hnorm
        simpa using hnorm
      have h2 := Complex.normSq_eq_norm_sq a
      nlinarith [norm_nonneg a]
    have hpolar : a = Complex.exp ((Complex.arg a : ℂ) * Complex.I) := by
      nth_rewrite 1 [show a = (‖a‖ : ℂ) * Complex.exp ((Complex.arg a : ℂ) * Complex.I) from
        (Complex.norm_mul_exp_arg_mul_I a).symm]
      rw [hna]
      norm_num
    have hconj : (starRingEnd ℂ) a = Complex.exp (-(Complex.arg a : ℂ) * Complex.I) := by
      rw [conj_polar, hna]
      norm_num
    refine ⟨-2 * Complex.arg a, 0, 0, a, hna, hext _ _ _ _ ?_ ?_ ?_ ?_⟩
    · rw [hzero, Complex.exp_zero]
      ring
    · rw [hb0, hzero, Complex.exp_zero]
      simp
    · rw [hb0, hzero, Complex.exp_zero]
      ring
    · rw [hzero, Complex.exp_zero, hconj,
        show ((-2 * Complex.arg a : ℝ) : ℂ) * Complex.I
          = -(Complex.arg a : ℂ) * Complex.I + -(Complex.arg a : ℂ) * Complex.I from by
            push_cast; ring,
        Complex.exp_add]
      nth_rewrite 1 [hpolar]
      have hE : Complex.exp ((Complex.arg a : ℂ) * Complex.I)
          * Complex.exp (-(Complex.arg a : ℂ) * Complex.I) = 1 := by
        rw [← Complex.exp_add, show (Complex.arg a : ℂ) * Complex.I
          + -(Complex.arg a : ℂ) * Complex.I = 0 from by ring, Complex.exp_zero]
      linear_combination Complex.exp (-(Complex.arg a : ℂ) * Complex.I) * hE
  by_cases ha0 : a = 0
  · -- antidiagonal: U = [[0, −b̄],[b, 0]], ‖b‖ = 1
    have hnb : ‖b‖ = 1 := by
      have h1 : Complex.normSq b = 1 := by
        rw [ha0] at hnorm
        simpa using hnorm
      have h2 := Complex.normSq_eq_norm_sq b
      nlinarith [norm_nonneg b]
    have hpolar : b = Complex.exp ((Complex.arg b : ℂ) * Complex.I) := by
      nth_rewrite 1 [show b = (‖b‖ : ℂ) * Complex.exp ((Complex.arg b : ℂ) * Complex.I) from
        (Complex.norm_mul_exp_arg_mul_I b).symm]
      rw [hnb]
      norm_num
    have hconj : (starRingEnd ℂ) b = Complex.exp (-(Complex.arg b : ℂ) * Complex.I) := by
      rw [conj_polar, hnb]
      norm_num
    have hepi : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := by
      rw [show (Real.pi : ℂ) * Complex.I = Real.pi * Complex.I from rfl]
      exact Complex.exp_pi_mul_I
    refine ⟨Complex.arg b, Real.pi, Real.pi - Complex.arg b, 1, by norm_num,
      hext _ _ _ _ ?_ ?_ ?_ ?_⟩
    · rw [hepi, ha0]
      ring
    · rw [hepi, hconj,
        show ((Real.pi - Complex.arg b : ℝ) : ℂ) * Complex.I
          = (Real.pi : ℂ) * Complex.I + -(Complex.arg b : ℂ) * Complex.I from by push_cast; ring,
        Complex.exp_add, hepi]
      ring
    · rw [hepi]
      nth_rewrite 2 [hpolar]
      ring
    · rw [hepi, ha0, map_zero]
      ring
  · -- main case: a ≠ 0 ∧ b ≠ 0
    have hna1 : ‖a‖ ≤ 1 := by
      have h2 := Complex.normSq_eq_norm_sq a
      nlinarith [norm_nonneg a, norm_nonneg b, Complex.normSq_nonneg b,
        Complex.normSq_eq_norm_sq b]
    have hcos : Real.cos (Real.arccos ‖a‖) = ‖a‖ :=
      Real.cos_arccos (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (norm_nonneg a)) hna1
    have hsin : Real.sin (Real.arccos ‖a‖) = ‖b‖ := by
      rw [Real.sin_arccos,
        show (1 : ℝ) - ‖a‖ ^ 2 = ‖b‖ ^ 2 from by
          nlinarith [Complex.normSq_eq_norm_sq a, Complex.normSq_eq_norm_sq b]]
      exact Real.sqrt_sq (norm_nonneg b)
    set A := Complex.arg a with hA
    set B := Complex.arg b with hB
    set t := Real.arccos ‖a‖ with ht
    have hIpos : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      norm_num
    have hIneg : Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) = -Complex.I := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
      norm_num
    have hkey00 : Complex.exp (((A - t : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((t : ℝ) : ℂ) * Complex.I) = Complex.exp ((A : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hkey10 : Complex.exp (((A - t : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((B - A + Real.pi / 2 : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((t : ℝ) : ℂ) * Complex.I) * (-Complex.I)
        = Complex.exp ((B : ℂ) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add,
        show ((A - t : ℝ) : ℂ) * Complex.I + ((B - A + Real.pi / 2 : ℝ) : ℂ) * Complex.I
            + ((t : ℝ) : ℂ) * Complex.I
          = ((B : ℝ) : ℂ) * Complex.I + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I from by
            push_cast; ring,
        Complex.exp_add, hIpos]
      rw [show Complex.exp (((B : ℝ) : ℂ) * Complex.I) * Complex.I * -Complex.I
          = Complex.exp (((B : ℝ) : ℂ) * Complex.I) * (-(Complex.I * Complex.I)) from by ring,
        Complex.I_mul_I]
      ring
    have hkey01 : Complex.exp (((A - t : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((-A - B - Real.pi / 2 : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((t : ℝ) : ℂ) * Complex.I) * (-Complex.I)
        = -Complex.exp ((-B : ℂ) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add,
        show ((A - t : ℝ) : ℂ) * Complex.I + ((-A - B - Real.pi / 2 : ℝ) : ℂ) * Complex.I
            + ((t : ℝ) : ℂ) * Complex.I
          = ((-B : ℝ) : ℂ) * Complex.I + ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I from by
            push_cast; ring,
        Complex.exp_add, hIneg]
      rw [show Complex.exp (((-B : ℝ) : ℂ) * Complex.I) * -Complex.I * -Complex.I
          = Complex.exp (((-B : ℝ) : ℂ) * Complex.I) * (Complex.I * Complex.I) from by ring,
        Complex.I_mul_I]
      push_cast
      ring
    have hkey11 : Complex.exp (((A - t : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((B - A + Real.pi / 2 : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((-A - B - Real.pi / 2 : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((t : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((-A : ℂ) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hpa : a = (‖a‖ : ℂ) * Complex.exp ((A : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I a).symm
    have hpb : b = (‖b‖ : ℂ) * Complex.exp ((B : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I b).symm
    have hca : (starRingEnd ℂ) a = (‖a‖ : ℂ) * Complex.exp ((-A : ℂ) * Complex.I) := by
      rw [conj_polar]
    have hcb : (starRingEnd ℂ) b = (‖b‖ : ℂ) * Complex.exp ((-B : ℂ) * Complex.I) := by
      rw [conj_polar]
    refine ⟨B - A + Real.pi / 2, 2 * t, -A - B - Real.pi / 2,
      Complex.exp (((A - t : ℝ) : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I _,
      hext _ _ _ _ ?_ ?_ ?_ ?_⟩
    · rw [one_add_exp (2 * t), show 2 * t / 2 = t from by ring, hcos]
      conv_rhs => rw [hpa]
      linear_combination (‖a‖ : ℂ) * hkey00
    · rw [one_sub_exp (2 * t), show 2 * t / 2 = t from by ring, hsin, hcb]
      linear_combination (‖b‖ : ℂ) * hkey01
    · rw [one_sub_exp (2 * t), show 2 * t / 2 = t from by ring, hsin]
      conv_rhs => rw [hpb]
      linear_combination (‖b‖ : ℂ) * hkey10
    · rw [one_add_exp (2 * t), show 2 * t / 2 = t from by ring, hcos, hca]
      linear_combination (‖a‖ : ℂ) * hkey11

end SKEFTHawking.RossSelinger
