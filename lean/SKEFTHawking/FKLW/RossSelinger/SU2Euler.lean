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

end SKEFTHawking.RossSelinger
