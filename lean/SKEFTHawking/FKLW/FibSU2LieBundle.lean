/-
Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer F.13 (FibSU2LieBundle, session 48):
bridge SU2LieAlgebra's general Ad-action API to the σ_Fib_*_SU-specific
3-bundle used by the H_Fib spanning argument.

## What this module ships (~80 LoC)

  - **`tracelessSkewHermitian_conj_σ_Fib_1_SU_mat`** and
    **`..._σ_Fib_2_SU_mat`** — the σ_Fib_*-instances of the general
    `tracelessSkewHermitian_conj_specialUnitary` (Layer F.12).

  - **`σ_Fib_lie_bundle (X : Matrix _ _ ℂ)`** — the 3-element bundle
    `(X, σ_Fib_1_SU_mat·X·σ_Fib_1_SU_mat†, σ_Fib_2_SU_mat·X·σ_Fib_2_SU_mat†)`
    of Ad-rotated Lie directions. For X ∈ 𝔰𝔲(2) all three components
    are also in 𝔰𝔲(2).

  - **`σ_Fib_lie_bundle_mem_tracelessSkewHermitian`** — combined
    membership: triple Ad-conjugates stay in 𝔰𝔲(2).

  - **`σ_Fib_lie_bundle_pauliDet`** — shortcut def for the load-bearing
    `pauliDet` of the 3-bundle. Used in Layer F.14+ to apply F.8's
    Cramer-rule lin-indep criterion.

## Pipeline Invariant compliance

  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new project-local axioms): RESPECTED.
  - ADR-003 (zero sorry): RESPECTED.
-/

import Mathlib
import SKEFTHawking.FKLW.SU2LieAlgebra
import SKEFTHawking.FKLW.FibSU2Rep

set_option autoImplicit false

namespace SKEFTHawking.FKLW.FibSU2LieBundle

open SKEFTHawking SKEFTHawking.FKLW SKEFTHawking.FKLW.SU2LieAlgebra

/-- **σ_Fib_1_SU_mat Ad-conjugation preserves 𝔰𝔲(2)** (Layer F.13). -/
theorem tracelessSkewHermitian_conj_σ_Fib_1_SU_mat
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose ∈
      tracelessSkewHermitian (Fin 2) :=
  tracelessSkewHermitian_conj_specialUnitary σ_Fib_1_SU hX

/-- **σ_Fib_2_SU_mat Ad-conjugation preserves 𝔰𝔲(2)** (Layer F.13). -/
theorem tracelessSkewHermitian_conj_σ_Fib_2_SU_mat
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose ∈
      tracelessSkewHermitian (Fin 2) :=
  tracelessSkewHermitian_conj_specialUnitary σ_Fib_2_SU hX

/-- **The σ_Fib 3-bundle of Lie directions** for X ∈ 𝔰𝔲(2):
`(X, Ad(σ_Fib_1) X, Ad(σ_Fib_2) X)`. Each component lies in 𝔰𝔲(2)
when X does (see `σ_Fib_lie_bundle_mem_tracelessSkewHermitian`).

This is the load-bearing tuple for the H_Fib spanning argument:
its `pauliDet` measures ℝ-linear independence (via Layer F.8), and
non-zero `pauliDet` translates to "the three Lie-direction conjugates
span 𝔰𝔲(2)". -/
noncomputable def σ_Fib_lie_bundle (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ ×
      Matrix (Fin 2) (Fin 2) ℂ :=
  (X,
   σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose,
   σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose)

/-- **All three components of `σ_Fib_lie_bundle X` are in 𝔰𝔲(2)**
when X is. -/
theorem σ_Fib_lie_bundle_mem_tracelessSkewHermitian
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    (σ_Fib_lie_bundle X).1 ∈ tracelessSkewHermitian (Fin 2) ∧
    (σ_Fib_lie_bundle X).2.1 ∈ tracelessSkewHermitian (Fin 2) ∧
    (σ_Fib_lie_bundle X).2.2 ∈ tracelessSkewHermitian (Fin 2) :=
  ⟨hX,
   tracelessSkewHermitian_conj_σ_Fib_1_SU_mat hX,
   tracelessSkewHermitian_conj_σ_Fib_2_SU_mat hX⟩

/-- **`pauliDet` of the σ_Fib Lie bundle** for X ∈ 𝔰𝔲(2). Shortcut def
for the determinant criterion: `σ_Fib_lie_bundle_pauliDet X ≠ 0` ↔
the 3-bundle is ℝ-linearly independent in 𝔰𝔲(2) (via Layer F.8). -/
noncomputable def σ_Fib_lie_bundle_pauliDet
    (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  pauliDet (σ_Fib_lie_bundle X).1
           (σ_Fib_lie_bundle X).2.1
           (σ_Fib_lie_bundle X).2.2

/-- **Unfold form** for `σ_Fib_lie_bundle_pauliDet`. -/
theorem σ_Fib_lie_bundle_pauliDet_eq (X : Matrix (Fin 2) (Fin 2) ℂ) :
    σ_Fib_lie_bundle_pauliDet X =
      pauliDet X
        (σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose)
        (σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose) := rfl

/-! ## §2. Spanning reduction (Layer F.14, session 48)

Closes the structural reduction: **σ_Fib 3-bundle ℝ-spans 𝔰𝔲(2)
at X if and only if `σ_Fib_lie_bundle_pauliDet X ≠ 0`** (one direction
of the iff — the load-bearing one — shipped here; the other direction
is downstream when needed).

Substantive remaining content: producing an explicit X ∈ 𝔰𝔲(2) with
`σ_Fib_lie_bundle_pauliDet X ≠ 0`. Plan: for X = `paulI_x`, compute
explicitly using σ_Fib_1's diagonal action + σ_Fib_2's F-conjugate
structure (Layer F.15+, multi-session trig computation).
-/

/-- **HEADLINE — σ_Fib 3-bundle lin-indep from non-zero pauliDet**.
If `σ_Fib_lie_bundle_pauliDet X ≠ 0`, then the 3-bundle
`(X, σ_Fib_1·X·σ_Fib_1†, σ_Fib_2·X·σ_Fib_2†)` is ℝ-linearly
independent in `Matrix (Fin 2) (Fin 2) ℂ`. Direct application of
Layer F.8 `tracelessSkewHermitian_lin_indep_of_pauliDet_ne_zero`. -/
theorem σ_Fib_lie_bundle_lin_indep
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (h_det : σ_Fib_lie_bundle_pauliDet X ≠ 0)
    {a b c : ℝ}
    (h_lin : (a : ℂ) • X +
             (b : ℂ) • (σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose) +
             (c : ℂ) • (σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 :=
  tracelessSkewHermitian_lin_indep_of_pauliDet_ne_zero h_det h_lin

/-! ## §3. σ_Fib_1 Ad-action on paulI_x (Layer F.15, session 48)

Substantive trigonometric content begins here. σ_Fib_1_SU_mat is
diagonal (= `ω_Fib_C • σ_Fib_1` = `diag(ω·R1, ω·R_τ)`), so its
Ad-conjugation of paulI_x has a clean closed form:
`σ_Fib_1·paulI_x·σ_Fib_1† = !![0, (ω·R1)·conj(ω·R_τ)·I; (ω·R_τ)·conj(ω·R1)·I, 0]`.

Substantive remaining content for the full spanning argument:
  - **F.16**: extract Pauli coords of this matrix using
    `(ω·R1)·conj(ω·R_τ) = R1·conj(R_τ) = exp(-7πi/5)` (unit-modulus
    times unit-modulus conjugate cancellation).
  - **F.17**: compute σ_Fib_2·paulI_x·σ_Fib_2† via F·σ_Fib_1·F.
  - **F.18**: show pauliDet ≠ 0 and apply F.14.
-/

open Matrix in
/-- **HEADLINE — diagonal 2×2 Ad-conjugation of paulI_x**.
For any complex α, β, conjugation `diag(α, β) · paulI_x · diag(α, β)†`
gives the off-diagonal matrix `!![0, α·conj β·I; β·conj α·I, 0]`. -/
theorem diag_conj_paulI_x (α β : ℂ) :
    (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℂ) * paulI_x *
      (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose =
    !![0, α * star β * Complex.I;
       β * star α * Complex.I, 0] := by
  unfold paulI_x SKEFTHawking.σ_x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
          Matrix.smul_apply, smul_eq_mul] <;>
    ring

/-- σ_Fib_1_SU_mat in explicit 2×2 form: `diag(ω_Fib_C·R1_C, ω_Fib_C·R_τ_C)`. -/
theorem σ_Fib_1_SU_mat_diagonal_form :
    σ_Fib_1_SU_mat =
    !![ω_Fib_C * R1_C, 0; 0, ω_Fib_C * Rtau_C] := by
  unfold σ_Fib_1_SU_mat σ_Fib_1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul]

/-- **HEADLINE F.15 — σ_Fib_1 Ad-action on paulI_x explicit matrix form**.
Composes `σ_Fib_1_SU_mat_diagonal_form` with `diag_conj_paulI_x`. -/
theorem σ_Fib_1_SU_mat_conj_paulI_x_eq :
    σ_Fib_1_SU_mat * paulI_x * σ_Fib_1_SU_mat.conjTranspose =
    !![0, (ω_Fib_C * R1_C) * star (ω_Fib_C * Rtau_C) * Complex.I;
       (ω_Fib_C * Rtau_C) * star (ω_Fib_C * R1_C) * Complex.I, 0] := by
  rw [σ_Fib_1_SU_mat_diagonal_form, diag_conj_paulI_x]

end SKEFTHawking.FKLW.FibSU2LieBundle
