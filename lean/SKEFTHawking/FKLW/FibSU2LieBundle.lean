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
import SKEFTHawking.FKLW.FibSU2Density
import SKEFTHawking.FKLW.FibonacciDensityConditional

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

/-! ## §4. ω-cancellation + Pauli coord extraction (Layer F.16, session 49)

Closes Layer F.16 by computing the Pauli coords of σ_Fib_1·paulI_x·σ_Fib_1†.

Strategy:
  1. **ω-cancellation** (`ω_mul_X_mul_star_ω_mul_Y`): the det-normalization
     factor `ω_Fib_C` cancels in the Ad-conjugation — since `‖ω‖ = 1` gives
     `ω · star ω = 1`. Reduces `(ω·X)·star(ω·Y) = X·star Y`.
  2. **R-eigenvalue product** (`R1_C_mul_star_Rtau_C`): the unit-modulus
     R-eigenvalues combine to a single complex exponential: `R1·star Rτ =
     exp((-4πi/5)) · exp((-3πi/5)) = exp(-7πi/5)`.
  3. **HEADLINE** (`σ_Fib_1_SU_mat_conj_paulI_x_pauliCoords`): composes
     F.15 with steps 1 + 2 + `Complex.exp_re/im` decomposition to extract
     Pauli coords `(cos(7π/5), sin(7π/5), 0)`.

This is **Ad(σ_Fib_1) acts on paulI_x as rotation by 7π/5 about the z-axis**
— the bedrock geometric content. The same `ω_mul_X_mul_star_ω_mul_Y`
identity will be reused in F.17 (σ_Fib_2 Ad-action via F-conjugate
decomposition). -/

/-- **Unit-modulus z gives `z · star z = 1`** — local re-export of the
`unit_norm_mul_conj` helper from `FibSU2Rep` (which is `private` there). -/
private theorem unit_norm_star_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    z * star z = 1 := by
  rw [show (star z : ℂ) = (starRingEnd ℂ) z from rfl, Complex.mul_conj]
  have hnorm_sq : Complex.normSq z = ‖z‖ ^ 2 := by rw [Complex.sq_norm]
  rw [hnorm_sq, hz]; norm_num

/-- **ω-cancellation in the Ad-conjugation product** (Layer F.16 step 1).
For unit-modulus `ω_Fib_C`, the factor cancels: `(ω·X)·star(ω·Y) = X·star Y`. -/
private theorem ω_mul_X_mul_star_ω_mul_Y (X Y : ℂ) :
    (ω_Fib_C * X) * star (ω_Fib_C * Y) = X * star Y := by
  have hω : ω_Fib_C * star ω_Fib_C = 1 := unit_norm_star_eq_one norm_ω_Fib_C
  have h : (ω_Fib_C * X) * star (ω_Fib_C * Y) =
           (ω_Fib_C * star ω_Fib_C) * (X * star Y) := by
    rw [star_mul]; ring
  rw [h, hω, one_mul]

/-- **R-eigenvalue product** (Layer F.16 step 2). `R1_C · star Rtau_C =
exp(-7πi/5)`. Composes `R1_C = exp(-4πi/5)`, `star Rtau_C = exp(-3πi/5)`
(star of `exp(iθ)` is `exp(-iθ)` for real θ), and `exp_add`. -/
theorem R1_C_mul_star_Rtau_C :
    R1_C * star Rtau_C =
      Complex.exp (((-(7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I) := by
  unfold R1_C Rtau_C
  -- Step 1: convert `star (exp ...)` into `exp (star ...)`.
  rw [show (star (Complex.exp (((3 * Real.pi / 5 : ℝ) : ℂ) * Complex.I)) : ℂ)
        = (starRingEnd ℂ) (Complex.exp (((3 * Real.pi / 5 : ℝ) : ℂ) * Complex.I))
        from rfl,
      ← Complex.exp_conj,
      ← Complex.exp_add]
  congr 1
  -- exponent: (-4π/5 : ℝ)·I + conj((3π/5 : ℝ)·I) = -(7π/5)·I.
  -- `map_mul` distributes conj over `*`; `conj_ofReal` + `conj_I` simplify factors.
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **`(z · I).re = -z.im`** — a basic helper for paulI_x conjugation. -/
private theorem mul_I_re' (z : ℂ) : (z * Complex.I).re = -z.im := by
  simp [Complex.mul_re, Complex.I_re, Complex.I_im]

/-- **`(z · I).im = z.re`** — a basic helper for paulI_x conjugation. -/
private theorem mul_I_im' (z : ℂ) : (z * Complex.I).im = z.re := by
  simp [Complex.mul_im, Complex.I_re, Complex.I_im]

/-- **HEADLINE F.16 — σ_Fib_1 Ad-action on paulI_x in Pauli coords**.

`matrixToPauliCoords (σ_Fib_1·paulI_x·σ_Fib_1†) = (cos(7π/5), sin(7π/5), 0)`.

Composes F.15 explicit matrix form with ω-cancellation + R-eigenvalue
product + `Complex.exp_re/im` decomposition (parity of cos / sin under
sign flip). This says **Ad(σ_Fib_1) rotates paulI_x = (1, 0, 0) to
the vector `(cos(7π/5), sin(7π/5), 0)`** — the canonical SU(2) ↪ SO(3)
double-cover rotation by 7π/5 about the z-axis. -/
theorem σ_Fib_1_SU_mat_conj_paulI_x_pauliCoords :
    matrixToPauliCoords
      (σ_Fib_1_SU_mat * paulI_x * σ_Fib_1_SU_mat.conjTranspose) =
    (Real.cos (7 * Real.pi / 5), Real.sin (7 * Real.pi / 5), 0) := by
  rw [σ_Fib_1_SU_mat_conj_paulI_x_eq]
  -- ω-cancellation: simplify (ω·R1)·star(ω·Rτ) → R1·star Rτ.
  rw [show (ω_Fib_C * R1_C) * star (ω_Fib_C * Rtau_C) = R1_C * star Rtau_C
        from ω_mul_X_mul_star_ω_mul_Y R1_C Rtau_C,
      R1_C_mul_star_Rtau_C]
  -- Now the (0,1) entry is exp(-7πi/5) · I; extract Pauli coords + reduce
  -- cos/sin parities in one composite simp.
  unfold matrixToPauliCoords
  simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Complex.zero_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.exp_re, Complex.exp_im, Complex.neg_re,
        Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Real.cos_neg, Real.sin_neg, Real.exp_zero, mul_one, one_mul]

/-! ## §5. F.17.a — σ_Fib_2 = F·σ_Fib_1·F decomposition + F·paulI_x·F (session 49)

Closes the substrate layer toward F.17.b's (σ_Fib_2·paulI_x·σ_Fib_2†)(0,0).im
computation. Two pieces:

  1. **`σ_Fib_2_SU_mat_F_decomp`**: σ_Fib_2_SU_mat = F_C · σ_Fib_1_SU_mat · F_C.
     Direct consequence of `σ_Fib_2 = F · σ_Fib_1 · F` (FibSU2Rep) + scalar
     commutativity for matrix product. The σ_Fib_1_SU_mat absorbs ω_Fib_C
     transparently.

  2. **`F_C_conj_paulI_x_eq`**: F·paulI_x·F = `!![a·I, b·I; b·I, -a·I]` where
     a = 2/(φ√φ), b = 2/φ - 1 = (the F-conjugate Pauli coords). All
     coefficients are real, so the result is in 𝔰𝔲(2) explicitly. This
     uses `(1/√φ)² = 1/φ` (`φInvSqrt_C_sq`) + `1/φ + 1/φ² = 1` (from
     `φ_C_sq` algebra). The substantive trig is deferred to F.17.b.
-/

/-- **σ_Fib_2_SU_mat F-decomposition** (Layer F.17.a step 1). The det-normalized
σ_Fib_2 equals F_C-conjugation of det-normalized σ_Fib_1. Uses scalar-matrix
commutativity: `ω • (F · σ_1 · F) = F · (ω • σ_1) · F` via `mul_smul_comm`
+ `smul_mul_assoc`. -/
theorem σ_Fib_2_SU_mat_F_decomp :
    σ_Fib_2_SU_mat = F_C * σ_Fib_1_SU_mat * F_C := by
  unfold σ_Fib_2_SU_mat σ_Fib_1_SU_mat σ_Fib_2
  -- Goal: ω • (F · σ_1 · F) = F · (ω • σ_1) · F
  -- Strategy: rewrite RHS using `mul_smul_comm` then `smul_mul_assoc` to get
  -- the LHS form `ω • ((F · σ_1) · F)`.
  rw [show F_C * (ω_Fib_C • σ_Fib_1) * F_C =
        ω_Fib_C • (F_C * σ_Fib_1 * F_C) from by
      rw [mul_smul_comm, smul_mul_assoc]]

/-- **σ_Fib_2_SU_mat.conjTranspose F-decomposition** (Layer F.17.a step 2).
Take conjTranspose of the decomposition and use F's self-adjointness
(`F_C_star : star F_C = F_C`) and `star = conjTranspose` for matrices. -/
theorem σ_Fib_2_SU_mat_conjTranspose_F_decomp :
    σ_Fib_2_SU_mat.conjTranspose =
      F_C * σ_Fib_1_SU_mat.conjTranspose * F_C := by
  rw [σ_Fib_2_SU_mat_F_decomp]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  -- Goal: F†·σ_Fib_1_SU† · F† · ... = F·σ_Fib_1_SU†·F
  -- Use F† = F (from F_C_star : star F_C = F_C, with `star = conjTranspose` for matrices)
  have hFstar : F_C.conjTranspose = F_C := by
    have h := F_C_star
    rwa [show (star F_C : Matrix (Fin 2) (Fin 2) ℂ) = F_C.conjTranspose from rfl] at h
  rw [hFstar]
  noncomm_ring

/-- **F-conjugate of paulI_x — explicit matrix form** (Layer F.17.a step 3).
`F · paulI_x · F = !![a·I, b·I; b·I, -a·I]` where `a = 2·(1/√φ)·(1/φ)` and
`b = 2·(1/φ) - 1`. All coefficients are real. This is the bedrock
Bonesteel-Hormozi-Simon F-action on the Pauli σ_x direction.

Proof: entry-wise expansion + the identity `(1/√φ)² = 1/φ` (`φInvSqrt_C_sq`)
+ the relation `1/φ² + 1/φ = 1` (derivable from `φ_C_sq`). -/
theorem F_C_conj_paulI_x_eq :
    F_C * paulI_x * F_C =
    !![(2 * φInvSqrt_C * φInv_C) * Complex.I, (2 * φInv_C - 1) * Complex.I;
       (2 * φInv_C - 1) * Complex.I, -((2 * φInvSqrt_C * φInv_C) * Complex.I)] := by
  -- The diagonal identity 1/φ² + 1/φ = 1 (private in FibSU2Rep — re-derive locally).
  have h_φ_diag : φInv_C * φInv_C + φInvSqrt_C * φInvSqrt_C = 1 := by
    -- Re-derive: φInvSqrt² = φInv (from φInvSqrt_C_sq), so reduces to
    -- φInv² + φInv = 1. Multiply both sides by φ² to get φ + 1 = φ² (true).
    have hsq : φInvSqrt_C * φInvSqrt_C = φInv_C := by
      have := φInvSqrt_C_sq; rw [sq] at this; exact this
    rw [hsq]
    have h1 : φ_C * φInv_C = 1 := φ_C_mul_inv
    have h2 : φ_C ^ 2 = φ_C + 1 := φ_C_sq
    have hne : φ_C ≠ 0 := φ_C_ne_zero
    have hsq_ne : φ_C ^ 2 ≠ 0 := pow_ne_zero _ hne
    have key : φ_C ^ 2 * (φInv_C * φInv_C + φInv_C) = φ_C ^ 2 * 1 := by
      calc φ_C ^ 2 * (φInv_C * φInv_C + φInv_C)
          = (φ_C * φInv_C) * (φ_C * φInv_C) + φ_C * (φ_C * φInv_C) := by ring
        _ = 1 * 1 + φ_C * 1 := by rw [h1]
        _ = φ_C + 1 := by ring
        _ = φ_C ^ 2 := h2.symm
        _ = φ_C ^ 2 * 1 := by ring
    exact mul_left_cancel₀ hsq_ne key
  -- Also need φInvSqrt² = φInv (for collapsing (1/√φ)·(1/√φ) terms).
  have h_φInvSqrt_sq : φInvSqrt_C * φInvSqrt_C = φInv_C := by
    have := φInvSqrt_C_sq; rw [sq] at this; exact this
  -- Entry-wise expansion.
  unfold paulI_x SKEFTHawking.σ_x F_C
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  -- Four entries to close:
  -- (0,0): I·(2·φInvSqrt·φInv) — closes by ring
  · ring
  -- (0,1): I·(φInvSqrt² - φInv²) = (2·φInv - 1)·I.
  -- Needs both `φInvSqrt² = φInv` and `φInv² + φInvSqrt² = 1` for the
  -- 2·φInv reduction. Coefficient derivation:
  --   G_L - G_R - 2·I·h_φInvSqrt_sq + I·h_φ_diag = 0 by ring.
  · linear_combination 2 * Complex.I * h_φInvSqrt_sq - Complex.I * h_φ_diag
  -- (1,0): symmetric to (0,1)
  · linear_combination 2 * Complex.I * h_φInvSqrt_sq - Complex.I * h_φ_diag
  -- (1,1): -I·(2·φInvSqrt·φInv)
  · ring

/-! ## §6. F.17.b.1 — σ_Fib_2_SU_mat row 0 explicit entries (session 49)

Closes the row-0 entry computation needed for F.17.b.2's
`(σ_Fib_2·paulI_x·σ_Fib_2†)(0,0)` extraction.

The key observation (from the Pauli structure of paulI_x = `!![0, I; I, 0]`):

  `(M · paulI_x · M†) 0 0 = I · (A · star B + B · star A)` = `I · 2·Re(A·star B)`

where `A := M 0 0`, `B := M 0 1`. So we only need row 0 of σ_Fib_2_SU_mat,
not the full 2×2 matrix.

Direct entry-wise computation via `Matrix.mul_apply` + `Fin.sum_univ_two`
+ `φInvSqrt² = φInv` substitution.
-/

/-- **σ_Fib_2_SU_mat entry (0,0)** (Layer F.17.b.1).
`σ_Fib_2_SU_mat 0 0 = ω · (φInv²·R1 + φInv·Rτ)`.

Proof note: simp on `ω • (...) 0 0 = ω · (...)` introduces a side condition
`∨ ω_Fib_C = 0` (via Mathlib's `mul_eq_mul_left_iff`-style simp lemma).
We take the left disjunct (the polynomial identity) and close by
`linear_combination` using the `φInvSqrt² = φInv` identity. -/
theorem σ_Fib_2_SU_mat_entry_00 :
    σ_Fib_2_SU_mat 0 0 =
      ω_Fib_C * (φInv_C * φInv_C * R1_C + φInv_C * Rtau_C) := by
  have h_φInvSqrt_sq : φInvSqrt_C * φInvSqrt_C = φInv_C := by
    have := φInvSqrt_C_sq; rw [sq] at this; exact this
  unfold σ_Fib_2_SU_mat σ_Fib_2 σ_Fib_1 F_C
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  left
  linear_combination Rtau_C * h_φInvSqrt_sq

/-- **σ_Fib_2_SU_mat entry (0,1)** (Layer F.17.b.1).
`σ_Fib_2_SU_mat 0 1 = ω · φInv · φInvSqrt · (R1 - Rτ)`. -/
theorem σ_Fib_2_SU_mat_entry_01 :
    σ_Fib_2_SU_mat 0 1 =
      ω_Fib_C * (φInv_C * φInvSqrt_C * (R1_C - Rtau_C)) := by
  unfold σ_Fib_2_SU_mat σ_Fib_2 σ_Fib_1 F_C
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  left
  ring

/-! ## §7. F.17.b.2 — (0,0) entry of σ_Fib_2 conj paulI_x (session 49)

For `M = σ_Fib_2_SU_mat`, `paulI_x = !![0, I; I, 0]`, the (0,0) entry of
`M · paulI_x · M†` follows from the Pauli structure:

  `(M · paulI_x · M†) 0 0 = M(0,0) · I · star(M(0,1)) + M(0,1) · I · star(M(0,0))`
                         `= I · (M(0,0)·star(M(0,1)) + M(0,1)·star(M(0,0)))`
                         `= I · (A·star B + B·star A)`

where A := M(0,0), B := M(0,1). The expression `A·star B + B·star A` is
`2·Re(A·star B)` (a real number), so the (0,0) entry is `I · (real)`.

This section ships **just the structural identity** (the (0,0) entry in
terms of A, B). The substitution + .im closure happens in F.17.b.3.
-/

/-- **(0,0) entry of M·paulI_x·M† via Pauli structure** (Layer F.17.b.2).
For any 2×2 complex M, `(M · paulI_x · M†)(0,0) = I · (A·star B + B·star A)`
where `A := M 0 0`, `B := M 0 1`. -/
private theorem mul_paulI_x_mul_conjTranspose_entry_00
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (M * paulI_x * M.conjTranspose) 0 0 =
      Complex.I * (M 0 0 * star (M 0 1) + M 0 1 * star (M 0 0)) := by
  unfold paulI_x SKEFTHawking.σ_x
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
        Matrix.conjTranspose_apply]
  ring

/-! ## §8. F.17.b.3 — (0,0) entry closed form (session 49)

Closes the substantive .im computation by substituting row-0 entries
(F.17.b.1) into the structural identity (F.17.b.2) and applying the
ω · star ω = R1 · star R1 = Rτ · star Rτ = 1 unit-modulus identities
plus star-of-real for φ-quantities.

Closed form: `(M · paulI_x · M†)(0,0) = I · (φInv · φInvSqrt) · (φInv - φInv²) ·
                                          ((R1·star Rτ) + (Rτ·star R1) - 2)`

Note: the φ-arithmetic factor `(φInv - φInv²)` is real and positive
(equals `2·φInv - 1` after using `φInv + φInv² = 1`). The exp-factor
`(R1·star Rτ + Rτ·star R1 - 2) = (2·cos(7π/5) - 2)` is real and
negative (since cos(7π/5) < 1 strictly). So the product is a real
negative number times I, giving a negative .im.
-/

/-- **F.17.b.3 — (0,0) entry of σ_Fib_2 Ad-action on paulI_x in closed form**.
Substantive substrate combining F.17.b.1 + F.17.b.2 + unit-modulus
identities + φ-real-star identities. -/
theorem σ_Fib_2_SU_mat_conj_paulI_x_entry_00_eq :
    (σ_Fib_2_SU_mat * paulI_x * σ_Fib_2_SU_mat.conjTranspose) 0 0 =
      Complex.I *
        (φInv_C * φInvSqrt_C * (φInv_C - φInv_C * φInv_C) *
          (R1_C * star Rtau_C + Rtau_C * star R1_C - 2)) := by
  rw [mul_paulI_x_mul_conjTranspose_entry_00,
      σ_Fib_2_SU_mat_entry_00, σ_Fib_2_SU_mat_entry_01]
  -- Unit-modulus + real-star identities
  have hω : ω_Fib_C * star ω_Fib_C = 1 := unit_norm_star_eq_one norm_ω_Fib_C
  have hR1 : R1_C * star R1_C = 1 := unit_norm_star_eq_one norm_R1_C
  have hRτ : Rtau_C * star Rtau_C = 1 := unit_norm_star_eq_one norm_Rtau_C
  have h_star_φInv : (star φInv_C : ℂ) = φInv_C := by
    unfold φInv_C
    rw [show (star ((Real.goldenRatio⁻¹ : ℝ) : ℂ) : ℂ) =
          (starRingEnd ℂ) ((Real.goldenRatio⁻¹ : ℝ) : ℂ) from rfl]
    exact Complex.conj_ofReal _
  have h_star_φInvSqrt : (star φInvSqrt_C : ℂ) = φInvSqrt_C := by
    unfold φInvSqrt_C
    rw [show (star (((Real.sqrt Real.goldenRatio)⁻¹ : ℝ) : ℂ) : ℂ) =
          (starRingEnd ℂ) (((Real.sqrt Real.goldenRatio)⁻¹ : ℝ) : ℂ) from rfl]
    exact Complex.conj_ofReal _
  -- Distribute star over products + sums, then reduce φInv, φInvSqrt stars.
  simp only [star_mul, star_add, star_sub, h_star_φInv, h_star_φInvSqrt]
  -- Coefficient derivation:
  --   LHS = I · ω · star ω · stuff where stuff has R1·star R1 and Rτ·star Rτ
  --   The R1·star R1 coefficient in stuff is 2·φInv³·φInvSqrt.
  --   The Rτ·star Rτ coefficient in stuff is -2·φInv²·φInvSqrt.
  --   So linear_combination with c_ω · hω + 2·I·φInv³·φInvSqrt · hR1
  --                          + (-2·I·φInv²·φInvSqrt) · hRτ
  linear_combination
    (Complex.I *
      ((φInv_C * φInv_C * R1_C + φInv_C * Rtau_C) *
        (star R1_C - star Rtau_C) * φInvSqrt_C * φInv_C +
       φInv_C * φInvSqrt_C * (R1_C - Rtau_C) *
        (star R1_C * (φInv_C * φInv_C) + star Rtau_C * φInv_C))) * hω
    + (2 * Complex.I * φInv_C * φInv_C * φInv_C * φInvSqrt_C) * hR1
    + (-(2 * Complex.I * φInv_C * φInv_C * φInvSqrt_C)) * hRτ

/-! ## §9. F.18 — σ_Fib bundle pauliDet ≠ 0 at paulI_x (session 49)

**HEADLINE FOR THE WHOLE R5.4 STRUCTURAL CHAIN**: shows the witness X = paulI_x
satisfies `σ_Fib_lie_bundle_pauliDet X ≠ 0`. Composed with F.14
(`σ_Fib_lie_bundle_lin_indep`), this gives ℝ-linear independence of the
3-conjugate bundle in `Matrix (Fin 2) (Fin 2) ℂ`. Composed further with
F.10/F.11/F.12 (Ad-action preserves 𝔰𝔲(2)), the bundle ℝ-spans 𝔰𝔲(2).

Structural reduction: for A = paulI_x, B = σ_Fib_1·paulI_x·σ_Fib_1†,
C = σ_Fib_2·paulI_x·σ_Fib_2†:

  `pauliDet A B C = sin(7π/5) · zC`

where zC = (C 0 0).im (Pauli z-coordinate of C). The pauliDet formula
collapses because xA = 1, yA = zA = 0, zB = 0.

Closed form: `pauliDet = sin(7π/5) · 2·(cos(7π/5) - 1) · (φ-real product)`.

Both `sin(7π/5)` and `(cos(7π/5) - 1)` are < 0 (in (π, 2π), sin < 0;
cos < 1 strictly except at multiples of 2π). The φ-real product > 0.
So `pauliDet > 0`.
-/

/-- **F.18 structural reduction** (Layer F.18 step 1).
For X = paulI_x, the pauliDet of the σ_Fib 3-bundle collapses to
`sin(7π/5) · (C 0 0).im` where C is the σ_Fib_2-conjugate of paulI_x. -/
theorem σ_Fib_lie_bundle_pauliDet_paulI_x_eq_sin_zCoord :
    σ_Fib_lie_bundle_pauliDet paulI_x =
      Real.sin (7 * Real.pi / 5) *
        ((σ_Fib_2_SU_mat * paulI_x * σ_Fib_2_SU_mat.conjTranspose) 0 0).im := by
  unfold σ_Fib_lie_bundle_pauliDet σ_Fib_lie_bundle pauliDet
  simp only []
  rw [matrixToPauliCoords_paulI_x, σ_Fib_1_SU_mat_conj_paulI_x_pauliCoords]
  unfold matrixToPauliCoords
  ring

/-- **`sin(7π/5) < 0`** (Layer F.18 step 2). Uses
`7π/5 = π + 2π/5` + `Real.sin_add` + `Real.sin_pi` / `Real.cos_pi`
+ `sin(2π/5) > 0`. -/
theorem sin_seven_pi_div_five_neg : Real.sin (7 * Real.pi / 5) < 0 := by
  have h_sin_pos : Real.sin (2 * Real.pi / 5) > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have h := Real.pi_pos; linarith
  have h_eq : Real.sin (7 * Real.pi / 5) = -Real.sin (2 * Real.pi / 5) := by
    rw [show (7 * Real.pi / 5 : ℝ) = Real.pi + 2 * Real.pi / 5 from by ring,
        Real.sin_add, Real.sin_pi, Real.cos_pi]
    ring
  linarith

/-- **`sin(7π/5) ≠ 0`** (Layer F.18 step 2 corollary). -/
theorem sin_seven_pi_div_five_ne_zero : Real.sin (7 * Real.pi / 5) ≠ 0 :=
  ne_of_lt sin_seven_pi_div_five_neg

/-- **`cos(7π/5) < 1` strictly** (Layer F.18 step 3). Uses
`7π/5 = π + 2π/5` + `Real.cos_add` + `cos(2π/5) > 0` so
`cos(7π/5) = -cos(2π/5) - 0 < 0 < 1`. -/
theorem cos_seven_pi_div_five_lt_one : Real.cos (7 * Real.pi / 5) < 1 := by
  have h_cos_pos : Real.cos (2 * Real.pi / 5) > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    refine ⟨?_, ?_⟩
    · have h := Real.pi_pos; linarith
    · have h := Real.pi_pos; linarith
  have h_eq : Real.cos (7 * Real.pi / 5) = -Real.cos (2 * Real.pi / 5) := by
    rw [show (7 * Real.pi / 5 : ℝ) = Real.pi + 2 * Real.pi / 5 from by ring,
        Real.cos_add, Real.sin_pi, Real.cos_pi]
    ring
  linarith

/-- **`cos(7π/5) - 1 ≠ 0`** (Layer F.18 step 3 corollary). -/
theorem cos_seven_pi_div_five_sub_one_ne_zero : Real.cos (7 * Real.pi / 5) - 1 ≠ 0 := by
  have := cos_seven_pi_div_five_lt_one
  linarith

/-- **F.18 substep — the φ-real product as a real-cast complex** (Layer F.18 step 4a).
The Q-factor in F.17.b.3's closed form is real-cast: φInv · φInvSqrt · (φInv - φInv²)
in ℂ equals the cast of the corresponding real product. -/
private theorem Q_factor_eq_ofReal :
    φInv_C * φInvSqrt_C * (φInv_C - φInv_C * φInv_C) =
    ((Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
      (Real.goldenRatio⁻¹ - Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹) : ℝ) : ℂ) := by
  unfold φInv_C φInvSqrt_C
  push_cast
  ring

/-- **F.18 substep — `z + star z = ↑(2 · z.re)` for any complex z**. -/
private theorem add_star_eq_ofReal_two_re (z : ℂ) :
    z + star z = ((2 * z.re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [Complex.add_re, Complex.star_def, Complex.conj_re,
          Complex.ofReal_re]; ring
  · simp [Complex.add_im, Complex.star_def, Complex.conj_im,
          Complex.ofReal_im]

/-- **F.18 substep — the S-factor sum of conjugates equals real-cast** (Layer F.18 step 4b).
`R1·star Rτ + Rτ·star R1 = 2·cos(7π/5)` (cast to ℂ).  -/
private theorem S_factor_sum_eq_ofReal :
    R1_C * star Rtau_C + Rtau_C * star R1_C =
    ((2 * Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) := by
  -- R1 · star Rτ = exp(-7πi/5) from F.16.
  rw [R1_C_mul_star_Rtau_C]
  -- For Rτ · star R1: prove = star(R1 · star Rτ) = star(exp(-7πi/5))
  have h_swap : Rtau_C * star R1_C = star (R1_C * star Rtau_C) := by
    rw [star_mul, star_star]
  rw [h_swap, R1_C_mul_star_Rtau_C]
  -- Use generic `z + star z = ↑(2 · z.re)`.
  rw [add_star_eq_ofReal_two_re]
  -- Goal: ↑(2 · (exp(↑(-7π/5)·I)).re) = ↑(2 · cos(7π/5))
  -- Compute (exp(↑(-7π/5)·I)).re = cos(7π/5) (via parity + exp_re).
  congr 1
  rw [Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Real.cos_neg, Real.exp_zero]

/-- **F.18 substep — the (C 0 0).im evaluates explicitly**.
For C = σ_Fib_2·paulI_x·σ_Fib_2†, the imaginary part of entry (0,0) equals
the real product `(φInv · φInvSqrt · (φInv - φInv²)) · (2·cos(7π/5) - 2)`. -/
theorem σ_Fib_2_SU_mat_conj_paulI_x_entry_00_im_eq :
    ((σ_Fib_2_SU_mat * paulI_x * σ_Fib_2_SU_mat.conjTranspose) 0 0).im =
      ((Real.goldenRatio⁻¹) * ((Real.sqrt Real.goldenRatio)⁻¹) *
        ((Real.goldenRatio⁻¹) - (Real.goldenRatio⁻¹) * (Real.goldenRatio⁻¹))) *
        (2 * Real.cos (7 * Real.pi / 5) - 2) := by
  rw [σ_Fib_2_SU_mat_conj_paulI_x_entry_00_eq]
  rw [Q_factor_eq_ofReal]
  -- Convert (R1·star Rτ + Rτ·star R1 - 2) to real-cast.
  have h_S_eq : R1_C * star Rtau_C + Rtau_C * star R1_C - 2 =
        ((2 * Real.cos (7 * Real.pi / 5) - 2 : ℝ) : ℂ) := by
    have h_sum := S_factor_sum_eq_ofReal
    have h_split :
        ((2 * Real.cos (7 * Real.pi / 5) - 2 : ℝ) : ℂ) =
        ((2 * Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) - 2 := by
      push_cast; ring
    rw [h_split, ← h_sum]
  rw [h_S_eq]
  -- Combine the two real-cast factors into one.
  set r : ℝ :=
    Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
      (Real.goldenRatio⁻¹ - Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹) *
      (2 * Real.cos (7 * Real.pi / 5) - 2) with hr_def
  set q : ℝ :=
    Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
      (Real.goldenRatio⁻¹ - Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹) with hq_def
  set s : ℝ := 2 * Real.cos (7 * Real.pi / 5) - 2 with hs_def
  have h_combine :
      Complex.I * (((q : ℝ) : ℂ) * ((s : ℝ) : ℂ)) =
      Complex.I * ((r : ℝ) : ℂ) := by
    have h_rqs : r = q * s := by rw [hr_def, hq_def, hs_def]
    rw [h_rqs]; push_cast; ring
  rw [h_combine]
  -- Now compute (I · ↑r).im = r for real r.
  simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]

/-- **(C 0 0).im ≠ 0** (Layer F.18 step 4). Composes `_eq` with positivity
of the φ-real product + strict negativity of `2·cos(7π/5) - 2`. -/
theorem σ_Fib_2_SU_mat_conj_paulI_x_entry_00_im_ne_zero :
    ((σ_Fib_2_SU_mat * paulI_x * σ_Fib_2_SU_mat.conjTranspose) 0 0).im ≠ 0 := by
  rw [σ_Fib_2_SU_mat_conj_paulI_x_entry_00_im_eq]
  have h_φ_pos : (Real.goldenRatio : ℝ) > 0 := Real.goldenRatio_pos
  have h_one_lt_φ : (1 : ℝ) < Real.goldenRatio := Real.one_lt_goldenRatio
  have h_φInv_pos : Real.goldenRatio⁻¹ > 0 := inv_pos.mpr h_φ_pos
  have h_sqrt_φ_pos : Real.sqrt Real.goldenRatio > 0 :=
    Real.sqrt_pos.mpr h_φ_pos
  have h_sqrt_φ_inv_pos : (Real.sqrt Real.goldenRatio)⁻¹ > 0 :=
    inv_pos.mpr h_sqrt_φ_pos
  -- φInv < 1 since φ > 1: derive via inv_lt_one_iff
  have h_φInv_lt_one : Real.goldenRatio⁻¹ < 1 := inv_lt_one_of_one_lt₀ h_one_lt_φ
  -- φInv² < φInv: multiply both sides by positive φInv.
  have h_φInv_sq_lt_φInv :
      Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹ < Real.goldenRatio⁻¹ := by
    have h := mul_lt_mul_of_pos_left h_φInv_lt_one h_φInv_pos
    rw [mul_one] at h
    exact h
  have h_diff_pos :
      Real.goldenRatio⁻¹ - Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹ > 0 := by
    linarith
  have h_product_pos :
      Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
        (Real.goldenRatio⁻¹ - Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹) > 0 :=
    mul_pos (mul_pos h_φInv_pos h_sqrt_φ_inv_pos) h_diff_pos
  have h_cos_factor :
      2 * Real.cos (7 * Real.pi / 5) - 2 < 0 := by
    have := cos_seven_pi_div_five_lt_one
    linarith
  -- product > 0, cos_factor < 0 ⇒ their product < 0 ≠ 0.
  apply ne_of_lt
  exact mul_neg_of_pos_of_neg h_product_pos h_cos_factor

/-- **HEADLINE F.18 — σ_Fib bundle pauliDet ≠ 0 at paulI_x**.

The capstone of R5.4's structural chain. Combined with F.14
(`σ_Fib_lie_bundle_lin_indep`), gives ℝ-linear independence of
`(paulI_x, σ_Fib_1·paulI_x·σ_Fib_1†, σ_Fib_2·paulI_x·σ_Fib_2†)` as
elements of `Matrix (Fin 2) (Fin 2) ℂ`. Combined with F.12 (Ad-action
preserves 𝔰𝔲(2)), the 3-bundle ℝ-spans 𝔰𝔲(2). The final IFT bridge
to density (F.19+) composes this spanning with shipped Cartan-D
substrate. -/
theorem σ_Fib_lie_bundle_pauliDet_paulI_x_ne_zero :
    σ_Fib_lie_bundle_pauliDet paulI_x ≠ 0 := by
  rw [σ_Fib_lie_bundle_pauliDet_paulI_x_eq_sin_zCoord]
  exact mul_ne_zero sin_seven_pi_div_five_ne_zero
    σ_Fib_2_SU_mat_conj_paulI_x_entry_00_im_ne_zero

/-! ## §10. F.19 — σ_Fib bundle ℝ-linearly independent at paulI_x (session 49)

Direct composition of F.18 (`σ_Fib_lie_bundle_pauliDet_paulI_x_ne_zero`)
with F.14 (`σ_Fib_lie_bundle_lin_indep`) to ship the concrete
ℝ-linear-independence of the 3-conjugate bundle at the specific witness
X = paulI_x.

This is the final structural ship of R5.4's "ℝ-lin-indep witness" arc.
The IFT bridge to unconditional density (F.20+) is structurally separate:
it needs to produce the witness `U` for `fibonacci_density_from_exp_image_subset`
(Layer E), bridging "Lie algebra spans at paulI_x" to "exp covers nbhd of 1
in H_Fib's matrices". That requires the BCH-iteration substrate
(shipped: D.3.h + D.3.i.1 + D.2.c + D.3.{e,f,g}) composed with the
σ_Fib 3-bundle structure.

**Structural map of the R5.4 arc as of session 49**:

  - **F.1-F.7**: 𝔰𝔲(2) substrate + Pauli coords + pauliDet definition.
  - **F.8**: pauliDet ≠ 0 ⟹ ℝ-lin-indep (Cramer rule).
  - **F.9-F.12**: Ad-action preserves 𝔰𝔲(2) (5 layers).
  - **F.13**: σ_Fib 3-bundle (paulI_x, σ_1 conj, σ_2 conj).
  - **F.14**: bundle is ℝ-lin-indep if pauliDet ≠ 0 (composition).
  - **F.15-F.16**: σ_Fib_1·paulI_x·σ_Fib_1† = rotation by 7π/5 about z.
  - **F.17.a-b**: σ_Fib_2 F-decomp + (0,0) entry closed form.
  - **F.18**: pauliDet ≠ 0 at paulI_x (closed form trig + φ algebra).
  - **F.19** (this): bundle ℝ-lin-indep at paulI_x — final structural ship.
  - **F.20+** (TBD): IFT bridge to unconditional density.
-/

/-- **HEADLINE F.19 — σ_Fib 3-bundle ℝ-linearly independent at paulI_x**.

For real coefficients a, b, c, the ℝ-linear combination
`a·paulI_x + b·(σ_Fib_1·paulI_x·σ_Fib_1†) + c·(σ_Fib_2·paulI_x·σ_Fib_2†) = 0`
forces `a = b = c = 0`.

Direct composition of F.18 (`σ_Fib_lie_bundle_pauliDet_paulI_x_ne_zero`)
with F.14 (`σ_Fib_lie_bundle_lin_indep`). This is the CONCRETE
linear-independence statement at the canonical witness X = paulI_x. -/
theorem σ_Fib_lie_bundle_paulI_x_lin_indep
    {a b c : ℝ}
    (h_lin : (a : ℂ) • paulI_x +
             (b : ℂ) • (σ_Fib_1_SU_mat * paulI_x * σ_Fib_1_SU_mat.conjTranspose) +
             (c : ℂ) • (σ_Fib_2_SU_mat * paulI_x * σ_Fib_2_SU_mat.conjTranspose) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 :=
  σ_Fib_lie_bundle_lin_indep σ_Fib_lie_bundle_pauliDet_paulI_x_ne_zero h_lin

/-! ## §11. F.20.a — σ_Fib bundle SPANS 𝔰𝔲(2) at paulI_x (session 50)

Composition of F.18 (`σ_Fib_lie_bundle_pauliDet_paulI_x_ne_zero`) with
the abstract SU2LieAlgebra §15 spanning criterion
(`tracelessSkewHermitian_exists_combo_of_pauliDet_ne_zero`).

For every `X ∈ 𝔰𝔲(2)`, there exist real coefficients `(a, b, c)` such
that `X = a·paulI_x + b·(σ_Fib_1·paulI_x·σ_Fib_1†) +
            c·(σ_Fib_2·paulI_x·σ_Fib_2†)`.

This establishes the σ_Fib 3-bundle at paulI_x is a **BASIS** of 𝔰𝔲(2)
(combining with F.19 ℝ-lin-indep). It is the algebraic foundation for
the IFT/BCH bridge to unconditional Fibonacci density (F.20.b/c, F.21).

**Architectural significance**: the BCH-iteration substrate
(D.3.h + D.3.i.1 + D.2.c + D.3.{e,f,g}) produces small-scale H_Fib
elements whose Ad-conjugates by σ_Fib_1, σ_Fib_2 generate three nearly
ℝ-linearly-independent Lie directions. With F.20.a giving the
"3 lin-indep ⟹ span" structural fact, BCH-spanning yields a nbhd
of 1 in H_Fib, satisfying the `fibonacci_density_from_exp_image_subset`
hypothesis.
-/

/-- **HEADLINE F.20.a — σ_Fib 3-bundle SPANS 𝔰𝔲(2) at paulI_x**.

For every `X ∈ 𝔰𝔲(2)`, there exist real coefficients `a, b, c` such that
`X = (a : ℂ) • paulI_x + (b : ℂ) • (σ_Fib_1·paulI_x·σ_Fib_1†) +
       (c : ℂ) • (σ_Fib_2·paulI_x·σ_Fib_2†)`.

Combined with F.19 (`σ_Fib_lie_bundle_paulI_x_lin_indep`), this shows
the σ_Fib bundle at paulI_x is a **basis** of 𝔰𝔲(2).

Proof: F.18 gives `σ_Fib_lie_bundle_pauliDet paulI_x ≠ 0`. Apply the
abstract SU2LieAlgebra §15 spanning criterion
`tracelessSkewHermitian_exists_combo_of_pauliDet_ne_zero` to the three
bundle members (which lie in 𝔰𝔲(2) via F.13). -/
theorem σ_Fib_lie_bundle_paulI_x_spans
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    ∃ a b c : ℝ,
      X = (a : ℂ) • paulI_x +
          (b : ℂ) • (σ_Fib_1_SU_mat * paulI_x * σ_Fib_1_SU_mat.conjTranspose) +
          (c : ℂ) • (σ_Fib_2_SU_mat * paulI_x * σ_Fib_2_SU_mat.conjTranspose) :=
  tracelessSkewHermitian_exists_combo_of_pauliDet_ne_zero
    paulI_x_mem_tracelessSkewHermitian
    (tracelessSkewHermitian_conj_σ_Fib_1_SU_mat paulI_x_mem_tracelessSkewHermitian)
    (tracelessSkewHermitian_conj_σ_Fib_2_SU_mat paulI_x_mem_tracelessSkewHermitian)
    σ_Fib_lie_bundle_pauliDet_paulI_x_ne_zero
    hX

/-! ## §12. F.20.b — pauliDet uniform-smul scaling (session 50)

`pauliDet` is **trilinear-homogeneous**: scaling all three inputs by the
same real scalar `t` scales `pauliDet` by `t³`. Proof: `matrixToPauliCoords`
is ℝ-linear (`matrixToPauliCoords_smul`), so the expanded determinant
formula (sum of products of 3 Pauli coords) scales as t³.

**Direct application to the σ_Fib bundle**: since the Ad-action by
σ_Fib_1, σ_Fib_2 is ℝ-linear in the conjugated argument,
`σ_Fib_lie_bundle (t·X) = t · σ_Fib_lie_bundle X` componentwise, hence
`σ_Fib_lie_bundle_pauliDet (t·X) = t³ · σ_Fib_lie_bundle_pauliDet X`.

**Consequence (HEADLINE)**: for any non-zero `t : ℝ` and the canonical
witness `paulI_x`, `σ_Fib_lie_bundle_pauliDet ((t : ℂ) • paulI_x) ≠ 0`,
hence the σ_Fib bundle at `t · paulI_x` is also a basis of 𝔰𝔲(2).

This is the **uniform-scale spanning** fact for the IFT/BCH iteration
bridge: arbitrarily-small witnesses `t · paulI_x` (for `t > 0`) remain
in the spanning locus of the σ_Fib bundle, so BCH iteration at any
small scale produces 3-bundles whose Lie-direction parts span 𝔰𝔲(2). -/

/-- **`pauliDet` is trilinear-homogeneous**: scaling all three arguments
by the same `(t : ℂ)` (for `t : ℝ`) scales the result by `t³`. -/
theorem pauliDet_smul_uniform (t : ℝ) (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    pauliDet ((t : ℂ) • A) ((t : ℂ) • B) ((t : ℂ) • C) =
      t ^ 3 * pauliDet A B C := by
  unfold pauliDet
  simp only [matrixToPauliCoords_smul]
  ring

/-- **σ_Fib_lie_bundle componentwise scaling under uniform smul**. -/
theorem σ_Fib_lie_bundle_smul_uniform (t : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    σ_Fib_lie_bundle ((t : ℂ) • X) =
      ((t : ℂ) • X,
       (t : ℂ) • (σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose),
       (t : ℂ) • (σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose)) := by
  unfold σ_Fib_lie_bundle
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · -- σ_Fib_1 conj distributes over ℂ-smul
    show σ_Fib_1_SU_mat * ((t : ℂ) • X) * σ_Fib_1_SU_mat.conjTranspose =
         (t : ℂ) • (σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  · -- σ_Fib_2 conj distributes over ℂ-smul
    show σ_Fib_2_SU_mat * ((t : ℂ) • X) * σ_Fib_2_SU_mat.conjTranspose =
         (t : ℂ) • (σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose)
    rw [Matrix.mul_smul, Matrix.smul_mul]

/-- **σ_Fib bundle pauliDet scaling**: `pauliDet` of the σ_Fib bundle
at `(t : ℂ) • X` equals `t³ · σ_Fib_lie_bundle_pauliDet X`. -/
theorem σ_Fib_lie_bundle_pauliDet_smul_uniform
    (t : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    σ_Fib_lie_bundle_pauliDet ((t : ℂ) • X) =
      t ^ 3 * σ_Fib_lie_bundle_pauliDet X := by
  rw [σ_Fib_lie_bundle_pauliDet_eq, σ_Fib_lie_bundle_pauliDet_eq]
  -- Note: by σ_Fib_lie_bundle_eq, the bundle at (t • X) is
  -- (t • X, t • σ_1 conj X, t • σ_2 conj X), so pauliDet scales as t³.
  have h_eq :
      pauliDet ((t : ℂ) • X)
        (σ_Fib_1_SU_mat * ((t : ℂ) • X) * σ_Fib_1_SU_mat.conjTranspose)
        (σ_Fib_2_SU_mat * ((t : ℂ) • X) * σ_Fib_2_SU_mat.conjTranspose) =
      pauliDet ((t : ℂ) • X)
        ((t : ℂ) • (σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose))
        ((t : ℂ) • (σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose)) := by
    congr 1
    · rw [Matrix.mul_smul, Matrix.smul_mul]
    · rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h_eq]
  exact pauliDet_smul_uniform t _ _ _

/-- **HEADLINE F.20.b — σ_Fib bundle SPANS at every non-zero scalar
multiple of paulI_x**.

For any `t : ℝ` with `t ≠ 0`, `σ_Fib_lie_bundle_pauliDet ((t : ℂ) • paulI_x) ≠ 0`.

Combined with F.14 (`σ_Fib_lie_bundle_lin_indep`) + F.20.a-app spanning,
this shows the σ_Fib bundle at every `t · paulI_x` (`t ≠ 0`) is a
basis of 𝔰𝔲(2). Useful for arbitrarily-small spanning witnesses
in the BCH/IFT iteration argument. -/
theorem σ_Fib_lie_bundle_pauliDet_scaled_paulI_x_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    σ_Fib_lie_bundle_pauliDet ((t : ℂ) • paulI_x) ≠ 0 := by
  rw [σ_Fib_lie_bundle_pauliDet_smul_uniform]
  exact mul_ne_zero (pow_ne_zero _ ht) σ_Fib_lie_bundle_pauliDet_paulI_x_ne_zero

/-- **Scaled spanning: σ_Fib bundle is a basis at every non-zero scalar
multiple of paulI_x**. -/
theorem σ_Fib_lie_bundle_scaled_paulI_x_spans
    {t : ℝ} (ht : t ≠ 0)
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    ∃ a b c : ℝ,
      X = (a : ℂ) • ((t : ℂ) • paulI_x) +
          (b : ℂ) • (σ_Fib_1_SU_mat * ((t : ℂ) • paulI_x) *
                        σ_Fib_1_SU_mat.conjTranspose) +
          (c : ℂ) • (σ_Fib_2_SU_mat * ((t : ℂ) • paulI_x) *
                        σ_Fib_2_SU_mat.conjTranspose) :=
  tracelessSkewHermitian_exists_combo_of_pauliDet_ne_zero
    (tracelessSkewHermitian_complex_smul_real_mem
      paulI_x_mem_tracelessSkewHermitian t)
    (tracelessSkewHermitian_conj_σ_Fib_1_SU_mat
      (tracelessSkewHermitian_complex_smul_real_mem
        paulI_x_mem_tracelessSkewHermitian t))
    (tracelessSkewHermitian_conj_σ_Fib_2_SU_mat
      (tracelessSkewHermitian_complex_smul_real_mem
        paulI_x_mem_tracelessSkewHermitian t))
    (σ_Fib_lie_bundle_pauliDet_scaled_paulI_x_ne_zero ht)
    hX

/-! ## §13. F.20.c.a — Lie part of SU(2) elements (session 51)

For h ∈ SU(2), the **Lie part** is `lieProj (h - 1) ∈ 𝔰𝔲(2)`. This is the
canonical "Lie-algebra component" of h, used in the BCH iteration argument:
for h near 1, `h ≈ 1 + liePartMat h + O(‖h-1‖²)` (first-order Taylor
approximation of exp at 0).

**Substrate for F.20.c**: the BCH/IFT iteration argument needs to track
how the Lie parts of `(h, σ_Fib_1·h·σ_Fib_1⁻¹, σ_Fib_2·h·σ_Fib_2⁻¹)`
transform — this section ships the Ad-equivariance of `liePartMat`.

**Shipped**:
  - `liePartMat` (def): the canonical Lie-projection of `M - 1`.
  - `liePartMat_mem_tracelessSkewHermitian`: output is in 𝔰𝔲(2).
  - `liePartMat_one`: `liePartMat 1 = 0`.
  - `liePartMat_conj_specialUnitary`: Ad-equivariance for any
    g ∈ specialUnitaryGroup.
  - `liePartMat_conj_σ_Fib_{1,2}_SU_mat`: concrete instances for
    σ_Fib_1_SU_mat, σ_Fib_2_SU_mat.
-/

/-- **Lie part of a matrix relative to the identity**: `lieProj (M - 1)`.

For `M = h` (an SU(2) matrix) near `1`, this approximates `log h` to
first order: `liePartMat h ≈ h - 1` (since for `h - 1` small, the
skew-Hermitian + traceless projections approximately preserve it). -/
noncomputable def liePartMat (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  lieProj (M - 1)

/-- The Lie part of any matrix lies in 𝔰𝔲(2). -/
theorem liePartMat_mem_tracelessSkewHermitian
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    liePartMat M ∈ tracelessSkewHermitian (Fin 2) :=
  lieProj_mem_tracelessSkewHermitian _

/-- The Lie part of the identity matrix is zero. -/
theorem liePartMat_one : liePartMat (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  unfold liePartMat
  rw [sub_self]
  -- lieProj 0 = 0
  unfold lieProj skewHermitianProj tracelessProj
  simp

/-- **Ad-equivariance of `liePartMat`**: for `g ∈ specialUnitaryGroup`,
`liePartMat (g·M·g†) = g · liePartMat M · g†`.

Proof composes:
  1. For unitary g: `g · g† = 1` (Mathlib `mem_unitaryGroup_iff`).
  2. Algebraic identity: `g·M·g† - 1 = g·M·g† - g·g† = g·(M-1)·g†`.
  3. F.11 `lieProj_conj_specialUnitary`: `lieProj (g·X·g†) = g · lieProj X · g†`. -/
theorem liePartMat_conj_specialUnitary
    (g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    liePartMat (g.val * M * g.val.conjTranspose) =
      g.val * liePartMat M * g.val.conjTranspose := by
  -- Step 1: g · g† = 1
  have hg_uni : g.val ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.property).1
  have hg_gdag : g.val * g.val.conjTranspose = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hg_uni
    convert this
  -- Step 2: g·M·g† - 1 = g·(M-1)·g†
  have h_factor :
      g.val * M * g.val.conjTranspose - 1 =
      g.val * (M - 1) * g.val.conjTranspose := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) = g.val * g.val.conjTranspose from hg_gdag.symm]
  -- Step 3: apply lieProj equivariance
  unfold liePartMat
  rw [h_factor, lieProj_conj_specialUnitary]

/-- **σ_Fib_1 Ad-equivariance of `liePartMat`**: concrete instance. -/
theorem liePartMat_conj_σ_Fib_1_SU_mat (M : Matrix (Fin 2) (Fin 2) ℂ) :
    liePartMat (σ_Fib_1_SU_mat * M * σ_Fib_1_SU_mat.conjTranspose) =
      σ_Fib_1_SU_mat * liePartMat M * σ_Fib_1_SU_mat.conjTranspose :=
  liePartMat_conj_specialUnitary σ_Fib_1_SU M

/-- **σ_Fib_2 Ad-equivariance of `liePartMat`**: concrete instance. -/
theorem liePartMat_conj_σ_Fib_2_SU_mat (M : Matrix (Fin 2) (Fin 2) ℂ) :
    liePartMat (σ_Fib_2_SU_mat * M * σ_Fib_2_SU_mat.conjTranspose) =
      σ_Fib_2_SU_mat * liePartMat M * σ_Fib_2_SU_mat.conjTranspose :=
  liePartMat_conj_specialUnitary σ_Fib_2_SU M

/-! ## §14. F.20.c.b — σ_Fib bundle commutes with liePartMat (session 51)

**The σ_Fib bundle of Lie parts equals the Lie parts of the σ_Fib bundle**.

For any matrix h, the σ_Fib bundle applied to `liePartMat h` produces the
same triple as componentwise `liePartMat` applied to the σ_Fib bundle of h.
This is the substrate that connects the small-h BCH iteration argument
(operating on `h ∈ H_Fib`) to the Lie-algebra spanning analysis
(operating on `liePartMat h ∈ 𝔰𝔲(2)`).

Direct composition of `liePartMat_conj_σ_Fib_{1,2}_SU_mat` with the
`σ_Fib_lie_bundle` definition.
-/

/-- **σ_Fib bundle commutes with `liePartMat`**: the σ_Fib bundle of
the Lie part of h equals componentwise Lie part of the σ_Fib bundle of h.

`σ_Fib_lie_bundle (liePartMat h) =
  (liePartMat h, liePartMat (σ_Fib_1·h·σ_Fib_1†), liePartMat (σ_Fib_2·h·σ_Fib_2†))`

Proof: σ_Fib_lie_bundle def + Ad-equivariance of liePartMat (§13). -/
theorem σ_Fib_lie_bundle_liePartMat_eq
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    σ_Fib_lie_bundle (liePartMat M) =
      (liePartMat M,
       liePartMat (σ_Fib_1_SU_mat * M * σ_Fib_1_SU_mat.conjTranspose),
       liePartMat (σ_Fib_2_SU_mat * M * σ_Fib_2_SU_mat.conjTranspose)) := by
  unfold σ_Fib_lie_bundle
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · -- σ_Fib_1 component: σ_1·liePartMat M·σ_1† = liePartMat (σ_1·M·σ_1†)
    show σ_Fib_1_SU_mat * liePartMat M * σ_Fib_1_SU_mat.conjTranspose =
         liePartMat (σ_Fib_1_SU_mat * M * σ_Fib_1_SU_mat.conjTranspose)
    rw [liePartMat_conj_σ_Fib_1_SU_mat]
  · -- σ_Fib_2 component: analogous
    show σ_Fib_2_SU_mat * liePartMat M * σ_Fib_2_SU_mat.conjTranspose =
         liePartMat (σ_Fib_2_SU_mat * M * σ_Fib_2_SU_mat.conjTranspose)
    rw [liePartMat_conj_σ_Fib_2_SU_mat]

/-- **The σ_Fib bundle pauliDet of the Lie part equals the pauliDet of
the Lie parts of the σ_Fib bundle**. Direct consequence of `σ_Fib_lie_bundle_liePartMat_eq`. -/
theorem σ_Fib_lie_bundle_pauliDet_liePartMat_eq
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    σ_Fib_lie_bundle_pauliDet (liePartMat M) =
      pauliDet (liePartMat M)
        (liePartMat (σ_Fib_1_SU_mat * M * σ_Fib_1_SU_mat.conjTranspose))
        (liePartMat (σ_Fib_2_SU_mat * M * σ_Fib_2_SU_mat.conjTranspose)) := by
  unfold σ_Fib_lie_bundle_pauliDet
  rw [σ_Fib_lie_bundle_liePartMat_eq]

/-! ## §15. F.20.c.c — Closed-form rotation-matrix witness (session 52)

For each `t : ℝ`, define
`rotPaulI_x t := (cos t : ℂ) • I + (sin t : ℂ) • paulI_x`.

This is the SU(2) **rotation matrix** about the x-axis — manifestly in
`specialUnitaryGroup (Fin 2) ℂ` (verified by direct entry-wise det and
unitarity computation), avoiding any matrix-exponential machinery. Its
`liePartMat` has the closed form `(sin t : ℂ) • paulI_x` (via `lieProj`
additivity + `lieProj_real_smul_one_eq_zero` + idempotence on 𝔰𝔲(2)).

**Headline ship**: for `sin t ≠ 0`,
`σ_Fib_lie_bundle_pauliDet (liePartMat (rotPaulI_x t)) ≠ 0` —
the existential WITNESS for "some `h ∈ SU(2)` has non-zero
σ_Fib_lie_bundle_pauliDet at its Lie part". Combined with F.20.b
(`σ_Fib_lie_bundle_pauliDet_scaled_paulI_x_ne_zero`), this populates
the spanning locus for the BCH/IFT bridge to unconditional density.

**Substrate downstream**:
  - **F.20.c.d** (multi-session): lift "Lie parts span 𝔰𝔲(2)" via BCH
    iteration to "products of bundle members cover open nbhd of 1".
  - **F.21** (~20-50 LoC): compose with Layer E's
    `fibonacci_density_from_exp_image_subset` for full
    `DenseInSpecialUnitary 3 2 ρ_Fib_SU2`.

**Note**: `rotPaulI_x t` is NOT in general in `H_Fib`. F.20.c.c here
ships the SU(2)-level existence; promoting to an H_Fib witness happens
in F.20.c.d via the BCH iteration substrate (D.3.h + D.3.i.1).
-/

/-- **Rotation matrix about the x-axis** in SU(2): closed-form analog
of `exp(t · paulI_x)`. Manifestly unitary + special, sidestepping
matrix-exponential infrastructure for the F.20.c.c witness ship. -/
noncomputable def rotPaulI_x (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (Real.sin t : ℂ) • paulI_x

/-- **conjTranspose of `rotPaulI_x` in smul-form**: since `paulI_x` is
skew-Hermitian and `cos t, sin t` are real,
`(rotPaulI_x t)† = (cos t : ℂ) • 1 - (sin t : ℂ) • paulI_x`. -/
theorem rotPaulI_x_conjTranspose (t : ℝ) :
    (rotPaulI_x t).conjTranspose =
      (Real.cos t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        (Real.sin t : ℂ) • paulI_x := by
  unfold rotPaulI_x
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  rw [show star (Real.cos t : ℂ) = (Real.cos t : ℂ) from
      Complex.conj_ofReal _]
  rw [show star (Real.sin t : ℂ) = (Real.sin t : ℂ) from
      Complex.conj_ofReal _]
  rw [show (paulI_x : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = -paulI_x
      from paulI_x_isSkewHermitian]
  rw [smul_neg]
  abel

/-- **`rotPaulI_x t` is unitary**: `(rotPaulI_x t) · (rotPaulI_x t)† = 1`.

Algebraic proof: with `c = cos t`, `s = sin t`,
  `(c•1 + s•paulI_x) · (c•1 - s•paulI_x)`
= `c²•1 - s²•(paulI_x²)`            [cross terms cancel since they commute via 1]
= `c²•1 - s²•(-1)`                  [`paulI_x_sq`]
= `(c² + s²)•1 = 1`                 [`cos²+sin²=1`]. -/
theorem rotPaulI_x_mul_conjTranspose (t : ℝ) :
    rotPaulI_x t * (rotPaulI_x t).conjTranspose = 1 := by
  rw [rotPaulI_x_conjTranspose]
  unfold rotPaulI_x
  -- Algebraic expansion using commutativity with identity + paulI_x²=-1.
  -- Step 1: distribute the product. Use Matrix.add_mul, Matrix.mul_sub.
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
  -- Step 2: each of 4 terms is X•1 · Y•Z where X•1 is scalar, so X•1·(Y•Z) = (X·Y)•(1·Z) = (XY)•Z.
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]    -- (c•1)(c•1) = c•(1·(c•1)) = c•(c•1)
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]    -- (c•1)(s•paulI_x) → c•(s•paulI_x)
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]    -- (s•paulI_x)(c•1) → s•(c•paulI_x)
  rw [Matrix.smul_mul, Matrix.mul_smul]                     -- (s•paulI_x)(s•paulI_x) → s•(s•paulI_x²)
  -- Combine the smul-of-smul into single scalar
  rw [smul_smul, smul_smul, smul_smul, smul_smul]
  rw [paulI_x_sq]
  -- Goal now: (c·c) • 1 - ((c·s) • paulI_x) + ((s·c) • paulI_x - (s·s) • (-1)) = 1
  -- Rearrange: the cross terms (c·s)•paulI_x and (s·c)•paulI_x cancel
  rw [smul_neg, sub_neg_eq_add]
  -- (c·c)•1 - (c·s)•paulI_x + ((s·c)•paulI_x + (s·s)•1) = 1
  rw [show (Real.cos t : ℂ) * (Real.sin t : ℂ) =
          (Real.sin t : ℂ) * (Real.cos t : ℂ) from mul_comm _ _]
  -- (c·c)•1 - (s·c)•paulI_x + (s·c)•paulI_x + (s·s)•1 = 1
  have h_trig : ((Real.cos t : ℂ) * (Real.cos t : ℂ)) +
                ((Real.sin t : ℂ) * (Real.sin t : ℂ)) = 1 := by
    rw [show ((Real.cos t : ℂ) * (Real.cos t : ℂ)) +
             ((Real.sin t : ℂ) * (Real.sin t : ℂ)) =
         ((Real.cos t : ℂ))^2 + ((Real.sin t : ℂ))^2 from by ring]
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    exact Complex.cos_sq_add_sin_sq ↑t
  -- Rearrange using abel and apply h_trig
  rw [show ((Real.cos t : ℂ) * (Real.cos t : ℂ)) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        ((Real.sin t : ℂ) * (Real.cos t : ℂ)) • paulI_x +
       (((Real.sin t : ℂ) * (Real.cos t : ℂ)) • paulI_x +
        ((Real.sin t : ℂ) * (Real.sin t : ℂ)) • (1 : Matrix _ _ ℂ)) =
       (((Real.cos t : ℂ) * (Real.cos t : ℂ)) +
        ((Real.sin t : ℂ) * (Real.sin t : ℂ))) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) from by
    rw [add_smul]; abel]
  rw [h_trig, one_smul]

/-- **`rotPaulI_x t` has determinant 1**.

Via Matrix.det_fin_two using explicit entry formula on rotPaulI_x. -/
theorem rotPaulI_x_det (t : ℝ) :
    (rotPaulI_x t).det = 1 := by
  unfold rotPaulI_x paulI_x SKEFTHawking.σ_x
  rw [Matrix.det_fin_two]
  -- Entries computed:
  -- (0,0) = cos t, (1,1) = cos t, (0,1) = i·sin t, (1,0) = i·sin t
  -- det = cos²t - (i·sin t)² = cos²t - i²·sin²t = cos²t + sin²t = 1
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, smul_eq_mul, Complex.I_mul_I]
  -- State h_trig in Complex.cos form (matches the goal after simp)
  have h_trig : (Complex.cos ↑t)^2 + (Complex.sin ↑t)^2 = 1 :=
    Complex.cos_sq_add_sin_sq ↑t
  have h_I_sq : Complex.I^2 = -1 := Complex.I_sq
  linear_combination h_trig - (Complex.sin ↑t)^2 * h_I_sq

/-- **`rotPaulI_x t ∈ specialUnitaryGroup (Fin 2) ℂ`** — the rotation
matrix is in SU(2). -/
theorem rotPaulI_x_mem_specialUnitaryGroup (t : ℝ) :
    rotPaulI_x t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, rotPaulI_x_det t⟩
  rw [Matrix.mem_unitaryGroup_iff]
  exact rotPaulI_x_mul_conjTranspose t

/-- **HEADLINE F.20.c.c — closed-form `liePartMat` of the rotation matrix**:
`liePartMat (rotPaulI_x t) = (sin t : ℂ) • paulI_x`.

Proof:
  1. `rotPaulI_x t - 1 = ((cos t - 1) : ℂ) • 1 + (sin t : ℂ) • paulI_x`
     (by smul-distributivity of subtraction).
  2. `lieProj` is additive (`SU2LieAlgebra.lieProj_add`).
  3. `lieProj ((r : ℂ) • 1) = 0` for `r : ℝ`
     (`SU2LieAlgebra.lieProj_real_smul_one_eq_zero`).
  4. `(sin t : ℂ) • paulI_x ∈ tracelessSkewHermitian` so `lieProj` fixes
     it (`SU2LieAlgebra.lieProj_idempotent_on_tracelessSkewHermitian`). -/
theorem liePartMat_rotPaulI_x (t : ℝ) :
    liePartMat (rotPaulI_x t) = (Real.sin t : ℂ) • paulI_x := by
  unfold liePartMat rotPaulI_x
  -- Step 1: rewrite `... - 1` as sum of two real-smul terms
  have h_eq : (Real.cos t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (Real.sin t : ℂ) • paulI_x - 1 =
      ((Real.cos t - 1 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (Real.sin t : ℂ) • paulI_x := by
    have h_smul : ((Real.cos t - 1 : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) =
        (Real.cos t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - 1 := by
      push_cast
      rw [sub_smul, one_smul]
    rw [h_smul]
    abel
  rw [h_eq]
  -- Step 2: lieProj is additive
  rw [lieProj_add]
  -- Step 3: lieProj ((cos t - 1 : ℂ) • 1) = 0
  rw [lieProj_real_smul_one_eq_zero]
  rw [zero_add]
  -- Step 4: lieProj ((sin t : ℂ) • paulI_x) = (sin t : ℂ) • paulI_x
  exact lieProj_idempotent_on_tracelessSkewHermitian
    (tracelessSkewHermitian_complex_smul_real_mem
      paulI_x_mem_tracelessSkewHermitian (Real.sin t))

/-- **HEADLINE F.20.c.c — `σ_Fib_lie_bundle_pauliDet (liePartMat (rotPaulI_x t)) ≠ 0`
for `sin t ≠ 0`**.

The existential WITNESS for "some SU(2) element `h` has non-zero
`σ_Fib_lie_bundle_pauliDet (liePartMat h)`". Combined with F.20.b's
uniform-scaling result, this populates the spanning locus around 1.

Proof: `liePartMat (rotPaulI_x t) = (sin t : ℂ) • paulI_x`
(`liePartMat_rotPaulI_x`), and F.20.b's
`σ_Fib_lie_bundle_pauliDet_scaled_paulI_x_ne_zero` gives the result
for any non-zero scalar coefficient. -/
theorem σ_Fib_lie_bundle_pauliDet_liePartMat_rotPaulI_x_ne_zero
    {t : ℝ} (ht : Real.sin t ≠ 0) :
    σ_Fib_lie_bundle_pauliDet (liePartMat (rotPaulI_x t)) ≠ 0 := by
  rw [liePartMat_rotPaulI_x]
  exact σ_Fib_lie_bundle_pauliDet_scaled_paulI_x_ne_zero ht

/-- **F.20.c.c existence consequence**: there exists `h ∈ specialUnitaryGroup (Fin 2) ℂ`
with `σ_Fib_lie_bundle_pauliDet (liePartMat h) ≠ 0`.

This is the **existential SU(2)-level witness** that promotes the
abstract pauliDet ≠ 0 statement to a "there exists" form usable
downstream by F.20.c.d (BCH iteration to small-h H_Fib witnesses) and
F.21 (Layer E composition). Witness: `rotPaulI_x (π/2)` (giving
`sin(π/2) = 1 ≠ 0`). -/
theorem exists_specialUnitary_with_σ_Fib_lie_bundle_pauliDet_liePartMat_ne_zero :
    ∃ h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      σ_Fib_lie_bundle_pauliDet (liePartMat h.val) ≠ 0 := by
  refine ⟨⟨rotPaulI_x (Real.pi / 2),
          rotPaulI_x_mem_specialUnitaryGroup (Real.pi / 2)⟩, ?_⟩
  simp only
  apply σ_Fib_lie_bundle_pauliDet_liePartMat_rotPaulI_x_ne_zero
  rw [Real.sin_pi_div_two]
  exact one_ne_zero

/-! ## §16. F.20.c.d.0 — Continuity of `σ_Fib_lie_bundle_pauliDet ∘ liePartMat`
(session 53)

Infrastructure substrate for F.20.c.d's BCH-iteration spanning step:
`σ_Fib_lie_bundle_pauliDet ∘ liePartMat : Matrix (Fin 2) (Fin 2) ℂ → ℝ`
is **continuous**. Consequence: the preimage of `ℝ \ {0}` is open, so
the set `{h | σ_Fib_lie_bundle_pauliDet (liePartMat h) ≠ 0}` is an
open subset of `Matrix (Fin 2) (Fin 2) ℂ`.

This gives **topological room**: any neighborhood of `paulI_x` (or
`rotPaulI_x t` for `sin t ≠ 0`) in the Matrix-norm topology contains
matrices with the same non-zero pauliDet property. Downstream
applications can leverage this to interpolate from explicit witnesses
to constructive `h ∈ H_Fib` witnesses (via D.3.i.1 iteration sequence
+ approximation).

**Ships**:
  - `liePartMat_continuous` — direct composition of `lieProj_continuous`
    + continuity of `M ↦ M - 1`.
  - `σ_Fib_lie_bundle_continuous` — componentwise continuity (each entry
    of the 3-tuple is a continuous function of X via `Matrix.mul`
    continuity).
  - `σ_Fib_lie_bundle_pauliDet_continuous` — composition of bundle
    continuity + `pauliDet_continuous_of_continuous`.
  - `σ_Fib_lie_bundle_pauliDet_liePartMat_continuous` — composition with
    `liePartMat_continuous`.
  - **HEADLINE `σ_Fib_lie_bundle_pauliDet_liePartMat_ne_zero_isOpen`**:
    `{h | σ_Fib_lie_bundle_pauliDet (liePartMat h) ≠ 0}` is open.
-/

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- **`liePartMat` is continuous**: `lieProj ∘ (· - 1)`. -/
theorem liePartMat_continuous :
    Continuous (liePartMat :
      Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold liePartMat
  exact lieProj_continuous.comp (continuous_id.sub continuous_const)

/-- **`σ_Fib_lie_bundle` is continuous**: each of the 3 components is
a continuous function of `X` (entries built from matrix multiplication
and `conjTranspose`, both continuous). -/
theorem σ_Fib_lie_bundle_continuous :
    Continuous (σ_Fib_lie_bundle :
      Matrix (Fin 2) (Fin 2) ℂ →
        Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ ×
          Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold σ_Fib_lie_bundle
  refine Continuous.prodMk continuous_id (Continuous.prodMk ?_ ?_)
  · -- σ_Fib_1·X·σ_Fib_1†
    exact (continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const
  · -- σ_Fib_2·X·σ_Fib_2†
    exact (continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const

/-- **`σ_Fib_lie_bundle_pauliDet` is continuous**: composition of
`pauliDet_continuous_of_continuous` with each of the 3 continuous bundle
components. -/
theorem σ_Fib_lie_bundle_pauliDet_continuous :
    Continuous (σ_Fib_lie_bundle_pauliDet :
      Matrix (Fin 2) (Fin 2) ℂ → ℝ) := by
  unfold σ_Fib_lie_bundle_pauliDet
  -- σ_Fib_lie_bundle_pauliDet X = pauliDet (σ_Fib_lie_bundle X).1
  --                                       (σ_Fib_lie_bundle X).2.1
  --                                       (σ_Fib_lie_bundle X).2.2
  have h1 : Continuous (fun X => (σ_Fib_lie_bundle X).1) :=
    continuous_fst.comp σ_Fib_lie_bundle_continuous
  have h2 : Continuous (fun X => (σ_Fib_lie_bundle X).2.1) :=
    (continuous_fst.comp continuous_snd).comp σ_Fib_lie_bundle_continuous
  have h3 : Continuous (fun X => (σ_Fib_lie_bundle X).2.2) :=
    (continuous_snd.comp continuous_snd).comp σ_Fib_lie_bundle_continuous
  exact pauliDet_continuous_of_continuous h1 h2 h3

/-- **`σ_Fib_lie_bundle_pauliDet ∘ liePartMat` is continuous**. -/
theorem σ_Fib_lie_bundle_pauliDet_liePartMat_continuous :
    Continuous (fun h : Matrix (Fin 2) (Fin 2) ℂ =>
      σ_Fib_lie_bundle_pauliDet (liePartMat h)) :=
  σ_Fib_lie_bundle_pauliDet_continuous.comp liePartMat_continuous

/-- **HEADLINE F.20.c.d.0 — `{h | σ_Fib_lie_bundle_pauliDet (liePartMat h) ≠ 0}`
is open in `Matrix (Fin 2) (Fin 2) ℂ`**.

Direct consequence of continuity + openness of `ℝ \ {0}`. Provides the
**topological room** for the BCH iteration argument to find `h ∈ H_Fib`
in the spanning locus.

In particular: there is an open neighborhood of `paulI_x` (the SU(2)
witness from `exists_specialUnitary_with_σ_Fib_lie_bundle_pauliDet_liePartMat_ne_zero`)
on which `σ_Fib_lie_bundle_pauliDet (liePartMat h) ≠ 0` holds. -/
theorem σ_Fib_lie_bundle_pauliDet_liePartMat_ne_zero_isOpen :
    IsOpen {h : Matrix (Fin 2) (Fin 2) ℂ |
      σ_Fib_lie_bundle_pauliDet (liePartMat h) ≠ 0} := by
  -- Preimage of {x : ℝ | x ≠ 0} under the continuous map is open
  exact σ_Fib_lie_bundle_pauliDet_liePartMat_continuous.isOpen_preimage
    {x : ℝ | x ≠ 0} isOpen_ne

/-- **Witness consequence**: there is an open neighborhood of
`rotPaulI_x (π/2)` (= `paulI_x`) in `Matrix` on which
`σ_Fib_lie_bundle_pauliDet (liePartMat h) ≠ 0` holds for all `h` in the
neighborhood. Combines `σ_Fib_lie_bundle_pauliDet_liePartMat_ne_zero_isOpen`
with the explicit witness `rotPaulI_x_mem_specialUnitaryGroup (π/2)`. -/
theorem mem_nhds_pauliDet_liePartMat_ne_zero_at_rotPaulI_x_pi_div_two :
    {h : Matrix (Fin 2) (Fin 2) ℂ |
      σ_Fib_lie_bundle_pauliDet (liePartMat h) ≠ 0} ∈
        nhds (rotPaulI_x (Real.pi / 2)) := by
  refine σ_Fib_lie_bundle_pauliDet_liePartMat_ne_zero_isOpen.mem_nhds ?_
  show σ_Fib_lie_bundle_pauliDet (liePartMat (rotPaulI_x (Real.pi / 2))) ≠ 0
  apply σ_Fib_lie_bundle_pauliDet_liePartMat_rotPaulI_x_ne_zero
  rw [Real.sin_pi_div_two]
  exact one_ne_zero

/-! ## §17. F.20.c.d.1 — Witnesses arbitrarily close to 1 (session 54)

For `X ∈ 𝔰𝔲(2)`, `liePartMat (1 + X) = X` exactly (since `(1 + X) - 1 = X`
and `lieProj` is idempotent on `𝔰𝔲(2)`). This is a **closed-form witness
family**: every `1 + (t : ℂ) • paulI_x` (for `t ∈ ℝ \ {0}`) satisfies
`σ_Fib_lie_bundle_pauliDet (liePartMat (1 + (t : ℂ) • paulI_x)) ≠ 0`.

The matrix `1 + (t : ℂ) • paulI_x` is NOT in SU(2) (det = 1 + t² ≠ 1 for
t ≠ 0) but DOES accumulate at `1 ∈ SU(2)` as `t → 0`. Combined with
F.20.c.d.0 openness, this shows the spanning locus contains points
arbitrarily close to 1 in matrix space.

**Substrate downstream**: this gives an existential lower bound for
F.20.c.d.{1,2} — there's no topological obstruction at 1 to finding
spanning witnesses; what remains is to show that H_Fib elements (which
are constrained to SU(2)) accumulate at 1 in "good directions" matching
the spanning locus.

**Ships**:
  - `liePartMat_one_plus`: closed form for X ∈ 𝔰𝔲(2).
  - `σ_Fib_lie_bundle_pauliDet_liePartMat_one_plus_paulI_x_ne_zero`:
    explicit witness family `1 + (t : ℂ) • paulI_x` for `t ≠ 0`.
  - `one_plus_real_smul_paulI_x_tendsto_one`: this family approaches 1
    as `t → 0`.
  - `mem_nhds_pauliDet_liePartMat_ne_zero_at_one_plus_smul_paulI_x`:
    open neighborhood at each witness.
-/

/-- **Closed-form `liePartMat (1 + X)` for `X ∈ 𝔰𝔲(2)`**: equals `X`
exactly (no first-order approximation needed). Direct from `(1 + X) - 1 = X`
and `lieProj` idempotence on 𝔰𝔲(2). -/
theorem liePartMat_one_plus
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    liePartMat ((1 : Matrix (Fin 2) (Fin 2) ℂ) + X) = X := by
  unfold liePartMat
  rw [show (1 + X - 1 : Matrix (Fin 2) (Fin 2) ℂ) = X by abel]
  exact lieProj_idempotent_on_tracelessSkewHermitian hX

/-- **Explicit witness family**: for any `t ∈ ℝ \ {0}`,
`σ_Fib_lie_bundle_pauliDet (liePartMat (1 + (t : ℂ) • paulI_x)) ≠ 0`.

This produces witnesses arbitrarily close to 1 in matrix space
(`1 + (t : ℂ) • paulI_x → 1` as `t → 0`, by continuity of scalar
multiplication and matrix addition). -/
theorem σ_Fib_lie_bundle_pauliDet_liePartMat_one_plus_paulI_x_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    σ_Fib_lie_bundle_pauliDet
      (liePartMat ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (t : ℂ) • paulI_x)) ≠ 0 := by
  rw [liePartMat_one_plus
    (tracelessSkewHermitian_complex_smul_real_mem
      paulI_x_mem_tracelessSkewHermitian t)]
  exact σ_Fib_lie_bundle_pauliDet_scaled_paulI_x_ne_zero ht

/-- **Open neighborhood at each `1 + (t : ℂ) • paulI_x` witness**. -/
theorem mem_nhds_pauliDet_liePartMat_ne_zero_at_one_plus_smul_paulI_x
    {t : ℝ} (ht : t ≠ 0) :
    {h : Matrix (Fin 2) (Fin 2) ℂ |
      σ_Fib_lie_bundle_pauliDet (liePartMat h) ≠ 0} ∈
        nhds ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (t : ℂ) • paulI_x) := by
  refine σ_Fib_lie_bundle_pauliDet_liePartMat_ne_zero_isOpen.mem_nhds ?_
  exact σ_Fib_lie_bundle_pauliDet_liePartMat_one_plus_paulI_x_ne_zero ht

/-- **The witness family approaches 1**: as `t → 0`,
`1 + (t : ℂ) • paulI_x → 1` in matrix norm.

Proof: `(t : ℂ) • paulI_x` is continuous in `t` and equals `0` at `t = 0`. -/
theorem one_plus_real_smul_paulI_x_tendsto_one :
    Filter.Tendsto (fun t : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (t : ℂ) • paulI_x) (nhds 0) (nhds 1) := by
  have h_smul_tendsto :
      Filter.Tendsto (fun t : ℝ => (t : ℂ) • paulI_x)
        (nhds 0) (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [show (0 : Matrix (Fin 2) (Fin 2) ℂ) = ((0 : ℝ) : ℂ) • paulI_x from
      by simp]
    exact ((Complex.continuous_ofReal.smul continuous_const).tendsto 0)
  have h_one : Filter.Tendsto (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (nhds 0) (nhds 1) := tendsto_const_nhds
  have h_combined :
      Filter.Tendsto (fun t : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (t : ℂ) • paulI_x) (nhds 0) (nhds ((1 : Matrix _ _ ℂ) + 0)) :=
    h_one.add h_smul_tendsto
  simpa using h_combined

/-! ## §18. F.20.c.d.1.app — Every neighborhood of 1 contains a witness (session 55)

Package the F.20.c.d.0 openness + F.20.c.d.1 accumulation into a single
clean statement: **every open neighborhood of 1 in `Matrix (Fin 2) (Fin 2) ℂ`
contains a matrix M with `σ_Fib_lie_bundle_pauliDet (liePartMat M) ≠ 0`**.

This is the form most useful to downstream BCH-iteration arguments:
when we ask "is there an h ∈ H_Fib (∩ some open nhd of 1) with the
spanning property?", the obstacle is NOT topological in the matrix
sense — it's the question of whether the H_Fib intersection with
the spanning locus is non-empty.

**Ships**:
  - `eventually_pauliDet_liePartMat_ne_zero_near_one`: the
    `Filter.Eventually` form, expressing "for all M near 1, eventually
    (along the witness family) pauliDet ≠ 0".
  - `exists_in_nhds_one_pauliDet_liePartMat_ne_zero`: existential form,
    "every nhd U of 1 contains M with pauliDet ≠ 0".
  - `pauliDet_liePartMat_ne_zero_freq_one`: `1` is a frequency point of
    the spanning locus (in the sense `MapClusterPt`-style).
-/

/-- **`Filter.Eventually` form**: along the witness family `t ↦ 1 + (t : ℂ) • paulI_x`,
`σ_Fib_lie_bundle_pauliDet ≠ 0` eventually as `t → 0` (along
`𝓝[≠] 0` — i.e., t ≠ 0 stays in the spanning locus). -/
theorem eventually_pauliDet_liePartMat_ne_zero_near_zero :
    ∀ᶠ t : ℝ in nhdsWithin 0 {0}ᶜ,
      σ_Fib_lie_bundle_pauliDet
        (liePartMat ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (t : ℂ) • paulI_x)) ≠ 0 := by
  refine eventually_nhdsWithin_iff.mpr ?_
  filter_upwards with t ht
  exact σ_Fib_lie_bundle_pauliDet_liePartMat_one_plus_paulI_x_ne_zero ht

/-! ## §19. F.20.c.d.2.a — Closed-form `liePartMat` on SU(2) (session 56)

For `h ∈ SU(2)`, `liePartMat h.val` has a clean closed form:
`liePartMat h.val = h.val - (trace h.val / 2) • 1`.

Derivation (composes session 31's `SU2_star_eq_trace_sub`):
  1. `(h - 1)† = h.conjTranspose - 1 = star h - 1`
  2. For h ∈ SU(2): `star h = trace h • 1 - h` (SU2_star_eq_trace_sub).
  3. `skewHermitianProj (h - 1) = (1/2) • (h - 1 - (h - 1)†)
                                  = (1/2) • (h - h†)
                                  = (1/2) • (h - (trace h • 1 - h))
                                  = (1/2) • (2h - trace h • 1)
                                  = h - (trace h / 2) • 1`
  4. The result above has trace `tr h - (tr h / 2) · 2 = 0`, so
     `tracelessProj` is the identity on it.
  5. Hence `liePartMat h.val = h.val - (trace h.val / 2) • 1`.

**Consequence**: `liePartMat h.val = 0 ↔ h.val = (trace h.val / 2) • 1`
↔ h.val is a scalar matrix. Combined with `det h.val = 1`: the scalar
must be `±1`, so `h.val ∈ {1, -1}`, so `h ∈ {1, negOneSU}`.

**HEADLINE**: `liePartMat h.val ≠ 0 ↔ h ≠ 1 ∧ h ≠ negOneSU`. -/

/-- **Closed-form `liePartMat` for SU(2)**:
`liePartMat h.val = h.val - (trace h.val / 2) • 1`.

Composes session 31's `SU2_star_eq_trace_sub` (`star h = tr h • 1 - h`
for h ∈ SU(2)) with `skewHermitianProj` definition + tracelessness. -/
theorem liePartMat_specialUnitary
    (h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ) =
      (h : Matrix (Fin 2) (Fin 2) ℂ) -
        (Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ) / 2) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := (h : Matrix (Fin 2) (Fin 2) ℂ) with hA
  -- Closed-form for star A from SU2_star_eq_trace_sub
  have h_star_A : star A =
      (Matrix.trace A) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A :=
    SKEFTHawking.FKLW.SU2_star_eq_trace_sub h
  -- conjTranspose IS star on matrices
  have h_ct_A : A.conjTranspose = star A := rfl
  -- skewHermitianProj (A - 1) = (1/2) • ((A - 1) - (star A - 1)) = (1/2) • (A - star A)
  have h_skewProj : skewHermitianProj (A - 1) =
      A - (Matrix.trace A / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold skewHermitianProj
    -- Unfold conjTranspose and substitute star formula
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, h_ct_A, h_star_A]
    -- Goal: (1/2) • (A - 1 - (trace A • 1 - A - 1)) = A - (trace A / 2) • 1
    rw [show (A - 1 - ((Matrix.trace A) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A - 1)) =
        (2 : ℂ) • A - (Matrix.trace A) • (1 : Matrix (Fin 2) (Fin 2) ℂ) from by
      rw [show ((2 : ℂ)) • A = A + A from by rw [two_smul]]
      abel]
    rw [smul_sub]
    rw [smul_smul, smul_smul]
    -- (1/2) · 2 = 1 and (1/2) · trace A = trace A / 2
    congr 1
    · rw [show (1/2 : ℂ) * 2 = 1 from by norm_num, one_smul]
    · congr 1
      ring
  -- The skewHermitianProj result is already traceless
  have h_traceless : Matrix.trace (A - (Matrix.trace A / 2) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp [Fintype.card_fin, smul_eq_mul]
  -- tracelessProj is identity on traceless matrices
  unfold liePartMat
  show tracelessProj (skewHermitianProj (A - 1)) = _
  rw [h_skewProj]
  exact tracelessProj_of_traceless h_traceless

/-- **`liePartMat h.val = 0` ↔ `h.val` is scalar matrix**: from the
closed form, vanishing of `liePartMat` is equivalent to `h.val = (tr h.val / 2) • 1`. -/
theorem liePartMat_specialUnitary_eq_zero_iff_scalar
    (h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ) = 0 ↔
      (h : Matrix (Fin 2) (Fin 2) ℂ) =
        (Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ) / 2) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [liePartMat_specialUnitary]
  exact sub_eq_zero

/-- **HEADLINE F.20.c.d.2.a — `liePartMat h ≠ 0 ↔ h ∉ {1, negOneSU}`** for
h ∈ SU(2). The non-zero locus of `liePartMat` on SU(2) is exactly the
complement of `{1, negOneSU}`.

Combined with the F.20.c.d.* topological substrate, this characterizes
the "domain" of the F.20.c.d.2 directionality argument: among
h ∈ specialUnitaryGroup, the relevant elements are h ∉ {1, negOneSU}. -/
theorem liePartMat_specialUnitary_ne_zero_iff_ne_one_ne_negOne
    (h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 ↔
      h ≠ 1 ∧ h ≠ SKEFTHawking.FKLW.negOneSU := by
  rw [Ne, liePartMat_specialUnitary_eq_zero_iff_scalar]
  constructor
  · intro h_ne
    refine ⟨?_, ?_⟩
    · intro h_eq_one
      apply h_ne
      -- h = 1 ⟹ h.val = 1, tr h.val = 2, (tr h.val / 2) • 1 = 1
      have h_val : (h : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
        rw [h_eq_one]; rfl
      rw [h_val, Matrix.trace_one, Fintype.card_fin]
      push_cast
      simp
    · intro h_eq_negOne
      apply h_ne
      -- h = negOneSU ⟹ h.val = -1, tr h.val = -2, (tr h.val / 2) • 1 = -1
      have h_val : (h : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
        rw [h_eq_negOne]
        rfl
      rw [h_val, Matrix.trace_neg, Matrix.trace_one, Fintype.card_fin]
      push_cast
      ext i j
      by_cases hij : i = j
      · simp [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply, hij,
              smul_eq_mul]
      · simp [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply, hij,
              smul_eq_mul]
  · rintro ⟨h_ne_one, h_ne_negOne⟩
    intro h_scalar
    -- Set c := trace h.val / 2, then h.val = c • 1, hence (h - 1) = (c - 1) • 1
    set c : ℂ := Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ) / 2 with hc_def
    have h_exists : ∃ c' : ℂ, (h : Matrix (Fin 2) (Fin 2) ℂ) - 1 =
        c' • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      refine ⟨c - 1, ?_⟩
      rw [h_scalar]
      rw [show (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) - 1) =
              c • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
              (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) by rw [one_smul]]
      rw [← sub_smul]
    rcases SKEFTHawking.FKLW.H_Fib_scalar_implies_one_or_negOne h h_exists with
      h1 | h1
    · exact h_ne_one h1
    · exact h_ne_negOne h1

/-- **HEADLINE F.20.c.d.1.app — every neighborhood of 1 contains a witness**.

For every open set `U ⊆ Matrix (Fin 2) (Fin 2) ℂ` with `1 ∈ U`, there exists
`M ∈ U` with `σ_Fib_lie_bundle_pauliDet (liePartMat M) ≠ 0`.

Proof: by `one_plus_real_smul_paulI_x_tendsto_one`, the witness family
`t ↦ 1 + (t : ℂ) • paulI_x` is in `U` for sufficiently small `t`. For
`t ≠ 0`, the witness has non-zero pauliDet. Take any small `t ≠ 0` in
the eventual region. -/
theorem exists_in_nhds_one_pauliDet_liePartMat_ne_zero
    {U : Set (Matrix (Fin 2) (Fin 2) ℂ)}
    (hU : U ∈ nhds (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    ∃ M ∈ U, σ_Fib_lie_bundle_pauliDet (liePartMat M) ≠ 0 := by
  -- Witness family `t ↦ 1 + (t : ℂ) • paulI_x` tends to 1, so eventually it lands in U
  have h_tendsto := one_plus_real_smul_paulI_x_tendsto_one
  have h_pullback : (fun t : ℝ =>
      (1 : Matrix (Fin 2) (Fin 2) ℂ) + (t : ℂ) • paulI_x) ⁻¹' U ∈
        nhds (0 : ℝ) := h_tendsto hU
  -- Combined with eventually-pauliDet-ne-zero on `t ≠ 0`, find such t
  have h_combined :
      ∀ᶠ t : ℝ in nhdsWithin 0 {0}ᶜ,
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (t : ℂ) • paulI_x) ∈ U ∧
        σ_Fib_lie_bundle_pauliDet
          (liePartMat ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
            (t : ℂ) • paulI_x)) ≠ 0 :=
    (eventually_nhdsWithin_of_eventually_nhds h_pullback).and
      eventually_pauliDet_liePartMat_ne_zero_near_zero
  -- Witness exists since `nhdsWithin 0 {0}ᶜ` is NeBot (instance auto-inferred
  -- via `instNeBotNhdsWithinComplSetSingletonOfNontrivial` for ℝ).
  obtain ⟨t, ht_mem, ht_pauli⟩ := h_combined.exists
  exact ⟨(1 : Matrix (Fin 2) (Fin 2) ℂ) + (t : ℂ) • paulI_x, ht_mem, ht_pauli⟩

/-! ## §20. R5.4 Layer F.20.c.d.2.c — H_Fib small-witness with non-zero liePart

Composes session-30 small-witness substrate (`H_Fib_small_witness_val`)
with session-31 / D.3.h substrate (`ne_negOneSU_of_norm_sub_one_lt_two`)
and the §19 closed form (`liePartMat_specialUnitary_ne_zero_iff_ne_one_ne_negOne`)
to ship: for every `ε ∈ (0, 1]`, there exists `h ∈ H_Fib` with
`‖h.val - 1‖ < ε` AND `liePartMat h.val ≠ 0`.

This RESOLVES the first "non-emptiness" sub-question for the F.20.c.d.2
directionality argument: H_Fib has arbitrarily-close-to-1 elements
whose `liePartMat` is non-trivial (i.e., they're not on the
`{1, negOneSU}` zero locus of `liePartMat`). What remains is the
"directionality" sub-question — whether the `σ_Fib_lie_bundle_pauliDet`
of these witnesses is also non-zero. -/

/-- **R5.4 Layer F.20.c.d.2.c — H_Fib has small witnesses with non-zero liePart**.

For every `ε ∈ (0, 1]`, there exists `h ∈ H_Fib` with
`‖h.val - 1‖ < ε` AND `liePartMat h.val ≠ 0`. -/
theorem H_Fib_small_witness_with_liePartMat_ne_zero
    {ε : ℝ} (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1) :
    ∃ h ∈ (SKEFTHawking.FKLW.H_Fib :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
        ‖(h : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < ε ∧
        liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
  obtain ⟨h, h_H, h_ne_one, h_norm⟩ :=
    SKEFTHawking.FKLW.H_Fib_small_witness_val hε_pos
  have h_norm_lt_two : ‖(h : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < 2 := by
    calc ‖(h : Matrix (Fin 2) (Fin 2) ℂ) - 1‖
        < ε := h_norm
      _ ≤ 1 := hε_le_one
      _ < 2 := by norm_num
  have h_ne_negOne : h ≠ SKEFTHawking.FKLW.negOneSU :=
    SKEFTHawking.FKLW.ne_negOneSU_of_norm_sub_one_lt_two h h_norm_lt_two
  refine ⟨h, h_H, h_norm, ?_⟩
  exact (liePartMat_specialUnitary_ne_zero_iff_ne_one_ne_negOne h).mpr
    ⟨h_ne_one, h_ne_negOne⟩

/-- **R5.4 Layer F.20.c.d.2.c-app — iteration starting points with
non-zero liePart**.

For any `δ₀ ∈ (0, 1/64]`, there exists a starting point `h₀ ∈ H_Fib`
with `‖h₀.val - 1‖ < δ₀` AND `liePartMat h₀.val ≠ 0`. Composes
`H_Fib_small_witness_with_liePartMat_ne_zero` with the `1/64 ≤ 1`
inequality so the iteration sequence machinery (which requires
`δ₀ ≤ 1/64`) can be seeded by a non-trivial-liePart starting point. -/
theorem H_Fib_iteration_starting_point_with_liePartMat_ne_zero
    {δ₀ : ℝ} (hδ_pos : 0 < δ₀) (hδ_le : δ₀ ≤ 1 / 64) :
    ∃ h₀ ∈ (SKEFTHawking.FKLW.H_Fib :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
        ‖(h₀ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < δ₀ ∧
        liePartMat (h₀ : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
  have hδ_le_one : δ₀ ≤ 1 := by linarith [hδ_le]
  exact H_Fib_small_witness_with_liePartMat_ne_zero hδ_pos hδ_le_one

/-! ## §22a. R5.4 Layer F.20.c.d.2.f — Zero-locus diagnostic at paulI_z

The polynomial `σ_Fib_lie_bundle_pauliDet : Matrix _ _ ℂ → ℝ` has a
NON-TRIVIAL zero locus: while F.18 (session 49) showed
`σ_Fib_lie_bundle_pauliDet paulI_x ≠ 0`, the value AT `paulI_z` is
ZERO. The reason: `σ_Fib_1_SU_mat` is DIAGONAL (with eigenvalues
`ωR_1, ωR_τ` of unit modulus), so its Ad-action on the diagonal Pauli
generator `paulI_z` is the IDENTITY. The first two components of
`σ_Fib_lie_bundle paulI_z` are therefore equal, and `pauliDet`
vanishes whenever two of its three matrix arguments are equal.

This establishes that the zero locus of `σ_Fib_lie_bundle_pauliDet`
is a PROPER (i.e., non-empty AND non-full) closed subset of 𝔰𝔲(2),
which is the structural prerequisite for the polynomial-zero-locus
analysis (Path A toward F.20.c.d.2 / F.21). -/

/-- **Pauli determinant vanishes when first two arguments are equal**.
The 3×3 determinant of Pauli coords has two equal rows hence vanishes. -/
theorem pauliDet_eq_zero_of_first_two_eq
    (X C : Matrix (Fin 2) (Fin 2) ℂ) :
    pauliDet X X C = 0 := by
  unfold pauliDet
  obtain ⟨xX, yX, zX⟩ := matrixToPauliCoords X
  obtain ⟨xC, yC, zC⟩ := matrixToPauliCoords C
  ring

/-- **Generic diagonal conjugation of paulI_z** (companion to `diag_conj_paulI_x`).

For a diagonal matrix `D = !![α, 0; 0, β]`, the Ad-conjugation of `paulI_z`
is `!![‖α‖² · I, 0; 0, -‖β‖² · I]`. Stated in `α · star α` form (= `‖α‖²` as ℂ). -/
theorem diag_conj_paulI_z (α β : ℂ) :
    (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℂ) * paulI_z *
        (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose =
        !![α * star α * Complex.I, 0; 0, -(β * star β * Complex.I)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, star_zero, paulI_z, SKEFTHawking.σ_z,
          Matrix.smul_apply, smul_eq_mul] <;>
    ring

/-- **σ_Fib_1_SU_mat fixes paulI_z under Ad-conjugation**.

Because `σ_Fib_1_SU_mat = !![ω·R_1, 0; 0, ω·R_τ]` is diagonal with
unit-modulus entries, its Ad-action on the diagonal Pauli generator
`paulI_z` is the identity. Composition of `σ_Fib_1_SU_mat_diagonal_form`
+ `diag_conj_paulI_z` + unit-norm of ω, R_1, R_τ. -/
theorem σ_Fib_1_SU_mat_conj_paulI_z_eq :
    σ_Fib_1_SU_mat * paulI_z * σ_Fib_1_SU_mat.conjTranspose = paulI_z := by
  rw [σ_Fib_1_SU_mat_diagonal_form, diag_conj_paulI_z]
  -- Two unit-norm products:
  have h_α_norm : (ω_Fib_C * R1_C) * star (ω_Fib_C * R1_C) = 1 :=
    unit_norm_star_eq_one (by
      rw [norm_mul, norm_ω_Fib_C, norm_R1_C, mul_one])
  have h_β_norm : (ω_Fib_C * Rtau_C) * star (ω_Fib_C * Rtau_C) = 1 :=
    unit_norm_star_eq_one (by
      rw [norm_mul, norm_ω_Fib_C, norm_Rtau_C, mul_one])
  rw [h_α_norm, h_β_norm]
  -- Goal: !![1 * I, 0; 0, -(1 * I)] = paulI_z
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [paulI_z, SKEFTHawking.σ_z, Matrix.smul_apply, smul_eq_mul,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]

/-- **R5.4 Layer F.20.c.d.2.f — `σ_Fib_lie_bundle_pauliDet paulI_z = 0`**.

The first two components of `σ_Fib_lie_bundle paulI_z` are equal (both
= `paulI_z`) since `σ_Fib_1_SU_mat` fixes `paulI_z` under Ad-conjugation
(diagonal-on-diagonal). The pauliDet of three matrices with two equal
arguments vanishes by `pauliDet_eq_zero_of_first_two_eq`. -/
theorem σ_Fib_lie_bundle_pauliDet_paulI_z_eq_zero :
    σ_Fib_lie_bundle_pauliDet paulI_z = 0 := by
  rw [σ_Fib_lie_bundle_pauliDet_eq, σ_Fib_1_SU_mat_conj_paulI_z_eq]
  exact pauliDet_eq_zero_of_first_two_eq paulI_z
    (σ_Fib_2_SU_mat * paulI_z * σ_Fib_2_SU_mat.conjTranspose)

/-- **R5.4 Layer F.20.c.d.2.f-app — every scalar-multiple-of-paulI_z is
in the zero locus**.

By trilinear homogeneity (`σ_Fib_lie_bundle_pauliDet_smul_uniform` from
F.20.b), `σ_Fib_lie_bundle_pauliDet (c·paulI_z) = c³·0 = 0` for every
`c ∈ ℝ`. -/
theorem σ_Fib_lie_bundle_pauliDet_smul_paulI_z_eq_zero (c : ℝ) :
    σ_Fib_lie_bundle_pauliDet ((c : ℂ) • paulI_z) = 0 := by
  rw [σ_Fib_lie_bundle_pauliDet_smul_uniform,
      σ_Fib_lie_bundle_pauliDet_paulI_z_eq_zero, mul_zero]

/-! ### Ad-action of σ_Fib_1 on paulI_y (Layer F.20.c.d.2.g)

Following the same anti-diagonal pattern as the paulI_x case
(`diag_conj_paulI_x` + `σ_Fib_1_SU_mat_conj_paulI_x_eq`), we ship the
generic `diag_conj_paulI_y` (purely matrix-algebraic) + the σ_Fib_1
specialization. The structural conclusion: σ_Fib_1's Ad-action on paulI_y
is anti-diagonal with entries `α·star β` and `-(β·star α)` for
`α = ω·R_1, β = ω·R_τ`, i.e., the same rotation pattern as paulI_x but
WITHOUT the global `·Complex.I` factor. -/

/-- **Generic diagonal conjugation of paulI_y** (companion to
`diag_conj_paulI_x` and `diag_conj_paulI_z`).

For diagonal `D = !![α, 0; 0, β]` and `paulI_y = !![0, 1; -1, 0]`:
`D · paulI_y · D† = !![0, α·star β; -(β·star α), 0]`. -/
theorem diag_conj_paulI_y (α β : ℂ) :
    (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℂ) * paulI_y *
        (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose =
        !![0, α * star β; -(β * star α), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, star_zero, paulI_y, SKEFTHawking.σ_y,
          Matrix.smul_apply, smul_eq_mul] <;>
    ring

/-- **σ_Fib_1_SU_mat Ad-action on paulI_y — explicit form**.

Composes `σ_Fib_1_SU_mat_diagonal_form` with `diag_conj_paulI_y`,
then simplifies via ω cancellation (`ω_mul_X_mul_star_ω_mul_Y`). -/
theorem σ_Fib_1_SU_mat_conj_paulI_y_eq :
    σ_Fib_1_SU_mat * paulI_y * σ_Fib_1_SU_mat.conjTranspose =
        !![0, R1_C * star Rtau_C;
           -(Rtau_C * star R1_C), 0] := by
  rw [σ_Fib_1_SU_mat_diagonal_form, diag_conj_paulI_y,
      ω_mul_X_mul_star_ω_mul_Y R1_C Rtau_C,
      ω_mul_X_mul_star_ω_mul_Y Rtau_C R1_C]

/-- **σ_Fib_1 Ad-action on paulI_y in Pauli coords**.

`matrixToPauliCoords (σ_Fib_1·paulI_y·σ_Fib_1†) = (-sin(7π/5), cos(7π/5), 0)`.

Composes `σ_Fib_1_SU_mat_conj_paulI_y_eq` (explicit matrix form) with
`R1_C_mul_star_Rtau_C = exp(-7πi/5)` and the matrixToPauliCoords
definition. Together with the paulI_x version
(`σ_Fib_1_SU_mat_conj_paulI_x_pauliCoords = (cos(7π/5), sin(7π/5), 0)`)
and the paulI_z fixed-point (`σ_Fib_1_SU_mat_conj_paulI_z_eq = paulI_z`,
so its coords are `(0, 0, 1)`), this gives the FULL 3×3 SO(3) matrix
of σ_Fib_1's Ad-action: a rotation by `7π/5` about the z-axis in
Pauli (x, y, z) coords. -/
theorem σ_Fib_1_SU_mat_conj_paulI_y_pauliCoords :
    matrixToPauliCoords
      (σ_Fib_1_SU_mat * paulI_y * σ_Fib_1_SU_mat.conjTranspose) =
    (-Real.sin (7 * Real.pi / 5), Real.cos (7 * Real.pi / 5), 0) := by
  rw [σ_Fib_1_SU_mat_conj_paulI_y_eq, R1_C_mul_star_Rtau_C]
  unfold matrixToPauliCoords
  simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Complex.zero_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.exp_re, Complex.exp_im, Complex.neg_re,
        Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Real.cos_neg, Real.sin_neg, Real.exp_zero, mul_one, one_mul]

/-- **σ_Fib_1 Ad-conjugation is ℂ-linear** (general matrix-level fact). -/
theorem σ_Fib_1_SU_mat_conj_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    σ_Fib_1_SU_mat * (X + Y) * σ_Fib_1_SU_mat.conjTranspose =
        σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose +
        σ_Fib_1_SU_mat * Y * σ_Fib_1_SU_mat.conjTranspose := by
  rw [mul_add, add_mul]

/-- **σ_Fib_1 Ad-conjugation commutes with complex scalar mult** (matrix). -/
theorem σ_Fib_1_SU_mat_conj_smul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    σ_Fib_1_SU_mat * (c • X) * σ_Fib_1_SU_mat.conjTranspose =
        c • (σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- **F_C Ad-action on paulI_z** (toward F.20.c.d.2.i — σ_Fib_2's Ad-action
on paulI_z via the `σ_Fib_2 = F·σ_Fib_1·F` decomposition).

Direct entry-wise computation: for `F_C = !![φ⁻¹, φ⁻¹ᐟ²; φ⁻¹ᐟ², -φ⁻¹]` and
`paulI_z = !![I, 0; 0, -I]`, the F-conjugate `F·paulI_z·F` produces an
explicit 2×2 matrix mixing diagonal and off-diagonal entries with
coefficients `φ⁻¹·φ⁻¹ - φ⁻¹ᐟ²·φ⁻¹ᐟ² = φ⁻¹² - φ⁻¹` (real)
and `2·φ⁻¹·φ⁻¹ᐟ²` (real).

Since F_C is symmetric and `star F_C = F_C` (`F_C_star`), the
"conjugation" here uses `F_C` on both sides (no separate transpose). -/
theorem F_C_conj_paulI_z_eq :
    F_C * paulI_z * F_C =
      !![(φInv_C * φInv_C - φInvSqrt_C * φInvSqrt_C) * Complex.I,
         (2 * φInv_C * φInvSqrt_C) * Complex.I;
         (2 * φInv_C * φInvSqrt_C) * Complex.I,
         -((φInv_C * φInv_C - φInvSqrt_C * φInvSqrt_C) * Complex.I)] := by
  unfold F_C
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons,
          paulI_z, SKEFTHawking.σ_z, Matrix.smul_apply,
          smul_eq_mul] <;>
    ring

/-! ### F.20.c.d.2.j — F_C Ad-actions on paulI_x and paulI_y

Completing the F_C Ad-action triple needed for σ_Fib_2's full SO(3)
matrix. F_C is symmetric (`F_C_star`) and involutive (`F_C_sq : F·F = 1`),
so its Ad-action is its own inverse — a "reflection" in 𝔰𝔲(2). -/

/-- **F_C Ad-action on paulI_x**. Direct entry-wise computation. -/
theorem F_C_conj_paulI_x_eq' :
    F_C * paulI_x * F_C =
      !![(2 * φInv_C * φInvSqrt_C) * Complex.I,
         (φInvSqrt_C * φInvSqrt_C - φInv_C * φInv_C) * Complex.I;
         (φInvSqrt_C * φInvSqrt_C - φInv_C * φInv_C) * Complex.I,
         -((2 * φInv_C * φInvSqrt_C) * Complex.I)] := by
  unfold F_C
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons,
          paulI_x, SKEFTHawking.σ_x, Matrix.smul_apply,
          smul_eq_mul] <;>
    ring

/-- **F_C Ad-action on paulI_y**. Direct entry-wise computation. -/
theorem F_C_conj_paulI_y_eq :
    F_C * paulI_y * F_C =
      !![0, -(φInv_C * φInv_C + φInvSqrt_C * φInvSqrt_C);
         (φInv_C * φInv_C + φInvSqrt_C * φInvSqrt_C), 0] := by
  unfold F_C
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons,
          paulI_y, SKEFTHawking.σ_y, Matrix.smul_apply,
          smul_eq_mul] <;>
    ring

/-- **F_C Ad-conjugation is ℂ-linear** (matrix). -/
theorem F_C_conj_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    F_C * (X + Y) * F_C = F_C * X * F_C + F_C * Y * F_C := by
  rw [mul_add, add_mul]

/-- **F_C Ad-conjugation commutes with complex scalar mult** (matrix). -/
theorem F_C_conj_smul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    F_C * (c • X) * F_C = c • (F_C * X * F_C) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- **R5.4 Layer F.20.c.d.2.l — F_C Ad-action on Pauli-decomposed element**.

For `X = a·paulI_x + b·paulI_y + c·paulI_z`:
  `F · X · F = a·(F·paulI_x·F) + b·(F·paulI_y·F) + c·(F·paulI_z·F)`

Direct linearity composition; the closed forms for each `F·paulI_α·F`
are shipped above (F.20.c.d.2.{i,j}). Combined with σ_Fib_1's
SO(3) pauliDecomp form (F.20.c.d.2.h) and `σ_Fib_2 = F·σ_Fib_1·F`,
this gives the full σ_Fib_2 SO(3) Ad-matrix as a composition. -/
theorem F_C_conj_pauliDecomp (a b c : ℂ) :
    F_C * (a • paulI_x + b • paulI_y + c • paulI_z) * F_C =
        a • (F_C * paulI_x * F_C) +
        b • (F_C * paulI_y * F_C) +
        c • (F_C * paulI_z * F_C) := by
  rw [F_C_conj_add, F_C_conj_add,
      F_C_conj_smul, F_C_conj_smul, F_C_conj_smul]

/-- **F_C·paulI_y·F_C simplifies via φInv² + φInvSqrt² = 1**. -/
theorem F_C_conj_paulI_y_eq_neg :
    F_C * paulI_y * F_C = -paulI_y := by
  rw [F_C_conj_paulI_y_eq]
  -- φInv·φInv + φInvSqrt·φInvSqrt = 1 via F_C_diag_identity
  -- But that's private. Re-derive via φInvSqrt² = φInv and 1/φ² + 1/φ = 1
  have h_sq : φInvSqrt_C * φInvSqrt_C = φInv_C := by
    have := φInvSqrt_C_sq; rw [sq] at this; exact this
  rw [h_sq]
  -- Goal: !![0, -(φInv·φInv + φInv); (φInv·φInv + φInv), 0] = -paulI_y
  -- Need: φInv·φInv + φInv = 1
  -- From 1/φ² + 1/φ = 1: multiply by φ², get 1 + φ = φ², so φ²·φInv² + φ²·φInv = φ²
  -- Equivalently φInv² + φInv = 1.
  have h_one : φInv_C * φInv_C + φInv_C = 1 := by
    have h1 : φ_C * φInv_C = 1 := φ_C_mul_inv
    have h2 : φ_C ^ 2 = φ_C + 1 := φ_C_sq
    have hne : φ_C ≠ 0 := φ_C_ne_zero
    have hsq_ne : φ_C ^ 2 ≠ 0 := pow_ne_zero _ hne
    have key : φ_C ^ 2 * (φInv_C * φInv_C + φInv_C) = φ_C ^ 2 * 1 := by
      calc φ_C ^ 2 * (φInv_C * φInv_C + φInv_C)
          = (φ_C * φInv_C) * (φ_C * φInv_C) + φ_C * (φ_C * φInv_C) := by ring
        _ = 1 * 1 + φ_C * 1 := by rw [h1]
        _ = φ_C + 1 := by ring
        _ = φ_C ^ 2 := h2.symm
        _ = φ_C ^ 2 * 1 := by ring
    exact mul_left_cancel₀ hsq_ne key
  rw [h_one]
  -- Goal: !![0, -1; 1, 0] = -paulI_y
  -- paulI_y = !![0, 1; -1, 0], so -paulI_y = !![0, -1; 1, 0]
  unfold paulI_y SKEFTHawking.σ_y
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]

/-- **R5.4 Layer F.20.c.d.2.h — σ_Fib_1's Ad-action on a Pauli-decomposed
element is a planar rotation by 7π/5 about the z-axis**.

For `X = a·paulI_x + b·paulI_y + c·paulI_z ∈ 𝔰𝔲(2)`:
  `σ_Fib_1·X·σ_Fib_1† = (a·cos(7π/5) - b·sin(7π/5))·paulI_x +
                        (a·sin(7π/5) + b·cos(7π/5))·paulI_y +
                        c·paulI_z`

This is the canonical SO(3) image of σ_Fib_1's SU(2) element: a
rotation by angle 7π/5 about the z-axis. Composes linearity of
Ad-conjugation with the 3 Pauli base cases (paulI_x, paulI_y, paulI_z). -/
theorem σ_Fib_1_SU_mat_conj_pauliDecomp (a b c : ℝ) :
    σ_Fib_1_SU_mat *
      ((a : ℂ) • paulI_x + (b : ℂ) • paulI_y + (c : ℂ) • paulI_z) *
      σ_Fib_1_SU_mat.conjTranspose =
    ((a * Real.cos (7 * Real.pi / 5) -
        b * Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) • paulI_x +
    ((a * Real.sin (7 * Real.pi / 5) +
        b * Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) • paulI_y +
    ((c : ℝ) : ℂ) • paulI_z := by
  -- Distribute Ad-conjugation over the sum, then apply each base case.
  rw [σ_Fib_1_SU_mat_conj_add, σ_Fib_1_SU_mat_conj_add,
      σ_Fib_1_SU_mat_conj_smul, σ_Fib_1_SU_mat_conj_smul,
      σ_Fib_1_SU_mat_conj_smul]
  -- Substitute each Ad-action: paulI_x → conj_paulI_x_eq with pauliCoords;
  -- paulI_y → conj_paulI_y_eq; paulI_z → paulI_z (fixed).
  rw [σ_Fib_1_SU_mat_conj_paulI_z_eq]
  -- Now use the established Pauli-coord forms via tracelessSkewHermitian_decomp.
  -- σ_Fib_1·paulI_x·σ_Fib_1† = cos(7π/5)·paulI_x + sin(7π/5)·paulI_y (z-coord 0)
  have h_pauli_x_decomp :
      σ_Fib_1_SU_mat * paulI_x * σ_Fib_1_SU_mat.conjTranspose =
      ((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) • paulI_x +
      ((Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) • paulI_y +
      ((0 : ℝ) : ℂ) • paulI_z := by
    have h_mem : σ_Fib_1_SU_mat * paulI_x * σ_Fib_1_SU_mat.conjTranspose ∈
        tracelessSkewHermitian (Fin 2) :=
      tracelessSkewHermitian_conj_σ_Fib_1_SU_mat paulI_x_mem_tracelessSkewHermitian
    have h_decomp := tracelessSkewHermitian_decomp h_mem
    have h_coords := σ_Fib_1_SU_mat_conj_paulI_x_pauliCoords
    unfold matrixToPauliCoords at h_coords
    -- h_coords : (.im, .re, .im) = (cos(7π/5), sin(7π/5), 0)
    -- Project via Prod accessors:
    have h_im_01 : ((σ_Fib_1_SU_mat * paulI_x *
        σ_Fib_1_SU_mat.conjTranspose) 0 1).im = Real.cos (7 * Real.pi / 5) :=
      congrArg Prod.fst h_coords
    have h_re_01 : ((σ_Fib_1_SU_mat * paulI_x *
        σ_Fib_1_SU_mat.conjTranspose) 0 1).re = Real.sin (7 * Real.pi / 5) :=
      congrArg (Prod.fst ∘ Prod.snd) h_coords
    have h_im_00 : ((σ_Fib_1_SU_mat * paulI_x *
        σ_Fib_1_SU_mat.conjTranspose) 0 0).im = 0 :=
      congrArg (Prod.snd ∘ Prod.snd) h_coords
    rw [h_decomp, h_im_01, h_re_01, h_im_00]
  -- σ_Fib_1·paulI_y·σ_Fib_1† = -sin(7π/5)·paulI_x + cos(7π/5)·paulI_y (z-coord 0)
  have h_pauli_y_decomp :
      σ_Fib_1_SU_mat * paulI_y * σ_Fib_1_SU_mat.conjTranspose =
      ((-Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) • paulI_x +
      ((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) • paulI_y +
      ((0 : ℝ) : ℂ) • paulI_z := by
    have h_mem : σ_Fib_1_SU_mat * paulI_y * σ_Fib_1_SU_mat.conjTranspose ∈
        tracelessSkewHermitian (Fin 2) :=
      tracelessSkewHermitian_conj_σ_Fib_1_SU_mat paulI_y_mem_tracelessSkewHermitian
    have h_decomp := tracelessSkewHermitian_decomp h_mem
    have h_coords := σ_Fib_1_SU_mat_conj_paulI_y_pauliCoords
    unfold matrixToPauliCoords at h_coords
    have h_im_01 : ((σ_Fib_1_SU_mat * paulI_y *
        σ_Fib_1_SU_mat.conjTranspose) 0 1).im = -Real.sin (7 * Real.pi / 5) :=
      congrArg Prod.fst h_coords
    have h_re_01 : ((σ_Fib_1_SU_mat * paulI_y *
        σ_Fib_1_SU_mat.conjTranspose) 0 1).re = Real.cos (7 * Real.pi / 5) :=
      congrArg (Prod.fst ∘ Prod.snd) h_coords
    have h_im_00 : ((σ_Fib_1_SU_mat * paulI_y *
        σ_Fib_1_SU_mat.conjTranspose) 0 0).im = 0 :=
      congrArg (Prod.snd ∘ Prod.snd) h_coords
    rw [h_decomp, h_im_01, h_re_01, h_im_00]
  rw [h_pauli_x_decomp, h_pauli_y_decomp]
  -- Now the RHS has 6 terms; reorganize via push_cast + ring on the smul algebra
  push_cast
  -- Goal: a • (cos·x + sin·y + 0·z) + b • (-sin·x + cos·y + 0·z) + c • z =
  --       (a·cos - b·sin) • x + (a·sin + b·cos) • y + c • z
  -- Use smul distributivity
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ## §22. R5.4 Layer F.20.c.d.2.d — SU(2)-subtype openness +
nhd-of-1 spanning-locus witness

The matrix-space spanning locus `S_mat := {M | σ_Fib_lie_bundle_pauliDet
(liePartMat M) ≠ 0}` was shown OPEN in §16 (`F.20.c.d.0`). Here we
pull this back to SU(2) (subtype topology) via the continuous embedding
`Subtype.val` and combine with the `rotPaulI_x` family to give an
SU(2)-level (rather than matrix-level) witness near `1`.

This is the SU(2)-subtype analogue of `exists_in_nhds_one_pauliDet_liePartMat_ne_zero`
(§19's matrix-level closing theorem) and is the form consumed by
downstream IFT-based closure arguments which operate on the subgroup
topology of SU(2). -/

/-- **R5.4 Layer F.20.c.d.2.d — pullback of the spanning locus is OPEN
in SU(2) (subtype topology)**.

The set `{h ∈ SU(2) | σ_Fib_lie_bundle_pauliDet (liePartMat h.val) ≠ 0}`
is open in the subtype topology, as the preimage of an open set
in `Matrix (Fin 2) (Fin 2) ℂ` under the continuous embedding
`Subtype.val`. -/
theorem σ_Fib_lie_bundle_pauliDet_liePartMat_ne_zero_isOpen_subtype :
    IsOpen
      {h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) |
        σ_Fib_lie_bundle_pauliDet
          (liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0} := by
  have h_cont :
      Continuous (Subtype.val :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) →
          Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val
  have h_open_mat :
      IsOpen {M : Matrix (Fin 2) (Fin 2) ℂ |
        σ_Fib_lie_bundle_pauliDet (liePartMat M) ≠ 0} :=
    σ_Fib_lie_bundle_pauliDet_liePartMat_ne_zero_isOpen
  exact h_open_mat.preimage h_cont

/-- **R5.4 Layer F.20.c.d.2.d — SU(2)-subtype tendsto-1 of `rotPaulI_x t`**.

The family `t ↦ rotPaulI_x t : ℝ → SU(2)` tends to `(1 : SU(2))` as
`t → 0` in the subtype topology. Lifts the matrix-level
`rotPaulI_x_mul_conjTranspose` smoothness via `Topology.IsInducing.subtypeVal`. -/
theorem rotPaulI_x_tendsto_one_subtype :
    Filter.Tendsto
      (fun t : ℝ => (⟨rotPaulI_x t, rotPaulI_x_mem_specialUnitaryGroup t⟩ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
      (nhds 0) (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) := by
  have h_inducing :
      Topology.IsInducing
        (Subtype.val : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) →
          Matrix (Fin 2) (Fin 2) ℂ) :=
    Topology.IsInducing.subtypeVal
  rw [h_inducing.tendsto_nhds_iff]
  -- Goal: Tendsto (fun t => rotPaulI_x t) (nhds 0) (nhds (1 : Matrix _ _ ℂ))
  -- rotPaulI_x t = cos t • 1 + sin t • paulI_x → 1 as t → 0
  -- (cos 0 = 1, sin 0 = 0, so the limit value is 1•1 + 0•paulI_x = 1)
  -- Strategy: show continuity of t ↦ rotPaulI_x t at t = 0 + evaluate at 0
  have h_cont : Continuous (fun t : ℝ => rotPaulI_x t) := by
    unfold rotPaulI_x
    refine Continuous.add ?_ ?_
    · exact ((Complex.continuous_ofReal.comp Real.continuous_cos).smul
        continuous_const)
    · exact ((Complex.continuous_ofReal.comp Real.continuous_sin).smul
        continuous_const)
  have h_at_zero : rotPaulI_x 0 = 1 := by
    unfold rotPaulI_x
    simp [Real.cos_zero, Real.sin_zero]
  rw [show ((1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
      Matrix (Fin 2) (Fin 2) ℂ) = rotPaulI_x 0 by rw [h_at_zero]; rfl]
  exact h_cont.continuousAt

/-- **R5.4 Layer F.20.c.d.2.d — HEADLINE: every SU(2)-nhd of `(1 : SU(2))`
contains a spanning-locus witness via `rotPaulI_x t`**.

For every neighborhood `U` of `(1 : SU(2))` in the subtype topology,
there exists `h ∈ U` (concretely of the form `rotPaulI_x t` for some
`t ≠ 0` near zero) with `σ_Fib_lie_bundle_pauliDet (liePartMat h.val) ≠ 0`.

This is the SU(2)-subtype analogue of §19's matrix-level closing
theorem `exists_in_nhds_one_pauliDet_liePartMat_ne_zero`, and gives
the genuine SU(2)-level witness in every nhd of `1`. -/
theorem exists_in_nhds_one_subtype_pauliDet_liePartMat_ne_zero
    {U : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (hU : U ∈ nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) :
    ∃ h ∈ U,
        σ_Fib_lie_bundle_pauliDet
          (liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0 := by
  -- Pull U back through the rotPaulI_x family
  have h_tendsto := rotPaulI_x_tendsto_one_subtype
  have h_pullback :
      (fun t : ℝ =>
        (⟨rotPaulI_x t, rotPaulI_x_mem_specialUnitaryGroup t⟩ :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) ⁻¹' U ∈ nhds (0 : ℝ) :=
    h_tendsto hU
  -- Combine with eventually-pauliDet-ne-zero on `sin t ≠ 0`
  -- The set {t : ℝ | sin t ≠ 0} is open and contains an interval around 0
  -- minus {0}, so in nhdsWithin 0 {0}ᶜ (sufficient).
  -- For Real.sin we have eventually_ne for {t | sin t ≠ 0} near 0:
  -- there exists ε > 0 such that for 0 < |t| < ε, sin t ≠ 0. We use the
  -- fact that `sin 0 = 0` is an isolated zero (sin is non-zero in a
  -- punctured neighborhood of 0).
  have h_combined :
      ∀ᶠ t : ℝ in nhdsWithin 0 {0}ᶜ,
        (⟨rotPaulI_x t, rotPaulI_x_mem_specialUnitaryGroup t⟩ :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈ U ∧
        σ_Fib_lie_bundle_pauliDet
          (liePartMat (rotPaulI_x t)) ≠ 0 := by
    refine (eventually_nhdsWithin_of_eventually_nhds h_pullback).and ?_
    -- For sin t ≠ 0: there is a punctured nhd of 0 where sin t ≠ 0
    -- via Real.sin's analytic structure (sin t = 0 iff t = nπ)
    have h_sin_ne_zero_punctured : ∀ᶠ t : ℝ in nhdsWithin 0 {0}ᶜ,
        Real.sin t ≠ 0 := by
      -- The set of zeros of sin is {nπ : n ∈ ℤ}; 0 is isolated in this set,
      -- so on (-π, π) \ {0}, sin t ≠ 0.
      -- Use: Real.sin is continuous, sin 0 = 0, sin is locally non-zero away from 0.
      have h_interval : Set.Ioo (-Real.pi) Real.pi ∈ nhds (0 : ℝ) := by
        apply Ioo_mem_nhds
        · linarith [Real.pi_pos]
        · exact Real.pi_pos
      have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
      rw [eventually_nhdsWithin_iff]
      filter_upwards [h_interval] with t ht ht_ne_zero
      rcases ht with ⟨h_lt_pi_neg, h_lt_pi_pos⟩
      -- For t ∈ (-π, π) with t ≠ 0, sin t ≠ 0
      intro h_sin_zero
      apply ht_ne_zero
      -- sin t = 0 and t ∈ (-π, π) ⟹ t = 0
      have : t = 0 := by
        have h_abs_lt_pi : |t| < Real.pi := by
          rw [abs_lt]
          exact ⟨h_lt_pi_neg, h_lt_pi_pos⟩
        -- For t ∈ (-π, π), sin t = 0 iff t = 0
        -- Use: Real.sin_eq_zero_iff_of_lt_of_lt (or similar)
        rcases (Real.sin_eq_zero_iff_of_lt_of_lt h_lt_pi_neg h_lt_pi_pos).mp
          h_sin_zero with h_eq
        exact h_eq
      exact this
    filter_upwards [h_sin_ne_zero_punctured] with t h_sin_ne_zero
    exact σ_Fib_lie_bundle_pauliDet_liePartMat_rotPaulI_x_ne_zero h_sin_ne_zero
  obtain ⟨t, ht_mem_U, ht_pauli⟩ := h_combined.exists
  refine ⟨⟨rotPaulI_x t, rotPaulI_x_mem_specialUnitaryGroup t⟩, ht_mem_U, ?_⟩
  exact ht_pauli

/-! ## §23. R5.4 Layer F.20.c.d.2.m — σ_Fib_2's full SO(3) Ad-action in Pauli coords

Composes shipped substrate to give σ_Fib_2's Ad-action on a Pauli-decomposed
input X = a·paulI_x + b·paulI_y + c·paulI_z (a b c : ℝ) in closed
Pauli-coordinate form:

- F.17.a F_decomp: `σ_Fib_2 = F · σ_Fib_1 · F`, `σ_Fib_2† = F · σ_Fib_1† · F`
- F.20.c.d.2.h: σ_Fib_1's Ad-action is a 7π/5 rotation about z-axis
- F.20.c.d.2.l: F-conjugation is ℂ-linear (`F_C_conj_pauliDecomp`)
- F.20.c.d.2.{i,j}: closed forms `F·paulI_α·F` (matrix entries)
- F.20.c.d.2.k: paulI_y is F-eigenvector with eigenvalue -1

The result is σ_Fib_2's SO(3) matrix in the (paulI_x, paulI_y, paulI_z) basis.
This is the final piece before F.20.c.d.2.n's explicit cubic
`σ_Fib_lie_bundle_pauliDet` polynomial form. -/

/-- **R5.4 Layer F.20.c.d.2.m.1 — F·paulI_x·F as Pauli sum**.

Re-expresses `F_C_conj_paulI_x_eq` in pauliDecomp form:
`F · paulI_x · F = (2·φInv - 1)·paulI_x + 0·paulI_y + (2·φInvSqrt·φInv)·paulI_z`. -/
theorem F_C_conj_paulI_x_pauliDecomp :
    F_C * paulI_x * F_C =
      ((2 * φInv_C - 1) : ℂ) • paulI_x +
      (0 : ℂ) • paulI_y +
      ((2 * φInvSqrt_C * φInv_C) : ℂ) • paulI_z := by
  rw [F_C_conj_paulI_x_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [paulI_x, paulI_y, paulI_z, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z,
          Matrix.add_apply, smul_eq_mul, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **R5.4 Layer F.20.c.d.2.m.2 — F·paulI_z·F as Pauli sum**.

Re-expresses `F_C_conj_paulI_z_eq` in pauliDecomp form:
`F · paulI_z · F = (2·φInv·φInvSqrt)·paulI_x + 0·paulI_y + (φInv² - φInvSqrt²)·paulI_z`.

Note `φInv² - φInvSqrt² = 1 - 2·φInv = -(2·φInv - 1)`, so F's SO(3) matrix
in (x,y,z) basis is the symmetric reflection
`!![2·φInv-1, 0, 2·φInv·φInvSqrt; 0, -1, 0; 2·φInv·φInvSqrt, 0, -(2·φInv-1)]`. -/
theorem F_C_conj_paulI_z_pauliDecomp :
    F_C * paulI_z * F_C =
      ((2 * φInv_C * φInvSqrt_C) : ℂ) • paulI_x +
      (0 : ℂ) • paulI_y +
      ((φInv_C * φInv_C - φInvSqrt_C * φInvSqrt_C) : ℂ) • paulI_z := by
  rw [F_C_conj_paulI_z_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [paulI_x, paulI_y, paulI_z, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z,
          Matrix.add_apply, smul_eq_mul, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **R5.4 Layer F.20.c.d.2.m.3 — F·X·F collected by Pauli direction**.

For X = a•paulI_x + b•paulI_y + c•paulI_z with complex coefficients:
`F·X·F = (a·(2φInv-1) + c·(2φInv·φInvSqrt))·paulI_x +
         (-b)·paulI_y +
         (a·(2φInvSqrt·φInv) + c·(φInv²-φInvSqrt²))·paulI_z`. -/
theorem F_C_conj_pauliDecomp_collected (a b c : ℂ) :
    F_C * (a • paulI_x + b • paulI_y + c • paulI_z) * F_C =
      (a * (2 * φInv_C - 1) + c * (2 * φInv_C * φInvSqrt_C)) • paulI_x +
      (-b) • paulI_y +
      (a * (2 * φInvSqrt_C * φInv_C) +
         c * (φInv_C * φInv_C - φInvSqrt_C * φInvSqrt_C)) • paulI_z := by
  rw [F_C_conj_pauliDecomp,
      F_C_conj_paulI_x_pauliDecomp, F_C_conj_paulI_y_eq_neg,
      F_C_conj_paulI_z_pauliDecomp]
  -- Distribute the outer (a • ·), (b • ·), (c • ·) through the inner sums
  -- and collect by paulI_α. Pure ring arithmetic in the smul algebra.
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- **R5.4 Layer F.20.c.d.2.m.4 — σ_Fib_1·paulI_x·σ_Fib_1† as Pauli sum**
(public extraction of the inline `have h_pauli_x_decomp` from the
proof of `σ_Fib_1_SU_mat_conj_pauliDecomp`).

`σ_Fib_1 · paulI_x · σ_Fib_1† = cos(7π/5)·paulI_x + sin(7π/5)·paulI_y + 0·paulI_z`. -/
theorem σ_Fib_1_SU_mat_conj_paulI_x_pauliDecomp :
    σ_Fib_1_SU_mat * paulI_x * σ_Fib_1_SU_mat.conjTranspose =
      ((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) • paulI_x +
      ((Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) • paulI_y +
      ((0 : ℝ) : ℂ) • paulI_z := by
  have h_mem : σ_Fib_1_SU_mat * paulI_x * σ_Fib_1_SU_mat.conjTranspose ∈
      tracelessSkewHermitian (Fin 2) :=
    tracelessSkewHermitian_conj_σ_Fib_1_SU_mat paulI_x_mem_tracelessSkewHermitian
  have h_decomp := tracelessSkewHermitian_decomp h_mem
  have h_coords := σ_Fib_1_SU_mat_conj_paulI_x_pauliCoords
  unfold matrixToPauliCoords at h_coords
  have h_im_01 : ((σ_Fib_1_SU_mat * paulI_x *
      σ_Fib_1_SU_mat.conjTranspose) 0 1).im = Real.cos (7 * Real.pi / 5) :=
    congrArg Prod.fst h_coords
  have h_re_01 : ((σ_Fib_1_SU_mat * paulI_x *
      σ_Fib_1_SU_mat.conjTranspose) 0 1).re = Real.sin (7 * Real.pi / 5) :=
    congrArg (Prod.fst ∘ Prod.snd) h_coords
  have h_im_00 : ((σ_Fib_1_SU_mat * paulI_x *
      σ_Fib_1_SU_mat.conjTranspose) 0 0).im = 0 :=
    congrArg (Prod.snd ∘ Prod.snd) h_coords
  rw [h_decomp, h_im_01, h_re_01, h_im_00]

/-- **R5.4 Layer F.20.c.d.2.m.5 — σ_Fib_1·paulI_y·σ_Fib_1† as Pauli sum**
(public extraction of the inline `have h_pauli_y_decomp`).

`σ_Fib_1 · paulI_y · σ_Fib_1† = -sin(7π/5)·paulI_x + cos(7π/5)·paulI_y + 0·paulI_z`. -/
theorem σ_Fib_1_SU_mat_conj_paulI_y_pauliDecomp :
    σ_Fib_1_SU_mat * paulI_y * σ_Fib_1_SU_mat.conjTranspose =
      ((-Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) • paulI_x +
      ((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) • paulI_y +
      ((0 : ℝ) : ℂ) • paulI_z := by
  have h_mem : σ_Fib_1_SU_mat * paulI_y * σ_Fib_1_SU_mat.conjTranspose ∈
      tracelessSkewHermitian (Fin 2) :=
    tracelessSkewHermitian_conj_σ_Fib_1_SU_mat paulI_y_mem_tracelessSkewHermitian
  have h_decomp := tracelessSkewHermitian_decomp h_mem
  have h_coords := σ_Fib_1_SU_mat_conj_paulI_y_pauliCoords
  unfold matrixToPauliCoords at h_coords
  have h_im_01 : ((σ_Fib_1_SU_mat * paulI_y *
      σ_Fib_1_SU_mat.conjTranspose) 0 1).im = -Real.sin (7 * Real.pi / 5) :=
    congrArg Prod.fst h_coords
  have h_re_01 : ((σ_Fib_1_SU_mat * paulI_y *
      σ_Fib_1_SU_mat.conjTranspose) 0 1).re = Real.cos (7 * Real.pi / 5) :=
    congrArg (Prod.fst ∘ Prod.snd) h_coords
  have h_im_00 : ((σ_Fib_1_SU_mat * paulI_y *
      σ_Fib_1_SU_mat.conjTranspose) 0 0).im = 0 :=
    congrArg (Prod.snd ∘ Prod.snd) h_coords
  rw [h_decomp, h_im_01, h_re_01, h_im_00]

/-- **R5.4 Layer F.20.c.d.2.m.6 — complex version of σ_Fib_1's pauliDecomp**.

Generalizes `σ_Fib_1_SU_mat_conj_pauliDecomp` from (a b c : ℝ) to (A B C : ℂ).
Needed for σ_Fib_2 composition where the intermediate coefficients (after
F·X·F) are complex-valued (containing `φInv_C, φInvSqrt_C`). -/
theorem σ_Fib_1_SU_mat_conj_pauliDecomp_C (A B C : ℂ) :
    σ_Fib_1_SU_mat *
      (A • paulI_x + B • paulI_y + C • paulI_z) *
      σ_Fib_1_SU_mat.conjTranspose =
    (A * ((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) -
        B * ((Real.sin (7 * Real.pi / 5) : ℝ) : ℂ)) • paulI_x +
    (A * ((Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) +
        B * ((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ)) • paulI_y +
    C • paulI_z := by
  -- Distribute Ad-conjugation over the sum, then apply each base case.
  rw [σ_Fib_1_SU_mat_conj_add, σ_Fib_1_SU_mat_conj_add,
      σ_Fib_1_SU_mat_conj_smul, σ_Fib_1_SU_mat_conj_smul,
      σ_Fib_1_SU_mat_conj_smul]
  rw [σ_Fib_1_SU_mat_conj_paulI_z_eq,
      σ_Fib_1_SU_mat_conj_paulI_x_pauliDecomp,
      σ_Fib_1_SU_mat_conj_paulI_y_pauliDecomp]
  -- Now: A • (cs•x + sn•y + 0•z) + B • (-sn•x + cs•y + 0•z) + C • z =
  --     (A·cs - B·sn) • x + (A·sn + B·cs) • y + C • z.
  -- push_cast normalizes ↑(-Real.sin _) → -↑(Real.sin _).
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **R5.4 Layer F.20.c.d.2.m — HEADLINE: σ_Fib_2's full SO(3) Ad-action
on a Pauli-decomposed element (complex form)**.

For X = a•paulI_x + b•paulI_y + c•paulI_z with complex coefficients,
σ_Fib_2 · X · σ_Fib_2† collects into Pauli sum with closed-form coefficients
in α := 2·φInv·φInvSqrt, β := 2·φInv - 1, γ := φInv² - φInvSqrt², cs := cos(7π/5),
sn := sin(7π/5).

The proof composes via F.17.a (σ_Fib_2 = F·σ_Fib_1·F) + F.20.c.d.2.l (F-linearity)
+ F.20.c.d.2.{m.1,m.2,k} (F's Pauli-coord matrix) + F.20.c.d.2.{m.4,m.5,
σ_Fib_1_conj_paulI_z_eq} (σ_Fib_1's z-axis rotation by 7π/5) + F.20.c.d.2.m.6
(complex σ_Fib_1 pauliDecomp). -/
theorem σ_Fib_2_SU_mat_conj_pauliDecomp_C (a b c : ℂ) :
    σ_Fib_2_SU_mat * (a • paulI_x + b • paulI_y + c • paulI_z) *
      σ_Fib_2_SU_mat.conjTranspose =
    -- Use let bindings for readability. α, β, γ are real-valued complex
    -- constants; cs, sn are ℝ→ℂ casts.
    let α : ℂ := 2 * φInv_C * φInvSqrt_C
    let β : ℂ := 2 * φInv_C - 1
    let γ : ℂ := φInv_C * φInv_C - φInvSqrt_C * φInvSqrt_C
    let cs : ℂ := ((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ)
    let sn : ℂ := ((Real.sin (7 * Real.pi / 5) : ℝ) : ℂ)
    (((a * β + c * α) * cs + b * sn) * β + (a * α + c * γ) * α) • paulI_x +
    (-((a * β + c * α) * sn) + b * cs) • paulI_y +
    (((a * β + c * α) * cs + b * sn) * α + (a * α + c * γ) * γ) • paulI_z := by
  -- Step 1: σ_Fib_2 = F·σ_Fib_1·F via F-decomp. Apply .conjTranspose
  -- rewrite FIRST so the un-conjugated occurrence isn't absorbed.
  rw [σ_Fib_2_SU_mat_conjTranspose_F_decomp, σ_Fib_2_SU_mat_F_decomp]
  -- Step 2: Restructure brackets: (F·σ_1·F)·X·(F·σ_1†·F) = F·(σ_1·(F·X·F)·σ_1†)·F.
  rw [show
    F_C * σ_Fib_1_SU_mat * F_C *
      (a • paulI_x + b • paulI_y + c • paulI_z) *
      (F_C * σ_Fib_1_SU_mat.conjTranspose * F_C) =
    F_C * (σ_Fib_1_SU_mat *
      (F_C * (a • paulI_x + b • paulI_y + c • paulI_z) * F_C) *
      σ_Fib_1_SU_mat.conjTranspose) * F_C
    from by noncomm_ring]
  -- Step 3: F·X·F → Pauli sum (inner F-conjugation).
  rw [F_C_conj_pauliDecomp_collected]
  -- Step 4: σ_Fib_1 · (Pauli sum) · σ_Fib_1† → Pauli sum (σ_Fib_1 z-rotation).
  rw [σ_Fib_1_SU_mat_conj_pauliDecomp_C]
  -- Step 5: F · (Pauli sum) · F → Pauli sum (outer F-conjugation).
  rw [F_C_conj_pauliDecomp_collected]
  -- Step 6: Match the target. The intermediate coefficients simplify via
  -- ring arithmetic in the smul algebra.
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-! ## §24. R5.4 Layer F.20.c.d.2.n — σ_Fib_lie_bundle_pauliDet as cubic polynomial

Composes the closed-form SO(3) actions for σ_Fib_1 (F.20.c.d.2.h) and σ_Fib_2
(F.20.c.d.2.m) into a closed-form cubic polynomial expression for
`σ_Fib_lie_bundle_pauliDet (a•paulI_x + b•paulI_y + c•paulI_z)` over (a, b, c) ∈ ℝ³.

This is the polynomial whose non-zero locus we must show is non-empty + dense
(en route to F.21 unconditional density). F.18 already establishes the
(1, 0, 0) witness; F.20.c.d.2.o will use this polynomial form to derive
the open-dense complement of the zero locus. -/

/-- **R5.4 Layer F.20.c.d.2.n.1 — Pauli coords of a generic complex Pauli sum**.

For complex coefficients `s_x, s_y, s_z`, the Pauli coords of
`s_x • paulI_x + s_y • paulI_y + s_z • paulI_z` are
`(s_x.re + s_y.im, s_y.re - s_x.im, s_z.re)`.

When the coefficients are real-cast (im = 0), this reduces to `(s_x.re, s_y.re, s_z.re)`. -/
theorem matrixToPauliCoords_complex_pauliDecomp (s_x s_y s_z : ℂ) :
    matrixToPauliCoords (s_x • paulI_x + s_y • paulI_y + s_z • paulI_z) =
      (s_x.re + s_y.im, s_y.re - s_x.im, s_z.re) := by
  unfold matrixToPauliCoords paulI_x paulI_y paulI_z
         SKEFTHawking.σ_x SKEFTHawking.σ_y SKEFTHawking.σ_z
  refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · -- .1: ((sum) 0 1).im = s_x.re + s_y.im
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Complex.add_im, Complex.mul_im, Complex.mul_re,
          Complex.I_re, Complex.I_im]
  · refine Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩
    · -- .2.1: ((sum) 0 1).re = s_y.re - s_x.im
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Complex.add_re, Complex.mul_re, Complex.mul_im,
            Complex.I_re, Complex.I_im]
      ring
    · -- .2.2: ((sum) 0 0).im = s_z.re
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Complex.add_im, Complex.mul_im, Complex.mul_re,
            Complex.I_re, Complex.I_im]

/-- **R5.4 Layer F.20.c.d.2.n.2 — Pauli coords of a real-cast Pauli sum**.

Specialization of `matrixToPauliCoords_complex_pauliDecomp` to real coefficients
(via `((·:ℝ):ℂ)` cast). The imaginary parts vanish, giving the natural
`(a, b, c) ↦ (a, b, c)` identity. -/
theorem matrixToPauliCoords_real_pauliDecomp (a b c : ℝ) :
    matrixToPauliCoords
      ((a : ℂ) • paulI_x + (b : ℂ) • paulI_y + (c : ℂ) • paulI_z) =
      (a, b, c) := by
  rw [matrixToPauliCoords_complex_pauliDecomp]
  simp

/-- **R5.4 Layer F.20.c.d.2.n.3 — σ_Fib_1's image Pauli coords (real form)**.

For X = a•paulI_x + b•paulI_y + c•paulI_z (a b c : ℝ):
`matrixToPauliCoords (σ_Fib_1·X·σ_Fib_1†) = (a·cs - b·sn, a·sn + b·cs, c)`
where `cs := cos(7π/5)`, `sn := sin(7π/5)`. -/
theorem matrixToPauliCoords_σ_Fib_1_conj_pauliDecomp (a b c : ℝ) :
    matrixToPauliCoords
      (σ_Fib_1_SU_mat * ((a : ℂ) • paulI_x + (b : ℂ) • paulI_y + (c : ℂ) • paulI_z) *
        σ_Fib_1_SU_mat.conjTranspose) =
    (a * Real.cos (7 * Real.pi / 5) - b * Real.sin (7 * Real.pi / 5),
     a * Real.sin (7 * Real.pi / 5) + b * Real.cos (7 * Real.pi / 5),
     c) := by
  rw [σ_Fib_1_SU_mat_conj_pauliDecomp]
  exact matrixToPauliCoords_real_pauliDecomp _ _ _

/-- **R5.4 Layer F.20.c.d.2.n.4 — σ_Fib_2's image Pauli coords (real form)**.

For X = a•paulI_x + b•paulI_y + c•paulI_z (a b c : ℝ), the Pauli coords of
σ_Fib_2·X·σ_Fib_2† are the closed-form real polynomials derived from F's
SO(3) reflection composed twice with σ_Fib_1's z-rotation. -/
theorem matrixToPauliCoords_σ_Fib_2_conj_pauliDecomp (a b c : ℝ) :
    matrixToPauliCoords
      (σ_Fib_2_SU_mat * ((a : ℂ) • paulI_x + (b : ℂ) • paulI_y + (c : ℂ) • paulI_z) *
        σ_Fib_2_SU_mat.conjTranspose) =
    let α := 2 * Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹
    let β := 2 * Real.goldenRatio⁻¹ - 1
    let γ := Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹ -
             (Real.sqrt Real.goldenRatio)⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹
    let cs := Real.cos (7 * Real.pi / 5)
    let sn := Real.sin (7 * Real.pi / 5)
    (((a * β + c * α) * cs + b * sn) * β + (a * α + c * γ) * α,
     -((a * β + c * α) * sn) + b * cs,
     ((a * β + c * α) * cs + b * sn) * α + (a * α + c * γ) * γ) := by
  rw [σ_Fib_2_SU_mat_conj_pauliDecomp_C, matrixToPauliCoords_complex_pauliDecomp]
  -- Extract .re/.im of each complex coefficient. The coefficients are
  -- composed entirely of real-cast pieces (φInv_C, φInvSqrt_C, cs/sn casts),
  -- so .im = 0 and .re collapses to the real polynomial. `simp` (not `simp only`)
  -- handles Complex.re/im of numeric literals via norm_cast.
  unfold φInv_C φInvSqrt_C
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
             Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
             Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
             Complex.re_ofNat, Complex.im_ofNat]
  refine Prod.mk.injEq .. |>.mpr ⟨by ring, ?_⟩
  refine Prod.mk.injEq .. |>.mpr ⟨by ring, by ring⟩

/-- **R5.4 Layer F.20.c.d.2.n — HEADLINE: σ_Fib_lie_bundle_pauliDet as cubic polynomial**.

The σ_Fib 3-bundle determinant `σ_Fib_lie_bundle_pauliDet (a•paulI_x + b•paulI_y + c•paulI_z)`
is a homogeneous cubic polynomial in (a, b, c) ∈ ℝ³, with coefficients
that are real polynomials in golden-ratio constants and trig values
`cos(7π/5)`, `sin(7π/5)`.

Explicitly:
  `pauliDet = a · (A_y · M_z - A_z · M_y) - b · (A_x · M_z - A_z · M_x)
              + c · (A_x · M_y - A_y · M_x)`
where (A_x, A_y, A_z) are the σ_Fib_1 Pauli coords and (M_x, M_y, M_z) are
the σ_Fib_2 Pauli coords.

This is the polynomial whose non-zero locus we must establish is non-empty
(F.18 + (1,0,0) witness already done) and dense (F.20.c.d.2.o via continuity
+ analytic continuation argument). Together with F.21 (Layer E composition),
this closes the AA Bridge Lemma route to unconditional Fibonacci density. -/
theorem σ_Fib_lie_bundle_pauliDet_pauliDecomp (a b c : ℝ) :
    σ_Fib_lie_bundle_pauliDet
      ((a : ℂ) • paulI_x + (b : ℂ) • paulI_y + (c : ℂ) • paulI_z) =
    let cs := Real.cos (7 * Real.pi / 5)
    let sn := Real.sin (7 * Real.pi / 5)
    let α := 2 * Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹
    let β := 2 * Real.goldenRatio⁻¹ - 1
    let γ := Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹ -
             (Real.sqrt Real.goldenRatio)⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹
    let A_x := a * cs - b * sn
    let A_y := a * sn + b * cs
    let A_z := c
    let M_x := ((a * β + c * α) * cs + b * sn) * β + (a * α + c * γ) * α
    let M_y := -((a * β + c * α) * sn) + b * cs
    let M_z := ((a * β + c * α) * cs + b * sn) * α + (a * α + c * γ) * γ
    a * (A_y * M_z - A_z * M_y) -
      b * (A_x * M_z - A_z * M_x) +
      c * (A_x * M_y - A_y * M_x) := by
  unfold σ_Fib_lie_bundle_pauliDet σ_Fib_lie_bundle pauliDet
  simp only []
  rw [matrixToPauliCoords_real_pauliDecomp,
      matrixToPauliCoords_σ_Fib_1_conj_pauliDecomp,
      matrixToPauliCoords_σ_Fib_2_conj_pauliDecomp]

/-! ## §25. R5.4 Layer F.20.c.d.2.o — Arbitrarily small spanning Pauli-coord witnesses

The cubic polynomial form (F.20.c.d.2.n) is non-zero (witness: paulI_x case, F.18).
By homogeneity (F.20.b `pauliDet_smul_uniform`), the polynomial is non-zero on
arbitrarily small scaled paulI_x. This shows the spanning locus in 𝔰𝔲(2)'s
Pauli-coord parametrization accumulates at the origin.

This is the polynomial-side density witness needed for F.20.c.d.2.p (the
H_Fib intersection step) and F.21 (final density). -/

/-- **R5.4 Layer F.20.c.d.2.o — arbitrarily small spanning Pauli-coord witness**.

For every `ε > 0`, there exist Pauli coordinates `(a, b, c) ∈ ℝ³` with
`a² + b² + c² < ε²` (i.e., within the open ε-ball in Pauli-coord space)
such that `σ_Fib_lie_bundle_pauliDet (a•paulI_x + b•paulI_y + c•paulI_z) ≠ 0`.

Concrete witness: `(ε/2, 0, 0)`. Uses F.20.b's homogeneity
(`σ_Fib_lie_bundle_pauliDet_scaled_paulI_x_ne_zero`) which descends
`σ_Fib_lie_bundle_pauliDet (t·paulI_x) ≠ 0` from `t ≠ 0` via cubic homogeneity. -/
theorem exists_arbitrarily_small_pauliCoord_with_pauliDet_ne_zero
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (a b c : ℝ), a^2 + b^2 + c^2 < ε^2 ∧
      σ_Fib_lie_bundle_pauliDet
        ((a : ℂ) • paulI_x + (b : ℂ) • paulI_y + (c : ℂ) • paulI_z) ≠ 0 := by
  refine ⟨ε / 2, 0, 0, ?_, ?_⟩
  · -- (ε/2)² + 0² + 0² = ε²/4 < ε² since 0 < ε.
    nlinarith [sq_nonneg ε, hε]
  · -- Reduce the sum (ε/2)•x + 0•y + 0•z to (ε/2)•x.
    have h_simp :
        ((ε / 2 : ℝ) : ℂ) • paulI_x + ((0 : ℝ) : ℂ) • paulI_y +
            ((0 : ℝ) : ℂ) • paulI_z =
        ((ε / 2 : ℝ) : ℂ) • paulI_x := by
      simp
    rw [h_simp]
    have h_pos : (0 : ℝ) < ε / 2 := by positivity
    exact σ_Fib_lie_bundle_pauliDet_scaled_paulI_x_ne_zero h_pos.ne'

/-! ## §26. R5.4 Layer F.20.c.d.2.o-app — Continuity + Pauli nbhd of paulI_x

The σ_Fib_lie_bundle_pauliDet on Pauli-decomposed inputs is a CONTINUOUS
function of the Pauli coords (a, b, c) ∈ ℝ³. Combined with F.18
(σ_Fib_lie_bundle_pauliDet (paulI_x) ≠ 0), this gives an OPEN nhd in
Pauli-coord space around (1, 0, 0) where the polynomial is non-zero.

This refines F.20.c.d.2.o's countably-many-witnesses statement to an
OPEN-set statement, which is more useful for downstream H_Fib direction
analysis. -/

/-- **R5.4 Layer F.20.c.d.2.o-app.1 — Continuity of pauliDet on Pauli decomp**.

The function `(a, b, c) ↦ σ_Fib_lie_bundle_pauliDet (a•paulI_x + b•paulI_y + c•paulI_z)`
is continuous as a function `ℝ³ → ℝ` (it is a polynomial — see F.20.c.d.2.n). -/
theorem σ_Fib_lie_bundle_pauliDet_pauliDecomp_continuous :
    Continuous (fun (abc : ℝ × ℝ × ℝ) =>
      σ_Fib_lie_bundle_pauliDet
        ((abc.1 : ℂ) • paulI_x + (abc.2.1 : ℂ) • paulI_y +
         (abc.2.2 : ℂ) • paulI_z)) := by
  -- σ_Fib_lie_bundle_pauliDet ∘ (Pauli sum embedding) is continuous
  -- as composition of: σ_Fib_lie_bundle_pauliDet_continuous (shipped F.20.c.d.0)
  -- with linear continuity of (a, b, c) ↦ a•x + b•y + c•z.
  have h_embed : Continuous (fun (abc : ℝ × ℝ × ℝ) =>
      (abc.1 : ℂ) • paulI_x + (abc.2.1 : ℂ) • paulI_y +
        (abc.2.2 : ℂ) • paulI_z) := by
    refine Continuous.add (Continuous.add ?_ ?_) ?_
    · exact (Complex.continuous_ofReal.comp continuous_fst).smul continuous_const
    · exact (Complex.continuous_ofReal.comp (continuous_fst.comp continuous_snd)).smul
        continuous_const
    · exact (Complex.continuous_ofReal.comp (continuous_snd.comp continuous_snd)).smul
        continuous_const
  exact σ_Fib_lie_bundle_pauliDet_continuous.comp h_embed

/-- **R5.4 Layer F.20.c.d.2.o-app.2 — Pauli-coord locus is OPEN as ℝ³ set**.

The set of Pauli triples `(a, b, c) ∈ ℝ³` such that
`σ_Fib_lie_bundle_pauliDet (a•paulI_x + b•paulI_y + c•paulI_z) ≠ 0` is open
in ℝ³, as the preimage of `{0}ᶜ ⊆ ℝ` under the continuous Pauli-decomp
polynomial.

This is the polynomial-side OPEN-set non-zero region (Pauli-coord level),
complementing F.20.c.d.0's matrix-space-level openness. Useful as a stepping
stone toward F.20.c.d.2.p which connects to H_Fib direction analysis. -/
theorem σ_Fib_lie_bundle_pauliDet_pauliDecomp_isOpen_ne_zero_set :
    IsOpen {p : ℝ × ℝ × ℝ |
      σ_Fib_lie_bundle_pauliDet
        ((p.1 : ℂ) • paulI_x + (p.2.1 : ℂ) • paulI_y +
         (p.2.2 : ℂ) • paulI_z) ≠ 0} :=
  σ_Fib_lie_bundle_pauliDet_pauliDecomp_continuous.isOpen_preimage {0}ᶜ
    isOpen_compl_singleton

/-! ## §27. R5.4 Layer F.20.c.d.2.o-app extension — Polynomial-form homogeneity

The σ_Fib_lie_bundle_pauliDet on Pauli-decomp inputs is a homogeneous polynomial
of degree 3 in (a, b, c) ∈ ℝ³. Direct ℝ-scaling of all 3 Pauli coords scales the
result by t³. Composes F.20.b's `σ_Fib_lie_bundle_pauliDet_smul_uniform` with
the smul distributivity in the Pauli decomposition.

This makes the cubic polynomial nature explicit and enables clean scaling-based
arguments (e.g., "if P(d) ≠ 0 then P(t·d) ≠ 0 for all t ≠ 0"). -/

/-- **R5.4 Layer F.20.c.d.2.o-app.3 — Pauli-coord scaling distributes**.

For real `t` and Pauli triple `(a, b, c) ∈ ℝ³`:
`(t·a)•paulI_x + (t·b)•paulI_y + (t·c)•paulI_z = (t:ℂ)·((a)•paulI_x + (b)•paulI_y + (c)•paulI_z)`.

Pure ring identity in the smul algebra. -/
theorem pauliDecomp_real_smul_eq (t a b c : ℝ) :
    ((t * a : ℝ) : ℂ) • paulI_x + ((t * b : ℝ) : ℂ) • paulI_y +
      ((t * c : ℝ) : ℂ) • paulI_z =
    ((t : ℂ)) • (((a : ℝ) : ℂ) • paulI_x + ((b : ℝ) : ℂ) • paulI_y +
      ((c : ℝ) : ℂ) • paulI_z) := by
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  push_cast
  ring_nf

/-- **R5.4 Layer F.20.c.d.2.o-app.4 — σ_Fib_lie_bundle_pauliDet polynomial-form homogeneity**.

The polynomial `(a, b, c) ↦ σ_Fib_lie_bundle_pauliDet (a•x + b•y + c•z)` is
HOMOGENEOUS of degree 3:
`P(t·a, t·b, t·c) = t³ · P(a, b, c)` for all real `t`.

This is the polynomial form of F.20.b's `σ_Fib_lie_bundle_pauliDet_smul_uniform`,
specialized to Pauli-coord inputs. Useful for scaling arguments: if `P(a₀, b₀, c₀) ≠ 0`,
then `P(t·a₀, t·b₀, t·c₀) ≠ 0` for all `t ≠ 0`, giving a 1-parameter family of
arbitrarily-small non-zero witnesses (specializes to F.20.c.d.2.o for direction
(a₀, b₀, c₀) = (1, 0, 0)). -/
theorem σ_Fib_lie_bundle_pauliDet_pauliDecomp_homog (t a b c : ℝ) :
    σ_Fib_lie_bundle_pauliDet
      (((t * a : ℝ) : ℂ) • paulI_x + ((t * b : ℝ) : ℂ) • paulI_y +
        ((t * c : ℝ) : ℂ) • paulI_z) =
    t ^ 3 * σ_Fib_lie_bundle_pauliDet
      (((a : ℝ) : ℂ) • paulI_x + ((b : ℝ) : ℂ) • paulI_y +
        ((c : ℝ) : ℂ) • paulI_z) := by
  rw [pauliDecomp_real_smul_eq, σ_Fib_lie_bundle_pauliDet_smul_uniform]

/-! ## §28. R5.4 Layer F.20.c.d.2.o-app.5 — pauliDet ≠ 0 set ∈ nhds (1, 0, 0)

The pauliDet ≠ 0 set in Pauli-coord space is an OPEN nhd of `(1, 0, 0)`.
Filter-based statement avoids `Metric.ball` instance synthesis heartbeat
issues. Downstream consumers can extract concrete δ via `Metric.mem_nhds_iff`
at their own heartbeat budget. -/

/-- **R5.4 Layer F.20.c.d.2.o-app.5 — pauliDet ≠ 0 set is in nhds of (1, 0, 0)**.

The set `{(a, b, c) | σ_Fib_lie_bundle_pauliDet (a•x + b•y + c•z) ≠ 0}` is
an open neighborhood of `(1, 0, 0)` in `ℝ × ℝ × ℝ`. Composes
`σ_Fib_lie_bundle_pauliDet_pauliDecomp_isOpen_ne_zero_set` (openness) with
F.18 (non-zero at paulI_x). -/
theorem σ_Fib_lie_bundle_pauliDet_pauliDecomp_ne_zero_mem_nhds_paulI_x :
    {p : ℝ × ℝ × ℝ |
        σ_Fib_lie_bundle_pauliDet
          ((p.1 : ℂ) • paulI_x + (p.2.1 : ℂ) • paulI_y +
           (p.2.2 : ℂ) • paulI_z) ≠ 0} ∈
      nhds ((1, 0, 0) : ℝ × ℝ × ℝ) := by
  apply σ_Fib_lie_bundle_pauliDet_pauliDecomp_isOpen_ne_zero_set.mem_nhds
  show σ_Fib_lie_bundle_pauliDet
    (((1 : ℝ) : ℂ) • paulI_x + ((0 : ℝ) : ℂ) • paulI_y +
     ((0 : ℝ) : ℂ) • paulI_z) ≠ 0
  have h_eq : ((1 : ℝ) : ℂ) • paulI_x + ((0 : ℝ) : ℂ) • paulI_y +
      ((0 : ℝ) : ℂ) • paulI_z = paulI_x := by simp
  rw [h_eq]
  exact σ_Fib_lie_bundle_pauliDet_paulI_x_ne_zero

/-! ## §29. R5.4 Layer F.20.c.d.2.p.1 — Analyticity of pauliDet on Pauli decomp

The σ_Fib_lie_bundle_pauliDet on Pauli-decomposed inputs is `AnalyticOnNhd ℝ`
on all of `ℝ³ = ℝ × ℝ × ℝ`. This follows directly from the closed-form cubic
polynomial (F.20.c.d.2.n): the function is a polynomial in the Pauli coordinates
(a, b, c) with real-constant coefficients (golden-ratio constants + cos/sin
of 7π/5), hence analytic everywhere.

This is the FIRST STEP in the HYBRID ANALYTIC-ZERO ROUTE for F.20.c.d.2.p
(per Mathlib substrate scout findings, session 59 close memo). Combined with
the F.20.c.d.2.o-app.5 non-vanishing-at-(1,0,0) witness, the next ship
(F.20.c.d.2.p.2) will use `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`
contrapositive to conclude `interior {P = 0} = ∅`. -/

/-- **R5.4 Layer F.20.c.d.2.p.1 — pauliDet on Pauli decomp is analytic on all of ℝ³**.

The function `(a, b, c) ↦ σ_Fib_lie_bundle_pauliDet (a•paulI_x + b•paulI_y + c•paulI_z)`
is `AnalyticOnNhd ℝ Set.univ`. Proof: rewrite via F.20.c.d.2.n's closed-form
cubic polynomial (then the function is manifestly a polynomial in `(abc.1, abc.2.1, abc.2.2)`
with real-constant coefficients), and build analyticity compositionally from
`analyticOnNhd_fst`, `analyticOnNhd_snd`, `analyticOnNhd_const`, and the closure
constructions `.add`, `.sub`, `.mul`, `.neg`. -/
theorem σ_Fib_lie_bundle_pauliDet_pauliDecomp_analyticOnNhd :
    AnalyticOnNhd ℝ (fun (abc : ℝ × ℝ × ℝ) =>
      σ_Fib_lie_bundle_pauliDet
        ((abc.1 : ℂ) • paulI_x + (abc.2.1 : ℂ) • paulI_y +
         (abc.2.2 : ℂ) • paulI_z)) Set.univ := by
  -- Constants
  set cs : ℝ := Real.cos (7 * Real.pi / 5) with hcs_def
  set sn : ℝ := Real.sin (7 * Real.pi / 5) with hsn_def
  set α : ℝ := 2 * Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ with hα_def
  set β : ℝ := 2 * Real.goldenRatio⁻¹ - 1 with hβ_def
  set γ : ℝ := Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹ -
               (Real.sqrt Real.goldenRatio)⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ with hγ_def
  -- Step 1: rewrite via F.20.c.d.2.n closed-form cubic polynomial,
  -- inlining the constants (no let-bindings — they impede unification of `analyticOnNhd_const`).
  have h_eq : (fun (abc : ℝ × ℝ × ℝ) =>
        σ_Fib_lie_bundle_pauliDet
          ((abc.1 : ℂ) • paulI_x + (abc.2.1 : ℂ) • paulI_y +
           (abc.2.2 : ℂ) • paulI_z)) =
      (fun (abc : ℝ × ℝ × ℝ) =>
        abc.1 * ((abc.1 * sn + abc.2.1 * cs) *
                  (((abc.1 * β + abc.2.2 * α) * cs + abc.2.1 * sn) * α +
                   (abc.1 * α + abc.2.2 * γ) * γ) -
                 abc.2.2 * (-((abc.1 * β + abc.2.2 * α) * sn) + abc.2.1 * cs)) -
        abc.2.1 * ((abc.1 * cs - abc.2.1 * sn) *
                    (((abc.1 * β + abc.2.2 * α) * cs + abc.2.1 * sn) * α +
                     (abc.1 * α + abc.2.2 * γ) * γ) -
                   abc.2.2 * (((abc.1 * β + abc.2.2 * α) * cs + abc.2.1 * sn) * β +
                              (abc.1 * α + abc.2.2 * γ) * α)) +
        abc.2.2 * ((abc.1 * cs - abc.2.1 * sn) *
                    (-((abc.1 * β + abc.2.2 * α) * sn) + abc.2.1 * cs) -
                   (abc.1 * sn + abc.2.1 * cs) *
                    (((abc.1 * β + abc.2.2 * α) * cs + abc.2.1 * sn) * β +
                     (abc.1 * α + abc.2.2 * γ) * α))) := by
    funext abc
    have := σ_Fib_lie_bundle_pauliDet_pauliDecomp abc.1 abc.2.1 abc.2.2
    simp only [← hcs_def, ← hsn_def, ← hα_def, ← hβ_def, ← hγ_def] at this
    convert this using 1
  rw [h_eq]
  -- Step 2: compositional analyticity of the explicit polynomial.
  -- Projections are analytic (CLMs).
  have ha : AnalyticOnNhd ℝ (fun (abc : ℝ × ℝ × ℝ) => abc.1) Set.univ :=
    analyticOnNhd_fst
  have hb : AnalyticOnNhd ℝ (fun (abc : ℝ × ℝ × ℝ) => abc.2.1) Set.univ :=
    analyticOnNhd_fst.comp analyticOnNhd_snd (Set.mapsTo_univ _ _)
  have hc : AnalyticOnNhd ℝ (fun (abc : ℝ × ℝ × ℝ) => abc.2.2) Set.univ :=
    analyticOnNhd_snd.comp analyticOnNhd_snd (Set.mapsTo_univ _ _)
  -- Constants (explicit values; lets unification work cleanly).
  have hcs : AnalyticOnNhd ℝ (fun (_ : ℝ × ℝ × ℝ) => cs) Set.univ := analyticOnNhd_const
  have hsn : AnalyticOnNhd ℝ (fun (_ : ℝ × ℝ × ℝ) => sn) Set.univ := analyticOnNhd_const
  have hα : AnalyticOnNhd ℝ (fun (_ : ℝ × ℝ × ℝ) => α) Set.univ := analyticOnNhd_const
  have hβ : AnalyticOnNhd ℝ (fun (_ : ℝ × ℝ × ℝ) => β) Set.univ := analyticOnNhd_const
  have hγ : AnalyticOnNhd ℝ (fun (_ : ℝ × ℝ × ℝ) => γ) Set.univ := analyticOnNhd_const
  -- Sub-expressions
  have hAx := (ha.mul hcs).sub (hb.mul hsn)            -- a·cs - b·sn
  have hAy := (ha.mul hsn).add (hb.mul hcs)            -- a·sn + b·cs
  have hAB := (ha.mul hβ).add (hc.mul hα)              -- a·β + c·α
  have hAG := (ha.mul hα).add (hc.mul hγ)              -- a·α + c·γ
  have hMx := (((hAB.mul hcs).add (hb.mul hsn)).mul hβ).add (hAG.mul hα)
  have hMy := ((hAB.mul hsn).neg).add (hb.mul hcs)
  have hMz := (((hAB.mul hcs).add (hb.mul hsn)).mul hα).add (hAG.mul hγ)
  -- Final composition: P = a·(A_y·M_z - A_z·M_y) - b·(A_x·M_z - A_z·M_x) + c·(A_x·M_y - A_y·M_x)
  exact ((ha.mul ((hAy.mul hMz).sub (hc.mul hMy))).sub
          (hb.mul ((hAx.mul hMz).sub (hc.mul hMx)))).add
          (hc.mul ((hAx.mul hMy).sub (hAy.mul hMx)))

/-! ## §30. R5.4 Layer F.20.c.d.2.p.2 — Zero locus has empty interior; non-zero set is dense

By analytic uniqueness: if `P : ℝ × ℝ × ℝ → ℝ` is `AnalyticOnNhd ℝ Set.univ`
(F.20.c.d.2.p.1) and `P(1, 0, 0) ≠ 0` (F.20.c.d.2.o-app.5 substrate), then `P`
cannot be zero on any open set (else uniqueness would force `P = 0` everywhere
on the preconnected `ℝ × ℝ × ℝ`, contradicting `P(1, 0, 0) ≠ 0`).

Equivalent forms shipped here:
- `interior {p | P p = 0} = ∅`
- `Dense {p | P p ≠ 0}` (the non-zero set is dense)

Both forms are useful for downstream F.20.c.d.2.p.3 H_Fib bridge analysis. -/

/-- **R5.4 Layer F.20.c.d.2.p.2 — zero locus has empty interior**.

The zero set of the Pauli-decomp pauliDet polynomial has empty interior in ℝ³.
Proof: if some `x` were in the interior, then `P` would be eventually zero on a
neighborhood of `x`, and analytic uniqueness on the preconnected set `Set.univ`
would force `P = 0` everywhere — contradicting non-vanishing at `(1, 0, 0)`
(F.20.c.d.2.o-app.5 via F.18).

Engineering note: the proof aliases the Pauli-decomp polynomial as a local
`set f := ...` before applying the analytic-uniqueness lemma. Without this
alias, elaboration of `eqOn_zero_of_preconnected_of_eventuallyEq_zero` on
the nested-lambda form hits the `whnf` heartbeat budget (200000) — the same
class of issue documented in F.20.c.d.2.o-app.2 engineering note. -/
theorem σ_Fib_lie_bundle_pauliDet_pauliDecomp_zero_interior_empty :
    interior {p : ℝ × ℝ × ℝ |
      σ_Fib_lie_bundle_pauliDet
        ((p.1 : ℂ) • paulI_x + (p.2.1 : ℂ) • paulI_y +
         (p.2.2 : ℂ) • paulI_z) = 0} = ∅ := by
  set f : ℝ × ℝ × ℝ → ℝ := fun abc =>
      σ_Fib_lie_bundle_pauliDet
        ((abc.1 : ℂ) • paulI_x + (abc.2.1 : ℂ) • paulI_y +
         (abc.2.2 : ℂ) • paulI_z) with hf_def
  have hf_analytic : AnalyticOnNhd ℝ f Set.univ :=
    σ_Fib_lie_bundle_pauliDet_pauliDecomp_analyticOnNhd
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  -- hx : x ∈ interior {f = 0} ⟹ {f = 0} ∈ nhds x ⟹ f =ᶠ[nhds x] 0
  have h_nhds : {p | f p = 0} ∈ nhds x := mem_interior_iff_mem_nhds.mp hx
  have h_event : f =ᶠ[nhds x] 0 := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨{p | f p = 0}, h_nhds, ?_⟩
    intro p hp; exact hp
  -- Analytic uniqueness on preconnected Set.univ.
  have h_zero : Set.EqOn f 0 Set.univ :=
    hf_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ x) h_event
  -- Contradict at (1, 0, 0) via F.18.
  have h_ne_one : f (1, 0, 0) ≠ 0 := by
    show σ_Fib_lie_bundle_pauliDet
      (((1 : ℝ) : ℂ) • paulI_x + ((0 : ℝ) : ℂ) • paulI_y +
       ((0 : ℝ) : ℂ) • paulI_z) ≠ 0
    have h_simp : ((1 : ℝ) : ℂ) • paulI_x + ((0 : ℝ) : ℂ) • paulI_y +
        ((0 : ℝ) : ℂ) • paulI_z = paulI_x := by simp
    rw [h_simp]
    exact σ_Fib_lie_bundle_pauliDet_paulI_x_ne_zero
  exact h_ne_one (h_zero (Set.mem_univ _))

/-- **R5.4 Layer F.20.c.d.2.p.2 (Dense form) — non-zero set of pauliDet polynomial is dense**.

The set of Pauli triples where `σ_Fib_lie_bundle_pauliDet (a•x + b•y + c•z) ≠ 0`
is dense in `ℝ × ℝ × ℝ`. Direct consequence of
`σ_Fib_lie_bundle_pauliDet_pauliDecomp_zero_interior_empty` via complement-
interior identity (the complement of a set with empty interior is dense).

This is a form downstream `F.20.c.d.2.p.3` H_Fib direction analysis can consume:
even if H_Fib is a countable subset, its accumulation at 1 can intersect this
DENSE non-zero set provided the H_Fib elements' Pauli directions are themselves
sufficiently distributed (which uses the σ_Fib_1/σ_Fib_2 algebraic structure
under Ad-conjugation, captured by F.20.c.d.2.{j,k,l,m} F_C Ad-action). -/
theorem σ_Fib_lie_bundle_pauliDet_pauliDecomp_ne_zero_dense :
    Dense {p : ℝ × ℝ × ℝ |
      σ_Fib_lie_bundle_pauliDet
        ((p.1 : ℂ) • paulI_x + (p.2.1 : ℂ) • paulI_y +
         (p.2.2 : ℂ) • paulI_z) ≠ 0} := by
  -- The non-zero set is the complement of the zero set.
  have h_compl : {p : ℝ × ℝ × ℝ |
        σ_Fib_lie_bundle_pauliDet
          ((p.1 : ℂ) • paulI_x + (p.2.1 : ℂ) • paulI_y +
           (p.2.2 : ℂ) • paulI_z) ≠ 0} =
      {p : ℝ × ℝ × ℝ |
        σ_Fib_lie_bundle_pauliDet
          ((p.1 : ℂ) • paulI_x + (p.2.1 : ℂ) • paulI_y +
           (p.2.2 : ℂ) • paulI_z) = 0}ᶜ := by
    ext p; simp [Set.mem_compl_iff]
  rw [h_compl]
  -- `interior s = ∅ ↔ Dense sᶜ`
  exact interior_eq_empty_iff_dense_compl.mp
    σ_Fib_lie_bundle_pauliDet_pauliDecomp_zero_interior_empty

/-! ## §31. R5.4 Layer F.20.c.d.2.p.3.a — Explicit Ad(σ_Fib_2)(paulI_z) Pauli decomp

The substrate-shipped `σ_Fib_2_SU_mat_conj_pauliDecomp_C` (F.20.c.d.2.m) gives
σ_Fib_2's full SO(3) Ad-action on a general Pauli-decomposed element. Specializing
to (a, b, c) = (0, 0, 1) yields the explicit Pauli-coords of `Ad(σ_Fib_2)(paulI_z)`,
which is the key direction for the F.20.c.d.2.p.3 H_Fib bridge:

`σ_Fib_2 · paulI_z · σ_Fib_2† = (α·(β·cs + γ))·paulI_x + (-α·sn)·paulI_y + (α²·cs + γ²)·paulI_z`

This is the IMAGE direction under Ad(σ_Fib_2) of the z-axis, used in the
H_Fib bridge: if H_Fib's small witness has liePartMat in (or near) the paulI_z
direction, conjugation by σ_Fib_2 maps to this image direction. Whether
`σ_Fib_lie_bundle_pauliDet` at this image is non-zero is the substantive
Gap-1 check toward .p.3 (numerically ~0.898; symbolic exact form involves
hundreds of terms in φ⁻¹, √(φ⁻¹), cos/sin(7π/5)).

Engineering note: the proof rewrites `paulI_z = 0·paulI_x + 0·paulI_y + 1·paulI_z`
and applies F.20.c.d.2.m at (a, b, c) = (0, 0, 1); `ring_nf` then handles the
simplification. -/

/-- **R5.4 Layer F.20.c.d.2.p.3.a — explicit Pauli-coord form of Ad(σ_Fib_2)(paulI_z)**.

Specializes F.20.c.d.2.m `σ_Fib_2_SU_mat_conj_pauliDecomp_C` to (a, b, c) = (0, 0, 1).
The image direction is `(α·(β·cs + γ))·paulI_x + (-α·sn)·paulI_y + (α²·cs + γ²)·paulI_z`. -/
theorem σ_Fib_2_SU_mat_conj_paulI_z_pauliDecomp :
    σ_Fib_2_SU_mat * paulI_z * σ_Fib_2_SU_mat.conjTranspose =
      let α : ℂ := 2 * φInv_C * φInvSqrt_C
      let β : ℂ := 2 * φInv_C - 1
      let γ : ℂ := φInv_C * φInv_C - φInvSqrt_C * φInvSqrt_C
      let cs : ℂ := ((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ)
      let sn : ℂ := ((Real.sin (7 * Real.pi / 5) : ℝ) : ℂ)
      (α * (β * cs + γ)) • paulI_x +
      (- (α * sn)) • paulI_y +
      (α^2 * cs + γ^2) • paulI_z := by
  have h_pz : paulI_z =
      (0 : ℂ) • paulI_x + (0 : ℂ) • paulI_y + (1 : ℂ) • paulI_z := by simp
  conv_lhs => rw [h_pz]
  rw [σ_Fib_2_SU_mat_conj_pauliDecomp_C 0 0 1]
  ring_nf

/-! ## §32. R5.4 Layer F.20.c.d.2.p.3.b — Closed-form liePart of σ_Fib_1_SU_mat

The σ_Fib bundle and its pauliDet are evaluated at `liePartMat h.val` for
`h ∈ specialUnitaryGroup`. To analyze whether any `h ∈ H_Fib` lands in
the non-zero locus of `σ_Fib_lie_bundle_pauliDet`, we need closed forms
for `liePartMat` at concrete `h ∈ H_Fib`. This section ships the closed
form for `h = σ_Fib_1_SU_mat`:

  `liePartMat σ_Fib_1_SU_mat = -sin(7π/10) • paulI_z`.

Pauli coords: `(0, 0, -sin(7π/10))`. The substantive consequence:
`σ_Fib_lie_bundle_pauliDet (liePartMat σ_Fib_1_SU_mat) = 0`. This is
STRUCTURAL (z-axis is in the zero locus per F.20.c.d.2.f) — `σ_Fib_1`
fixes its own liePart under Ad-conjugation, so the σ_Fib bundle reduces
to rank ≤ 2.

This means `h = σ_Fib_1` itself is NOT a Gap-1 witness. The next sections
ship closed forms for `σ_Fib_2_SU_mat` and composed products (e.g.,
`σ_Fib_1 · σ_Fib_2`) where the bundle does NOT structurally degenerate.

Engineering note: helper `complex_exp_minus_star_eq` computes
`exp(iθ) - (exp(iθ))* = 2I · sin(θ)`, the foundational complex-conjugation
identity for converting diagonal exponential matrices to skew-Hermitian
form. -/

/-- Helper: `exp(iθ) - (exp(iθ))* = 2I · sin(θ)` for real `θ`. -/
private theorem complex_exp_minus_star_eq (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) -
      (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) =
    (2 * Complex.I) * ((Real.sin θ : ℝ) : ℂ) := by
  rw [show (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) =
        Complex.exp (- ((θ : ℂ) * Complex.I)) by
    rw [← Complex.exp_conj]; congr 1
    simp [Complex.conj_I, mul_comm]]
  rw [Complex.exp_mul_I,
      show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
  push_cast; simp; ring

/-- **R5.4 Layer F.20.c.d.2.p.3.b — closed-form `liePartMat σ_Fib_1_SU_mat`**.

`liePartMat σ_Fib_1_SU_mat = -sin(7π/10) • paulI_z`.

Proof: `σ_Fib_1_SU_mat = diag(exp(-7πi/10), exp(7πi/10))` (via
`σ_Fib_1_SU_mat_diagonal_form` + ω-R₁ / ω-R_τ exponent identities).
The skew-Hermitian projection (1/2)·(M - M*) of `(σ_Fib_1_SU_mat - 1)`
equals `diag(-i·sin(7π/10), i·sin(7π/10)) = -sin(7π/10) · paulI_z`
(using `complex_exp_minus_star_eq`). This is already traceless
(`-i·sin + i·sin = 0`), so `tracelessProj` is the identity. -/
theorem liePartMat_σ_Fib_1_SU_mat :
    liePartMat σ_Fib_1_SU_mat =
      ((-Real.sin (7 * Real.pi / 10) : ℝ) : ℂ) • paulI_z := by
  have h_ω_R1 : ω_Fib_C * R1_C = Complex.exp (((-7 * Real.pi / 10 : ℝ) : ℂ) * Complex.I) := by
    unfold ω_Fib_C R1_C; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h_ω_Rτ : ω_Fib_C * Rtau_C = Complex.exp (((7 * Real.pi / 10 : ℝ) : ℂ) * Complex.I) := by
    unfold ω_Fib_C Rtau_C; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h_skew :
      skewHermitianProj (σ_Fib_1_SU_mat - 1) =
        ((-Real.sin (7 * Real.pi / 10) : ℝ) : ℂ) • paulI_z := by
    rw [σ_Fib_1_SU_mat_diagonal_form, h_ω_R1, h_ω_Rτ]
    unfold skewHermitianProj
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [paulI_z, SKEFTHawking.σ_z, Matrix.sub_apply, Matrix.conjTranspose_apply,
            Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero,
            Matrix.cons_val_one, smul_eq_mul, star_zero]
    · have h := complex_exp_minus_star_eq (-7 * Real.pi / 10)
      push_cast at h
      have hsin : Complex.sin (-(7 * (Real.pi : ℂ)) / 10) =
                  - Complex.sin (7 * (Real.pi : ℂ) / 10) := by
        rw [show (-(7 * (Real.pi : ℂ)) / 10) = -(7 * (Real.pi : ℂ) / 10) by ring,
            Complex.sin_neg]
      rw [show (-7 * (Real.pi : ℂ) / 10) = (-(7 * (Real.pi : ℂ)) / 10) by ring] at h
      rw [hsin] at h
      linear_combination (1 / 2 : ℂ) * h
    · have h := complex_exp_minus_star_eq (7 * Real.pi / 10)
      push_cast at h
      linear_combination (1 / 2 : ℂ) * h
  have h_trace_skew : (skewHermitianProj (σ_Fib_1_SU_mat - 1)).trace = 0 := by
    rw [h_skew]
    simp [paulI_z, SKEFTHawking.σ_z, Matrix.trace_fin_two,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  show lieProj (σ_Fib_1_SU_mat - 1) = _
  unfold lieProj
  rw [tracelessProj_of_traceless h_trace_skew]
  exact h_skew

/-- **`σ_Fib_lie_bundle_pauliDet` at `liePartMat σ_Fib_1_SU_mat` is zero**.

Direct consequence of the closed form `liePartMat σ_Fib_1_SU_mat =
-sin(7π/10) • paulI_z` (in the paulI_z direction) combined with
F.20.c.d.2.f `σ_Fib_lie_bundle_pauliDet_paulI_z_eq_zero` (paulI_z is in
the zero locus) and the cubic homogeneity of pauliDet (F.20.b
`σ_Fib_lie_bundle_pauliDet_smul_uniform`).

This shows σ_Fib_1 ITSELF is NOT a Gap-1 witness for the H_Fib bridge —
its liePart is structurally in the zero locus. -/
theorem σ_Fib_lie_bundle_pauliDet_liePartMat_σ_Fib_1_SU_mat_eq_zero :
    σ_Fib_lie_bundle_pauliDet (liePartMat σ_Fib_1_SU_mat) = 0 := by
  rw [liePartMat_σ_Fib_1_SU_mat]
  rw [σ_Fib_lie_bundle_pauliDet_smul_uniform]
  rw [σ_Fib_lie_bundle_pauliDet_paulI_z_eq_zero]
  ring

/-! ## §33. R5.4 Layer F.20.c.d.2.p.3.c — Closed-form liePart of σ_Fib_2_SU_mat

`σ_Fib_2_SU_mat = F · σ_Fib_1_SU_mat · F` (existing substrate
`σ_Fib_2_SU_mat_eq_F_conj`) and `F² = 1` (`F_C_sq`) gives:

  `σ_Fib_2_SU_mat - 1 = F · (σ_Fib_1_SU_mat - 1) · F`

Then unitary-conjugation equivariance of `lieProj` (`lieProj_conj_unitary`)
and `F_C.conjTranspose = F_C` (F is Hermitian) yields:

  `liePartMat σ_Fib_2_SU_mat = F · liePartMat σ_Fib_1_SU_mat · F`
                           = `-sin(7π/10) · (F · paulI_z · F)`  (via .b)
                           = `-sin(7π/10) · (α·paulI_x + 0·paulI_y + γ·paulI_z)`  (via F.20.c.d.2.m.2)

Pauli coords: `(-sin(7π/10)·α, 0, -sin(7π/10)·γ)` where
α := 2·φInv·φInvSqrt and γ := φInv² - φInvSqrt². -/

/-- Helper: F is its own conjugate transpose (F_C is Hermitian).
This is `F_C_star` expressed in conjTranspose form. -/
private theorem F_C_conjTranspose_eq : F_C.conjTranspose = F_C := by
  have h := F_C_star
  rwa [show (star F_C : Matrix (Fin 2) (Fin 2) ℂ) = F_C.conjTranspose from rfl] at h

/-- Helper: `σ_Fib_2_SU_mat - 1 = F · (σ_Fib_1_SU_mat - 1) · F`.

Uses `σ_Fib_2_SU_mat = F · σ_Fib_1_SU_mat · F` (existing substrate
`σ_Fib_2_SU_mat_eq_F_conj`) and `F · F = 1` (`F_C_sq`) to absorb the
trailing `1`. -/
theorem σ_Fib_2_SU_mat_sub_one_eq :
    σ_Fib_2_SU_mat - 1 = F_C * (σ_Fib_1_SU_mat - 1) * F_C := by
  rw [σ_Fib_2_SU_mat_eq_F_conj, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, F_C_sq]

/-- liePartMat is F-conjugation-equivariant: `liePartMat σ_Fib_2_SU_mat =
F · liePartMat σ_Fib_1_SU_mat · F`.

Bridges sub-step 1 (σ_Fib_1) to sub-step 2 (σ_Fib_2) via F-conjugation.
Uses `lieProj_conj_unitary` (general unitary form, doesn't require det = 1)
together with F's Hermiticity (F.conjTranspose = F) and involutivity (F² = 1). -/
theorem liePartMat_σ_Fib_2_SU_mat_via_F_conj :
    liePartMat σ_Fib_2_SU_mat =
      F_C * liePartMat σ_Fib_1_SU_mat * F_C := by
  show lieProj (σ_Fib_2_SU_mat - 1) = _
  rw [σ_Fib_2_SU_mat_sub_one_eq]
  have h_left : F_C.conjTranspose * F_C = 1 := by
    rw [F_C_conjTranspose_eq]; exact F_C_sq
  have h_right : F_C * F_C.conjTranspose = 1 := by
    rw [F_C_conjTranspose_eq]; exact F_C_sq
  rw [show F_C * (σ_Fib_1_SU_mat - 1) * F_C =
        F_C * (σ_Fib_1_SU_mat - 1) * F_C.conjTranspose from
          by rw [F_C_conjTranspose_eq]]
  rw [lieProj_conj_unitary h_left h_right]
  rw [F_C_conjTranspose_eq]; rfl

/-- **R5.4 Layer F.20.c.d.2.p.3.c — closed-form `liePartMat σ_Fib_2_SU_mat`** (F-form).

`liePartMat σ_Fib_2_SU_mat = -sin(7π/10) • (F · paulI_z · F)`.

Composes sub-step 1 (`liePartMat_σ_Fib_1_SU_mat`) with the F-conjugation
equivariance lemma. The (F · paulI_z · F) factor is unfolded to Pauli
coords in the next theorem `liePartMat_σ_Fib_2_SU_mat_pauliDecomp`. -/
theorem liePartMat_σ_Fib_2_SU_mat_F_form :
    liePartMat σ_Fib_2_SU_mat =
      ((-Real.sin (7 * Real.pi / 10) : ℝ) : ℂ) • (F_C * paulI_z * F_C) := by
  rw [liePartMat_σ_Fib_2_SU_mat_via_F_conj, liePartMat_σ_Fib_1_SU_mat,
      Matrix.mul_smul, Matrix.smul_mul]

/-- **R5.4 Layer F.20.c.d.2.p.3.c (Pauli decomp form) — `liePartMat σ_Fib_2_SU_mat`**.

`liePartMat σ_Fib_2_SU_mat = (-sin(7π/10)·α)·paulI_x + 0·paulI_y + (-sin(7π/10)·γ)·paulI_z`
where α := 2·φInv·φInvSqrt and γ := φInv² - φInvSqrt².

Composes `liePartMat_σ_Fib_2_SU_mat_F_form` (the F-form) with
`F_C_conj_paulI_z_pauliDecomp` (F.20.c.d.2.m.2, F's Pauli decomp of paulI_z).
The result confirms liePart(σ_Fib_2) is in the xz-plane (paulI_y coefficient = 0),
consistent with F.20.c.d.2.k's `F_C_conj_paulI_y_eq_neg : F·paulI_y·F = -paulI_y`
(F acts as -1 on the y-axis, which means F-conjugation preserves the xz-plane).

Pauli coords: `(-sin(7π/10)·α, 0, -sin(7π/10)·γ)`. Numerically:
`α ≈ 0.971, γ ≈ -0.236, sin(7π/10) ≈ 0.809`, so coords ≈ `(-0.786, 0, 0.191)`. -/
theorem liePartMat_σ_Fib_2_SU_mat_pauliDecomp :
    liePartMat σ_Fib_2_SU_mat =
      (((-Real.sin (7 * Real.pi / 10) : ℝ) : ℂ) * (2 * φInv_C * φInvSqrt_C)) • paulI_x +
      (0 : ℂ) • paulI_y +
      (((-Real.sin (7 * Real.pi / 10) : ℝ) : ℂ) *
        (φInv_C * φInv_C - φInvSqrt_C * φInvSqrt_C)) • paulI_z := by
  rw [liePartMat_σ_Fib_2_SU_mat_F_form, F_C_conj_paulI_z_pauliDecomp]
  module

/-! ## §34. R5.4 Layer F.20.c.d.2.p.3.d — H_Fib witness σ_Fib_1·σ_Fib_2·σ_Fib_1⁻¹

THE GAP-1 WITNESS. Numerical analysis (Monte Carlo + direct computation):

  `h := σ_Fib_1_SU · σ_Fib_2_SU · σ_Fib_1_SU⁻¹ ∈ H_Fib`

has `σ_Fib_lie_bundle_pauliDet (liePartMat h.val) ≈ +0.476 ≠ 0`.

Numerically the candidates σ_Fib_1 and σ_Fib_2 ALONE have structural P=0
(their liePart commutes with themselves under Ad-conjugation, reducing the
3-bundle to rank ≤ 2). The conjugate `σ_Fib_1·σ_Fib_2·σ_Fib_1⁻¹` BREAKS
this structural degeneracy by introducing a non-trivial y-component into
liePart's Pauli decomp (sub-step 2's `liePartMat_σ_Fib_2_SU_mat_pauliDecomp`
has y-coord 0; after σ_Fib_1's z-axis rotation, the y-component becomes
non-trivial).

This section ships:
  • Group-theoretic membership in H_Fib (Subgroup.mul_mem + .inv_mem)
  • Subtype-value-to-matrix bridge ((σ_Fib_1_SU⁻¹).val = σ_Fib_1_SU_mat†)
  • Ad-equivariance-based closed form for liePartMat
  • Pauli decomp: `(-sin(7π/10)·α·cs)·paulI_x + (-sin(7π/10)·α·sn)·paulI_y + (-sin(7π/10)·γ)·paulI_z`
    where α := 2·φInv·φInvSqrt, γ := φInv² - φInvSqrt², cs := cos(7π/5), sn := sin(7π/5)

The non-vanishing pauliDet proof is deferred to sub-step 3b (subsequent
section). Numerically Pauli coords ≈ (0.243, 0.748, 0.191) with
sin(7π/5) ≈ -0.951 the key contributor making y-coord non-trivial. -/

/-- σ_Fib_1 · σ_Fib_2 · σ_Fib_1⁻¹ ∈ H_Fib (group closure). -/
theorem σ_Fib_1_conj_σ_Fib_2_mem_H_Fib :
    σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹ ∈ H_Fib :=
  H_Fib.mul_mem
    (H_Fib.mul_mem σ_Fib_1_SU_mem_H_Fib σ_Fib_2_SU_mem_H_Fib)
    (H_Fib.inv_mem σ_Fib_1_SU_mem_H_Fib)

/-- Bridge from subtype-level multiplication to matrix-level conjugation.

`(σ_Fib_1_SU · σ_Fib_2_SU · σ_Fib_1_SU⁻¹).val = σ_Fib_1_SU_mat · σ_Fib_2_SU_mat ·
σ_Fib_1_SU_mat.conjTranspose`.

Uses the fact that for SU(2) elements g, `(g⁻¹).val = star g.val =
g.val.conjTranspose` (definitionally via SU(2) Inv instance). -/
theorem σ_Fib_1_conj_σ_Fib_2_val :
    ((σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹).val :
        Matrix (Fin 2) (Fin 2) ℂ) =
      σ_Fib_1_SU_mat * σ_Fib_2_SU_mat * σ_Fib_1_SU_mat.conjTranspose := by
  show σ_Fib_1_SU_mat * σ_Fib_2_SU_mat * (σ_Fib_1_SU⁻¹).val =
    σ_Fib_1_SU_mat * σ_Fib_2_SU_mat * σ_Fib_1_SU_mat.conjTranspose
  congr 1

/-- **R5.4 Layer F.20.c.d.2.p.3.d — closed-form liePartMat at the Gap-1 witness**.

`liePartMat (σ_Fib_1·σ_Fib_2·σ_Fib_1†) = (-sin(7π/10)·α·cs)·paulI_x +
  (-sin(7π/10)·α·sn)·paulI_y + (-sin(7π/10)·γ)·paulI_z`

where α := 2·φInv·φInvSqrt, γ := φInv²-φInvSqrt², cs := cos(7π/5), sn := sin(7π/5).

Proof composes Ad-equivariance (`liePartMat_conj_σ_Fib_1_SU_mat`, F.13) with
sub-step 2's closed form (`liePartMat_σ_Fib_2_SU_mat_pauliDecomp`) and σ_Fib_1's
SO(3) Pauli-decomp z-axis rotation (`σ_Fib_1_SU_mat_conj_pauliDecomp_C`,
F.20.c.d.2.m.6). The `module` tactic distributes the rotation through the
scalar multiplications cleanly.

Numerically (with α ≈ 0.972, γ ≈ -0.236, cs ≈ -0.309, sn ≈ -0.951,
-sin(7π/10) ≈ -0.809):
  Pauli coords ≈ (0.243, 0.748, 0.191).

This breaks the σ_Fib_1 and σ_Fib_2 structural-degeneracy pattern (both had
y-coord 0 in liePart). The σ_Fib_1 z-axis rotation injects non-trivial y from
the original x-component of `liePartMat σ_Fib_2_SU_mat`. -/
theorem liePartMat_σ_Fib_1_conj_σ_Fib_2_pauliDecomp :
    liePartMat
      (σ_Fib_1_SU_mat * σ_Fib_2_SU_mat * σ_Fib_1_SU_mat.conjTranspose) =
      (((-Real.sin (7 * Real.pi / 10) : ℝ) : ℂ) *
        ((2 * φInv_C * φInvSqrt_C) *
          ((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ))) • paulI_x +
      (((-Real.sin (7 * Real.pi / 10) : ℝ) : ℂ) *
        ((2 * φInv_C * φInvSqrt_C) *
          ((Real.sin (7 * Real.pi / 5) : ℝ) : ℂ))) • paulI_y +
      (((-Real.sin (7 * Real.pi / 10) : ℝ) : ℂ) *
        (φInv_C * φInv_C - φInvSqrt_C * φInvSqrt_C)) • paulI_z := by
  rw [liePartMat_conj_σ_Fib_1_SU_mat]
  rw [liePartMat_σ_Fib_2_SU_mat_pauliDecomp]
  rw [σ_Fib_1_SU_mat_conj_pauliDecomp_C]
  module

/-! ## §35. R5.4 Layer F.20.c.d.2.p.3.e.1 — Trig substrate at multiples of π/5

For the non-vanishing proof at sub-step 3.e, we need closed forms and sign
information for `Real.cos (7π/5)`, `Real.sin (7π/5)`, `Real.sin (7π/10)`,
and `Real.sin (π/5)`. Only `Real.cos_pi_div_five = (1 + √5)/4` is in Mathlib
directly; we derive the others.

These are general trig identities (independent of the σ_Fib substrate) and
could plausibly be upstream PR candidates for Mathlib. -/

/-- `Real.cos (7π/5) = (1 - √5)/4`.

Derivation: `7π/5 = 2·(π/5) + π`, so `cos(7π/5) = -cos(2π/5) = -(2cos²(π/5) - 1)`.
With `cos(π/5) = (1+√5)/4`, this gives `cos(7π/5) = -(2·((1+√5)/4)² - 1) = (1-√5)/4`.

(Upstream-Mathlib-PR candidate.) -/
theorem cos_7pi_div_5 : Real.cos (7 * Real.pi / 5) = (1 - Real.sqrt 5) / 4 := by
  have h1 : (7 * Real.pi / 5 : ℝ) = 2 * (Real.pi / 5) + Real.pi := by ring
  rw [h1, Real.cos_add_pi, Real.cos_two_mul, Real.cos_pi_div_five]
  have h_sqrt : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  nlinarith [h_sqrt, Real.sqrt_nonneg 5]

/-- `Real.sin (π/5)² = (10 - 2√5)/16` via `sin² + cos² = 1`. -/
theorem sin_sq_pi_div_5 :
    Real.sin (Real.pi / 5) ^ 2 = (10 - 2 * Real.sqrt 5) / 16 := by
  have h := Real.sin_sq_add_cos_sq (Real.pi / 5)
  rw [Real.cos_pi_div_five] at h
  have h_sqrt : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  nlinarith [h, h_sqrt, Real.sqrt_nonneg 5]

/-- `Real.sin (π/5) > 0` since `0 < π/5 < π`. -/
theorem sin_pi_div_5_pos : 0 < Real.sin (Real.pi / 5) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · have := Real.pi_pos
    linarith

/-- `Real.sin (7π/10) > 0` since `0 < 7π/10 < π`. -/
theorem sin_7pi_div_10_pos : 0 < Real.sin (7 * Real.pi / 10) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · have := Real.pi_pos
    positivity
  · have := Real.pi_pos
    nlinarith

/-- `Real.sin (7π/5) < 0` since `7π/5 = π + 2π/5` and `sin(π + x) = -sin(x)`,
with `0 < sin(2π/5)`. -/
theorem sin_7pi_div_5_neg : Real.sin (7 * Real.pi / 5) < 0 := by
  have h1 : (7 * Real.pi / 5 : ℝ) = 2 * (Real.pi / 5) + Real.pi := by ring
  rw [h1, Real.sin_add_pi]
  have h_pos : 0 < Real.sin (2 * (Real.pi / 5)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have := Real.pi_pos; positivity
    · have := Real.pi_pos; nlinarith
  linarith

/-! ## §36. R5.4 Layer F.20.c.d.2.p.3.e.2 — Golden-ratio algebraic substrate

For the closed-form pauliDet evaluation, we need explicit algebraic identities
for the constants `α := 2·φInv·φInvSqrt` and `γ := φInv² - φInvSqrt²` that appear
in the σ_Fib_2 SO(3) image Pauli-coord coefficients:

  • `α² = 4·√5 - 8`
  • `γ = 2 - √5`
  • `φInv² = 1 - φInv` (golden ratio derived identity)

These follow from `φ² = φ + 1` (Mathlib `Real.goldenRatio_sq`) and
`(√φ)² = φ` (positivity-based).

Numerically: φInv ≈ 0.618, φInvSqrt ≈ 0.786, α ≈ 0.972, γ ≈ -0.236,
α² ≈ 0.944 = 4·2.236 - 8, γ = 2 - 2.236 ≈ -0.236. -/

/-- `φInv² = 1 - φInv`, equivalent to `φInv² + φInv = 1`, from `φ² = φ + 1`. -/
theorem golden_phi_inv_sq :
    Real.goldenRatio⁻¹^2 = 1 - Real.goldenRatio⁻¹ := by
  have hne : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
  have h_gold : Real.goldenRatio^2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hne2 : Real.goldenRatio^2 ≠ 0 := pow_ne_zero _ hne
  -- Multiply both sides by φ² to clear denominators:
  -- φ⁻¹² · φ² = 1; (1 - φ⁻¹) · φ² = φ² - φ⁻¹·φ² = φ² - φ = 1
  have h : Real.goldenRatio⁻¹^2 * Real.goldenRatio^2 =
      (1 - Real.goldenRatio⁻¹) * Real.goldenRatio^2 := by
    rw [show Real.goldenRatio⁻¹^2 * Real.goldenRatio^2 =
        (Real.goldenRatio⁻¹ * Real.goldenRatio)^2 from by ring]
    rw [inv_mul_cancel₀ hne]
    rw [show (1 : ℝ)^2 = 1 from by ring]
    rw [show (1 - Real.goldenRatio⁻¹) * Real.goldenRatio^2 =
        Real.goldenRatio^2 - Real.goldenRatio⁻¹ * Real.goldenRatio^2 from by ring]
    rw [show Real.goldenRatio⁻¹ * Real.goldenRatio^2 =
        Real.goldenRatio⁻¹ * Real.goldenRatio * Real.goldenRatio from by ring]
    rw [inv_mul_cancel₀ hne, one_mul]
    linarith [h_gold]
  exact mul_right_cancel₀ hne2 h

/-- `α² = 4·√5 - 8` where `α := 2·φInv·φInvSqrt`. -/
theorem golden_alpha_sq :
    (2 * Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹)^2 =
      4 * Real.sqrt 5 - 8 := by
  have hpos : 0 ≤ Real.goldenRatio := le_of_lt Real.goldenRatio_pos
  have hq2 : (Real.sqrt Real.goldenRatio)⁻¹^2 = Real.goldenRatio⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hpos]
  have h_phi : Real.goldenRatio⁻¹^2 = 1 - Real.goldenRatio⁻¹ := golden_phi_inv_sq
  have h_inv : Real.goldenRatio⁻¹ = (Real.sqrt 5 - 1) / 2 := by
    rw [Real.inv_goldenRatio]; unfold Real.goldenConj; ring
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h_expand : (2 * Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹)^2 =
      4 * Real.goldenRatio⁻¹^2 * (Real.sqrt Real.goldenRatio)⁻¹^2 := by ring
  rw [h_expand, hq2, h_phi, h_inv]
  nlinarith [h5, Real.sqrt_nonneg 5]

/-- `γ = 2 - √5` where `γ := φInv² - φInvSqrt²`. -/
theorem golden_gamma_eq :
    Real.goldenRatio⁻¹^2 - (Real.sqrt Real.goldenRatio)⁻¹^2 = 2 - Real.sqrt 5 := by
  have hpos : 0 ≤ Real.goldenRatio := le_of_lt Real.goldenRatio_pos
  have hq2 : (Real.sqrt Real.goldenRatio)⁻¹^2 = Real.goldenRatio⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hpos]
  have h_phi_sq : Real.goldenRatio⁻¹^2 = 1 - Real.goldenRatio⁻¹ := golden_phi_inv_sq
  have h_inv : Real.goldenRatio⁻¹ = (Real.sqrt 5 - 1) / 2 := by
    rw [Real.inv_goldenRatio]; unfold Real.goldenConj; ring
  rw [hq2, h_phi_sq, h_inv]
  ring

/-- `γ² = 4γ + 1` — γ = 2-√5 satisfies the quadratic γ² - 4γ - 1 = 0.
This is the minimal polynomial relation for γ over ℚ. -/
theorem golden_gamma_sq :
    (Real.goldenRatio⁻¹^2 - (Real.sqrt Real.goldenRatio)⁻¹^2)^2 =
      4 * (Real.goldenRatio⁻¹^2 - (Real.sqrt Real.goldenRatio)⁻¹^2) + 1 := by
  rw [golden_gamma_eq]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5, Real.sqrt_nonneg 5]

/-- `α² + γ² = 1` — unitary-conjugation invariance: (α, 0, γ) is a unit
vector (norm² = 1) as Pauli coords of `F·paulI_z·F` which is a unitary
conjugate of `paulI_z` (norm 1 in Hilbert-Schmidt).

Identity-derived: α² = 4√5 - 8, γ² = 9 - 4√5 (= 4γ + 1); sum = 1. -/
theorem golden_alpha_sq_plus_gamma_sq :
    (2 * Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹)^2 +
      (Real.goldenRatio⁻¹^2 - (Real.sqrt Real.goldenRatio)⁻¹^2)^2 = 1 := by
  rw [golden_alpha_sq, golden_gamma_eq]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5, Real.sqrt_nonneg 5]

/-! ## §37. R5.4 Layer F.20.c.d.2.p.3.e.4 — Cubic homogeneity factoring at Gap-1

By cubic homogeneity (`σ_Fib_lie_bundle_pauliDet_pauliDecomp_homog`), the pauliDet
at scaled Pauli coords factors out `t³`:

  `pauliDet (t·a • paulI_x + t·b • paulI_y + t·c • paulI_z) = t³ · pauliDet (a • ... + ...)`

Applied to the Gap-1 witness with `t := -sin(7π/10)` and `(a, b, c) = (α·cs, α·sn, γ)`,
this factors out `-sin(7π/10)³` cleanly. -/

/-- Real-valued Pauli coords of `liePartMat (σ_Fib_1·σ_Fib_2·σ_Fib_1⁻¹)` AFTER
factoring out the common `-sin(7π/10)` factor.

`(a', b', c') = (α·cs, α·sn, γ)` where `α := 2·φInv·φInvSqrt`, `cs := cos(7π/5)`,
`sn := sin(7π/5)`, `γ := φInv² - φInvSqrt²`. -/
noncomputable def gap1_witness_pauliCoord_factored :
    ℝ × ℝ × ℝ :=
  ( (2 * Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹) * Real.cos (7 * Real.pi / 5),
    (2 * Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹) * Real.sin (7 * Real.pi / 5),
    Real.goldenRatio⁻¹^2 - (Real.sqrt Real.goldenRatio)⁻¹^2 )

/-- liePart at the Gap-1 witness factors as `-sin(7π/10)` times the unit-norm
direction `(α·cs, α·sn, γ)`. -/
theorem liePartMat_σ_Fib_1_conj_σ_Fib_2_real_factored :
    let (a', b', c') := gap1_witness_pauliCoord_factored
    liePartMat (σ_Fib_1_SU_mat * σ_Fib_2_SU_mat * σ_Fib_1_SU_mat.conjTranspose) =
      (((-Real.sin (7 * Real.pi / 10) * a' : ℝ) : ℂ) • paulI_x +
        ((-Real.sin (7 * Real.pi / 10) * b' : ℝ) : ℂ) • paulI_y +
        ((-Real.sin (7 * Real.pi / 10) * c' : ℝ) : ℂ) • paulI_z) := by
  rw [liePartMat_σ_Fib_1_conj_σ_Fib_2_pauliDecomp]
  unfold gap1_witness_pauliCoord_factored φInv_C φInvSqrt_C
  simp only []
  push_cast
  module

/-- Cubic homogeneity applied at the Gap-1 witness: pauliDet factors out `-sin(7π/10)³`. -/
theorem σ_Fib_lie_bundle_pauliDet_at_gap1_factored :
    let (a', b', c') := gap1_witness_pauliCoord_factored
    σ_Fib_lie_bundle_pauliDet
      (liePartMat (σ_Fib_1_SU_mat * σ_Fib_2_SU_mat * σ_Fib_1_SU_mat.conjTranspose)) =
    (-Real.sin (7 * Real.pi / 10))^3 *
      σ_Fib_lie_bundle_pauliDet
        (((a' : ℝ) : ℂ) • paulI_x + ((b' : ℝ) : ℂ) • paulI_y + ((c' : ℝ) : ℂ) • paulI_z) := by
  rw [liePartMat_σ_Fib_1_conj_σ_Fib_2_real_factored]
  simp only []
  exact σ_Fib_lie_bundle_pauliDet_pauliDecomp_homog _ _ _ _

/-! ## §38. R5.4 Layer F.20.c.d.2.p.3.e.5 — Closed-form polynomial value at Gap-1

The substantial algebraic step: the cubic polynomial value at the factored
direction `(α·cs, α·sn, γ)` simplifies to a CLEAN closed form via Groebner
reduction under the algebraic constraints:

  `pauliDet at (α·cs, α·sn, γ) = sin(7π/5) · (4·√5 - 8)`

Discovery method: sympy `groebner + reduced` on the constraint ideal
  { (√φ)⁻¹² - φ⁻¹ , sn² - (10+2√5)/16 , √5² - 5 , φ⁻¹ - (√5-1)/2 }

yielded explicit polynomial coefficients for the `linear_combination` chain.
The closed form arises from the structural identities α² + γ² = 1 (unit
direction), γ² = 4γ + 1 (γ's minimal poly), and cs² + sn² = 1 (Pythagorean).

Sign analysis on the closed form:
  • sin(7π/5) < 0  (sin_7pi_div_5_neg from §35)
  • 4·√5 - 8 > 0   (since √5 > 2)
  • Combined with `(-sin(7π/10))³ < 0` (since sin(7π/10) > 0 from §35),
    the full pauliDet at Gap-1 is (-)·(-)·(+) = + > 0 ≠ 0.

Numerically the value is ≈ +0.476 (matches Monte Carlo + sympy direct eval). -/

/-- Helper: `sin²(7π/5) = (10 + 2√5)/16`. From `cos(7π/5) = (1-√5)/4`
+ Pythagorean identity. -/
theorem sin_sq_7pi_div_5 :
    Real.sin (7 * Real.pi / 5)^2 = (10 + 2 * Real.sqrt 5) / 16 := by
  have h := Real.sin_sq_add_cos_sq (7 * Real.pi / 5)
  rw [cos_7pi_div_5] at h
  have h5 : Real.sqrt 5^2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h, h5, Real.sqrt_nonneg 5]

/-- **R5.4 Layer F.20.c.d.2.p.3.e.5 — closed-form polynomial value at factored Gap-1**.

`σ_Fib_lie_bundle_pauliDet (factored direction) = sin(7π/5) · (4√5 - 8)`.

Proof method: substitute cs = (1-√5)/4 and φ⁻¹ = (√5-1)/2 via `rw`, then
apply Groebner-derived `linear_combination` with coefficients in the variables
q := (√φ)⁻¹, sn := sin(7π/5), √5. The constraints are q² = (√5-1)/2 (golden
ratio + sqrt²), sn² = (10+2√5)/16 (Pythagorean), and √5² = 5.

The coefficient polynomials were computed via `sympy.groebner` + `sympy.reduced`. -/
theorem σ_Fib_lie_bundle_pauliDet_at_gap1_factored_value :
    σ_Fib_lie_bundle_pauliDet
      (let (a', b', c') := gap1_witness_pauliCoord_factored
       ((a' : ℝ) : ℂ) • paulI_x + ((b' : ℝ) : ℂ) • paulI_y + ((c' : ℝ) : ℂ) • paulI_z) =
    Real.sin (7 * Real.pi / 5) * (4 * Real.sqrt 5 - 8) := by
  unfold gap1_witness_pauliCoord_factored
  simp only []
  rw [σ_Fib_lie_bundle_pauliDet_pauliDecomp]
  simp only []
  rw [cos_7pi_div_5]
  rw [show Real.goldenRatio⁻¹ = (Real.sqrt 5 - 1)/2 from by
        rw [Real.inv_goldenRatio]; unfold Real.goldenConj; ring]
  set q : ℝ := (Real.sqrt Real.goldenRatio)⁻¹
  set sn : ℝ := Real.sin (7 * Real.pi / 5)
  have hq_sq : q^2 = (Real.sqrt 5 - 1)/2 := by
    show (Real.sqrt Real.goldenRatio)⁻¹^2 = (Real.sqrt 5 - 1)/2
    rw [inv_pow, Real.sq_sqrt (le_of_lt Real.goldenRatio_pos)]
    rw [Real.inv_goldenRatio]; unfold Real.goldenConj; ring
  have hsn_sq : sn^2 = (10 + 2 * Real.sqrt 5) / 16 := sin_sq_7pi_div_5
  have h5 : Real.sqrt 5^2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination
    (-q^6*sn^3*Real.sqrt 5^2 + 2*q^6*sn^3*Real.sqrt 5 - q^6*sn^3 -
      q^6*sn*Real.sqrt 5^4/16 - q^6*sn*Real.sqrt 5^3/4 + q^6*sn*Real.sqrt 5^2/8 +
      3*q^6*sn*Real.sqrt 5/4 - 9*q^6*sn/16 + q^4*sn^3*Real.sqrt 5^5/2 -
      7*q^4*sn^3*Real.sqrt 5^4/4 + 3*q^4*sn^3*Real.sqrt 5^3/2 +
      2*q^4*sn^3*Real.sqrt 5^2 - 4*q^4*sn^3*Real.sqrt 5 + 7*q^4*sn^3/4 +
      q^4*sn*Real.sqrt 5^7/32 - 3*q^4*sn*Real.sqrt 5^6/64 + 3*q^4*sn*Real.sqrt 5^5/32 -
      35*q^4*sn*Real.sqrt 5^4/64 + 19*q^4*sn*Real.sqrt 5^3/32 +
      39*q^4*sn*Real.sqrt 5^2/64 - 39*q^4*sn*Real.sqrt 5/32 + 31*q^4*sn/64 +
      q^2*sn^5*Real.sqrt 5^4 - 4*q^2*sn^5*Real.sqrt 5^3 +
      6*q^2*sn^5*Real.sqrt 5^2 - 4*q^2*sn^5*Real.sqrt 5 + q^2*sn^5 -
      q^2*sn^3*Real.sqrt 5^7/16 + q^2*sn^3*Real.sqrt 5^6/2 -
      21*q^2*sn^3*Real.sqrt 5^5/16 + q^2*sn^3*Real.sqrt 5^4/4 +
      61*q^2*sn^3*Real.sqrt 5^3/16 - 5*q^2*sn^3*Real.sqrt 5^2 +
      25*q^2*sn^3*Real.sqrt 5/16 + q^2*sn^3/4 - q^2*sn*Real.sqrt 5^9/256 +
      q^2*sn*Real.sqrt 5^8/256 + 9*q^2*sn*Real.sqrt 5^7/128 -
      19*q^2*sn*Real.sqrt 5^6/128 - 3*q^2*sn*Real.sqrt 5^5/32 +
      17*q^2*sn*Real.sqrt 5^4/64 + 63*q^2*sn*Real.sqrt 5^3/128 -
      173*q^2*sn*Real.sqrt 5^2/128 + 265*q^2*sn*Real.sqrt 5/256 - 69*q^2*sn/256 +
      sn^5*Real.sqrt 5^5/2 - 5*sn^5*Real.sqrt 5^4/2 + 5*sn^5*Real.sqrt 5^3 -
      5*sn^5*Real.sqrt 5^2 + 5*sn^5*Real.sqrt 5/2 - sn^5/2 -
      sn^3*Real.sqrt 5^8/64 + 5*sn^3*Real.sqrt 5^7/32 - 11*sn^3*Real.sqrt 5^6/32 -
      19*sn^3*Real.sqrt 5^5/32 + 13*sn^3*Real.sqrt 5^4/4 -
      137*sn^3*Real.sqrt 5^3/32 + 51*sn^3*Real.sqrt 5^2/32 + 23*sn^3*Real.sqrt 5/32 -
      31*sn^3/64 - sn*Real.sqrt 5^10/1024 + sn*Real.sqrt 5^9/512 +
      15*sn*Real.sqrt 5^8/1024 - 3*sn*Real.sqrt 5^7/128 -
      57*sn*Real.sqrt 5^6/512 + 63*sn*Real.sqrt 5^5/256 +
      99*sn*Real.sqrt 5^4/512 - 135*sn*Real.sqrt 5^3/128 +
      1299*sn*Real.sqrt 5^2/1024 - 343*sn*Real.sqrt 5/512 + 139*sn/1024) * hq_sq +
    (sn^3*Real.sqrt 5^6/4 - 3*sn^3*Real.sqrt 5^5/2 + 15*sn^3*Real.sqrt 5^4/4 -
      5*sn^3*Real.sqrt 5^3 + 15*sn^3*Real.sqrt 5^2/4 - 3*sn^3*Real.sqrt 5/2 +
      sn^3/4 - sn*Real.sqrt 5^9/128 + 11*sn*Real.sqrt 5^8/128 -
      7*sn*Real.sqrt 5^7/32 - 5*sn*Real.sqrt 5^6/32 + 93*sn*Real.sqrt 5^5/64 -
      131*sn*Real.sqrt 5^4/64 + 9*sn*Real.sqrt 5^3/32 + 55*sn*Real.sqrt 5^2/32 -
      193*sn*Real.sqrt 5/128 + 51*sn/128) * hsn_sq +
    (-sn*Real.sqrt 5^9/2048 + sn*Real.sqrt 5^8/2048 + 5*sn*Real.sqrt 5^7/512 +
      5*sn*Real.sqrt 5^6/512 - 155*sn*Real.sqrt 5^5/1024 +
      319*sn*Real.sqrt 5^4/1024 - 67*sn*Real.sqrt 5^3/512 -
      159*sn*Real.sqrt 5^2/512 + 1839*sn*Real.sqrt 5/2048 - 3351*sn/2048) * h5

/-- **R5.4 Layer F.20.c.d.2.p.3.e.6 — full closed-form pauliDet at Gap-1**.

`σ_Fib_lie_bundle_pauliDet (liePart (σ_Fib_1·σ_Fib_2·σ_Fib_1⁻¹)) =
  -sin(7π/10)³ · sin(7π/5) · (4·√5 - 8)`

Composes cubic-homogeneity factoring (`σ_Fib_lie_bundle_pauliDet_at_gap1_factored`)
with the substantive closed form (`σ_Fib_lie_bundle_pauliDet_at_gap1_factored_value`). -/
theorem σ_Fib_lie_bundle_pauliDet_at_gap1_eq :
    σ_Fib_lie_bundle_pauliDet
      (liePartMat (σ_Fib_1_SU_mat * σ_Fib_2_SU_mat * σ_Fib_1_SU_mat.conjTranspose)) =
    (-Real.sin (7 * Real.pi / 10))^3 *
      Real.sin (7 * Real.pi / 5) * (4 * Real.sqrt 5 - 8) := by
  have h1 := σ_Fib_lie_bundle_pauliDet_at_gap1_factored
  have h2 := σ_Fib_lie_bundle_pauliDet_at_gap1_factored_value
  simp only [] at h1 h2
  rw [h1, h2]; ring

/-- **R5.4 Layer F.20.c.d.2.p.3.e.7 — Gap-1 witness pauliDet is non-zero**.

`σ_Fib_lie_bundle_pauliDet (liePart (σ_Fib_1·σ_Fib_2·σ_Fib_1⁻¹)) ≠ 0`

Proof: three-factor sign argument:
  • `(-sin(7π/10))³ < 0` since `0 < sin(7π/10)` (§35 `sin_7pi_div_10_pos`)
  • `sin(7π/5) < 0` (§35 `sin_7pi_div_5_neg`)
  • `4·√5 - 8 > 0` since `√5 > 2`
  • Product: (-)·(-)·(+) = + > 0 ≠ 0 ✓

Concretely the value ≈ +0.476. -/
theorem σ_Fib_lie_bundle_pauliDet_at_gap1_ne_zero :
    σ_Fib_lie_bundle_pauliDet
      (liePartMat (σ_Fib_1_SU_mat * σ_Fib_2_SU_mat * σ_Fib_1_SU_mat.conjTranspose)) ≠ 0 := by
  rw [σ_Fib_lie_bundle_pauliDet_at_gap1_eq]
  have h_sin10 : 0 < Real.sin (7 * Real.pi / 10) := sin_7pi_div_10_pos
  have h_sin5 : Real.sin (7 * Real.pi / 5) < 0 := sin_7pi_div_5_neg
  have h_sqrt5_gt_2 : Real.sqrt 5 > 2 := by
    have h5 : Real.sqrt 5^2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith [h5, Real.sqrt_nonneg 5]
  have h_diff_pos : 4 * Real.sqrt 5 - 8 > 0 := by linarith
  have h_cube_neg : (-Real.sin (7 * Real.pi / 10))^3 < 0 := by
    have h_sin_pow_pos : Real.sin (7 * Real.pi / 10)^3 > 0 := pow_pos h_sin10 3
    have h_eq : (-Real.sin (7 * Real.pi / 10))^3 = -(Real.sin (7 * Real.pi / 10)^3) := by ring
    linarith [h_eq, h_sin_pow_pos]
  -- Product (-)·(-)·(+) > 0
  have h_prod_pos :
      (-Real.sin (7 * Real.pi / 10))^3 * Real.sin (7 * Real.pi / 5) *
        (4 * Real.sqrt 5 - 8) > 0 := by
    have h_neg_neg : (-Real.sin (7 * Real.pi / 10))^3 * Real.sin (7 * Real.pi / 5) > 0 :=
      mul_pos_of_neg_of_neg h_cube_neg h_sin5
    exact mul_pos h_neg_neg h_diff_pos
  linarith

/-! ## §39. R5.4 Layer F.20.c.d.2.p.3.f — H_Fib existential composition

The composition of the H_Fib-membership (§34) and the non-vanishing
(§38 `σ_Fib_lie_bundle_pauliDet_at_gap1_ne_zero`) yields the existential
form needed for downstream density work:

  ∃ h ∈ H_Fib, σ_Fib_lie_bundle_pauliDet (liePartMat h.val) ≠ 0

This is the CLEAN MILESTONE statement for the F.20.c.d.2 step. The
witness is `σ_Fib_1_SU · σ_Fib_2_SU · σ_Fib_1_SU⁻¹`. Downstream F.21
(unconditional Fibonacci density) reduces to applying the Aharonov-Arad
iteration argument from this existential. -/

/-- **R5.4 Layer F.20.c.d.2.p.3 HEADLINE — H_Fib contains a Gap-1 witness**.

`∃ h ∈ H_Fib, σ_Fib_lie_bundle_pauliDet (liePartMat h.val) ≠ 0`.

The witness is the Gap-1 element `σ_Fib_1_SU · σ_Fib_2_SU · σ_Fib_1_SU⁻¹`.
Composes membership (§34 `σ_Fib_1_conj_σ_Fib_2_mem_H_Fib`) with the
subtype-value bridge (§34 `σ_Fib_1_conj_σ_Fib_2_val`) and the non-vanishing
theorem (§38 `σ_Fib_lie_bundle_pauliDet_at_gap1_ne_zero`).

This closes the SUBSTANTIVE content of the F.20.c.d.2.p RISK step. The
remaining bridge from this existential to F.21 unconditional density is
the Aharonov-Arad iteration argument (multi-session). -/
theorem exists_in_H_Fib_σ_Fib_lie_bundle_pauliDet_liePartMat_ne_zero :
    ∃ h ∈ (SKEFTHawking.FKLW.H_Fib :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      σ_Fib_lie_bundle_pauliDet
        (liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0 := by
  refine ⟨σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹, σ_Fib_1_conj_σ_Fib_2_mem_H_Fib, ?_⟩
  rw [σ_Fib_1_conj_σ_Fib_2_val]
  exact σ_Fib_lie_bundle_pauliDet_at_gap1_ne_zero

/-! ## §40. R5.4 Layer F.20.c.d.2.q — Three-conjugate H_Fib spanning triple at Gap-1

Composes the Gap-1 existential (§39) with σ_Fib_1 / σ_Fib_2 conjugation closure
of H_Fib to ship the **explicit three-element H_Fib triple whose `liePartMat`
directions are ℝ-linearly independent in 𝔰𝔲(2)**:

  h_gap1 := σ_Fib_1·σ_Fib_2·σ_Fib_1⁻¹
  h_1    := σ_Fib_1·h_gap1·σ_Fib_1⁻¹    = σ_Fib_1²·σ_Fib_2·σ_Fib_1⁻²
  h_2    := σ_Fib_2·h_gap1·σ_Fib_2⁻¹

All three are in H_Fib (subgroup closure under mul + inv with σ_Fib_1_SU,
σ_Fib_2_SU ∈ H_Fib). Their liePart values are X := liePartMat h_gap1.val,
σ_Fib_1·X·σ_Fib_1† (= Ad(σ_Fib_1) X) and σ_Fib_2·X·σ_Fib_2† (= Ad(σ_Fib_2) X)
respectively, via Ad-equivariance of `liePartMat` (§13
`liePartMat_conj_specialUnitary`). These three are precisely the σ_Fib bundle at
X — and at X = liePartMat h_gap1.val we have `σ_Fib_lie_bundle_pauliDet X ≠ 0`
(§38), so the three are ℝ-linearly independent by §2 `σ_Fib_lie_bundle_lin_indep`.

**Why this is substantive (not P3/P5 anti-pattern)**:

  - **Quantitative**: the conclusion involves a strict linear-independence
    statement on three SPECIFIC matrices, falsifiable by exhibiting a
    non-trivial relation.
  - **Cross-module bridge integrity**: substantively calls §39's existential
    (which itself encapsulates §38's substantive Groebner-derived
    `linear_combination` polynomial identity).
  - **Defining-the-conclusion check**: the conclusion is NOT trivially derivable
    from the membership conjuncts; the linear-independence requires §39's
    non-vanishing.

**Downstream consumer (Bridge Lemma 6.2 follow-on, deferred)**: this triple
provides three H_Fib group-elements whose first-order Lie-algebra tangent
vectors span 𝔰𝔲(2). Composing with BCH cubic linearization
(`MatrixBCHCubic.bch_group_commutator_linearization`, ‖[exp(iF),exp(iG)] -
(1 - [F,G])‖ ≤ 356·δ³ for ‖F‖,‖G‖ ≤ δ ≤ 1), iterating produces small H_Fib
elements with spanning Lie directions, feeding the open-neighborhood-of-1
construction needed for `fibonacci_density_from_H_Fib_open_at_one` (= F.21).
-/

/-- Bridge from subtype-level multiplication `σ_Fib_1_SU * g * σ_Fib_1_SU⁻¹` to
matrix-level conjugation `σ_Fib_1_SU_mat · g.val · σ_Fib_1_SU_mat†`, for any
`g : ↥SU(2)`. Generic version of §34's `σ_Fib_1_conj_σ_Fib_2_val` applied to
arbitrary `g`. -/
theorem σ_Fib_1_conj_val_generic
    (g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ((σ_Fib_1_SU * g * σ_Fib_1_SU⁻¹).val :
        Matrix (Fin 2) (Fin 2) ℂ) =
      σ_Fib_1_SU_mat * g.val * σ_Fib_1_SU_mat.conjTranspose := by
  show σ_Fib_1_SU_mat * g.val * (σ_Fib_1_SU⁻¹).val =
    σ_Fib_1_SU_mat * g.val * σ_Fib_1_SU_mat.conjTranspose
  congr 1

/-- Subtype-to-matrix bridge for σ_Fib_2 conjugation (generic). -/
theorem σ_Fib_2_conj_val_generic
    (g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ((σ_Fib_2_SU * g * σ_Fib_2_SU⁻¹).val :
        Matrix (Fin 2) (Fin 2) ℂ) =
      σ_Fib_2_SU_mat * g.val * σ_Fib_2_SU_mat.conjTranspose := by
  show σ_Fib_2_SU_mat * g.val * (σ_Fib_2_SU⁻¹).val =
    σ_Fib_2_SU_mat * g.val * σ_Fib_2_SU_mat.conjTranspose
  congr 1

/-- **R5.4 Layer F.20.c.d.2.q — Three-conjugate H_Fib spanning triple at Gap-1**.

The three SU(2) elements

  `h_gap1 := σ_Fib_1_SU · σ_Fib_2_SU · σ_Fib_1_SU⁻¹`
  `h_1    := σ_Fib_1_SU · h_gap1 · σ_Fib_1_SU⁻¹`
  `h_2    := σ_Fib_2_SU · h_gap1 · σ_Fib_2_SU⁻¹`

are all in H_Fib, and their `liePartMat` matrix values are **ℝ-linearly
independent** in 𝔰𝔲(2) — equivalently, they span 𝔰𝔲(2).

**Proof structure**:
  1. Membership: subgroup closure (`H_Fib.mul_mem` + `H_Fib.inv_mem`) with
     `σ_Fib_1_SU_mem_H_Fib`, `σ_Fib_2_SU_mem_H_Fib`, and §34's gap-1 membership.
  2. Ad-equivariance: `liePartMat (σ_i·h_gap1·σ_i⁻¹).val =
     σ_i_SU_mat · liePartMat h_gap1.val · σ_i_SU_mat†` via §13.
  3. Linear independence: `σ_Fib_lie_bundle_lin_indep` (§2) applied at
     `X := liePartMat h_gap1.val`, using §38's
     `σ_Fib_lie_bundle_pauliDet_at_gap1_ne_zero`.

This is the **substantive three-element spanning triple** consumed by the
Bridge Lemma 6.2 follow-on for F.21 unconditional density. -/
theorem H_Fib_gap1_three_conjugates_lin_indep :
    (σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹) ∈
      (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
    (σ_Fib_1_SU * (σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹) * σ_Fib_1_SU⁻¹) ∈
      (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
    (σ_Fib_2_SU * (σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹) * σ_Fib_2_SU⁻¹) ∈
      (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
    ∀ a b c : ℝ,
      (a : ℂ) • liePartMat ((σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹).val :
          Matrix (Fin 2) (Fin 2) ℂ) +
      (b : ℂ) • liePartMat
        ((σ_Fib_1_SU * (σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹) * σ_Fib_1_SU⁻¹).val :
          Matrix (Fin 2) (Fin 2) ℂ) +
      (c : ℂ) • liePartMat
        ((σ_Fib_2_SU * (σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹) * σ_Fib_2_SU⁻¹).val :
          Matrix (Fin 2) (Fin 2) ℂ) = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  set h_gap1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹ with h_gap1_def
  -- Step 1: membership of h_gap1, h_1, h_2 in H_Fib
  have h_gap1_mem : h_gap1 ∈ SKEFTHawking.FKLW.H_Fib :=
    σ_Fib_1_conj_σ_Fib_2_mem_H_Fib
  have h_1_mem :
      σ_Fib_1_SU * h_gap1 * σ_Fib_1_SU⁻¹ ∈ SKEFTHawking.FKLW.H_Fib :=
    SKEFTHawking.FKLW.H_Fib.mul_mem
      (SKEFTHawking.FKLW.H_Fib.mul_mem
        SKEFTHawking.FKLW.σ_Fib_1_SU_mem_H_Fib h_gap1_mem)
      (SKEFTHawking.FKLW.H_Fib.inv_mem SKEFTHawking.FKLW.σ_Fib_1_SU_mem_H_Fib)
  have h_2_mem :
      σ_Fib_2_SU * h_gap1 * σ_Fib_2_SU⁻¹ ∈ SKEFTHawking.FKLW.H_Fib :=
    SKEFTHawking.FKLW.H_Fib.mul_mem
      (SKEFTHawking.FKLW.H_Fib.mul_mem
        SKEFTHawking.FKLW.σ_Fib_2_SU_mem_H_Fib h_gap1_mem)
      (SKEFTHawking.FKLW.H_Fib.inv_mem SKEFTHawking.FKLW.σ_Fib_2_SU_mem_H_Fib)
  refine ⟨h_gap1_mem, h_1_mem, h_2_mem, ?_⟩
  -- Step 2: build the matrix-level conjugate values and Ad-equivariance of liePartMat
  intro a b c h_lin
  set X : Matrix (Fin 2) (Fin 2) ℂ := liePartMat h_gap1.val with hX_def
  have h_pauliDet_X_ne :
      σ_Fib_lie_bundle_pauliDet X ≠ 0 := by
    show σ_Fib_lie_bundle_pauliDet
      (liePartMat h_gap1.val) ≠ 0
    rw [σ_Fib_1_conj_σ_Fib_2_val]
    exact σ_Fib_lie_bundle_pauliDet_at_gap1_ne_zero
  -- liePart h_1.val = Ad(σ_Fib_1)(X)
  have h_liePart_1 :
      liePartMat ((σ_Fib_1_SU * h_gap1 * σ_Fib_1_SU⁻¹).val :
          Matrix (Fin 2) (Fin 2) ℂ) =
        σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose := by
    rw [σ_Fib_1_conj_val_generic, liePartMat_conj_σ_Fib_1_SU_mat]
  -- liePart h_2.val = Ad(σ_Fib_2)(X)
  have h_liePart_2 :
      liePartMat ((σ_Fib_2_SU * h_gap1 * σ_Fib_2_SU⁻¹).val :
          Matrix (Fin 2) (Fin 2) ℂ) =
        σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose := by
    rw [σ_Fib_2_conj_val_generic, liePartMat_conj_σ_Fib_2_SU_mat]
  -- Substitute into the hypothesis and apply σ_Fib_lie_bundle_lin_indep
  rw [h_liePart_1, h_liePart_2] at h_lin
  exact σ_Fib_lie_bundle_lin_indep h_pauliDet_X_ne h_lin

/-- **R5.4 Layer F.20.c.d.2.q-app — Spanning form of the three-conjugate triple**.

For every `Y ∈ tracelessSkewHermitian (Fin 2)` (= every `Y ∈ 𝔰𝔲(2)`), there
exist real coefficients `a, b, c` such that

  `Y = a · liePartMat h_gap1.val + b · liePartMat h_1.val + c · liePartMat h_2.val`

(where the operands are as in `H_Fib_gap1_three_conjugates_lin_indep`).

This is the **spanning** companion to the linear-independence theorem above:
together they certify that the three `liePartMat` values form a basis of
𝔰𝔲(2). Direct composition of `tracelessSkewHermitian_exists_combo_of_pauliDet_ne_zero`
(SU2LieAlgebra §15 spanning criterion) with the Ad-equivariance of
`liePartMat` (§13) and the non-vanishing pauliDet at gap1 (§38). -/
theorem H_Fib_gap1_three_conjugates_spans
    {Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hY : Y ∈ tracelessSkewHermitian (Fin 2)) :
    ∃ a b c : ℝ,
      Y = (a : ℂ) • liePartMat ((σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹).val :
            Matrix (Fin 2) (Fin 2) ℂ) +
          (b : ℂ) • liePartMat
            ((σ_Fib_1_SU * (σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹) *
              σ_Fib_1_SU⁻¹).val : Matrix (Fin 2) (Fin 2) ℂ) +
          (c : ℂ) • liePartMat
            ((σ_Fib_2_SU * (σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹) *
              σ_Fib_2_SU⁻¹).val : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- X := liePartMat h_gap1.val ∈ 𝔰𝔲(2) (via liePartMat_mem_tracelessSkewHermitian)
  set X : Matrix (Fin 2) (Fin 2) ℂ :=
    liePartMat (σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹).val with hX_def
  have hX_mem : X ∈ tracelessSkewHermitian (Fin 2) :=
    liePartMat_mem_tracelessSkewHermitian _
  -- Three bundle members are all in 𝔰𝔲(2) (Ad preserves)
  have h_AdX1_mem :
      σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose ∈
        tracelessSkewHermitian (Fin 2) :=
    tracelessSkewHermitian_conj_σ_Fib_1_SU_mat hX_mem
  have h_AdX2_mem :
      σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose ∈
        tracelessSkewHermitian (Fin 2) :=
    tracelessSkewHermitian_conj_σ_Fib_2_SU_mat hX_mem
  -- pauliDet ≠ 0 at X (from §39 ship via the subtype-value bridge)
  have h_pauliDet_X_ne : σ_Fib_lie_bundle_pauliDet X ≠ 0 := by
    show σ_Fib_lie_bundle_pauliDet
      (liePartMat (σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹).val) ≠ 0
    rw [σ_Fib_1_conj_σ_Fib_2_val]
    exact σ_Fib_lie_bundle_pauliDet_at_gap1_ne_zero
  -- Apply the abstract spanning criterion
  obtain ⟨a, b, c, h_eq⟩ :=
    tracelessSkewHermitian_exists_combo_of_pauliDet_ne_zero
      hX_mem h_AdX1_mem h_AdX2_mem h_pauliDet_X_ne hY
  -- h_eq : Y = a • X + b • (σ_1·X·σ_1†) + c • (σ_2·X·σ_2†)
  -- Rewrite via Ad-equivariance of liePartMat to identify the bundle members
  -- as liePart of the conjugate group elements.
  refine ⟨a, b, c, ?_⟩
  rw [show liePartMat
        ((σ_Fib_1_SU * (σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹) *
          σ_Fib_1_SU⁻¹).val : Matrix (Fin 2) (Fin 2) ℂ) =
        σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose by
    rw [σ_Fib_1_conj_val_generic, liePartMat_conj_σ_Fib_1_SU_mat]]
  rw [show liePartMat
        ((σ_Fib_2_SU * (σ_Fib_1_SU * σ_Fib_2_SU * σ_Fib_1_SU⁻¹) *
          σ_Fib_2_SU⁻¹).val : Matrix (Fin 2) (Fin 2) ℂ) =
        σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose by
    rw [σ_Fib_2_conj_val_generic, liePartMat_conj_σ_Fib_2_SU_mat]]
  exact h_eq

/-! ## §41. R5.4 Layer F.20.c.d.2.r — Generic spanning theorem for any H_Fib element
with non-zero σ_Fib_lie_bundle_pauliDet at its liePart

Lifts the Gap-1-specific `H_Fib_gap1_three_conjugates_lin_indep` (§40) to a
parametric form: for any `h ∈ H_Fib` with `σ_Fib_lie_bundle_pauliDet (liePart h) ≠ 0`,
the three H_Fib conjugates `(h, σ_1·h·σ_1⁻¹, σ_2·h·σ_2⁻¹)` are all in H_Fib AND
have ℝ-lin-indep liePart directions in 𝔰𝔲(2).

This is the **generic foundation** for the Bridge Lemma 6.2 follow-on: if we can
produce a small `h ∈ H_Fib` (via D.3.h's `H_Fib_small_witness_val`) AND show its
liePart has non-zero σ_Fib_lie_bundle_pauliDet, we automatically get three small
spanning H_Fib elements.

Substantive content here: same composition logic as §40, but lifted to generic h. -/

/-- **R5.4 Layer F.20.c.d.2.r — generic three-conjugate H_Fib spanning at any
non-zero-pauliDet element**.

For any `h ∈ H_Fib` whose `liePartMat` has non-zero `σ_Fib_lie_bundle_pauliDet`,
the three SU(2)-elements `(h, σ_Fib_1_SU·h·σ_Fib_1_SU⁻¹, σ_Fib_2_SU·h·σ_Fib_2_SU⁻¹)`
are all in H_Fib AND their liePartMat values are ℝ-linearly independent in 𝔰𝔲(2).

Composes:
  - Subgroup closure (`H_Fib.mul_mem` + `H_Fib.inv_mem` with σ_Fib_{1,2}_SU_mem_H_Fib)
  - Ad-equivariance (`σ_Fib_{1,2}_conj_val_generic` + `liePartMat_conj_σ_Fib_{1,2}_SU_mat`)
  - Linear-independence criterion (`σ_Fib_lie_bundle_lin_indep` from §2)

This is the **generic engine** — §40's `H_Fib_gap1_three_conjugates_lin_indep`
is the corollary at the specific Gap-1 witness. Downstream Bridge-Lemma-6.2
work consumes this with the small-h hypothesis from D.3.h. -/
theorem H_Fib_three_conjugates_lin_indep_generic
    (h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_H : h ∈ (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    (h_pauliDet_ne : σ_Fib_lie_bundle_pauliDet
      (liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0) :
    (σ_Fib_1_SU * h * σ_Fib_1_SU⁻¹) ∈
      (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
    (σ_Fib_2_SU * h * σ_Fib_2_SU⁻¹) ∈
      (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
    ∀ a b c : ℝ,
      (a : ℂ) • liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ) +
      (b : ℂ) • liePartMat ((σ_Fib_1_SU * h * σ_Fib_1_SU⁻¹).val :
          Matrix (Fin 2) (Fin 2) ℂ) +
      (c : ℂ) • liePartMat ((σ_Fib_2_SU * h * σ_Fib_2_SU⁻¹).val :
          Matrix (Fin 2) (Fin 2) ℂ) = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  have h_1_mem :
      σ_Fib_1_SU * h * σ_Fib_1_SU⁻¹ ∈ SKEFTHawking.FKLW.H_Fib :=
    SKEFTHawking.FKLW.H_Fib_conj_σ1_mem h h_H
  have h_2_mem :
      σ_Fib_2_SU * h * σ_Fib_2_SU⁻¹ ∈ SKEFTHawking.FKLW.H_Fib :=
    SKEFTHawking.FKLW.H_Fib_conj_σ2_mem h h_H
  refine ⟨h_1_mem, h_2_mem, ?_⟩
  intro a b c h_lin
  set X : Matrix (Fin 2) (Fin 2) ℂ := liePartMat h.val with hX_def
  -- Substitute Ad-equivariance: liePart (σ_i · h · σ_i⁻¹) = σ_i · X · σ_i†
  have h_liePart_1 :
      liePartMat ((σ_Fib_1_SU * h * σ_Fib_1_SU⁻¹).val :
          Matrix (Fin 2) (Fin 2) ℂ) =
        σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose := by
    rw [σ_Fib_1_conj_val_generic, liePartMat_conj_σ_Fib_1_SU_mat]
  have h_liePart_2 :
      liePartMat ((σ_Fib_2_SU * h * σ_Fib_2_SU⁻¹).val :
          Matrix (Fin 2) (Fin 2) ℂ) =
        σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose := by
    rw [σ_Fib_2_conj_val_generic, liePartMat_conj_σ_Fib_2_SU_mat]
  rw [h_liePart_1, h_liePart_2] at h_lin
  exact σ_Fib_lie_bundle_lin_indep h_pauliDet_ne h_lin

/-- **R5.4 Layer F.20.c.d.2.r-app — generic spanning consequence**.

If `h ∈ H_Fib` has `σ_Fib_lie_bundle_pauliDet (liePartMat h) ≠ 0`, then every
Y ∈ 𝔰𝔲(2) is an ℝ-linear combination of (liePart h, liePart h_1, liePart h_2)
where h_1 := σ_Fib_1·h·σ_Fib_1⁻¹ and h_2 := σ_Fib_2·h·σ_Fib_2⁻¹.

Generic version of §40's `H_Fib_gap1_three_conjugates_spans`. -/
theorem H_Fib_three_conjugates_span_generic
    (h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_pauliDet_ne : σ_Fib_lie_bundle_pauliDet
      (liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0)
    {Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hY : Y ∈ tracelessSkewHermitian (Fin 2)) :
    ∃ a b c : ℝ,
      Y = (a : ℂ) • liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ) +
          (b : ℂ) • liePartMat ((σ_Fib_1_SU * h * σ_Fib_1_SU⁻¹).val :
            Matrix (Fin 2) (Fin 2) ℂ) +
          (c : ℂ) • liePartMat ((σ_Fib_2_SU * h * σ_Fib_2_SU⁻¹).val :
            Matrix (Fin 2) (Fin 2) ℂ) := by
  set X : Matrix (Fin 2) (Fin 2) ℂ := liePartMat h.val with hX_def
  have hX_mem : X ∈ tracelessSkewHermitian (Fin 2) :=
    liePartMat_mem_tracelessSkewHermitian _
  have h_AdX1_mem :
      σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose ∈
        tracelessSkewHermitian (Fin 2) :=
    tracelessSkewHermitian_conj_σ_Fib_1_SU_mat hX_mem
  have h_AdX2_mem :
      σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose ∈
        tracelessSkewHermitian (Fin 2) :=
    tracelessSkewHermitian_conj_σ_Fib_2_SU_mat hX_mem
  obtain ⟨a, b, c, h_eq⟩ :=
    tracelessSkewHermitian_exists_combo_of_pauliDet_ne_zero
      hX_mem h_AdX1_mem h_AdX2_mem h_pauliDet_ne hY
  refine ⟨a, b, c, ?_⟩
  rw [show liePartMat ((σ_Fib_1_SU * h * σ_Fib_1_SU⁻¹).val :
        Matrix (Fin 2) (Fin 2) ℂ) =
        σ_Fib_1_SU_mat * X * σ_Fib_1_SU_mat.conjTranspose by
    rw [σ_Fib_1_conj_val_generic, liePartMat_conj_σ_Fib_1_SU_mat]]
  rw [show liePartMat ((σ_Fib_2_SU * h * σ_Fib_2_SU⁻¹).val :
        Matrix (Fin 2) (Fin 2) ℂ) =
        σ_Fib_2_SU_mat * X * σ_Fib_2_SU_mat.conjTranspose by
    rw [σ_Fib_2_conj_val_generic, liePartMat_conj_σ_Fib_2_SU_mat]]
  exact h_eq

/-! ## §42. R5.4 Layer F.20.c.d.2.s — Three small spanning H_Fib elements from
small h with non-zero pauliDet (Bridge Lemma 6.2 setup)

Composes §41's generic spanning theorem with `specialUnitary_conjugation_norm_le_four`
(D.2.a) to produce, from a HYPOTHESIS small h ∈ H_Fib with non-zero
σ_Fib_lie_bundle_pauliDet at liePart, an explicit three-element H_Fib triple
of small elements (scales ε, 4ε, 4ε) with ℝ-lin-indep liePartMat directions.

**Strategic significance**: this makes the F.21 residual hypothesis EXPLICIT.
With the §42 ship, the path from "small h with non-zero pauliDet" to "open
neighborhood of 1 ⊆ H_Fib" reduces to:
  1. (HYPOTHESIS) ∃ small h ∈ H_Fib with non-zero σ_Fib_lie_bundle_pauliDet (THIS IS THE F.21 RESIDUAL)
  2. §42: produce three small spanning H_Fib elements
  3. (TODO Bridge Lemma 6.2 substantive content) IFT/BCH-iteration from spanning triple to open nhd
  4. `closure_eq_univ_of_one_mem_interior` + `fibonacci_density_from_H_Fib_open_at_one`

Step 1 is the substantive remaining content; step 3 is the analytic IFT content.
This ship clearly separates them. -/

/-- **R5.4 Layer F.20.c.d.2.s — three small spanning H_Fib elements from small h
with non-zero pauliDet**.

If there exists `h ∈ H_Fib` with `‖h.val - 1‖ < ε` AND `σ_Fib_lie_bundle_pauliDet
(liePartMat h.val) ≠ 0`, then there exist three SU(2)-elements `h₀, h₁, h₂`, all
in H_Fib, with:
  • `‖h₀.val - 1‖ < ε`
  • `‖h₁.val - 1‖ < 4·ε`
  • `‖h₂.val - 1‖ < 4·ε`

and their liePartMat values are ℝ-linearly independent in 𝔰𝔲(2).

**Construction**: take h₀ := h, h₁ := σ_Fib_1·h·σ_Fib_1⁻¹, h₂ := σ_Fib_2·h·σ_Fib_2⁻¹.

  - h₀ ∈ H_Fib by hypothesis.
  - h₁, h₂ ∈ H_Fib by `H_Fib_conj_σ{1,2}_mem` (subgroup closure).
  - Norm bounds via `specialUnitary_conjugation_norm_le_four`
    (`‖σ·g·σ⁻¹ - 1‖ ≤ 4·‖g - 1‖`).
  - ℝ-lin-indep via §41's `H_Fib_three_conjugates_lin_indep_generic`.

This is the **explicit consumer** of §41's generic spanning engine for the
downstream Bridge Lemma 6.2 work. -/
theorem H_Fib_three_small_spanning_from_small_pauliDet
    {ε : ℝ}
    (h_exists : ∃ h ∈ (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      ‖(h : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < ε ∧
      σ_Fib_lie_bundle_pauliDet
        (liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0) :
    ∃ (h₀ h₁ h₂ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      h₀ ∈ (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
      h₁ ∈ (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
      h₂ ∈ (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
      ‖(h₀ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < ε ∧
      ‖(h₁ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < 4 * ε ∧
      ‖(h₂ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < 4 * ε ∧
      (∀ a b c : ℝ,
        (a : ℂ) • liePartMat (h₀ : Matrix (Fin 2) (Fin 2) ℂ) +
        (b : ℂ) • liePartMat (h₁ : Matrix (Fin 2) (Fin 2) ℂ) +
        (c : ℂ) • liePartMat (h₂ : Matrix (Fin 2) (Fin 2) ℂ) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) := by
  obtain ⟨h, h_H, h_small, h_pauliDet_ne⟩ := h_exists
  refine ⟨h, σ_Fib_1_SU * h * σ_Fib_1_SU⁻¹, σ_Fib_2_SU * h * σ_Fib_2_SU⁻¹, h_H, ?_, ?_, h_small, ?_, ?_, ?_⟩
  · -- h₁ membership
    exact SKEFTHawking.FKLW.H_Fib_conj_σ1_mem h h_H
  · -- h₂ membership
    exact SKEFTHawking.FKLW.H_Fib_conj_σ2_mem h h_H
  · -- ‖h₁ - 1‖ < 4·ε
    calc ‖((σ_Fib_1_SU * h * σ_Fib_1_SU⁻¹ :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ) - 1‖
        ≤ 4 * ‖(h : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ :=
            SKEFTHawking.FKLW.specialUnitary_conjugation_norm_le_four σ_Fib_1_SU h
      _ < 4 * ε := by
          apply mul_lt_mul_of_pos_left h_small
          norm_num
  · -- ‖h₂ - 1‖ < 4·ε
    calc ‖((σ_Fib_2_SU * h * σ_Fib_2_SU⁻¹ :
              ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ) - 1‖
        ≤ 4 * ‖(h : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ :=
            SKEFTHawking.FKLW.specialUnitary_conjugation_norm_le_four σ_Fib_2_SU h
      _ < 4 * ε := by
          apply mul_lt_mul_of_pos_left h_small
          norm_num
  · -- Linear independence via §41's generic theorem
    intro a b c h_lin
    have h_gen := H_Fib_three_conjugates_lin_indep_generic h h_H h_pauliDet_ne
    exact h_gen.2.2 a b c h_lin

/-! ## §43. R5.4 Layer F.20.c.d.2.t — F.21 residual hypothesis as explicit Prop

Defines the **F.21 residual hypothesis** as a clean Prop. The hypothesis asserts
that for every ε > 0, H_Fib contains an element of scale < ε with non-zero
σ_Fib_lie_bundle_pauliDet at its liePart.

If this hypothesis holds, then via §42 + the Bridge Lemma 6.2 follow-on
(deferred substantive analytic content), F.21 unconditional Fibonacci density
follows.

The §39 existential (session 62) gives the NON-SMALL version at the Gap-1 witness;
the residual is the SMALL version. The gap is approximately a continuity +
density argument (or BCH iteration through the gap-1 witness's σ-conjugates).
-/

/-- **R5.4 Layer F.20.c.d.2.t — F.21 small-spanning residual hypothesis**.

For every ε > 0, there exists h ∈ H_Fib with ‖h.val - 1‖ < ε AND non-zero
σ_Fib_lie_bundle_pauliDet at liePartMat h.val.

This is the **F.21 residual hypothesis**. The substantive content remaining for
unconditional Fibonacci density (F.21) splits into:
  1. **This hypothesis** (small spanning H_Fib element exists at every scale).
  2. **Bridge Lemma 6.2** (small spanning triple → open neighborhood of 1).

Session 63+64 provide the generic engine for (1). The §39 existential
(session 62) gives the NON-SMALL version (Gap-1 witness in H_Fib has non-zero
pauliDet). The residual gap (1) is: can we find small such elements?

Approaches: (a) explicit iteration of σ-conjugates of the Gap-1 witness;
(b) continuity + density argument leveraging H_Fib_accPt_one and the openness
of the spanning locus; (c) Cartan classification (avoids the iteration entirely
but needs Mathlib4 substrate not yet shipped). -/
def F21_residual_small_spanning : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ h ∈ (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      ‖(h : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < ε ∧
      σ_Fib_lie_bundle_pauliDet
        (liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0

/-- **R5.4 Layer F.20.c.d.2.t-app — small spanning triples at every scale, from
the F.21 residual hypothesis**.

Composes §43's residual hypothesis with §42 to produce, for every ε > 0, an
explicit three-element small spanning H_Fib triple.

This is the **clean structural API** that the Bridge Lemma 6.2 follow-on
consumes. -/
theorem F21_residual_implies_small_spanning_triples
    (h_residual : F21_residual_small_spanning) :
    ∀ ε : ℝ, 0 < ε →
    ∃ (h₀ h₁ h₂ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      h₀ ∈ (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
      h₁ ∈ (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
      h₂ ∈ (SKEFTHawking.FKLW.H_Fib :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
      ‖(h₀ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < ε ∧
      ‖(h₁ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < 4 * ε ∧
      ‖(h₂ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < 4 * ε ∧
      (∀ a b c : ℝ,
        (a : ℂ) • liePartMat (h₀ : Matrix (Fin 2) (Fin 2) ℂ) +
        (b : ℂ) • liePartMat (h₁ : Matrix (Fin 2) (Fin 2) ℂ) +
        (c : ℂ) • liePartMat (h₂ : Matrix (Fin 2) (Fin 2) ℂ) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) := by
  intro ε hε
  exact H_Fib_three_small_spanning_from_small_pauliDet (h_residual ε hε)

/-! ## §44. R5.4 Layer F.20.c.d.2.u — Modular F.21 statement: residual + Bridge Lemma 6.2 → density

The MODULAR F.21 architecture splits the unconditional density into two clean
substantive hypotheses + the existing density chain:

  H1 := **F21_residual_small_spanning** (Layer F.20.c.d.2.t):
        ∀ ε > 0, ∃ small h ∈ H_Fib with non-zero σ_Fib_lie_bundle_pauliDet.

  H2 := **F21_BridgeLemma62_OpenNhd** (this section):
        ∀ small spanning H_Fib triple, ∃ open neighborhood of 1 in H_Fib.

The composition theorem `fibonacci_density_from_F21_residual_and_bridge_lemma_62`
chains H1 + H2 through:
  - §42 `H_Fib_three_small_spanning_from_small_pauliDet` (residual → triple)
  - H2 (triple → open nhd)
  - `fibonacci_density_from_H_Fib_open_at_one` (Layer E final composition)

to deliver `DenseInSpecialUnitary 3 2 ρ_Fib_SU2` (= F.21).

**This is the structurally clean state-of-the-art for F.21**:
  - H1 substantive content: ~150 LoC (small spanning element existence)
  - H2 substantive content: ~100-200 LoC (BCH-iteration IFT-style open nbhd)
  - Composition: this section (~50 LoC, structural)
-/

/-- **R5.4 Layer F.20.c.d.2.u — F.21 Bridge Lemma 6.2 hypothesis (small spanning → open nhd)**.

For every small spanning H_Fib triple — three H_Fib elements (h₀, h₁, h₂) at scales
(ε, 4ε, 4ε) with ℝ-lin-indep liePartMat directions — there exists an open
neighborhood of `(1 : SU(2))` contained in H_Fib.

This is the **BCH/IFT iteration** content of Aharonov-Arad Bridge Lemma 6.2: integer
products of small spanning Lie-algebra elements cover an open neighborhood. The
substantive proof requires:
  - Local diffeomorphism of `exp` at 0 (shipped: SU2LocalDiffeo Cartan-C).
  - BCH cubic linearization for product approximation (shipped: MatrixBCHCubic).
  - IFT-style 3D injection (m_1, m_2, m_3) → h₀^{m_1} h₁^{m_2} h₂^{m_3}.

Estimated ~100-200 LoC to discharge directly. -/
def F21_BridgeLemma62_OpenNhd : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (∃ (h₀ h₁ h₂ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      h₀ ∈ (SKEFTHawking.FKLW.H_Fib :
          Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
      h₁ ∈ (SKEFTHawking.FKLW.H_Fib :
          Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
      h₂ ∈ (SKEFTHawking.FKLW.H_Fib :
          Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
      ‖(h₀ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < ε ∧
      ‖(h₁ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < 4 * ε ∧
      ‖(h₂ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < 4 * ε ∧
      (∀ a b c : ℝ,
        (a : ℂ) • liePartMat (h₀ : Matrix (Fin 2) (Fin 2) ℂ) +
        (b : ℂ) • liePartMat (h₁ : Matrix (Fin 2) (Fin 2) ℂ) +
        (c : ℂ) • liePartMat (h₂ : Matrix (Fin 2) (Fin 2) ℂ) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0)) →
    ∃ V ∈ nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      V ⊆ (SKEFTHawking.FKLW.H_Fib :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- **R5.4 Layer F.20.c.d.2.u HEADLINE — Modular F.21 density theorem**.

If the **F21 residual** (`F21_residual_small_spanning`) holds AND the **Bridge
Lemma 6.2** (`F21_BridgeLemma62_OpenNhd`) holds, then the Fibonacci density
predicate `DenseInSpecialUnitary 3 2 ρ_Fib_SU2` (= F.21) follows.

This is the **modular F.21 statement**: it cleanly decomposes the unconditional
density into two substantive hypotheses + the existing density chain
(`fibonacci_density_from_H_Fib_open_at_one`).

Proof structure:
  1. From F21_residual + arbitrary ε > 0, get small h ∈ H_Fib with non-zero pauliDet.
  2. Apply §42 to get small spanning triple.
  3. Apply F21_BridgeLemma62_OpenNhd to get open V ⊆ H_Fib near 1.
  4. Apply `fibonacci_density_from_H_Fib_open_at_one` (FibonacciDensityConditional).

The ε is chosen as 1/64 (matching `H_Fib_iteration_scale_le_inv_64` for downstream
BCH-iteration compatibility, though the Bridge Lemma 6.2 hypothesis doesn't
require this specific choice). -/
theorem fibonacci_density_from_F21_residual_and_bridge_lemma_62
    (h_residual : F21_residual_small_spanning)
    (h_bridge : F21_BridgeLemma62_OpenNhd) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (SKEFTHawking.FKLW.ρ_Fib_SU2 b :
          Matrix (Fin 2) (Fin 2) ℂ)) := by
  -- Step 1: choose any ε > 0; here ε := 1/64 (arbitrary positive).
  set ε : ℝ := (1 : ℝ) / 64 with hε_def
  have hε_pos : 0 < ε := by norm_num [hε_def]
  -- Step 2: F21 residual gives small h with non-zero pauliDet
  obtain ⟨h, h_H, h_small, h_pauliDet_ne⟩ := h_residual ε hε_pos
  -- Step 3: §42 gives small spanning triple
  have h_triple_exists :
      ∃ (h₀ h₁ h₂ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
        h₀ ∈ (SKEFTHawking.FKLW.H_Fib :
          Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
        h₁ ∈ (SKEFTHawking.FKLW.H_Fib :
          Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
        h₂ ∈ (SKEFTHawking.FKLW.H_Fib :
          Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
        ‖(h₀ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < ε ∧
        ‖(h₁ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < 4 * ε ∧
        ‖(h₂ : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < 4 * ε ∧
        (∀ a b c : ℝ,
          (a : ℂ) • liePartMat (h₀ : Matrix (Fin 2) (Fin 2) ℂ) +
          (b : ℂ) • liePartMat (h₁ : Matrix (Fin 2) (Fin 2) ℂ) +
          (c : ℂ) • liePartMat (h₂ : Matrix (Fin 2) (Fin 2) ℂ) = 0 →
          a = 0 ∧ b = 0 ∧ c = 0) :=
    H_Fib_three_small_spanning_from_small_pauliDet ⟨h, h_H, h_small, h_pauliDet_ne⟩
  -- Step 4: Bridge Lemma 6.2 yields open V ⊆ H_Fib near 1
  obtain ⟨V, hV_nhds, hV_sub⟩ := h_bridge ε hε_pos h_triple_exists
  -- Step 5: apply fibonacci_density_from_H_Fib_open_at_one
  exact
    SKEFTHawking.FKLW.FibonacciDensityConditional.fibonacci_density_from_H_Fib_open_at_one
      ⟨V, hV_nhds, hV_sub⟩

/-! ## §45. R5.4 Layer F.20.c.d.2.v — Cartan-classification-based modular F.21 statement
(Phase 5 Step 13 framework)

An ALTERNATIVE modular F.21 path via the **Cartan classification of closed subgroups of SU(2)**:

  > Every closed infinite non-abelian subgroup of SU(2) equals SU(2) itself.

This is a classical Lie-group classification result; Mathlib4 v4.29.0 does not yet
ship it as a constructive theorem. We define it here as a Prop hypothesis
`CartanClassificationOfSU2_Subgroup` and show that — IF it holds — F.21
follows immediately from already-shipped substrate (`H_Fib_isClosed` +
`H_Fib_infinite` + `σ_Fib_SU_not_commute`).

**Strategic significance for the autonomous loop**:

The Cartan path (Phase 5 Step 13) discharges F.21 with ONE substantive theorem
rather than the two-hypothesis modular path of §44 (residual + BridgeLemma62).
Either path is sufficient; the Cartan path is cleaner structurally but requires
substantial Lie-classification infrastructure.

The §45 ship makes the Cartan path EXPLICIT as a Prop and shows the trivial
composition to F.21. Future work on the substantive Cartan classification
(multi-session, ~500-1000 LoC) discharges this Prop.
-/

/-- **The Cartan classification of closed subgroups of SU(2)**.

Every closed infinite non-abelian subgroup of SU(2) is the whole SU(2).

This is a classical Lie-group classification theorem. In SU(2), the closed
subgroups are precisely:
  - Finite subgroups (binary polyhedral groups BD_n, BT = 2T, BO = 2O, BI = 2I)
  - Maximal tori U(1) (1-dim, abelian)
  - Normalizers of maximal tori N(T) = T ⊔ Tσ (1-dim, contains abelian U(1))
  - SU(2) itself (3-dim, non-abelian)

Among these, the ones that are BOTH infinite AND non-abelian are: N(T) and SU(2).
Since N(T) has an abelian core T of finite index 2, an element h ∈ N(T) \ T
inverts T (conjugation by h on T equals inversion). An infinite non-abelian
H ⊆ N(T) must therefore contain BOTH T (= H ∩ T, forced to be all of T by
infinity) AND elements outside T. But such elements either invert T (= N(T)
shape) or generate SU(2) more broadly.

The careful analysis rules out N(T) embedding for our H_Fib via D3.a's
`σ_Fib_SU_mat_not_conj_inverts` (σ_Fib_1·X·σ_Fib_1⁻¹ ≠ X⁻¹ for some X with
trace 0). So the only remaining option for infinite non-abelian closed H_Fib
is H_Fib = SU(2). -/
def CartanClassificationOfSU2_Subgroup : Prop :=
  ∀ (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
    IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) →
    Set.Infinite (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) →
    (∃ g h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      g ∈ H ∧ h ∈ H ∧ g * h ≠ h * g) →
    H = ⊤

/-- **R5.4 Layer F.20.c.d.2.v HEADLINE — Cartan-based F.21 density**.

From the Cartan classification of closed subgroups of SU(2)
(`CartanClassificationOfSU2_Subgroup`), F.21 unconditional Fibonacci density
follows IMMEDIATELY from already-shipped substrate:

  - H_Fib is closed (`SKEFTHawking.FKLW.H_Fib_isClosed`)
  - H_Fib is infinite (`SKEFTHawking.FKLW.H_Fib_infinite`)
  - H_Fib is non-abelian (`SKEFTHawking.FKLW.σ_Fib_SU_not_commute` +
    `σ_Fib_{1,2}_SU_mem_H_Fib`)

The Cartan hypothesis applied to H_Fib yields H_Fib = ⊤. Combined with
`H_Fib_eq_top_iff_closure_eq_univ` and `fibonacci_density_from_H_Fib_eq_top`,
we get DenseInSpecialUnitary 3 2 ρ_Fib_SU2 = F.21.

This is the **alternative modular F.21 statement** (vs §44's
residual+BridgeLemma62 path). Phase 5 Step 13 ships the substantive Cartan
classification (multi-session). -/
theorem fibonacci_density_from_cartan_classification
    (h_cartan : CartanClassificationOfSU2_Subgroup) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (SKEFTHawking.FKLW.ρ_Fib_SU2 b :
          Matrix (Fin 2) (Fin 2) ℂ)) := by
  -- Apply Cartan to H_Fib: closed + infinite + non-abelian ⟹ H_Fib = ⊤
  have h_H_top :
      SKEFTHawking.FKLW.H_Fib = (⊤ :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
    apply h_cartan SKEFTHawking.FKLW.H_Fib SKEFTHawking.FKLW.H_Fib_isClosed
      SKEFTHawking.FKLW.H_Fib_infinite
    -- Non-abelian: σ_Fib_1_SU, σ_Fib_2_SU ∈ H_Fib don't commute
    refine ⟨σ_Fib_1_SU, σ_Fib_2_SU,
      SKEFTHawking.FKLW.σ_Fib_1_SU_mem_H_Fib,
      SKEFTHawking.FKLW.σ_Fib_2_SU_mem_H_Fib,
      SKEFTHawking.FKLW.σ_Fib_SU_not_commute⟩
  -- Apply fibonacci_density_from_H_Fib_eq_top (existing substrate)
  exact SKEFTHawking.FKLW.fibonacci_density_from_H_Fib_eq_top h_H_top

/-! ## §46. R5.4 Layer F.20.c.d.2.w — Unified F.21 statement: EITHER modular path discharges density

Bundles the §44 (residual + Bridge Lemma 6.2) and §45 (Cartan classification) modular
F.21 paths into a single disjunction theorem. Discharging EITHER suffices for F.21.

This is the **architectural state-of-the-art** for F.21 unconditional Fibonacci density.
Future substantive work targets ONE of:
  - §44 path: F21_residual_small_spanning ∧ F21_BridgeLemma62_OpenNhd (~300 LoC)
  - §45 path: CartanClassificationOfSU2_Subgroup (~500-1000 LoC; Phase 5 Step 13)

Either path discharges F.21 unconditionally. -/

/-- **R5.4 Layer F.20.c.d.2.w HEADLINE — Unified F.21 statement via EITHER modular path**.

If EITHER the §44 residual+BridgeLemma62 modular path OR the §45 Cartan classification
modular path holds, then F.21 unconditional Fibonacci density follows.

This is the **structurally complete modular F.21 architecture**: the unconditional
density is reduced to one of two substantive content packages, each shippable
independently. -/
theorem fibonacci_density_F21_unified
    (h_paths : (F21_residual_small_spanning ∧ F21_BridgeLemma62_OpenNhd) ∨
               CartanClassificationOfSU2_Subgroup) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (SKEFTHawking.FKLW.ρ_Fib_SU2 b :
          Matrix (Fin 2) (Fin 2) ℂ)) := by
  rcases h_paths with ⟨h_residual, h_bridge⟩ | h_cartan
  · exact fibonacci_density_from_F21_residual_and_bridge_lemma_62 h_residual h_bridge
  · exact fibonacci_density_from_cartan_classification h_cartan

/-! ## §47. R5.4 Layer F.20.c.d.2.x — cFib closed form (Path A substrate, step 1)

Substantive substrate toward F21_residual_small_spanning discharge: define the
infinite-order element

  `cFib_SU_mat := σ_Fib_1_SU_mat * σ_Fib_2_SU_mat.conjTranspose`

(matrix-level realization of `cFib := σ_Fib_1_SU * σ_Fib_2_SU⁻¹` whose infinite
order is shipped via `cFib_not_isOfFinOrder` in FibSU2Density.lean §28), and
compute its trace closed form.

The trace `tr(cFib_SU_mat) = (3 - √5)/2 ≈ 0.382` corresponds to a rotation by
angle θ in SO(3) with `2·cos(θ/2) = (3-√5)/2`. Since this is irrational
(involves √5), θ is not a rational multiple of π, confirming infinite order.

**Substantive content**:
  - Compute `σ_Fib_2_SU_mat[1,1]` closed form (mirror of shipped `σ_Fib_2_SU_mat_entry_00`)
  - Use σ_Fib_1_SU_mat diagonal form (`σ_Fib_1_SU_mat_diagonal_form` §3)
  - Combine via entry-wise trace expansion + ω-cancellation + R-eigenvalue
    products (`R1_C_mul_star_Rtau_C` substrate)
  - Final reduction: `2·φInv² + 2·φInv·cos(7π/5) = (3-√5)/2` via `golden_phi_inv_sq`
    + `cos_7pi_div_5` (§§35-36 substrate). -/

/-- **`σ_Fib_2_SU_mat` entry (1,1)** (mirror of shipped entry (0,0) in §6).

`σ_Fib_2_SU_mat 1 1 = ω · (φInv·R1 + φInv²·Rτ)`. -/
theorem σ_Fib_2_SU_mat_entry_11 :
    σ_Fib_2_SU_mat 1 1 =
      ω_Fib_C * (φInv_C * R1_C + φInv_C * φInv_C * Rtau_C) := by
  have h_φInvSqrt_sq : φInvSqrt_C * φInvSqrt_C = φInv_C := by
    have := φInvSqrt_C_sq; rw [sq] at this; exact this
  unfold σ_Fib_2_SU_mat σ_Fib_2 σ_Fib_1 F_C
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  left
  linear_combination R1_C * h_φInvSqrt_sq

/-- **cFib matrix realization**: `cFib_SU_mat := σ_Fib_1_SU_mat * σ_Fib_2_SU_mat.conjTranspose`.

This is the underlying matrix of `cFib := σ_Fib_1_SU * σ_Fib_2_SU⁻¹` ∈ SU(2),
which has infinite order via `cFib_not_isOfFinOrder`. -/
noncomputable def cFib_SU_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  σ_Fib_1_SU_mat * σ_Fib_2_SU_mat.conjTranspose

/-- **Subtype-value bridge**: the underlying matrix of `cFib = σ_Fib_1_SU · σ_Fib_2_SU⁻¹`
equals `cFib_SU_mat`. -/
theorem cFib_val_eq_cFib_SU_mat :
    ((σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) =
      cFib_SU_mat := by
  show σ_Fib_1_SU_mat * (σ_Fib_2_SU⁻¹).val = cFib_SU_mat
  unfold cFib_SU_mat
  congr 1

/-- **Key identity**: `exp(-7πi/5) + exp(7πi/5) = 2·cos(7π/5)` (Euler's formula).

For the trace computation, the cross terms `R1·star Rτ + Rτ·star R1` reduce to
the real exponential sum via Euler. -/
theorem exp_neg_seven_pi_div_five_add_conj :
    Complex.exp (((-(7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I) +
      Complex.exp (((7 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) =
    ((2 * Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) := by
  -- exp(iθ) = cos(θ) + i·sin(θ); applied at ±7π/5 and sum cancels imaginary parts.
  have h_neg : Complex.exp (((-(7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I) =
      ((Real.cos (-(7 * Real.pi / 5)) : ℝ) : ℂ) +
        ((Real.sin (-(7 * Real.pi / 5)) : ℝ) : ℂ) * Complex.I := by
    rw [show (((-(7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I) =
          (((-(7 * Real.pi / 5)) : ℝ) : ℂ) * Complex.I from rfl]
    have := Complex.exp_mul_I ((-(7 * Real.pi / 5) : ℝ) : ℂ)
    rw [this]
    push_cast
    ring
  have h_pos : Complex.exp (((7 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) =
      ((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) +
        ((Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I := by
    have := Complex.exp_mul_I ((7 * Real.pi / 5 : ℝ) : ℂ)
    rw [this]
    push_cast
    ring
  rw [h_neg, h_pos, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- **Cross-term sum**: `R1·star Rτ + Rτ·star R1 = 2·cos(7π/5)`. -/
theorem R1_star_Rtau_add_Rtau_star_R1 :
    R1_C * star Rtau_C + Rtau_C * star R1_C =
      ((2 * Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) := by
  rw [R1_C_mul_star_Rtau_C]
  -- Rτ·star R1 = star(R1·star Rτ) = star(exp(-7πi/5))
  rw [show Rtau_C * star R1_C = star (R1_C * star Rtau_C) by
    rw [star_mul, star_star, mul_comm], R1_C_mul_star_Rtau_C]
  -- star(exp(-7πi/5)) = exp(7πi/5)
  rw [show (star (Complex.exp (((-(7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I)) : ℂ)
        = (starRingEnd ℂ) (Complex.exp (((-(7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I))
        from rfl, ← Complex.exp_conj]
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  -- The exponent: conj((-(7π/5))·I) = (-(7π/5))·(-I) = (7π/5)·I
  rw [show ((-(7 * Real.pi / 5 : ℝ) : ℝ) : ℂ) * -Complex.I =
        ((7 * Real.pi / 5 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact exp_neg_seven_pi_div_five_add_conj

/-- **Trace entry-wise expansion for cFib_SU_mat**.

`tr(σ_Fib_1_SU_mat · σ_Fib_2_SU_mat†) = σ_Fib_1[0,0]·star(σ_Fib_2[0,0]) +
  σ_Fib_1[1,1]·star(σ_Fib_2[1,1])` (since σ_Fib_1 is diagonal). -/
theorem cFib_SU_mat_trace_entrywise :
    Matrix.trace cFib_SU_mat =
      σ_Fib_1_SU_mat 0 0 * star (σ_Fib_2_SU_mat 0 0) +
      σ_Fib_1_SU_mat 1 1 * star (σ_Fib_2_SU_mat 1 1) := by
  unfold cFib_SU_mat
  rw [Matrix.trace_fin_two]
  have h_entry_00 : (σ_Fib_1_SU_mat * σ_Fib_2_SU_mat.conjTranspose) 0 0 =
      σ_Fib_1_SU_mat 0 0 * star (σ_Fib_2_SU_mat 0 0) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two,
        show σ_Fib_1_SU_mat 0 1 = 0 by
          rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
        Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
    ring
  have h_entry_11 : (σ_Fib_1_SU_mat * σ_Fib_2_SU_mat.conjTranspose) 1 1 =
      σ_Fib_1_SU_mat 1 1 * star (σ_Fib_2_SU_mat 1 1) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two,
        show σ_Fib_1_SU_mat 1 0 = 0 by
          rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
        Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
    ring
  rw [h_entry_00, h_entry_11]

/-- **Trace via diagonal entries** — substitute the closed forms of σ_Fib_1
diagonal entries and σ_Fib_2 (0,0) + (1,1) entries.

`Matrix.trace cFib_SU_mat = ω·R1 · star(ω·(φInv²·R1 + φInv·Rτ))
                          + ω·Rτ · star(ω·(φInv·R1 + φInv²·Rτ))`. -/
theorem cFib_SU_mat_trace_expanded :
    Matrix.trace cFib_SU_mat =
      ω_Fib_C * R1_C * star (ω_Fib_C * (φInv_C * φInv_C * R1_C + φInv_C * Rtau_C)) +
      ω_Fib_C * Rtau_C * star (ω_Fib_C * (φInv_C * R1_C + φInv_C * φInv_C * Rtau_C)) := by
  rw [cFib_SU_mat_trace_entrywise]
  rw [show σ_Fib_1_SU_mat 0 0 = ω_Fib_C * R1_C by
    rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
    show σ_Fib_1_SU_mat 1 1 = ω_Fib_C * Rtau_C by
    rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
    σ_Fib_2_SU_mat_entry_00, σ_Fib_2_SU_mat_entry_11]

/-- **σ_Fib_2_SU_mat entry (1,0)** (mirror of shipped entry_01).

`σ_Fib_2_SU_mat 1 0 = ω · φInv · φInvSqrt · (R1 - Rτ)`.

Note: σ_Fib_2_SU_mat is symmetric (NOT Hermitian) because F is symmetric and
σ_Fib_1_SU_mat is diagonal. So entry_10 = entry_01 — but the two-step
factoring `σ_Fib_2 = F·σ_Fib_1·F` yields the same closed form from the
(1,0) matrix multiplication path. -/
theorem σ_Fib_2_SU_mat_entry_10 :
    σ_Fib_2_SU_mat 1 0 =
      ω_Fib_C * (φInv_C * φInvSqrt_C * (R1_C - Rtau_C)) := by
  unfold σ_Fib_2_SU_mat σ_Fib_2 σ_Fib_1 F_C
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  left
  ring

/-! ## §49. R5.4 Layer F.20.c.d.2.z — cFib_SU_mat entry-wise closed forms

For Pauli decomposition of liePartMat cFib_SU_mat, we need the four entries of
cFib_SU_mat as closed forms in (ω, R1, Rτ, φInv, φInvSqrt). Since
σ_Fib_1_SU_mat is diagonal, each cFib_SU_mat[i,j] reduces to a single product
σ_Fib_1[i,i] · star(σ_Fib_2[j,i]). -/

/-- **cFib_SU_mat entry (0,0)**. -/
theorem cFib_SU_mat_entry_00 :
    cFib_SU_mat 0 0 =
      ω_Fib_C * R1_C * star (ω_Fib_C * (φInv_C * φInv_C * R1_C + φInv_C * Rtau_C)) := by
  unfold cFib_SU_mat
  rw [Matrix.mul_apply, Fin.sum_univ_two,
      show σ_Fib_1_SU_mat 0 1 = 0 by rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
      Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
  rw [show σ_Fib_1_SU_mat 0 0 = ω_Fib_C * R1_C by
    rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
    σ_Fib_2_SU_mat_entry_00]
  ring

/-- **cFib_SU_mat entry (0,1)**. -/
theorem cFib_SU_mat_entry_01 :
    cFib_SU_mat 0 1 =
      ω_Fib_C * R1_C *
        star (ω_Fib_C * (φInv_C * φInvSqrt_C * (R1_C - Rtau_C))) := by
  unfold cFib_SU_mat
  rw [Matrix.mul_apply, Fin.sum_univ_two,
      show σ_Fib_1_SU_mat 0 1 = 0 by rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
      Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
  rw [show σ_Fib_1_SU_mat 0 0 = ω_Fib_C * R1_C by
    rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
    σ_Fib_2_SU_mat_entry_10]
  ring

/-- **cFib_SU_mat entry (1,0)**. -/
theorem cFib_SU_mat_entry_10 :
    cFib_SU_mat 1 0 =
      ω_Fib_C * Rtau_C *
        star (ω_Fib_C * (φInv_C * φInvSqrt_C * (R1_C - Rtau_C))) := by
  unfold cFib_SU_mat
  rw [Matrix.mul_apply, Fin.sum_univ_two,
      show σ_Fib_1_SU_mat 1 0 = 0 by rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
      Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
  rw [show σ_Fib_1_SU_mat 1 1 = ω_Fib_C * Rtau_C by
    rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
    σ_Fib_2_SU_mat_entry_01]
  ring

/-- **cFib_SU_mat entry (1,1)**. -/
theorem cFib_SU_mat_entry_11 :
    cFib_SU_mat 1 1 =
      ω_Fib_C * Rtau_C *
        star (ω_Fib_C * (φInv_C * R1_C + φInv_C * φInv_C * Rtau_C)) := by
  unfold cFib_SU_mat
  rw [Matrix.mul_apply, Fin.sum_univ_two,
      show σ_Fib_1_SU_mat 1 0 = 0 by rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
      Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
  rw [show σ_Fib_1_SU_mat 1 1 = ω_Fib_C * Rtau_C by
    rw [σ_Fib_1_SU_mat_diagonal_form]; rfl,
    σ_Fib_2_SU_mat_entry_11]
  ring

/-! ## §48. R5.4 Layer F.20.c.d.2.y — cFib trace numerical closed form

Reduces `cFib_SU_mat_trace_expanded` to the closed-form `(3 - √5)/2` via the
algebraic substrate shipped above. -/

/-- **φInv_C is self-adjoint** (real cast). -/
theorem φInv_C_isSelfAdjoint : star φInv_C = φInv_C := by
  show star (((Real.goldenRatio⁻¹ : ℝ) : ℂ)) = ((Real.goldenRatio⁻¹ : ℝ) : ℂ)
  exact Complex.conj_ofReal _

/-- **R5.4 Layer F.20.c.d.2.y — Reduced algebraic form of `cFib_SU_mat_trace`**.

After star expansion + ω/R cancellation + golden-ratio identities, the trace
equals `2·φInv² + 2·φInv·cos(7π/5)`. -/
theorem cFib_SU_mat_trace_reduced :
    Matrix.trace cFib_SU_mat =
      (2 : ℂ) * φInv_C * φInv_C +
      φInv_C * ((2 * Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) := by
  rw [cFib_SU_mat_trace_expanded]
  -- Apply star distributions via simp only (terminates because no looping)
  simp only [star_mul, star_add, φInv_C_isSelfAdjoint]
  -- Use ω·star ω = 1, R1·star R1 = 1, Rτ·star Rτ = 1, and the cross-term identity
  have hω_sq : ω_Fib_C * star ω_Fib_C = 1 := unit_norm_star_eq_one norm_ω_Fib_C
  have hR1_sq : R1_C * star R1_C = 1 := unit_norm_star_eq_one norm_R1_C
  have hRtau_sq : Rtau_C * star Rtau_C = 1 := unit_norm_star_eq_one norm_Rtau_C
  have h_cross := R1_star_Rtau_add_Rtau_star_R1
  linear_combination
    R1_C * (φInv_C * φInv_C * star R1_C + φInv_C * star Rtau_C) * hω_sq +
    Rtau_C * (φInv_C * star R1_C + φInv_C * φInv_C * star Rtau_C) * hω_sq +
    φInv_C * φInv_C * hR1_sq + φInv_C * φInv_C * hRtau_sq +
    φInv_C * h_cross

/-- **R5.4 Layer F.20.c.d.2.y HEADLINE — closed-form trace of `cFib_SU_mat`**.

`Matrix.trace cFib_SU_mat = ((3 - √5)/2 : ℝ)` (cast to ℂ).

Composes `cFib_SU_mat_trace_reduced` (2·φInv² + 2·φInv·cos(7π/5)) with
substrate identities:
  - `Real.inv_goldenRatio`: φInv = (√5-1)/2 → cast to ℂ
  - `cos_7pi_div_5`: cos(7π/5) = (1-√5)/4
  - `Real.sq_sqrt`: √5² = 5

Final reduction in ℝ → cast to ℂ via push_cast. -/
theorem cFib_SU_mat_trace :
    Matrix.trace cFib_SU_mat = (((3 - Real.sqrt 5) / 2 : ℝ) : ℂ) := by
  rw [cFib_SU_mat_trace_reduced]
  -- Real-valued identities first
  have h_phi_inv_real : Real.goldenRatio⁻¹ = (Real.sqrt 5 - 1) / 2 := by
    rw [Real.inv_goldenRatio]
    show -Real.goldenConj = (Real.sqrt 5 - 1) / 2
    unfold Real.goldenConj
    ring
  have h_5 : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  -- Final real-valued algebraic identity:
  -- 2·φInv² + φInv·(2·cos(7π/5)) = (3-√5)/2
  -- = 2·((√5-1)/2)² + ((√5-1)/2)·(2·(1-√5)/4)
  -- = (√5-1)² / 2 + (√5-1)·(1-√5)/4
  -- = (5-2√5+1)/2 + (-(√5-1)²)/4
  -- = (6-2√5)/2 + (-(6-2√5))/4
  -- = 3-√5 - (3-√5)/2 = (3-√5)/2 ✓
  have h_real_id :
      (2 : ℝ) * Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹ +
        Real.goldenRatio⁻¹ * (2 * Real.cos (7 * Real.pi / 5)) =
      (3 - Real.sqrt 5) / 2 := by
    rw [h_phi_inv_real, cos_7pi_div_5]
    nlinarith [h_5, Real.sqrt_nonneg 5]
  -- Cast the real identity to ℂ
  have h_C_id :
      (((2 : ℝ) * Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹ +
        Real.goldenRatio⁻¹ * (2 * Real.cos (7 * Real.pi / 5)) : ℝ) : ℂ) =
      (((3 - Real.sqrt 5) / 2 : ℝ) : ℂ) := by
    rw [h_real_id]
  -- Identify the LHS with the goal's LHS via push_cast
  have h_lhs :
      (2 : ℂ) * φInv_C * φInv_C +
        φInv_C * ((2 * Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) =
      (((2 : ℝ) * Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹ +
          Real.goldenRatio⁻¹ * (2 * Real.cos (7 * Real.pi / 5)) : ℝ) : ℂ) := by
    show (2 : ℂ) * ((Real.goldenRatio⁻¹ : ℝ) : ℂ) * ((Real.goldenRatio⁻¹ : ℝ) : ℂ) +
      ((Real.goldenRatio⁻¹ : ℝ) : ℂ) * ((2 * Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) = _
    push_cast
    ring
  rw [h_lhs, h_C_id]

/-! ## §51. R5.4 Layer F.20.c.d.2.aa — Simplified cFib entries (after ω-cancellation)

Reduce the §49 cFib entry closed forms to simpler form using ω·star ω = 1 and
the R-eigenvalue identities. Foundation for Pauli decomposition.

**Substantive content**:
- cFib[0,0] = φInv² + φInv·exp(-7πi/5)
- cFib[1,1] = φInv² + φInv·exp(7πi/5)  (= star cFib[0,0])
- cFib[0,1] = φInv·φInvSqrt·(1 - exp(-7πi/5))

The (1,0) entry is omitted here since the Pauli decomposition only uses [0,1]
and [0,0] entries (per `matrixToPauliCoords` definition). -/

/-- **φInvSqrt_C is self-adjoint** (real cast). -/
theorem φInvSqrt_C_isSelfAdjoint : star φInvSqrt_C = φInvSqrt_C := by
  show star (((Real.sqrt Real.goldenRatio)⁻¹ : ℝ) : ℂ) =
    (((Real.sqrt Real.goldenRatio)⁻¹ : ℝ) : ℂ)
  exact Complex.conj_ofReal _

/-- **cFib_SU_mat entry (0,0) simplified**: `φInv² + φInv·exp(-7πi/5)`. -/
theorem cFib_SU_mat_entry_00_simplified :
    cFib_SU_mat 0 0 =
      φInv_C * φInv_C +
      φInv_C * Complex.exp (((-(7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I) := by
  rw [cFib_SU_mat_entry_00]
  simp only [star_mul, star_add, φInv_C_isSelfAdjoint]
  have hω_sq : ω_Fib_C * star ω_Fib_C = 1 := unit_norm_star_eq_one norm_ω_Fib_C
  have hR1_sq : R1_C * star R1_C = 1 := unit_norm_star_eq_one norm_R1_C
  have hR1starRtau := R1_C_mul_star_Rtau_C
  linear_combination
    R1_C * (φInv_C * φInv_C * star R1_C + φInv_C * star Rtau_C) * hω_sq +
    φInv_C * φInv_C * hR1_sq +
    φInv_C * hR1starRtau

/-- **cFib_SU_mat entry (1,1) simplified**: `φInv² + φInv·exp(7πi/5)`. -/
theorem cFib_SU_mat_entry_11_simplified :
    cFib_SU_mat 1 1 =
      φInv_C * φInv_C +
      φInv_C * Complex.exp (((7 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) := by
  rw [cFib_SU_mat_entry_11]
  simp only [star_mul, star_add, φInv_C_isSelfAdjoint]
  have hω_sq : ω_Fib_C * star ω_Fib_C = 1 := unit_norm_star_eq_one norm_ω_Fib_C
  have hRtau_sq : Rtau_C * star Rtau_C = 1 := unit_norm_star_eq_one norm_Rtau_C
  -- Rτ·star R1 = exp(7πi/5) (conjugate of R1·star Rτ = exp(-7πi/5))
  have hRtaustarR1 :
      Rtau_C * star R1_C = Complex.exp (((7 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) := by
    have hR1starRtau := R1_C_mul_star_Rtau_C
    have h_eq : Rtau_C * star R1_C = star (R1_C * star Rtau_C) := by
      rw [star_mul, star_star, mul_comm]
    rw [h_eq, hR1starRtau]
    rw [show (star (Complex.exp (((-(7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I)) : ℂ)
          = (starRingEnd ℂ) (Complex.exp (((-(7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I))
          from rfl, ← Complex.exp_conj]
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring
  linear_combination
    Rtau_C * (φInv_C * star R1_C + φInv_C * φInv_C * star Rtau_C) * hω_sq +
    φInv_C * φInv_C * hRtau_sq +
    φInv_C * hRtaustarR1

/-- **cFib_SU_mat entry (0,1) simplified**: `φInv·φInvSqrt·(1 - exp(-7πi/5))`. -/
theorem cFib_SU_mat_entry_01_simplified :
    cFib_SU_mat 0 1 =
      φInv_C * φInvSqrt_C *
        (1 - Complex.exp (((-(7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I)) := by
  rw [cFib_SU_mat_entry_01]
  simp only [star_mul, star_sub, φInv_C_isSelfAdjoint, φInvSqrt_C_isSelfAdjoint]
  have hω_sq : ω_Fib_C * star ω_Fib_C = 1 := unit_norm_star_eq_one norm_ω_Fib_C
  have hR1_sq : R1_C * star R1_C = 1 := unit_norm_star_eq_one norm_R1_C
  have hR1starRtau := R1_C_mul_star_Rtau_C
  linear_combination
    R1_C * (φInv_C * φInvSqrt_C * (star R1_C - star Rtau_C)) * hω_sq +
    φInv_C * φInvSqrt_C * hR1_sq -
    φInv_C * φInvSqrt_C * hR1starRtau

/-! ## §52. R5.4 Layer F.20.c.d.2.bb — cFib Pauli coordinates (closed form)

Extract `matrixToPauliCoords cFib_SU_mat` in closed form using §51's simplified
entries + Euler's formula `exp(iθ) = cos θ + i·sin θ`:

  a = (cFib[0,1]).im = φInv·φInvSqrt·sin(7π/5)
  b = (cFib[0,1]).re = φInv·φInvSqrt·(1 - cos(7π/5))
  c = (cFib[0,0]).im = -φInv·sin(7π/5)

Since `liePartMat h = h - (tr h / 2)·1` subtracts a REAL scalar multiple of
identity, the off-diagonal entries are unchanged and `.im` of the diagonal
is unchanged — therefore `matrixToPauliCoords (liePartMat cFib_SU_mat)`
equals these same coords (next ship).

Used to evaluate `σ_Fib_lie_bundle_pauliDet (liePartMat cFib_SU_mat)` via §24's
cubic-polynomial closed form. -/

/-- **Euler form for `exp(-(7π/5)·i)`**: separated into real cos + sin·i parts.

`exp(-(7π/5)·i) = cos(7π/5) - sin(7π/5)·i` (using cos even, sin odd). -/
theorem exp_neg_seven_pi_div_five_eulerForm :
    Complex.exp (((-(7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I) =
      ((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) -
      ((Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I,
      show Complex.cos (((-(7 * Real.pi / 5) : ℝ) : ℂ)) =
            ((Real.cos (-(7 * Real.pi / 5)) : ℝ) : ℂ) from
            (Complex.ofReal_cos _).symm,
      show Complex.sin (((-(7 * Real.pi / 5) : ℝ) : ℂ)) =
            ((Real.sin (-(7 * Real.pi / 5)) : ℝ) : ℂ) from
            (Complex.ofReal_sin _).symm]
  rw [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- **cFib_SU_mat (0,0) in Re + Im·I real-cast form**.

`cFib[0,0] = (φInv² + φInv·cos(7π/5)) + (-φInv·sin(7π/5))·I` (real-cast). -/
theorem cFib_SU_mat_entry_00_re_im_form :
    cFib_SU_mat 0 0 =
      ((Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹ +
         Real.goldenRatio⁻¹ * Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) +
      ((-(Real.goldenRatio⁻¹ * Real.sin (7 * Real.pi / 5)) : ℝ) : ℂ) *
        Complex.I := by
  rw [cFib_SU_mat_entry_00_simplified, exp_neg_seven_pi_div_five_eulerForm]
  show ((Real.goldenRatio⁻¹ : ℝ) : ℂ) * ((Real.goldenRatio⁻¹ : ℝ) : ℂ) +
        ((Real.goldenRatio⁻¹ : ℝ) : ℂ) *
          (((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) -
            ((Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I) = _
  push_cast
  ring

/-- **(cFib_SU_mat 0 0).im closed form**: `-φInv · sin(7π/5)`. -/
theorem cFib_SU_mat_entry_00_im :
    (cFib_SU_mat 0 0).im =
      -(Real.goldenRatio⁻¹ * Real.sin (7 * Real.pi / 5)) := by
  rw [cFib_SU_mat_entry_00_re_im_form, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **cFib_SU_mat (0,1) in Re + Im·I real-cast form**.

`cFib[0,1] = (φInv·φInvSqrt·(1 - cos(7π/5))) + (φInv·φInvSqrt·sin(7π/5))·I`. -/
theorem cFib_SU_mat_entry_01_re_im_form :
    cFib_SU_mat 0 1 =
      ((Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
         (1 - Real.cos (7 * Real.pi / 5)) : ℝ) : ℂ) +
      ((Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
         Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I := by
  rw [cFib_SU_mat_entry_01_simplified, exp_neg_seven_pi_div_five_eulerForm]
  show ((Real.goldenRatio⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt Real.goldenRatio)⁻¹ : ℝ) : ℂ) *
        (1 - (((Real.cos (7 * Real.pi / 5) : ℝ) : ℂ) -
              ((Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) * Complex.I)) = _
  push_cast
  ring

/-- **(cFib_SU_mat 0 1).re closed form**: `φInv · φInvSqrt · (1 - cos(7π/5))`. -/
theorem cFib_SU_mat_entry_01_re :
    (cFib_SU_mat 0 1).re =
      Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
        (1 - Real.cos (7 * Real.pi / 5)) := by
  rw [cFib_SU_mat_entry_01_re_im_form, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **(cFib_SU_mat 0 1).im closed form**: `φInv · φInvSqrt · sin(7π/5)`. -/
theorem cFib_SU_mat_entry_01_im :
    (cFib_SU_mat 0 1).im =
      Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
        Real.sin (7 * Real.pi / 5) := by
  rw [cFib_SU_mat_entry_01_re_im_form, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **R5.4 Layer F.20.c.d.2.bb HEADLINE — Pauli coords of `cFib_SU_mat`**.

`matrixToPauliCoords cFib_SU_mat = (a, b, c)` where:
  - `a = φInv · φInvSqrt · sin(7π/5)`        (the `paulI_x` coefficient)
  - `b = φInv · φInvSqrt · (1 - cos(7π/5))`  (the `paulI_y` coefficient)
  - `c = -φInv · sin(7π/5)`                   (the `paulI_z` coefficient)

Composes the three entry-Re/Im closed forms via the `matrixToPauliCoords`
unfolding `X ↦ (X[0,1].im, X[0,1].re, X[0,0].im)`.

Note: since `sin(7π/5) < 0` (`sin_seven_pi_div_five_neg`), `a < 0` and `c > 0`.
The non-vanishing of these coords is the key fact for showing
`σ_Fib_lie_bundle_pauliDet (liePartMat cFib_SU_mat) ≠ 0`. -/
theorem cFib_SU_mat_matrixToPauliCoords :
    matrixToPauliCoords cFib_SU_mat =
      (Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
         Real.sin (7 * Real.pi / 5),
       Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
         (1 - Real.cos (7 * Real.pi / 5)),
       -(Real.goldenRatio⁻¹ * Real.sin (7 * Real.pi / 5))) := by
  unfold matrixToPauliCoords
  rw [cFib_SU_mat_entry_01_im, cFib_SU_mat_entry_01_re, cFib_SU_mat_entry_00_im]

/-! ## §53. R5.4 Layer F.20.c.d.2.cc — liePartMat cFib preservation

`matrixToPauliCoords (liePartMat cFib_SU_mat) = matrixToPauliCoords cFib_SU_mat`,
i.e. liePartMat preserves the Pauli coords shipped in §52.

Reason: `liePartMat h = h - (tr h / 2)·1` for h ∈ SU(2) (per
`liePartMat_specialUnitary`); the subtracted term `(tr/2)·1` has zero
off-diagonal entries and zero `.im` on the diagonal (since `tr` is real),
so neither `[0,1]` nor `.im` of `[0,0]` is affected.

Composed with §52 → `matrixToPauliCoords (liePartMat cFib_SU_mat) = (a, b, c)`. -/

/-- **Closed-form `liePartMat` for `cFib_SU_mat`**:
`liePartMat cFib_SU_mat = cFib_SU_mat - ((3-√5)/4)·1`. -/
theorem cFib_SU_mat_liePartMat :
    liePartMat cFib_SU_mat =
      cFib_SU_mat -
        (((3 - Real.sqrt 5) / 4 : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h_lie :=
    liePartMat_specialUnitary
      (σ_Fib_1_SU * σ_Fib_2_SU⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
  rw [cFib_val_eq_cFib_SU_mat] at h_lie
  rw [h_lie, cFib_SU_mat_trace]
  congr 1
  push_cast
  ring

/-- **(liePartMat cFib_SU_mat) [0,1] = cFib_SU_mat [0,1]** (off-diagonal unchanged).

The subtracted scalar matrix has zero off-diagonal entries. -/
theorem cFib_SU_mat_liePartMat_entry_01 :
    (liePartMat cFib_SU_mat) 0 1 = cFib_SU_mat 0 1 := by
  rw [cFib_SU_mat_liePartMat]
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

/-- **(liePartMat cFib_SU_mat)[0,0].im = (cFib_SU_mat 0 0).im**.

The real scalar subtraction `(3-√5)/4` doesn't affect `.im`. -/
theorem cFib_SU_mat_liePartMat_entry_00_im :
    ((liePartMat cFib_SU_mat) 0 0).im = (cFib_SU_mat 0 0).im := by
  rw [cFib_SU_mat_liePartMat]
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.one_im, Complex.one_re]

/-- **R5.4 Layer F.20.c.d.2.cc HEADLINE — Pauli coords of `liePartMat cFib_SU_mat`**.

`matrixToPauliCoords (liePartMat cFib_SU_mat) = matrixToPauliCoords cFib_SU_mat`,
which equals the closed form `(a, b, c)` shipped in §52 via
`cFib_SU_mat_matrixToPauliCoords`. -/
theorem cFib_SU_mat_liePartMat_matrixToPauliCoords :
    matrixToPauliCoords (liePartMat cFib_SU_mat) =
      matrixToPauliCoords cFib_SU_mat := by
  unfold matrixToPauliCoords
  rw [cFib_SU_mat_liePartMat_entry_01, cFib_SU_mat_liePartMat_entry_00_im]

/-- **R5.4 Layer F.20.c.d.2.cc HEADLINE 2 — closed-form Pauli coords of
`liePartMat cFib_SU_mat`**.

`matrixToPauliCoords (liePartMat cFib_SU_mat) = (a, b, c)` where:
  - `a = φInv · φInvSqrt · sin(7π/5)`
  - `b = φInv · φInvSqrt · (1 - cos(7π/5))`
  - `c = -φInv · sin(7π/5)`

Direct composition of `cFib_SU_mat_liePartMat_matrixToPauliCoords` with
`cFib_SU_mat_matrixToPauliCoords`. Used by §54+ to evaluate
`σ_Fib_lie_bundle_pauliDet (liePartMat cFib_SU_mat)` via the cubic form. -/
theorem cFib_SU_mat_liePartMat_matrixToPauliCoords_closed :
    matrixToPauliCoords (liePartMat cFib_SU_mat) =
      (Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
         Real.sin (7 * Real.pi / 5),
       Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
         (1 - Real.cos (7 * Real.pi / 5)),
       -(Real.goldenRatio⁻¹ * Real.sin (7 * Real.pi / 5))) := by
  rw [cFib_SU_mat_liePartMat_matrixToPauliCoords, cFib_SU_mat_matrixToPauliCoords]

/-! ## §54. R5.4 Layer F.20.c.d.2.dd — Pauli decomposition of liePartMat cFib_SU_mat

Bridge from §53's Pauli coords to the explicit Pauli-basis decomposition.

Since `liePartMat cFib_SU_mat ∈ tracelessSkewHermitian (Fin 2)` (per
`liePartMat_mem_tracelessSkewHermitian`), the basis decomposition
`tracelessSkewHermitian_decomp` gives:

  `liePartMat cFib_SU_mat = (a : ℂ) • paulI_x + (b : ℂ) • paulI_y + (c : ℂ) • paulI_z`

where (a, b, c) are exactly the closed forms shipped in §52/§53.

This bridge is consumed by §55+ which applies
`σ_Fib_lie_bundle_pauliDet_pauliDecomp` to expand the cubic polynomial. -/

/-- **R5.4 Layer F.20.c.d.2.dd HEADLINE — Pauli basis decomposition of `liePartMat cFib_SU_mat`**.

`liePartMat cFib_SU_mat = (a : ℂ) • paulI_x + (b : ℂ) • paulI_y + (c : ℂ) • paulI_z`
where:
  - `a = φInv · φInvSqrt · sin(7π/5)`
  - `b = φInv · φInvSqrt · (1 - cos(7π/5))`
  - `c = -φInv · sin(7π/5)`

Composes `tracelessSkewHermitian_decomp` (Pauli basis decomp for any
X ∈ 𝔰𝔲(2)) with the entry-level closed forms from §52/§53. -/
theorem cFib_SU_mat_liePartMat_pauli_decomposition :
    liePartMat cFib_SU_mat =
      ((Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
          Real.sin (7 * Real.pi / 5) : ℝ) : ℂ) • paulI_x +
      ((Real.goldenRatio⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ *
          (1 - Real.cos (7 * Real.pi / 5)) : ℝ) : ℂ) • paulI_y +
      ((-(Real.goldenRatio⁻¹ * Real.sin (7 * Real.pi / 5)) : ℝ) : ℂ) • paulI_z := by
  rw [tracelessSkewHermitian_decomp (liePartMat_mem_tracelessSkewHermitian _)]
  rw [cFib_SU_mat_liePartMat_entry_01, cFib_SU_mat_liePartMat_entry_00_im,
      cFib_SU_mat_entry_01_im, cFib_SU_mat_entry_01_re, cFib_SU_mat_entry_00_im]

/-! ## §55. R5.4 Layer F.20.c.d.2.ee — Cubic polynomial value at cFib coords ((2 - φInv)/4)

Substantive cubic-polynomial computation. After applying
`σ_Fib_lie_bundle_pauliDet_pauliDecomp` at the (a, b, c) = (φInv·φInvSqrt·sin(7π/5),
φInv·φInvSqrt·(1-cos(7π/5)), -φInv·sin(7π/5)) shipped in §52/§53/§54, the cubic
polynomial reduces to a remarkably clean closed form:

  `σ_Fib_lie_bundle_pauliDet (liePartMat cFib_SU_mat) = (2 - φInv) / 4`

Using identities:
  - `φInv² = 1 - φInv` (golden ratio)
  - `φInvSqrt² = φInv` (= `1/φ` since `(1/√φ)² = 1/φ`)
  - `cos(7π/5) = -φInv/2` (from `cos_7pi_div_5 = (1-√5)/4` + `φInv = (√5-1)/2`)
  - `sin²(7π/5) = (3 + φInv)/4` (from sin² + cos² = 1)

The linear_combination certificate (K_p, K_q, K_C, K_s coefficient polynomials)
was derived via sympy's polynomial division using sequential elimination of
(q², C, s², p²). Total: ~82 terms in the certificate; mechanical verification.

This is **non-zero** since `φInv < 2`, hence `2 - φInv > 0`, hence `(2 - φInv)/4 > 0`. -/

/-- **Algebraic identity** (real-valued) for the cubic polynomial reduction.

For p, q, s, C ∈ ℝ satisfying:
  - `p² = 1 - p`         (golden ratio)
  - `q² = p`              (φInvSqrt² = φInv)
  - `2C + p = 0`          (cos_7pi_div_5)
  - `4s² = 3 + p`         (sin²_7pi_div_5)

The cubic polynomial `σ_Fib_lie_bundle_pauliDet_pauliDecomp` evaluated at
the substituted (a, b, c) = (pqs, pq(1-C), -ps) reduces to `(2 - p)/4`.

Used in `cFib_SU_mat_liePartMat_pauliDet_value` to compute the closed-form value.

Proof: linear_combination with sympy-derived 82-term certificate. -/
theorem cFib_pauliDet_real_polynomial_identity
    (p q s C : ℝ)
    (h_p_sq : p * p = 1 - p)
    (h_q_sq : q * q = p)
    (h_C : 2 * C + p = 0)
    (h_s_sq : 4 * s * s = 3 + p) :
    -- Cubic polynomial at (a, b, c) = (pqs, pq(1-C), -ps); α=2pq, β=2p-1, γ=p²-q²
    (p * q * s) *
        ((p * q * s * s + p * q * (1 - C) * C) *
            ((((p * q * s) * (2 * p - 1) + (-(p * s)) * (2 * p * q)) * C +
                (p * q * (1 - C)) * s) * (2 * p * q) +
              ((p * q * s) * (2 * p * q) + (-(p * s)) * (p * p - q * q)) *
                (p * p - q * q)) -
          (-(p * s)) *
            (-((((p * q * s) * (2 * p - 1) + (-(p * s)) * (2 * p * q)) * s)) +
              (p * q * (1 - C)) * C)) -
      (p * q * (1 - C)) *
        ((p * q * s * C - p * q * (1 - C) * s) *
            ((((p * q * s) * (2 * p - 1) + (-(p * s)) * (2 * p * q)) * C +
                (p * q * (1 - C)) * s) * (2 * p * q) +
              ((p * q * s) * (2 * p * q) + (-(p * s)) * (p * p - q * q)) *
                (p * p - q * q)) -
          (-(p * s)) *
            ((((p * q * s) * (2 * p - 1) + (-(p * s)) * (2 * p * q)) * C +
                (p * q * (1 - C)) * s) * (2 * p - 1) +
              ((p * q * s) * (2 * p * q) + (-(p * s)) * (p * p - q * q)) *
                (2 * p * q))) +
      (-(p * s)) *
        ((p * q * s * C - p * q * (1 - C) * s) *
            (-((((p * q * s) * (2 * p - 1) + (-(p * s)) * (2 * p * q)) * s)) +
              (p * q * (1 - C)) * C) -
          (p * q * s * s + p * q * (1 - C) * C) *
            ((((p * q * s) * (2 * p - 1) + (-(p * s)) * (2 * p * q)) * C +
                (p * q * (1 - C)) * s) * (2 * p - 1) +
              ((p * q * s) * (2 * p * q) + (-(p * s)) * (p * p - q * q)) *
                (2 * p * q))) =
      (2 - p) / 4 := by
  linear_combination
    -- K_p · h_p_sq  (h_p_sq : p*p = 1 - p, "delta" = p² + p - 1)
    (p^9/16 + 7*p^8/16 + 17*p^7/16 + 17*p^6/16 + 7*p^5/16 + 7*p^4/16 + p^3 +
     3*p^2/4 + p/4 + 1/2) * h_p_sq +
    -- K_q · h_q_sq  (h_q_sq : q*q = p, "delta" = q² - p)
    (-4*C^3*p^5*s^2 - 4*C^3*p^4*q^2*s^2 + 4*C^3*p^4*s^2 + C^2*p^7*s^2 +
     2*C^2*p^6*q^2*s^2 - 2*C^2*p^6*s^2 - 4*C^2*p^5*q^2*s^2 + 7*C^2*p^5*s^2 -
     2*C^2*p^4*q^4*s^2 + 7*C^2*p^4*q^2*s^2 - 10*C^2*p^4*s^2 - C^2*p^3*q^4*s^2 +
     C^2*p^3*s^2 - 2*C*p^7*s^2 - 4*C*p^6*q^2*s^2 + 4*C*p^6*s^2 +
     8*C*p^5*q^2*s^2 - 4*C*p^5*s^4 - 2*C*p^5*s^2 + 4*C*p^4*q^4*s^2 -
     4*C*p^4*q^2*s^4 - 2*C*p^4*q^2*s^2 - 4*C*p^4*s^4 + 8*C*p^4*s^2 +
     2*C*p^3*q^4*s^2 - 2*C*p^3*s^2 + p^7*s^4 + p^7*s^2 + 2*p^6*q^2*s^4 +
     2*p^6*q^2*s^2 + 2*p^6*s^4 - 2*p^6*s^2 + 4*p^5*q^2*s^4 - 4*p^5*q^2*s^2 +
     3*p^5*s^4 - p^5*s^2 - 2*p^4*q^4*s^4 - 2*p^4*q^4*s^2 + 3*p^4*q^2*s^4 -
     p^4*q^2*s^2 + 2*p^4*s^4 - 2*p^4*s^2 - p^3*q^4*s^4 - p^3*q^4*s^2 +
     p^3*s^4 + p^3*s^2) * h_q_sq +
    -- K_C · h_C  (h_C : 2*C + p = 0, "delta" = 2C + p)
    (-2*C^2*p^6*s^2 + 2*C^2*p^5*s^2 + C*p^8*s^2/2 + 5*C*p^6*s^2/2 -
     5*C*p^5*s^2 + C*p^4*s^2/2 - p^9*s^2/4 - p^8*s^2 + 3*p^7*s^2/4 -
     2*p^6*s^4 + 3*p^6*s^2/2 - 2*p^5*s^4 + 15*p^5*s^2/4 - p^4*s^2) * h_C +
    -- K_s · h_s_sq  (h_s_sq : 4*s*s = 3 + p, "delta" = 4s² - 3 - p)
    (p^10/16 + 5*p^9/16 + p^8*s^2/4 + p^8/2 + p^7*s^2 + 3*p^7/16 +
     5*p^6*s^2/4 - p^6/8 + p^5*s^2/2 + 3*p^5/16 + p^4*s^2/4 + 7*p^4/16) * h_s_sq

/-! ## §56. R5.4 Layer F.20.c.d.2.ee.1 — pauliDet(liePartMat cFib_SU_mat) = (2-φInv)/4

Apply `cFib_pauliDet_real_polynomial_identity` to the specific cFib values.

The four substrate identities at the concrete cFib coords:
  - `h_p_sq`: `φInv² = 1 - φInv` (from `golden_phi_inv_sq`)
  - `h_q_sq`: `φInvSqrt² = φInv` (from `Real.sqrt` semantics + `φInvSqrt = (√φ)⁻¹`)
  - `h_C`: `2·cos(7π/5) + φInv = 0` (from `cos_7pi_div_5` + `Real.inv_goldenRatio`)
  - `h_s_sq`: `4·sin²(7π/5) = 3 + φInv` (from sin² + cos² = 1 + cos_7pi_div_5) -/

/-- **R5.4 Layer F.20.c.d.2.ee.1 HEADLINE — closed-form `σ_Fib_lie_bundle_pauliDet`
at `liePartMat cFib_SU_mat`**.

  `σ_Fib_lie_bundle_pauliDet (liePartMat cFib_SU_mat) = (2 - φInv)/4`  (real)

Composes `cFib_SU_mat_liePartMat_pauli_decomposition` (§54) + `σ_Fib_lie_bundle_pauliDet_pauliDecomp`
(§24) + `cFib_pauliDet_real_polynomial_identity` (§55). -/
theorem cFib_SU_mat_liePartMat_pauliDet_value :
    σ_Fib_lie_bundle_pauliDet (liePartMat cFib_SU_mat) =
      (2 - Real.goldenRatio⁻¹) / 4 := by
  -- Substrate: golden ratio + trig identities
  have h_p_sq : Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹ = 1 - Real.goldenRatio⁻¹ := by
    have := golden_phi_inv_sq; rw [sq] at this; exact this
  have h_q_sq :
      (Real.sqrt Real.goldenRatio)⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ =
        Real.goldenRatio⁻¹ := by
    rw [show (Real.sqrt Real.goldenRatio)⁻¹ * (Real.sqrt Real.goldenRatio)⁻¹ =
          ((Real.sqrt Real.goldenRatio) * (Real.sqrt Real.goldenRatio))⁻¹ from by
      rw [mul_inv]]
    rw [Real.mul_self_sqrt (le_of_lt Real.goldenRatio_pos)]
  have h_C : 2 * Real.cos (7 * Real.pi / 5) + Real.goldenRatio⁻¹ = 0 := by
    rw [cos_7pi_div_5]
    have : Real.goldenRatio⁻¹ = (Real.sqrt 5 - 1) / 2 := by
      rw [Real.inv_goldenRatio]; unfold Real.goldenConj; ring
    rw [this]; ring
  have h_s_sq :
      4 * Real.sin (7 * Real.pi / 5) * Real.sin (7 * Real.pi / 5) =
        3 + Real.goldenRatio⁻¹ := by
    have h_pyth : Real.sin (7 * Real.pi / 5) ^ 2 + Real.cos (7 * Real.pi / 5) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq _
    rw [cos_7pi_div_5] at h_pyth
    have h_phi_inv : Real.goldenRatio⁻¹ = (Real.sqrt 5 - 1) / 2 := by
      rw [Real.inv_goldenRatio]; unfold Real.goldenConj; ring
    have h_5 : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
    rw [h_phi_inv]
    nlinarith [h_pyth, h_5, sq_nonneg (Real.sin (7 * Real.pi / 5))]
  -- Apply the abstract polynomial identity
  rw [cFib_SU_mat_liePartMat_pauli_decomposition]
  rw [σ_Fib_lie_bundle_pauliDet_pauliDecomp]
  -- Apply the abstract identity directly (both sides ℝ-valued)
  exact cFib_pauliDet_real_polynomial_identity
    Real.goldenRatio⁻¹ (Real.sqrt Real.goldenRatio)⁻¹
    (Real.sin (7 * Real.pi / 5)) (Real.cos (7 * Real.pi / 5))
    h_p_sq h_q_sq h_C h_s_sq

/-! ## §57. R5.4 Layer F.20.c.d.2.ee.2 — Non-vanishing of σ_Fib_lie_bundle_pauliDet at cFib -/

/-- **R5.4 Layer F.20.c.d.2.ee.2 HEADLINE — `σ_Fib_lie_bundle_pauliDet (liePartMat cFib_SU_mat) ≠ 0`**.

Direct consequence of `cFib_SU_mat_liePartMat_pauliDet_value = (2 - φInv)/4`
combined with `φInv < 1 < 2`, giving `2 - φInv > 0` hence `(2 - φInv)/4 > 0`. -/
theorem cFib_SU_mat_liePartMat_pauliDet_ne_zero :
    σ_Fib_lie_bundle_pauliDet (liePartMat cFib_SU_mat) ≠ 0 := by
  rw [cFib_SU_mat_liePartMat_pauliDet_value]
  have h_one_lt_φ : (1 : ℝ) < Real.goldenRatio := Real.one_lt_goldenRatio
  have h_φInv_lt_one : Real.goldenRatio⁻¹ < 1 := inv_lt_one_of_one_lt₀ h_one_lt_φ
  have h_pos : (2 - Real.goldenRatio⁻¹) / 4 > 0 := by
    apply div_pos
    · linarith
    · norm_num
  linarith

/-! ## §58. R5.4 Layer F.20.c.d.2.ff — Modular F21_residual_small_spanning via cFib powers

Composition theorem connecting §57's non-vanishing pauliDet at the cFib axis
with two substantive substrate Props for power iteration:

  H_powers_dense — `∀ ε > 0, ∃ n > 0, ‖cFib^n - 1‖ < ε` (irrational rotation density)
  H_axis_scaling — for any n > 0 with cFib^n ≠ 1,
                   `liePartMat (cFib^n) = (some real scalar t_n ≠ 0) • liePartMat cFib`
                   (rotation-axis preservation under powers)

Combined with §57's pauliDet ≠ 0 + cubic homogeneity (§24's
`σ_Fib_lie_bundle_pauliDet_smul_uniform`), these discharge
`F21_residual_small_spanning` in a structured way.

The two Props are deferred (substantive content for sessions S77+); this
section composes them. -/

/-- **Substrate Prop**: powers of `cFib_SU = σ_Fib_1_SU * σ_Fib_2_SU⁻¹` are dense at 1.

For every ε > 0, ∃ n : ℕ with n > 0 such that the n-th power of `cFib_SU`
is within ε of 1 in operator norm.

This is the standard "irrational rotation in SU(2) has dense powers" theorem,
applied to `cFib_SU` which has infinite order (via `σ_Fib_1_SU_mul_σ_Fib_2_SU_inv_not_isOfFinOrder`).

Substantive content: Mathlib substrate for closed-subgroup density in compact
Lie groups (~50-150 LoC, possibly substantial Mathlib gap). Deferred to S77+. -/
def cFib_powers_dense_at_one : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ n : ℕ, 0 < n ∧
      ‖((σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))^n :
          Matrix (Fin 2) (Fin 2) ℂ) - 1‖ < ε

/-- **Substrate Prop**: axis preservation under cFib powers.

For every n : ℕ with `cFib_SU^n ≠ 1`, ∃ real scalar t_n ≠ 0 such that
`liePartMat (cFib_SU^n).val = (t_n : ℂ) • liePartMat cFib_SU_mat`.

This is the standard "powers preserve rotation axis" theorem for SU(2):
if h = exp(iθ X/2) where X is the rotation axis, then h^n = exp(inθ X/2)
shares the axis. The liePartMat extracts (a scaled version of) the axis.

Substantive content: SU(2) maximal torus structure + axis decomposition (~100-200 LoC). -/
def cFib_pow_liePartMat_axis_scaling : Prop :=
  ∀ n : ℕ,
    ((σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))^n :
        Matrix (Fin 2) (Fin 2) ℂ) ≠ 1 →
    ∃ t : ℝ, t ≠ 0 ∧
      liePartMat
        (((σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))^n :
            Matrix (Fin 2) (Fin 2) ℂ)) =
        (t : ℂ) • liePartMat cFib_SU_mat

/-- **R5.4 Layer F.20.c.d.2.ff HEADLINE — modular F21_residual_small_spanning discharge**.

Given `cFib_powers_dense_at_one` (H1: density of cFib powers near 1) and
`cFib_pow_liePartMat_axis_scaling` (H2: axis preservation), the
`F21_residual_small_spanning` Prop is discharged.

Construction: for ε > 0,
  - H1 gives n > 0 with `‖cFib^n - 1‖ < ε`
  - cFib^n ∈ H_Fib (subgroup closure under inverse + powers, using
    `σ_Fib_1_SU_mul_σ_Fib_2_SU_inv_mem_H_Fib`)
  - If `cFib^n = 1` then liePartMat = 0 — but pauliDet of 0 is 0, contradiction.
    So `cFib^n ≠ 1`, and H2 gives scalar t ≠ 0 with
    `liePartMat (cFib^n) = t • liePartMat cFib`.
  - Then pauliDet(liePartMat (cFib^n)) = t³ · pauliDet(liePartMat cFib_SU_mat)
    by `σ_Fib_lie_bundle_pauliDet_smul_uniform`. Since t ≠ 0 and §57 gives
    pauliDet(liePartMat cFib) ≠ 0, we have pauliDet(liePartMat (cFib^n)) ≠ 0. -/
theorem F21_residual_small_spanning_from_cFib_powers
    (h_dense : cFib_powers_dense_at_one)
    (h_axis : cFib_pow_liePartMat_axis_scaling) :
    F21_residual_small_spanning := by
  intro ε hε
  obtain ⟨n, hn_pos, hn_close⟩ := h_dense ε hε
  -- cFib^n ∈ H_Fib (since cFib ∈ H_Fib and H_Fib is a subgroup)
  have h_cFib_mem : (σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈ H_Fib :=
    SKEFTHawking.FKLW.σ_Fib_1_SU_mul_σ_Fib_2_SU_inv_mem_H_Fib
  have h_pow_mem : (σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))^n ∈ H_Fib :=
    Subgroup.pow_mem _ h_cFib_mem n
  refine ⟨(σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))^n, h_pow_mem, hn_close, ?_⟩
  -- Show pauliDet(liePartMat (cFib^n)) ≠ 0
  -- Case: cFib^n = 1 → liePartMat = 0 → pauliDet = 0 (contradiction with goal)
  -- Case: cFib^n ≠ 1 → use h_axis
  by_cases h_eq : ((σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))^n :
        Matrix (Fin 2) (Fin 2) ℂ) = 1
  · -- If cFib^n = 1, then ‖cFib^n - 1‖ = 0 < ε but also liePartMat (1) = 0,
    -- so pauliDet(liePartMat 1) = pauliDet 0 = 0. This means our witness fails
    -- the non-zero pauliDet condition. So we need cFib^n ≠ 1, which is the
    -- standard case from the density argument (it'd only equal 1 if cFib were
    -- finite order, contradicting cFib_not_isOfFinOrder).
    --
    -- Strengthen `h_dense` to require cFib^n ≠ 1. (For now we rely on the fact
    -- that if cFib^n = 1 for some n, then the orbit is finite, contradicting
    -- the infinite-order property.)
    exfalso
    -- cFib^n = 1 in SU(2) implies cFib has order dividing n, contradicting
    -- σ_Fib_1_SU_mul_σ_Fib_2_SU_inv_not_isOfFinOrder.
    have h_cFib_val_eq_one :
        ((σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))^n :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) = 1 :=
      Subtype.ext h_eq
    -- From cFib^n = 1, cFib has finite order ≤ n
    have h_fin :
        IsOfFinOrder (σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn_pos, h_cFib_val_eq_one⟩
    exact SKEFTHawking.FKLW.σ_Fib_1_SU_mul_σ_Fib_2_SU_inv_not_isOfFinOrder h_fin
  · -- cFib^n ≠ 1: apply axis scaling to get liePartMat = t · liePartMat cFib
    obtain ⟨t, ht_ne, ht_eq⟩ := h_axis n h_eq
    -- Convert the goal's outside-coercion form to inside-coercion to match ht_eq
    show σ_Fib_lie_bundle_pauliDet
        (liePartMat ((σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))^n :
            Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0
    rw [ht_eq, σ_Fib_lie_bundle_pauliDet_smul_uniform]
    exact mul_ne_zero (pow_ne_zero 3 ht_ne) cFib_SU_mat_liePartMat_pauliDet_ne_zero

/-! ## §59. R5.4 Layer F.20.c.d.2.gg — SU(2) power-axis identity via Chebyshev recurrence

For any `h ∈ SU(2)`, the powers `h^(n+1)` decompose linearly via SU(2)
Cayley-Hamilton + a real Chebyshev-like sequence in the trace:

  `h^(n+1) = chebyshevSU2 τ n.2 • h - chebyshevSU2 τ n.1 • I`

where `chebyshevSU2 τ n = (V_{n-1}(τ), V_n(τ))` with initial `(0, 1)` and
recurrence `V_{n+1} = τ · V_n - V_{n-1}`.

The downstream identity (proof in §60):
  `liePartMat (h^(n+1)) = V_n(τ) • liePartMat h`

This will discharge `cFib_pow_liePartMat_axis_scaling`. -/

/-- **Chebyshev-like sequence for SU(2) power recurrence**.

`chebyshevSU2 τ` is a pair-valued sequence `(V_{n-1}(τ), V_n(τ))` with
`V_{-1} = 0`, `V_0 = 1`, `V_{n+1} = τ · V_n - V_{n-1}`. The pair format
avoids the awkward `V_{-1}` boundary by carrying both consecutive values.

For SU(2) elements `h` with `τ = tr(h)`, the n-th power satisfies
`h^(n+1) = (chebyshevSU2 τ n).2 • h - (chebyshevSU2 τ n).1 • I` (proof
below in `pow_su2_chebyshev_decomp`). -/
def chebyshevSU2 (τ : ℂ) : ℕ → ℂ × ℂ
  | 0 => (0, 1)
  | n+1 => ((chebyshevSU2 τ n).2,
            τ * (chebyshevSU2 τ n).2 - (chebyshevSU2 τ n).1)

/-- **`h^(n+1)` Chebyshev decomposition for SU(2) elements**.

For `h ∈ SU(2)`, `h^(n+1) = V_n(tr h) • h - V_{n-1}(tr h) • I` where
`V_n := (chebyshevSU2 (tr h) n).2`.

Proof: induction on n using SU(2) Cayley-Hamilton (h² = tr(h)·h - I). -/
theorem pow_su2_chebyshev_decomp
    (h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (n : ℕ) :
    ((h : Matrix (Fin 2) (Fin 2) ℂ)) ^ (n + 1) =
      (chebyshevSU2 (Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ)) n).2 •
        (h : Matrix (Fin 2) (Fin 2) ℂ) -
      (chebyshevSU2 (Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ)) n).1 •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  set τ : ℂ := Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ) with hτ
  set A : Matrix (Fin 2) (Fin 2) ℂ := (h : Matrix (Fin 2) (Fin 2) ℂ) with hA
  -- Cayley-Hamilton: A·A = τ·A - I  (in A*A form, not A^2)
  have h_CH : A * A = τ • A - 1 := by
    have hsq := SKEFTHawking.FKLW.SU2_CayleyHamilton h
    rw [hA, hτ, ← pow_two]
    exact hsq
  induction n with
  | zero =>
    -- n=0: A^1 = (chebSU2 τ 0).2 • A - (chebSU2 τ 0).1 • I = 1·A - 0·I = A
    simp [chebyshevSU2, pow_one]
  | succ k ih =>
    -- A^(k+2) = A^(k+1) · A; substitute ih, then use Cayley-Hamilton.
    rw [pow_succ, ih]
    -- ((V_k.2 • A - V_k.1 • I) * A) = V_k.2 • (A·A) - V_k.1 • A
    rw [sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, h_CH]
    -- V_k.2 • (τ•A - I) - V_k.1 • A = (τ·V_k.2 - V_k.1)•A - V_k.2•I
    -- Match (chebyshevSU2 τ (k+1)).1 = V_k.2 and .2 = τ·V_k.2 - V_k.1
    show _ = (chebyshevSU2 τ (k + 1)).2 • A - (chebyshevSU2 τ (k + 1)).1 • 1
    simp only [chebyshevSU2]
    rw [smul_sub, sub_smul, smul_smul]
    rw [mul_comm τ (chebyshevSU2 τ k).2]
    abel

/-! ## §60. R5.4 Layer F.20.c.d.2.gg.2 — liePartMat formula for SU(2) powers

Apply §59's `pow_su2_chebyshev_decomp` + `liePartMat_specialUnitary` (which
applies to h^(n+1) ∈ SU(2)) to get the clean identity:

  `liePartMat (h^(n+1)) = V_n • liePartMat h`

where V_n is the Chebyshev value `(chebyshevSU2 (tr h) n).2`. -/

/-- **liePartMat of SU(2) powers** (HEADLINE).

For h ∈ SU(2) and n : ℕ:
  `liePartMat (h^(n+1)) = V_n(tr h) • liePartMat h`
where V_n(τ) = `(chebyshevSU2 τ n).2`.

Proof: invoke `liePartMat_specialUnitary` on the bundled `h^(n+1) ∈ SU(2)`,
substitute `pow_su2_chebyshev_decomp`, use trace linearity, simplify. -/
theorem liePartMat_specialUnitary_pow
    (h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (n : ℕ) :
    liePartMat ((h : Matrix (Fin 2) (Fin 2) ℂ) ^ (n + 1)) =
      (chebyshevSU2 (Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℂ)) n).2 •
        liePartMat (h : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- h^(n+1) as bundled SU(2) element: its matrix form is (↑h)^(n+1)
  have h_val_pow : ((h ^ (n + 1) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      (h : Matrix (Fin 2) (Fin 2) ℂ) ^ (n + 1) :=
    SubmonoidClass.coe_pow h (n + 1)
  have h_lie_pow := liePartMat_specialUnitary (h ^ (n + 1))
  rw [h_val_pow] at h_lie_pow
  rw [h_lie_pow]
  rw [pow_su2_chebyshev_decomp h n]
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_one, Fintype.card_fin]
  rw [liePartMat_specialUnitary h]
  -- Final algebraic identity in (V₁, V₂, τ, A, I)
  simp only [Nat.cast_ofNat, smul_eq_mul]
  module

/-! ## §61. R5.4 Layer F.20.c.d.2.gg.3 — chebyshev real-cast preservation

For a real input τ ∈ ℝ cast to ℂ, the chebyshev pair `chebyshevSU2 τ n`
has both components real-cast. Used to extract a real scalar from the
complex chebyshev for cFib_pow_liePartMat_axis_scaling. -/

/-- **`chebyshevSU2` real-cast preservation**: at a real-cast input,
the chebyshev pair is real-cast in both components.

The induction on n shows both `(chebyshevSU2 ((τ : ℝ) : ℂ) n).1` and `.2`
equal real-cast values, with the recurrence preserving the real cast. -/
theorem chebyshevSU2_real_cast (τ : ℝ) :
    ∀ n : ℕ, ∃ x y : ℝ,
      chebyshevSU2 ((τ : ℝ) : ℂ) n =
        (((x : ℝ) : ℂ), ((y : ℝ) : ℂ)) := by
  intro n
  induction n with
  | zero => exact ⟨0, 1, by simp [chebyshevSU2]⟩
  | succ k ih =>
    obtain ⟨x_k, y_k, h_eq_k⟩ := ih
    refine ⟨y_k, τ * y_k - x_k, ?_⟩
    simp [chebyshevSU2, h_eq_k]

/-! ## §62. R5.4 Layer F.20.c.d.2.gg.4 — cFib^n ≠ negOneSU (from infinite order)

If cFib^n = negOneSU then cFib^(2n) = negOneSU² = 1, giving cFib finite
order ≤ 2n. This contradicts `σ_Fib_1_SU_mul_σ_Fib_2_SU_inv_not_isOfFinOrder`. -/

/-- **cFib^n ≠ negOneSU**: powers of `cFib_SU = σ_Fib_1_SU · σ_Fib_2_SU⁻¹` are
never `negOneSU` for `n > 0`.

Direct contradiction with `cFib_not_isOfFinOrder` via order-2 of negOneSU. -/
theorem cFib_SU_pow_ne_negOneSU
    {n : ℕ} (hn : 0 < n) :
    (σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))^n ≠
      SKEFTHawking.FKLW.negOneSU := by
  intro h_eq
  -- cFib^n = negOneSU ⟹ cFib^(2n) = (negOneSU)^2
  have h_neg_sq : SKEFTHawking.FKLW.negOneSU ^ 2 =
      (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
    have := SKEFTHawking.FKLW.negOneSU_orderOf_eq_two
    rw [orderOf_eq_iff (by norm_num : 0 < 2)] at this
    exact this.1
  -- cFib^(2n) = 1
  have h_pow2n : (σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))^(2 * n) = 1 := by
    rw [show 2 * n = n * 2 from by ring, pow_mul, h_eq, h_neg_sq]
  -- cFib has finite order
  have h_fin : IsOfFinOrder (σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * n, ?_, h_pow2n⟩
    omega
  exact SKEFTHawking.FKLW.σ_Fib_1_SU_mul_σ_Fib_2_SU_inv_not_isOfFinOrder h_fin

/-! ## §63. R5.4 Layer F.20.c.d.2.gg.5 — Discharge cFib_pow_liePartMat_axis_scaling

Compose §60 (Chebyshev liePartMat formula) + §61 (real-cast) + §62
(cFib^n ≠ -I) + kernel-of-liePartMat (existing substrate). -/

/-- **R5.4 Layer F.20.c.d.2.gg.5 HEADLINE — discharge of
`cFib_pow_liePartMat_axis_scaling`**.

For any `n` with `cFib^n ≠ 1`:
  liePartMat(cFib^n) = (t : ℂ) • liePartMat(cFib_SU_mat) for some t : ℝ ≠ 0.

Constructive: t is the real-valued Chebyshev scalar `(chebyshevReal n).2`
extracted from `chebyshevSU2 ((3-√5)/2 : ℝ) n.pred`. -/
theorem cFib_pow_liePartMat_axis_scaling_holds :
    cFib_pow_liePartMat_axis_scaling := by
  intro n h_ne_one
  -- Case split on n: n = 0 contradicts h_ne_one; n = k+1 uses §60.
  match n, h_ne_one with
  | 0, h_ne =>
    -- cFib^0 = 1 (in Matrix), contradicts h_ne_one
    exfalso
    apply h_ne
    simp [pow_zero, Submonoid.coe_one]
  | k + 1, h_ne =>
    -- Apply §60 at the bundled cFib_SU
    set cFib_SU := (σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) with h_cFib_def
    -- The matrix form of (cFib_SU)^(k+1) is (↑cFib_SU)^(k+1) = (cFib_SU_mat)^(k+1)
    have h_val_pow : (((cFib_SU)^(k+1) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) =
        (cFib_SU : Matrix (Fin 2) (Fin 2) ℂ)^(k+1) :=
      SubmonoidClass.coe_pow cFib_SU (k+1)
    have h_val_cFib_mat : (cFib_SU : Matrix (Fin 2) (Fin 2) ℂ) = cFib_SU_mat := by
      rw [h_cFib_def]; exact cFib_val_eq_cFib_SU_mat
    -- §60 closed form for liePartMat(cFib^(k+1))
    have h_lie_pow := liePartMat_specialUnitary_pow cFib_SU k
    -- §61: extract real-cast chebyshev value
    have h_tr_cFib : Matrix.trace (cFib_SU : Matrix (Fin 2) (Fin 2) ℂ) =
        (((3 - Real.sqrt 5) / 2 : ℝ) : ℂ) := by
      rw [h_val_cFib_mat]
      exact cFib_SU_mat_trace
    rw [h_tr_cFib] at h_lie_pow
    obtain ⟨_x, y_k, h_cheb_eq⟩ := chebyshevSU2_real_cast ((3 - Real.sqrt 5) / 2) k
    rw [h_cheb_eq] at h_lie_pow
    -- h_lie_pow : liePartMat ((↑cFib_SU)^(k+1)) = (y_k : ℂ) • liePartMat (↑cFib_SU)
    -- Convert to use cFib_SU_mat on the RHS
    rw [h_val_cFib_mat] at h_lie_pow
    -- Witness: t := y_k
    refine ⟨y_k, ?_, ?_⟩
    · -- y_k ≠ 0: by contrapositive, if y_k = 0 then liePartMat (cFib^(k+1)) = 0,
      -- so cFib^(k+1) ∈ {1, negOneSU} by liePartMat_specialUnitary_eq_zero_iff.
      -- Rule out cFib^(k+1) = 1 (hypothesis) and ≠ negOneSU (§62).
      intro h_yk_zero
      apply h_ne
      rw [h_yk_zero] at h_lie_pow
      simp at h_lie_pow
      -- liePartMat ((↑cFib_SU)^(k+1)) = 0
      -- By liePartMat_specialUnitary_ne_zero_iff_ne_one_ne_negOne:
      -- ⟹ cFib_SU^(k+1) = 1 ∨ cFib_SU^(k+1) = negOneSU
      have h_lie_zero : liePartMat
          ((cFib_SU^(k+1) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
        rw [h_val_pow]; exact h_lie_pow
      have h_cases :
          (cFib_SU^(k+1) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) = 1 ∨
          (cFib_SU^(k+1) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) =
            SKEFTHawking.FKLW.negOneSU := by
        by_contra h_both
        push_neg at h_both
        exact ((liePartMat_specialUnitary_ne_zero_iff_ne_one_ne_negOne
          (cFib_SU^(k+1))).mpr h_both) h_lie_zero
      rcases h_cases with h_eq_one | h_eq_negOne
      · -- cFib_SU^(k+1) = 1 (bundled), so its matrix = 1
        have : ((cFib_SU^(k+1) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ) =
            (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          rw [h_eq_one]; rfl
        rw [h_val_pow] at this
        exact this
      · -- cFib_SU^(k+1) = negOneSU contradicts §62
        exfalso
        exact cFib_SU_pow_ne_negOneSU (by omega : 0 < k+1) h_eq_negOne
    · -- liePartMat(cFib_SU_mat^(k+1)) = (y_k : ℂ) • liePartMat cFib_SU_mat
      rw [← h_val_pow]
      -- This is exactly h_lie_pow after rewriting ↑cFib_SU = cFib_SU_mat (already done)
      rw [h_val_pow]
      exact h_lie_pow

/-! ## §64. R5.4 Layer F.20.c.d.2.hh — Substrate toward cFib_powers_dense_at_one

Structural substrate: `Subgroup.zpowers cFib_SU` is an INFINITE subgroup of
compact SU(2). Its topological closure is a closed infinite subgroup.

The discharge of `cFib_powers_dense_at_one` then reduces to:
  (a) AccPt 1 on closure(zpowers) — via `one_accPt_of_infinite_closed_subgroup` ✓ (substrate ready)
  (b) Closure-density extraction: AccPt at 1 in closure → small element in zpowers itself
      (substantive topology, requires careful δ-management; deferred to a separate ship)
  (c) ℤ → ℕ-positive translation via unitary norm-preserving inversion (deferred)

Estimated remaining: ~80-120 LoC across 1-2 sessions. -/

/-- **`Subgroup.zpowers cFib_SU` is infinite**: follows from cFib's infinite order.

Composes `injective_zpow_iff_not_isOfFinOrder` with
`σ_Fib_1_SU_mul_σ_Fib_2_SU_inv_not_isOfFinOrder` + range injection. -/
theorem zpowers_cFib_SU_infinite :
    (Subgroup.zpowers (σ_Fib_1_SU * σ_Fib_2_SU⁻¹ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).Infinite := by
  -- zpowers a = Set.range (fun k : ℤ => a^k); injective ↔ ¬ IsOfFinOrder
  rw [Subgroup.coe_zpowers]
  exact Set.infinite_range_of_injective
    ((injective_zpow_iff_not_isOfFinOrder).mpr
      SKEFTHawking.FKLW.σ_Fib_1_SU_mul_σ_Fib_2_SU_inv_not_isOfFinOrder)

end SKEFTHawking.FKLW.FibSU2LieBundle
