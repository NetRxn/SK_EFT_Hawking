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

end SKEFTHawking.FKLW.FibSU2LieBundle
