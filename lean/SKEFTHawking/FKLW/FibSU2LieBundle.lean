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

end SKEFTHawking.FKLW.FibSU2LieBundle
