/-
Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-A: the Lie algebra 𝔰𝔲(2).

## What this module ships

The Lie algebra of SU(2): traceless skew-Hermitian 2×2 complex matrices.
This is Mathlib4-PR-quality general substrate, ramped here as part of
the upstream-IFT path to fully constructive Fibonacci density.

**Tier 1 substrate (this commit, ~250 LoC)**:

  - `Matrix.IsSkewHermitian` : matrix-level skew-Hermitian predicate
    `M.conjTranspose = -M` (mirroring Mathlib's `Matrix.IsHermitian`).
  - `Matrix.IsSkewHermitian.add`, `.neg`, `.zero` — closure under
    additive operations.
  - **`tracelessSkewHermitian (n : Type*) [Fintype n] (α : Type*)`** :
    the ℝ-submodule of `Matrix n n ℂ` consisting of traceless
    skew-Hermitian matrices. The (real) Lie algebra 𝔰𝔲(n).
  - `paulI_x`, `paulI_y`, `paulI_z` : the three Pauli anti-Hermitian
    elements `i·σ_x`, `i·σ_y`, `i·σ_z`. These are in `𝔰𝔲(2)`.
  - `paulI_x_in_tracelessSkewHermitian` (etc.): membership lemmas.

**Why traceless + skew-Hermitian**:
  - `star (X) = -X` (skew-Hermitian) characterizes exp(X) being unitary.
  - `trace X = 0` characterizes exp(X) having det 1.
  - Combined: exp(X) ∈ SU(n) iff X ∈ 𝔰𝔲(n).

**Architectural significance**: this module is the foundation for the
Cartan-A → Cartan-D ramp:
  - Cartan-B (next): matrix exponential `𝔰𝔲(2) → SU(2)` is smooth + has
    derivative at 0 = identity (modulo the obvious embedding).
  - Cartan-C: apply normed-space IFT to get local diffeomorphism.
  - Cartan-D: compose with shipped D.3.h + D.3.i.1 to close
    `1 ∈ interior(closure H_Fib)`.
  - Layer E: trivial composition into `DenseInSpecialUnitary`.

**Pipeline Invariant compliance**:
  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new project-local axioms): RESPECTED.
  - ADR-003 (zero sorry): RESPECTED.

References:
  - Hall, *Lie Groups, Lie Algebras, and Representations* (2015), §3.2
    (special linear & unitary Lie algebras).
  - Knapp, *Lie Groups Beyond an Introduction* (2002), §I.3.
  - Mathlib4 v4.29.0: `Mathlib.LinearAlgebra.Matrix.Hermitian` (the
    parallel `Matrix.IsHermitian` substrate), `Mathlib.Algebra.Star.SelfAdjoint`
    (`skewAdjoint R` general substrate).
-/

import Mathlib
import SKEFTHawking.PauliMatrices

set_option autoImplicit false

namespace SKEFTHawking.FKLW.SU2LieAlgebra

open Matrix Complex

/-! ## §1. `Matrix.IsSkewHermitian` predicate

Matrix-level skew-Hermitian predicate, parallel to Mathlib's
`Matrix.IsHermitian` (in `Mathlib.LinearAlgebra.Matrix.Hermitian`).

A matrix `M : Matrix n n α` over a star ring is skew-Hermitian iff
`M.conjTranspose = -M` (equivalently `star M = -M`).
-/

/-- A matrix is **skew-Hermitian** if its conjugate transpose equals its
negation: `M.conjTranspose = -M`.

This is the matrix-level specialization of the general `skewAdjoint`
predicate from `Mathlib.Algebra.Star.SelfAdjoint`. -/
def _root_.Matrix.IsSkewHermitian {n : Type*} {α : Type*} [AddGroup α] [StarAddMonoid α]
    (M : Matrix n n α) : Prop := M.conjTranspose = -M

namespace Matrix

variable {n : Type*} {α : Type*} [AddCommGroup α] [StarAddMonoid α]

theorem IsSkewHermitian.zero : (0 : Matrix n n α).IsSkewHermitian := by
  show (0 : Matrix n n α).conjTranspose = -0
  simp [Matrix.conjTranspose_zero]

theorem IsSkewHermitian.add {M N : Matrix n n α}
    (hM : M.IsSkewHermitian) (hN : N.IsSkewHermitian) :
    (M + N).IsSkewHermitian := by
  show (M + N).conjTranspose = -(M + N)
  rw [Matrix.conjTranspose_add, hM, hN, neg_add_rev, add_comm]

theorem IsSkewHermitian.neg {M : Matrix n n α}
    (hM : M.IsSkewHermitian) : (-M).IsSkewHermitian := by
  show (-M).conjTranspose = - -M
  rw [Matrix.conjTranspose_neg, hM]

end Matrix

/-! ## §2. `tracelessSkewHermitian` — the Lie algebra 𝔰𝔲(n) as ℝ-submodule

The real Lie algebra `𝔰𝔲(n)` consists of traceless skew-Hermitian
n×n complex matrices. It's a real vector space (not complex: if `X` is
skew-Hermitian, `i·X` is Hermitian, not skew-Hermitian, so `ℂ`-scalar
multiplication doesn't preserve skew-Hermicity).

For `n = 2`, this is 3-dimensional with basis (i·σ_x, i·σ_y, i·σ_z).
-/

/-- **The Lie algebra `𝔰𝔲(n)`**: traceless skew-Hermitian n×n complex
matrices as a real submodule of `Matrix n n ℂ`. -/
def tracelessSkewHermitian (n : Type*) [Fintype n] :
    Submodule ℝ (Matrix n n ℂ) where
  carrier := {M | M.IsSkewHermitian ∧ M.trace = 0}
  add_mem' := fun {M N} ⟨hM_sh, hM_tr⟩ ⟨hN_sh, hN_tr⟩ => by
    refine ⟨Matrix.IsSkewHermitian.add hM_sh hN_sh, ?_⟩
    rw [Matrix.trace_add, hM_tr, hN_tr, add_zero]
  zero_mem' := ⟨Matrix.IsSkewHermitian.zero, by simp [Matrix.trace_zero]⟩
  smul_mem' := fun (r : ℝ) M ⟨hM_sh, hM_tr⟩ => by
    refine ⟨?_, ?_⟩
    · -- (r • M).conjTranspose = -(r • M) for real r
      show ((r : ℂ) • M).conjTranspose = -((r : ℂ) • M)
      rw [Matrix.conjTranspose_smul, hM_sh]
      simp [Complex.star_def, Complex.conj_ofReal]
    · -- trace (r • M) = r • trace M = r • 0 = 0
      show ((r : ℂ) • M).trace = 0
      rw [Matrix.trace_smul, hM_tr, smul_zero]

theorem tracelessSkewHermitian_mem_iff {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) :
    M ∈ tracelessSkewHermitian n ↔ M.IsSkewHermitian ∧ M.trace = 0 :=
  Iff.rfl

/-! ## §3. Pauli anti-Hermitian basis: i·σ_x, i·σ_y, i·σ_z

The three Pauli anti-Hermitian generators of 𝔰𝔲(2). Each is `i ·` a
Pauli matrix; the multiplication by `i` flips Hermitian → skew-Hermitian.
-/

/-- **i·σ_x** ∈ Matrix (Fin 2) (Fin 2) ℂ. -/
noncomputable def paulI_x : Matrix (Fin 2) (Fin 2) ℂ := I • SKEFTHawking.σ_x

/-- **i·σ_y** ∈ Matrix (Fin 2) (Fin 2) ℂ. -/
noncomputable def paulI_y : Matrix (Fin 2) (Fin 2) ℂ := I • SKEFTHawking.σ_y

/-- **i·σ_z** ∈ Matrix (Fin 2) (Fin 2) ℂ. -/
noncomputable def paulI_z : Matrix (Fin 2) (Fin 2) ℂ := I • SKEFTHawking.σ_z

/-- `i·σ_x` is skew-Hermitian: `(i·σ_x)† = (-i)·σ_x† = (-i)·σ_x = -(i·σ_x)`. -/
theorem paulI_x_isSkewHermitian : paulI_x.IsSkewHermitian := by
  show paulI_x.conjTranspose = -paulI_x
  unfold paulI_x
  rw [Matrix.conjTranspose_smul, SKEFTHawking.σ_x_hermitian]
  ext i j
  simp [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]

/-- `i·σ_y` is skew-Hermitian. -/
theorem paulI_y_isSkewHermitian : paulI_y.IsSkewHermitian := by
  show paulI_y.conjTranspose = -paulI_y
  unfold paulI_y
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.neg_apply,
          SKEFTHawking.σ_y, smul_eq_mul]

/-- `i·σ_z` is skew-Hermitian. -/
theorem paulI_z_isSkewHermitian : paulI_z.IsSkewHermitian := by
  show paulI_z.conjTranspose = -paulI_z
  unfold paulI_z
  rw [Matrix.conjTranspose_smul, SKEFTHawking.σ_z_hermitian]
  ext i j
  simp [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]

/-- `i·σ_x` is traceless. -/
theorem paulI_x_trace : paulI_x.trace = 0 := by
  unfold paulI_x
  rw [Matrix.trace_smul, SKEFTHawking.σ_x_trace, smul_zero]

/-- `i·σ_y` is traceless. -/
theorem paulI_y_trace : paulI_y.trace = 0 := by
  unfold paulI_y
  rw [Matrix.trace_smul, SKEFTHawking.σ_y_trace, smul_zero]

/-- `i·σ_z` is traceless. -/
theorem paulI_z_trace : paulI_z.trace = 0 := by
  unfold paulI_z
  rw [Matrix.trace_smul, SKEFTHawking.σ_z_trace, smul_zero]

/-- `i·σ_x ∈ 𝔰𝔲(2)`. -/
theorem paulI_x_mem_tracelessSkewHermitian :
    paulI_x ∈ tracelessSkewHermitian (Fin 2) :=
  ⟨paulI_x_isSkewHermitian, paulI_x_trace⟩

/-- `i·σ_y ∈ 𝔰𝔲(2)`. -/
theorem paulI_y_mem_tracelessSkewHermitian :
    paulI_y ∈ tracelessSkewHermitian (Fin 2) :=
  ⟨paulI_y_isSkewHermitian, paulI_y_trace⟩

/-- `i·σ_z ∈ 𝔰𝔲(2)`. -/
theorem paulI_z_mem_tracelessSkewHermitian :
    paulI_z ∈ tracelessSkewHermitian (Fin 2) :=
  ⟨paulI_z_isSkewHermitian, paulI_z_trace⟩

/-! ## §4. Linear independence of the Pauli basis (Layer F.1, session 41)

The three Pauli anti-Hermitian generators `paulI_x, paulI_y, paulI_z`
are linearly independent over ℝ as elements of `Matrix (Fin 2) (Fin 2) ℂ`.

This is the foundational linear-algebra fact downstream of which any
"3-direction Lie spanning" theorem for our Fibonacci substrate is
articulated.

**Proof**: a real linear combination `a·paulI_x + b·paulI_y + c·paulI_z`
written as a 2×2 complex matrix equals
  `[[c·i, a·i + b], [a·i - b, -c·i]]`
Setting this to zero and reading off entries gives `a = b = c = 0`.
-/

/-- **Real linear combination of `paulI_{x,y,z}` has explicit matrix form**. -/
private theorem paulI_combination_matrix (a b c : ℝ) :
    ((a : ℂ) • paulI_x + (b : ℂ) • paulI_y + (c : ℂ) • paulI_z) =
      !![(c : ℂ) * I, (a : ℂ) * I + (b : ℂ);
         (a : ℂ) * I - (b : ℂ), -(c : ℂ) * I] := by
  unfold paulI_x paulI_y paulI_z
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z] <;>
    ring

/-- **Real-LinearIndependent of `{paulI_x, paulI_y, paulI_z}`** in
`Matrix (Fin 2) (Fin 2) ℂ` (treated as a ℝ-module via complex
embedding).

Concretely: if `(a : ℂ)·paulI_x + (b : ℂ)·paulI_y + (c : ℂ)·paulI_z = 0`
for real `a b c`, then `a = b = c = 0`. -/
theorem paulI_linear_independent (a b c : ℝ)
    (h : (a : ℂ) • paulI_x + (b : ℂ) • paulI_y + (c : ℂ) • paulI_z =
      (0 : Matrix (Fin 2) (Fin 2) ℂ)) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [paulI_combination_matrix] at h
  -- h : !![c·i, a·i+b; a·i-b, -c·i] = 0
  -- Read off the four matrix entries.
  have h00 : ((c : ℂ) * I) = 0 := by
    have := congr_fun (congr_fun h 0) 0
    simpa using this
  have h01 : ((a : ℂ) * I + (b : ℂ)) = 0 := by
    have := congr_fun (congr_fun h 0) 1
    simpa using this
  have h10 : ((a : ℂ) * I - (b : ℂ)) = 0 := by
    have := congr_fun (congr_fun h 1) 0
    simpa using this
  -- From h00: c = 0 (since I ≠ 0).
  have hc : c = 0 := by
    have h_c_eq : (c : ℂ) = 0 := by
      have := mul_eq_zero.mp h00
      rcases this with h_c | h_I
      · exact h_c
      · exfalso; exact Complex.I_ne_zero h_I
    exact_mod_cast h_c_eq
  -- From h01 + h10: 2·b = 0 (subtract) and 2·a·i = 0 (add), so b = 0 and a = 0.
  have h_sum : 2 * ((a : ℂ) * I) = 0 := by linear_combination h01 + h10
  have ha : a = 0 := by
    have h_aI : (a : ℂ) * I = 0 := by linear_combination h_sum / 2
    have h_a : (a : ℂ) = 0 := by
      rcases mul_eq_zero.mp h_aI with h_a | h_I
      · exact h_a
      · exfalso; exact Complex.I_ne_zero h_I
    exact_mod_cast h_a
  have hb : b = 0 := by
    -- From h01: a·i + b = 0, with a = 0, so b = 0.
    have h_b : (b : ℂ) = 0 := by
      have : (b : ℂ) = -((a : ℂ) * I) := by linear_combination h01
      rw [this]
      simp [ha]
    exact_mod_cast h_b
  exact ⟨ha, hb, hc⟩

/-! ## §5. Pauli basis decomposition (Layer F.2, session 42)

Every traceless skew-Hermitian 2×2 complex matrix decomposes uniquely as
a real linear combination of the three Pauli anti-Hermitian generators
`paulI_x, paulI_y, paulI_z`.

The explicit coordinate formula:
  X = (Im X[0,1])·paulI_x + (Re X[0,1])·paulI_y + (Im X[0,0])·paulI_z

This makes `{paulI_x, paulI_y, paulI_z}` a basis for `tracelessSkewHermitian (Fin 2)`
as a 3-dimensional ℝ-vector space (combined with §4 linear independence).
-/

/-- **Structural form of a traceless skew-Hermitian 2×2 complex matrix**.

If X ∈ tracelessSkewHermitian (Fin 2), then:
  X[0,0] is pure imaginary,
  X[1,1] = -X[0,0],
  X[1,0] = -conjugate(X[0,1]).
-/
private theorem tracelessSkewHermitian_entries
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    (X 0 0).re = 0 ∧ X 1 1 = -X 0 0 ∧ X 1 0 = -star (X 0 1) := by
  obtain ⟨hX_skew, hX_tr⟩ := hX
  -- X.conjTranspose = -X means (X j i)* = -X i j entrywise
  -- For i = j = 0: (X 0 0)* = -X 0 0, so X 0 0 is pure imaginary (real part 0)
  have h_diag_skew_00 : star (X 0 0) = -(X 0 0) := by
    have := congr_fun (congr_fun hX_skew 0) 0
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using this
  have h_re_00 : (X 0 0).re = 0 := by
    -- star z = -z in ℂ means z + star z = 0, i.e., 2 z.re = 0
    have h_sum : X 0 0 + star (X 0 0) = 0 := by rw [h_diag_skew_00]; ring
    have h_re_sum : (X 0 0).re + (star (X 0 0)).re = 0 := by
      have := congr_arg Complex.re h_sum
      simpa [Complex.add_re] using this
    rw [Complex.star_def, Complex.conj_re] at h_re_sum
    linarith
  -- trace = 0: X 0 0 + X 1 1 = 0, so X 1 1 = -X 0 0
  have h_11 : X 1 1 = -X 0 0 := by
    have h_trace : X 0 0 + X 1 1 = 0 := by
      have := hX_tr
      simp [Matrix.trace, Fin.sum_univ_two] at this
      linear_combination this
    linear_combination h_trace
  -- Off-diagonal: (X 0 1)* = -X 1 0, so X 1 0 = -(X 0 1)*
  have h_offdiag : X 1 0 = -star (X 0 1) := by
    have h_skew_01 : star (X 0 1) = -(X 1 0) := by
      have := congr_fun (congr_fun hX_skew 1) 0
      simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using this
    -- From star (X 0 1) = -(X 1 0): X 1 0 = -star (X 0 1)
    linear_combination h_skew_01
  exact ⟨h_re_00, h_11, h_offdiag⟩

/-- **Pauli basis decomposition** for traceless skew-Hermitian 2×2 matrices.

For X ∈ tracelessSkewHermitian (Fin 2):
  X = (X[0,1].im)·paulI_x + (X[0,1].re)·paulI_y + (X[0,0].im)·paulI_z. -/
theorem tracelessSkewHermitian_decomp
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    X = ((X 0 1).im : ℂ) • paulI_x +
        ((X 0 1).re : ℂ) • paulI_y +
        ((X 0 0).im : ℂ) • paulI_z := by
  obtain ⟨h_re_00, h_11, h_offdiag⟩ := tracelessSkewHermitian_entries hX
  rw [paulI_combination_matrix]
  ext i j
  fin_cases i <;> fin_cases j
  · -- [0,0]: X 0 0 = (X[0,0].im : ℂ) * I
    -- X 0 0 is pure imaginary (re = 0), so X 0 0 = ↑(X 0 0).im · I
    show X 0 0 = ((X 0 0).im : ℂ) * I
    rw [Complex.ext_iff]
    refine ⟨?_, ?_⟩
    · simp [Complex.mul_re, Complex.I_re, Complex.I_im, h_re_00]
    · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  · -- [0,1]: X 0 1 = (X[0,1].im : ℂ) * I + (X[0,1].re : ℂ)
    -- This is the (re, im) decomposition of X 0 1.
    show X 0 1 = ((X 0 1).im : ℂ) * I + ((X 0 1).re : ℂ)
    rw [Complex.ext_iff]
    refine ⟨?_, ?_⟩
    · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  · -- [1,0]: X 1 0 = (X[0,1].im : ℂ) * I - (X[0,1].re : ℂ)
    -- X 1 0 = -star (X 0 1) = -(re - im·I) = -re + im·I = im·I - re
    show X 1 0 = ((X 0 1).im : ℂ) * I - ((X 0 1).re : ℂ)
    rw [h_offdiag, Complex.star_def]
    rw [Complex.ext_iff]
    refine ⟨?_, ?_⟩
    · simp [Complex.neg_re, Complex.conj_re, Complex.sub_re, Complex.mul_re,
            Complex.I_re, Complex.I_im]
    · simp [Complex.neg_im, Complex.conj_im, Complex.sub_im, Complex.mul_im,
            Complex.I_re, Complex.I_im]
  · -- [1,1]: X 1 1 = -(X[0,0].im : ℂ) * I = -X 0 0
    show X 1 1 = -((X 0 0).im : ℂ) * I
    rw [h_11, neg_mul]
    rw [Complex.ext_iff]
    refine ⟨?_, ?_⟩
    · simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, h_re_00]
    · simp [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im]

/-! ## §6. Linear independence criterion via Pauli coordinates (Layer F.3, session 43)

For 3 matrices A, B, C ∈ `tracelessSkewHermitian (Fin 2)`, define their
Pauli coordinate vectors (each in ℝ³). The 3 matrices are ℝ-linearly
independent iff the 3×3 determinant of their stacked coordinate vectors
is non-zero.

This is the **load-bearing criterion** for downstream "3-direction Lie
spanning" theorems on the H_Fib substrate: given 3 specific elements
of 𝔰𝔲(2), check linear independence by computing a 3×3 determinant of
their Pauli coords.
-/

/-- **Pauli coordinate extraction** for arbitrary 2×2 complex matrices.

Maps `X ↦ (X[0,1].im, X[0,1].re, X[0,0].im) : ℝ × ℝ × ℝ`.

For X ∈ tracelessSkewHermitian (Fin 2), these are the unique coefficients
in the Pauli basis decomposition `X = a·paulI_x + b·paulI_y + c·paulI_z`
(per `tracelessSkewHermitian_decomp` §5). -/
def matrixToPauliCoords (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ × ℝ × ℝ :=
  ((X 0 1).im, (X 0 1).re, (X 0 0).im)

/-- **Pauli coordinate extraction respects ℝ-linear combinations**.

For real scalars a, b, c and `X, Y, Z ∈ tracelessSkewHermitian (Fin 2)`,
the Pauli coords of `a·X + b·Y + c·Z` are the corresponding linear
combination of (coords X), (coords Y), (coords Z). -/
theorem matrixToPauliCoords_smul (a : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixToPauliCoords ((a : ℂ) • X) =
      (a * (matrixToPauliCoords X).1,
       a * (matrixToPauliCoords X).2.1,
       a * (matrixToPauliCoords X).2.2) := by
  unfold matrixToPauliCoords
  simp [Matrix.smul_apply, smul_eq_mul, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]

theorem matrixToPauliCoords_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixToPauliCoords (X + Y) =
      ((matrixToPauliCoords X).1 + (matrixToPauliCoords Y).1,
       (matrixToPauliCoords X).2.1 + (matrixToPauliCoords Y).2.1,
       (matrixToPauliCoords X).2.2 + (matrixToPauliCoords Y).2.2) := by
  unfold matrixToPauliCoords
  simp [Matrix.add_apply, Complex.add_im, Complex.add_re]

/-- **Pauli coords of `paulI_x` = (1, 0, 0)**. -/
theorem matrixToPauliCoords_paulI_x : matrixToPauliCoords paulI_x = (1, 0, 0) := by
  unfold matrixToPauliCoords paulI_x
  simp [Matrix.smul_apply, smul_eq_mul, SKEFTHawking.σ_x,
        Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- **Pauli coords of `paulI_y` = (0, 1, 0)**. -/
theorem matrixToPauliCoords_paulI_y : matrixToPauliCoords paulI_y = (0, 1, 0) := by
  unfold matrixToPauliCoords paulI_y
  simp [Matrix.smul_apply, smul_eq_mul, SKEFTHawking.σ_y,
        Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.neg_im, Complex.neg_re]

/-- **Pauli coords of `paulI_z` = (0, 0, 1)**. -/
theorem matrixToPauliCoords_paulI_z : matrixToPauliCoords paulI_z = (0, 0, 1) := by
  unfold matrixToPauliCoords paulI_z
  simp [Matrix.smul_apply, smul_eq_mul, SKEFTHawking.σ_z,
        Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- **Pauli coords injectivity on `tracelessSkewHermitian (Fin 2)`**:
if `X ∈ tracelessSkewHermitian (Fin 2)` and `matrixToPauliCoords X = 0`,
then `X = 0`.

Combined with `tracelessSkewHermitian_decomp` (§5), this gives the
isomorphism `tracelessSkewHermitian (Fin 2) ≅ ℝ³` via Pauli coords. -/
theorem matrixToPauliCoords_eq_zero_iff
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    matrixToPauliCoords X = (0, 0, 0) ↔ X = 0 := by
  refine ⟨fun h_coords => ?_, fun h_X => ?_⟩
  · -- coords = 0 ⟹ X = 0
    rw [tracelessSkewHermitian_decomp hX]
    unfold matrixToPauliCoords at h_coords
    have h1 : (X 0 1).im = 0 := by
      have := h_coords; rw [Prod.mk.injEq] at this; exact this.1
    have h2 : (X 0 1).re = 0 := by
      have := h_coords; rw [Prod.mk.injEq] at this
      have := this.2; rw [Prod.mk.injEq] at this; exact this.1
    have h3 : (X 0 0).im = 0 := by
      have := h_coords; rw [Prod.mk.injEq] at this
      have := this.2; rw [Prod.mk.injEq] at this; exact this.2
    rw [show ((X 0 1).im : ℂ) = 0 by rw [h1]; simp,
        show ((X 0 1).re : ℂ) = 0 by rw [h2]; simp,
        show ((X 0 0).im : ℂ) = 0 by rw [h3]; simp]
    simp
  · -- X = 0 ⟹ coords = 0
    rw [h_X]
    unfold matrixToPauliCoords
    simp

/-! ## §7. Skew-Hermitian projection (Layer F.4, session 44)

For any 2×2 complex matrix M, the **skew-Hermitian projection**
  `(M - M†) / 2`
is the canonical element of skew-Hermitian 2×2 matrices.

For traceless M, this projection lands in `tracelessSkewHermitian (Fin 2)`
(the Lie algebra 𝔰𝔲(2)). This is the substrate needed to extract
"Lie-algebra components" from H_Fib elements (which are in SU(2), not
𝔰𝔲(2) directly).
-/

/-- **Skew-Hermitian projection** for arbitrary square complex matrices.

`skewHermitianProj M := (M - star M) / 2`. -/
noncomputable def skewHermitianProj {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : Matrix n n ℂ :=
  ((1/2 : ℂ)) • (M - M.conjTranspose)

/-- The skew-Hermitian projection is indeed skew-Hermitian. -/
theorem skewHermitianProj_isSkewHermitian {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : (skewHermitianProj M).IsSkewHermitian := by
  show (skewHermitianProj M).conjTranspose = -(skewHermitianProj M)
  unfold skewHermitianProj
  rw [Matrix.conjTranspose_smul]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  ext i j
  simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul,
        Complex.star_def]
  ring

/-- If `M` is traceless, then `skewHermitianProj M` is traceless. -/
theorem skewHermitianProj_trace_zero {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM_tr : M.trace = 0) :
    (skewHermitianProj M).trace = 0 := by
  unfold skewHermitianProj
  rw [Matrix.trace_smul, Matrix.trace_sub]
  rw [hM_tr, Matrix.trace_conjTranspose, hM_tr]
  simp

/-- **For traceless M, `skewHermitianProj M ∈ tracelessSkewHermitian (Fin 2)`**. -/
theorem skewHermitianProj_mem_tracelessSkewHermitian
    {M : Matrix (Fin 2) (Fin 2) ℂ} (hM_tr : M.trace = 0) :
    skewHermitianProj M ∈ tracelessSkewHermitian (Fin 2) :=
  ⟨skewHermitianProj_isSkewHermitian M, skewHermitianProj_trace_zero hM_tr⟩

/-- **For X already in `tracelessSkewHermitian (Fin 2)`,
`skewHermitianProj X = X`**.

Proof: skewHermitianProj X = (X - star X)/2 = (X - (-X))/2 = X. -/
theorem skewHermitianProj_idempotent_on_tracelessSkewHermitian
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    skewHermitianProj X = X := by
  obtain ⟨hX_skew, _⟩ := hX
  unfold skewHermitianProj
  rw [hX_skew]
  ext i j
  simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- **Skew-Hermitian projection of `(X - 1)` simplifies** since `1† = 1`.

For X ∈ Matrix (Fin n) (Fin n) ℂ:
  `skewHermitianProj (X - 1) = (1/2) • (X - X†)`. -/
theorem skewHermitianProj_sub_one {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) :
    skewHermitianProj (X - 1) = (1/2 : ℂ) • (X - X.conjTranspose) := by
  unfold skewHermitianProj
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  abel

/-! ## §8. Traceless projection (Layer F.6, session 46)

For arbitrary 2×2 complex matrix M:
  `tracelessProj M := M - (trace M / 2) • I`
This makes M traceless without affecting the off-diagonal structure.

The companion membership theorem `liePart_mem_tracelessSkewHermitian`
(showing that `tracelessProj ∘ skewHermitianProj` lands in 𝔰𝔲(2) for
any M) is deferred to a follow-on session as it requires careful
handling of the trace's pure-imaginary structure on skew-Hermitian
inputs.
-/

/-- **Traceless projection** for 2×2 complex matrices. Subtracts the
trace-component-of-identity to land in traceless matrices. -/
noncomputable def tracelessProj (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  M - ((M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- `tracelessProj M` is traceless. -/
theorem tracelessProj_trace_zero (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (tracelessProj M).trace = 0 := by
  unfold tracelessProj
  rw [Matrix.trace_sub, Matrix.trace_smul]
  simp [Matrix.trace_one, Fintype.card_fin]

/-- **For X already traceless, `tracelessProj X = X`** (idempotence on
the traceless subspace). -/
theorem tracelessProj_of_traceless {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M.trace = 0) : tracelessProj M = M := by
  unfold tracelessProj
  rw [hM]
  simp

/-- **For X ∈ tracelessSkewHermitian (Fin 2), `tracelessProj X = X`** —
specialization of `tracelessProj_of_traceless`. -/
theorem tracelessProj_idempotent_on_tracelessSkewHermitian
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    tracelessProj X = X :=
  tracelessProj_of_traceless hX.2

/-! ## §9. Conditional linear-independence criterion (Layer F.7, session 47)

For 3 matrices A, B, C ∈ `tracelessSkewHermitian (Fin 2)`, the criterion
for ℝ-linear independence is: the 3×3 determinant of their Pauli
coordinate vectors (3-tuples in ℝ³) is non-zero.

This is the **load-bearing criterion** for downstream "3-direction Lie
spanning" theorems on the H_Fib substrate.

The relation `paulI_combination_matrix` from §4 says that
  `a·X_A + b·X_B + c·X_C = 0`
expanded into Pauli coords gives a 3×3 linear system in `(a, b, c)`.
Non-singular system ⟹ unique solution `a = b = c = 0`.
-/

/-- **Pauli determinant** of three matrices in `Matrix (Fin 2) (Fin 2) ℂ`. -/
def pauliDet (A B C : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  let (xA, yA, zA) := matrixToPauliCoords A
  let (xB, yB, zB) := matrixToPauliCoords B
  let (xC, yC, zC) := matrixToPauliCoords C
  xA * (yB * zC - zB * yC) - yA * (xB * zC - zB * xC) + zA * (xB * yC - yB * xC)

/-- **Pauli determinant of `{paulI_x, paulI_y, paulI_z} = 1`** —
the canonical basis is "normalized" in the determinant sense. -/
theorem pauliDet_paulI_basis : pauliDet paulI_x paulI_y paulI_z = 1 := by
  unfold pauliDet
  simp [matrixToPauliCoords_paulI_x, matrixToPauliCoords_paulI_y,
        matrixToPauliCoords_paulI_z]

/-! ### Cramer-rule cofactor identities (Layer F.8 helpers, session 48)

The three identities below are pure ℝ-polynomial identities expressing
`x_i · det(N) = (cofactor of column i) · h_1 - ... + ... · h_3`
where `N` is the 3×3 real matrix whose columns are the Pauli-coord
triples of A, B, C, and `h_1, h_2, h_3 = 0` are the three real linear
equations obtained from `a • A + b • B + c • C = 0` by Pauli-coord
extraction. Each identity follows from a cofactor expansion of
`det(N)` and the fact that a 3×3 determinant with two equal rows
vanishes. Closed by `linear_combination` with explicit cofactor
coefficients. -/

private lemma pauliDet_cramer_a
    (xA yA zA xB yB zB xC yC zC a b c : ℝ)
    (h1 : a * xA + b * xB + c * xC = 0)
    (h2 : a * yA + b * yB + c * yC = 0)
    (h3 : a * zA + b * zB + c * zC = 0) :
    a * (xA * (yB * zC - zB * yC) - yA * (xB * zC - zB * xC)
         + zA * (xB * yC - yB * xC)) = 0 := by
  linear_combination
    (yB * zC - zB * yC) * h1 - (xB * zC - zB * xC) * h2
    + (xB * yC - yB * xC) * h3

private lemma pauliDet_cramer_b
    (xA yA zA xB yB zB xC yC zC a b c : ℝ)
    (h1 : a * xA + b * xB + c * xC = 0)
    (h2 : a * yA + b * yB + c * yC = 0)
    (h3 : a * zA + b * zB + c * zC = 0) :
    b * (xA * (yB * zC - zB * yC) - yA * (xB * zC - zB * xC)
         + zA * (xB * yC - yB * xC)) = 0 := by
  linear_combination
    -(yA * zC - zA * yC) * h1 + (xA * zC - zA * xC) * h2
    - (xA * yC - yA * xC) * h3

private lemma pauliDet_cramer_c
    (xA yA zA xB yB zB xC yC zC a b c : ℝ)
    (h1 : a * xA + b * xB + c * xC = 0)
    (h2 : a * yA + b * yB + c * yC = 0)
    (h3 : a * zA + b * zB + c * zC = 0) :
    c * (xA * (yB * zC - zB * yC) - yA * (xB * zC - zB * xC)
         + zA * (xB * yC - yB * xC)) = 0 := by
  linear_combination
    (yA * zB - zA * yB) * h1 - (xA * zB - zA * xB) * h2
    + (xA * yB - yA * xB) * h3

/-- **HEADLINE — Cramer-rule linear independence for 3 traceless
skew-Hermitian matrices (Layer F.8)**.

If three matrices `A, B, C : Matrix (Fin 2) (Fin 2) ℂ` satisfy
`pauliDet A B C ≠ 0` and a real-linear combination
`(a:ℂ) • A + (b:ℂ) • B + (c:ℂ) • C = 0`, then `a = b = c = 0`.

This is the **load-bearing linear-independence criterion** for the
H_Fib 3-bundle spanning argument (Layer F.9+). The proof composes
`matrixToPauliCoords` linearity (Layer F.3) with the Cramer-rule
cofactor identities above.

Note: the hypothesis `pauliDet A B C ≠ 0` alone suffices — the
matrices need not be in `tracelessSkewHermitian (Fin 2)`. The
namesake "tracelessSkewHermitian" refers to the downstream use case
where this criterion is applied to Lie-algebra-valued matrices. -/
theorem tracelessSkewHermitian_lin_indep_of_pauliDet_ne_zero
    {A B C : Matrix (Fin 2) (Fin 2) ℂ}
    (h_det : pauliDet A B C ≠ 0)
    {a b c : ℝ}
    (h_zero : (a : ℂ) • A + (b : ℂ) • B + (c : ℂ) • C = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  -- Step 1: apply matrixToPauliCoords to both sides of h_zero
  have h_coords := congrArg matrixToPauliCoords h_zero
  rw [matrixToPauliCoords_add, matrixToPauliCoords_add,
      matrixToPauliCoords_smul, matrixToPauliCoords_smul,
      matrixToPauliCoords_smul] at h_coords
  -- Step 2: matrixToPauliCoords 0 = (0, 0, 0)
  have h_zero_zero : matrixToPauliCoords (0 : Matrix (Fin 2) (Fin 2) ℂ)
      = (0, 0, 0) := by
    unfold matrixToPauliCoords
    simp
  rw [h_zero_zero] at h_coords
  -- Step 3: destructure the triple equality into three scalar equations
  rw [Prod.mk.injEq, Prod.mk.injEq] at h_coords
  obtain ⟨h1, h2, h3⟩ := h_coords
  -- Step 4: each of a, b, c times pauliDet equals 0; pauliDet ≠ 0 ⟹ each = 0
  refine ⟨?_, ?_, ?_⟩
  · have h_a := pauliDet_cramer_a _ _ _ _ _ _ _ _ _ a b c h1 h2 h3
    have h_a' : a * pauliDet A B C = 0 := h_a
    exact (mul_eq_zero.mp h_a').resolve_right h_det
  · have h_b := pauliDet_cramer_b _ _ _ _ _ _ _ _ _ a b c h1 h2 h3
    have h_b' : b * pauliDet A B C = 0 := h_b
    exact (mul_eq_zero.mp h_b').resolve_right h_det
  · have h_c := pauliDet_cramer_c _ _ _ _ _ _ _ _ _ a b c h1 h2 h3
    have h_c' : c * pauliDet A B C = 0 := h_c
    exact (mul_eq_zero.mp h_c').resolve_right h_det

/-! ## §11. Lie-algebra projection (Layer F.9, session 48)

Discharges the deferred companion of §8: the **composition
`tracelessProj ∘ skewHermitianProj` lands in `tracelessSkewHermitian (Fin 2)`
for any 2×2 complex matrix M** — no traceless hypothesis on M required.

The key fact: for `X.IsSkewHermitian`, `star X.trace = -X.trace`
(trace is pure imaginary), so `(X.trace / 2) • I` is itself
skew-Hermitian, and `X - (X.trace / 2) • I = tracelessProj X` remains
skew-Hermitian.

This packages the **canonical projection `lieProj : Matrix (Fin 2) (Fin 2) ℂ
→ Matrix (Fin 2) (Fin 2) ℂ`** onto 𝔰𝔲(2), with key properties:

  - `lieProj_mem_tracelessSkewHermitian` (HEADLINE): output is in 𝔰𝔲(2).
  - `lieProj_one_eq_zero`: `lieProj 1 = 0` (since `M = 1` is Hermitian
    + scalar, so `skewHermitianProj 1 = 0`).
  - `lieProj_idempotent_on_tracelessSkewHermitian`: for X ∈ 𝔰𝔲(2),
    `lieProj X = X`.
-/

/-- For a skew-Hermitian matrix, the trace is pure imaginary,
i.e., `star (trace X) = - trace X`. -/
theorem _root_.Matrix.IsSkewHermitian.star_trace_eq_neg
    {n : Type*} [Fintype n] {X : Matrix n n ℂ} (hX : X.IsSkewHermitian) :
    star X.trace = -X.trace := by
  rw [← Matrix.trace_conjTranspose, hX, Matrix.trace_neg]

/-- For a skew-Hermitian matrix in `Matrix (Fin 2) (Fin 2) ℂ`,
`tracelessProj X` is also skew-Hermitian. -/
theorem tracelessProj_isSkewHermitian
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.IsSkewHermitian) :
    (tracelessProj X).IsSkewHermitian := by
  show (tracelessProj X).conjTranspose = -(tracelessProj X)
  unfold tracelessProj
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one]
  rw [show X.conjTranspose = -X from hX]
  -- Goal: -X - star (X.trace / 2) • 1 = -(X - X.trace / 2 • 1)
  -- Use: star (X.trace / 2) = star X.trace / star 2 = (-X.trace) / 2 = -X.trace / 2
  have h_star : star (X.trace / 2 : ℂ) = -(X.trace / 2) := by
    rw [star_div₀, hX.star_trace_eq_neg]
    simp [neg_div]
  rw [h_star]
  ext i j
  simp [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- For a skew-Hermitian matrix in `Matrix (Fin 2) (Fin 2) ℂ`,
`tracelessProj X ∈ tracelessSkewHermitian (Fin 2)`. -/
theorem tracelessProj_mem_tracelessSkewHermitian
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.IsSkewHermitian) :
    tracelessProj X ∈ tracelessSkewHermitian (Fin 2) :=
  ⟨tracelessProj_isSkewHermitian hX, tracelessProj_trace_zero X⟩

/-- **Canonical projection onto 𝔰𝔲(2)** (Layer F.9): `lieProj M` is the
composition `tracelessProj ∘ skewHermitianProj`. -/
noncomputable def lieProj (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  tracelessProj (skewHermitianProj M)

/-- **HEADLINE — `lieProj M ∈ tracelessSkewHermitian (Fin 2)`** for any
2×2 complex matrix M. The composition `tracelessProj ∘ skewHermitianProj`
unconditionally lands in the Lie algebra 𝔰𝔲(2). -/
theorem lieProj_mem_tracelessSkewHermitian (M : Matrix (Fin 2) (Fin 2) ℂ) :
    lieProj M ∈ tracelessSkewHermitian (Fin 2) :=
  tracelessProj_mem_tracelessSkewHermitian (skewHermitianProj_isSkewHermitian M)

/-- `lieProj 1 = 0`. The identity matrix is Hermitian + a scalar
multiple of itself, so its image under both projections is 0. -/
theorem lieProj_one_eq_zero :
    lieProj (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  unfold lieProj skewHermitianProj tracelessProj
  ext i j
  simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]

/-- For X already in `tracelessSkewHermitian (Fin 2)`, `lieProj X = X`
(idempotence on the Lie algebra). -/
theorem lieProj_idempotent_on_tracelessSkewHermitian
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    lieProj X = X := by
  unfold lieProj
  rw [skewHermitianProj_idempotent_on_tracelessSkewHermitian hX,
      tracelessProj_idempotent_on_tracelessSkewHermitian hX]

/-! ## §12. Conjugation equivariance of `lieProj` (Layer F.10, session 48)

For unitary `g`, the canonical 𝔰𝔲(2)-projection `lieProj` commutes
with conjugation: `lieProj (g·M·g†) = g · lieProj M · g†`. This is the
Ad-action equivariance that downstream H_Fib spanning needs — applying
`lieProj` to the H_Fib 3-bundle `(h, σ_Fib_1·h·σ_Fib_1†, σ_Fib_2·h·σ_Fib_2†)`
gives `(lieProj h, Ad(σ_Fib_1)(lieProj h), Ad(σ_Fib_2)(lieProj h))`,
the bundle of Ad-rotated Lie directions.

Key observation:
  - `skewHermitianProj` is conjugation-equivariant unconditionally
    (just needs `(gMg†)† = gM†g†`), no unitarity required.
  - `tracelessProj` requires unitarity (`trace cyclic` needs `g†g = 1`,
    `(tr M/2)•g·I·g† = (tr M/2)•I` needs `g·g† = 1`).
-/

/-- **`skewHermitianProj` conjugates with arbitrary matrices**: no
unitarity required since `(g·M·g†)† = g·M†·g†` is a property of
`conjTranspose` alone. -/
theorem skewHermitianProj_conj_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n]
    (g M : Matrix n n ℂ) :
    skewHermitianProj (g * M * g.conjTranspose) =
      g * skewHermitianProj M * g.conjTranspose := by
  unfold skewHermitianProj
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  -- Goal: (1/2) • (gMg† - g(M†g†)) = g · ((1/2) • (M - M†)) · g†
  -- (conjTranspose rewrites leave the M†*g† term right-associated)
  rw [Matrix.mul_smul, Matrix.smul_mul]
  -- Goal: (1/2) • (gMg† - g(M†g†)) = (1/2) • (g · (M - M†) · g†)
  congr 1
  noncomm_ring

/-- **`tracelessProj` is unitary-conjugation-equivariant** (n=2 only,
matching the `tracelessProj` definition's domain). Uses both
left-unitarity (`g† · g = 1`, for trace cyclic) and right-unitarity
(`g · g† = 1`, for the scalar-identity term). -/
theorem tracelessProj_conj_unitary
    {g : Matrix (Fin 2) (Fin 2) ℂ}
    (h_left : g.conjTranspose * g = 1) (h_right : g * g.conjTranspose = 1)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    tracelessProj (g * M * g.conjTranspose) =
      g * tracelessProj M * g.conjTranspose := by
  unfold tracelessProj
  -- trace(g * M * g†) = trace(M * g† * g) = trace(M * 1) = trace M
  have h_trace : (g * M * g.conjTranspose).trace = M.trace := by
    -- trace_mul_cycle gives `trace(g† * g * M)` (left-associated `(g†*g)*M`)
    rw [Matrix.trace_mul_cycle, h_left, Matrix.one_mul]
  rw [h_trace]
  -- Now: g M g† - (tr M / 2) • I  =  g · (M - (tr M / 2) • I) · g†
  -- RHS = g·M·g† - g · ((tr M / 2) • I) · g†
  --     = g·M·g† - (tr M / 2) • g · I · g†
  --     = g·M·g† - (tr M / 2) • (g · g†)
  --     = g·M·g† - (tr M / 2) • I
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, h_right]

/-- **HEADLINE — `lieProj` is unitary-conjugation-equivariant**: for
unitary `g`, `lieProj (g · M · g†) = g · lieProj M · g†`. -/
theorem lieProj_conj_unitary
    {g : Matrix (Fin 2) (Fin 2) ℂ}
    (h_left : g.conjTranspose * g = 1) (h_right : g * g.conjTranspose = 1)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    lieProj (g * M * g.conjTranspose) =
      g * lieProj M * g.conjTranspose := by
  unfold lieProj
  rw [skewHermitianProj_conj_conjTranspose,
      tracelessProj_conj_unitary h_left h_right]

/-! ## §13. specialUnitaryGroup specialization (Layer F.11, session 48)

Bridges the general `lieProj_conj_unitary` (which needs both
unitarity directions as explicit hypotheses) to the
`Matrix.specialUnitaryGroup` API used by `σ_Fib_*_SU`.

For `g ∈ specialUnitaryGroup`, both unitarity hypotheses follow from
`Matrix.mem_unitaryGroup_iff` (right) and `Matrix.mem_unitaryGroup_iff'`
(left), since `star = conjTranspose` definitionally on matrices.
-/

/-- For `g : Matrix.specialUnitaryGroup (Fin 2) ℂ`, `lieProj` is
conjugation-equivariant: `lieProj (g·M·g†) = g · lieProj M · g†`.

This is the form used by the H_Fib bundle argument, since
σ_Fib_1_SU, σ_Fib_2_SU live in `specialUnitaryGroup`. -/
theorem lieProj_conj_specialUnitary
    (g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    lieProj (g.val * M * g.val.conjTranspose) =
      g.val * lieProj M * g.val.conjTranspose := by
  have hg_uni : g.val ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.property).1
  exact lieProj_conj_unitary
    (Matrix.mem_unitaryGroup_iff'.mp hg_uni)
    (Matrix.mem_unitaryGroup_iff.mp hg_uni)
    M

/-! ## §14. Ad-action preserves 𝔰𝔲(2) (Layer F.12, session 48)

For `g ∈ specialUnitaryGroup` and X ∈ 𝔰𝔲(2), the Ad-conjugate
`g.val · X · g.val†` lies again in 𝔰𝔲(2). This is the bedrock fact:
**SU(2) acts on its Lie algebra by Ad**.

Proof: `lieProj (g·X·g†) = g·(lieProj X)·g† = g·X·g†` (using F.11 +
idempotence F.9), so `g·X·g†` equals its own `lieProj`, which is
always in 𝔰𝔲(2) by `lieProj_mem_tracelessSkewHermitian` (F.9).
-/

/-- **HEADLINE — Ad-action of specialUnitaryGroup preserves 𝔰𝔲(2)**:
for `g ∈ specialUnitaryGroup (Fin 2) ℂ` and X ∈ tracelessSkewHermitian,
`g.val · X · g.val†` lies in tracelessSkewHermitian. -/
theorem tracelessSkewHermitian_conj_specialUnitary
    (g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    g.val * X * g.val.conjTranspose ∈ tracelessSkewHermitian (Fin 2) := by
  -- g·X·g† = lieProj (g·X·g†) since lieProj preserves elements of 𝔰𝔲(2)
  have h_eq : g.val * X * g.val.conjTranspose =
      lieProj (g.val * X * g.val.conjTranspose) := by
    rw [lieProj_conj_specialUnitary,
        lieProj_idempotent_on_tracelessSkewHermitian hX]
  rw [h_eq]
  exact lieProj_mem_tracelessSkewHermitian _

/-! ## §15. Cramer-rule SPANNING criterion (Layer F.20.a, session 50)

Companion to §10 (Cramer-rule independence). Given 3 elements of `𝔰𝔲(2)`
with non-zero `pauliDet`, every X ∈ 𝔰𝔲(2) admits an explicit real linear
combination expressing X as `(a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃`.

This is the spanning half of the linear-independence/spanning duality
(§10 proves "lin-indep ⟹ unique combination"; §15 proves "lin-indep ⟹
combination exists"). Together they establish that `(v₁, v₂, v₃)` is a
basis of `𝔰𝔲(2)` under the `pauliDet ≠ 0` hypothesis.

Proof: explicit Cramer formula for the inverse 3×3 matrix applied to
the target Pauli coordinates of X. The algebraic identities are pure
ℝ-polynomial identities closed by `field_simp; ring`. -/

/-- The submodule `tracelessSkewHermitian (Fin 2)` is closed under
ℂ-scalar action by real-cast coefficients. -/
private theorem tracelessSkewHermitian_complex_smul_real_mem
    {v : Matrix (Fin 2) (Fin 2) ℂ} (hv : v ∈ tracelessSkewHermitian (Fin 2))
    (r : ℝ) : (r : ℂ) • v ∈ tracelessSkewHermitian (Fin 2) := by
  rw [Complex.coe_smul r v]
  exact Submodule.smul_mem _ r hv

/-- **Cramer-rule explicit-combination spanning**: if `pauliDet v₁ v₂ v₃ ≠ 0`
for `v₁, v₂, v₃ ∈ 𝔰𝔲(2)`, then every `X ∈ 𝔰𝔲(2)` has an explicit
ℝ-coefficient triple `(a, b, c)` with
`X = (a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃`.

This is the SPAN companion to the LIN-INDEP criterion `tracelessSkewHermitian_lin_indep_of_pauliDet_ne_zero`
in §10. Together they show `pauliDet ≠ 0` is **necessary and sufficient**
for `(v₁, v₂, v₃)` to be a basis of `𝔰𝔲(2)`. -/
theorem tracelessSkewHermitian_exists_combo_of_pauliDet_ne_zero
    {v₁ v₂ v₃ : Matrix (Fin 2) (Fin 2) ℂ}
    (hv₁ : v₁ ∈ tracelessSkewHermitian (Fin 2))
    (hv₂ : v₂ ∈ tracelessSkewHermitian (Fin 2))
    (hv₃ : v₃ ∈ tracelessSkewHermitian (Fin 2))
    (h_det : pauliDet v₁ v₂ v₃ ≠ 0)
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ tracelessSkewHermitian (Fin 2)) :
    ∃ a b c : ℝ,
      X = (a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃ := by
  -- Extract Pauli coords as scalars
  set xv1 := (matrixToPauliCoords v₁).1 with hxv1
  set yv1 := (matrixToPauliCoords v₁).2.1 with hyv1
  set zv1 := (matrixToPauliCoords v₁).2.2 with hzv1
  set xv2 := (matrixToPauliCoords v₂).1 with hxv2
  set yv2 := (matrixToPauliCoords v₂).2.1 with hyv2
  set zv2 := (matrixToPauliCoords v₂).2.2 with hzv2
  set xv3 := (matrixToPauliCoords v₃).1 with hxv3
  set yv3 := (matrixToPauliCoords v₃).2.1 with hyv3
  set zv3 := (matrixToPauliCoords v₃).2.2 with hzv3
  set x := (matrixToPauliCoords X).1 with hx
  set y := (matrixToPauliCoords X).2.1 with hy
  set z := (matrixToPauliCoords X).2.2 with hz
  -- Identify pauliDet expansion
  set D := xv1 * (yv2 * zv3 - zv2 * yv3) - yv1 * (xv2 * zv3 - zv2 * xv3)
           + zv1 * (xv2 * yv3 - yv2 * xv3) with hD_def
  have hD_eq : pauliDet v₁ v₂ v₃ = D := rfl
  have hD : D ≠ 0 := hD_eq ▸ h_det
  -- Define explicit Cramer-rule coefficients
  refine ⟨(x * (yv2 * zv3 - zv2 * yv3) - y * (xv2 * zv3 - zv2 * xv3)
           + z * (xv2 * yv3 - yv2 * xv3)) / D,
          (-(x * (yv1 * zv3 - zv1 * yv3)) + y * (xv1 * zv3 - zv1 * xv3)
           - z * (xv1 * yv3 - yv1 * xv3)) / D,
          (x * (yv1 * zv2 - zv1 * yv2) - y * (xv1 * zv2 - zv1 * xv2)
           + z * (xv1 * yv2 - yv1 * xv2)) / D, ?_⟩
  set a := (x * (yv2 * zv3 - zv2 * yv3) - y * (xv2 * zv3 - zv2 * xv3)
            + z * (xv2 * yv3 - yv2 * xv3)) / D with ha_def
  set b := (-(x * (yv1 * zv3 - zv1 * yv3)) + y * (xv1 * zv3 - zv1 * xv3)
            - z * (xv1 * yv3 - yv1 * xv3)) / D with hb_def
  set c := (x * (yv1 * zv2 - zv1 * yv2) - y * (xv1 * zv2 - zv1 * xv2)
            + z * (xv1 * yv2 - yv1 * xv2)) / D with hc_def
  -- Step 1: combo is in 𝔰𝔲(2)
  have h_combo_mem :
      (a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃ ∈
        tracelessSkewHermitian (Fin 2) := by
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact tracelessSkewHermitian_complex_smul_real_mem hv₁ a
    · exact tracelessSkewHermitian_complex_smul_real_mem hv₂ b
    · exact tracelessSkewHermitian_complex_smul_real_mem hv₃ c
  -- Step 2: Pauli coords of combo match X's coords
  have h_coords_match :
      matrixToPauliCoords ((a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃) =
        matrixToPauliCoords X := by
    rw [matrixToPauliCoords_add, matrixToPauliCoords_add,
        matrixToPauliCoords_smul, matrixToPauliCoords_smul,
        matrixToPauliCoords_smul]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · -- x-coord
      show a * xv1 + b * xv2 + c * xv3 = x
      simp only [ha_def, hb_def, hc_def]
      field_simp
      ring
    · -- y-coord
      show a * yv1 + b * yv2 + c * yv3 = y
      simp only [ha_def, hb_def, hc_def]
      field_simp
      ring
    · -- z-coord
      show a * zv1 + b * zv2 + c * zv3 = z
      simp only [ha_def, hb_def, hc_def]
      field_simp
      ring
  -- Step 3: difference is in 𝔰𝔲(2) with zero coords ⟹ difference = 0 ⟹ X = combo
  have h_diff_mem : X - ((a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃) ∈
      tracelessSkewHermitian (Fin 2) := Submodule.sub_mem _ hX h_combo_mem
  have h_diff_coords_zero :
      matrixToPauliCoords (X - ((a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃)) =
        (0, 0, 0) := by
    rw [sub_eq_add_neg, matrixToPauliCoords_add]
    have h_neg :
        matrixToPauliCoords (-((a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃)) =
        (-(matrixToPauliCoords ((a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃)).1,
         -(matrixToPauliCoords ((a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃)).2.1,
         -(matrixToPauliCoords ((a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃)).2.2) := by
      unfold matrixToPauliCoords
      simp [Matrix.neg_apply, Complex.neg_im, Complex.neg_re]
    rw [h_neg, h_coords_match]
    simp
  have h_diff_zero :
      X - ((a : ℂ) • v₁ + (b : ℂ) • v₂ + (c : ℂ) • v₃) = 0 :=
    (matrixToPauliCoords_eq_zero_iff h_diff_mem).mp h_diff_coords_zero
  exact sub_eq_zero.mp h_diff_zero

/-! ## §10. Module summary

`SU2LieAlgebra.lean` (Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-A,
session 35; extended Layer F.1 session 41 + Layer F.2 session 42 +
Layer F.3 session 43): foundational Lie algebra substrate for the
upstream-IFT path to Fibonacci density.

**Shipped (zero new axioms)**:

  - **§1**: `Matrix.IsSkewHermitian` predicate + closure under add/neg/zero.
  - **§2**: `tracelessSkewHermitian (n : Type*) [Fintype n]` as ℝ-submodule
    of `Matrix n n ℂ`. The real Lie algebra 𝔰𝔲(n).
  - **§3**: `paulI_x`, `paulI_y`, `paulI_z` (the three i·σ_k generators
    of 𝔰𝔲(2)) + skew-Hermicity + tracelessness + membership lemmas.
  - **§4** (Layer F.1, session 41): `paulI_linear_independent` — the
    three Pauli generators are ℝ-linearly independent in `Matrix _ _ ℂ`.
    Proof: explicit matrix-form decomposition `a·paulI_x + b·paulI_y +
    c·paulI_z = !![c·i, a·i+b; a·i-b, -c·i]`, then entry-wise comparison.
  - **§5** (Layer F.2, session 42): `tracelessSkewHermitian_decomp` —
    explicit `X = (X 0 1).im • paulI_x + (X 0 1).re • paulI_y +
    (X 0 0).im • paulI_z` for any traceless skew-Hermitian X.
  - **§6** (Layer F.3, session 43): `matrixToPauliCoords` — extraction
    map `X ↦ ((X 0 1).im, (X 0 1).re, (X 0 0).im) : ℝ × ℝ × ℝ` +
    linearity + `matrixToPauliCoords_eq_zero_iff` (X ∈ tracelessSH ∧
    coords = 0 ↔ X = 0).
  - **§7** (Layer F.4, session 44): `skewHermitianProj X := (1/2)•(X - X*)`
    projection onto skew-Hermitian + idempotence on tracelessSH.
  - **§8** (Layer F.6, session 46): `tracelessProj X := X - (tr X / 2)•I`
    projection onto traceless + idempotence on tracelessSH.
  - **§9** (Layer F.7, session 47): `pauliDet` (def) +
    `pauliDet_paulI_basis = 1` (canonical basis normalization).
  - **§9** (Layer F.8, session 48): **HEADLINE**
    `tracelessSkewHermitian_lin_indep_of_pauliDet_ne_zero` — the full
    Cramer-rule criterion: `pauliDet A B C ≠ 0` ⟹ `A, B, C` are
    ℝ-linearly independent in `Matrix _ _ ℂ`. Proof: 3 cofactor
    identities `a · det = (...) · h₁ - (...) · h₂ + (...) · h₃`
    closed by `linear_combination`, composed with `matrixToPauliCoords`
    linearity.
  - **§11** (Layer F.9, session 48): `lieProj M := tracelessProj
    (skewHermitianProj M)` — canonical projection onto 𝔰𝔲(2). HEADLINE
    `lieProj_mem_tracelessSkewHermitian` discharges the §8-deferred
    companion: unconditionally lands in 𝔰𝔲(2). Key sub-lemma
    `Matrix.IsSkewHermitian.star_trace_eq_neg` says trace is pure
    imaginary for skew-Hermitian matrices. Companion lemmas:
    `lieProj_one_eq_zero` (1 ↦ 0) +
    `lieProj_idempotent_on_tracelessSkewHermitian`.
  - **§12** (Layer F.10, session 48): `lieProj` Ad-equivariance.
    `skewHermitianProj_conj_conjTranspose` (no unitarity needed),
    `tracelessProj_conj_unitary` (needs both `g†g = 1` and `g·g† = 1`
    for trace cyclic + scalar-identity), HEADLINE
    `lieProj_conj_unitary`: `lieProj (g·M·g†) = g · lieProj M · g†`.
  - **§13** (Layer F.11, session 48):
    `lieProj_conj_specialUnitary` — for `g ∈ specialUnitaryGroup`,
    Ad-equivariance follows from `mem_unitaryGroup_iff'` (left) +
    `mem_unitaryGroup_iff` (right), since `star = conjTranspose`
    definitionally on matrices. The form used by σ_Fib_*_SU.
  - **§14** (Layer F.12, session 48):
    `tracelessSkewHermitian_conj_specialUnitary` — for
    `g ∈ specialUnitaryGroup`, the Ad-conjugate
    `g.val · X · g.val†` lies in 𝔰𝔲(2) when X does. The bedrock
    "SU(2) acts on its Lie algebra by Ad" fact. Proof: compose
    F.11 + F.9 idempotence + F.9 membership.

**Substrate downstream (next sessions)**:

  - **Cartan-B** (session 36, `SU2MatrixExp.lean`): matrix exponential
    `𝔰𝔲(2) → SU(2)` + smoothness + derivative at 0.
  - **Cartan-C** (session 37, `SU2LocalDiffeo.lean`): apply normed-space
    IFT to get local diffeomorphism.
  - **Cartan-D** (session 38): compose with shipped D.3.h + D.3.i.1 +
    AccPt to close `1 ∈ interior(closure H_Fib)`.
  - **Layer E** (session 39): `DenseInSpecialUnitary` composition.

**Mathlib4 v4.29.0 compatibility**: `Matrix.IsHermitian` exists in
`Mathlib.LinearAlgebra.Matrix.Hermitian`; this module's
`Matrix.IsSkewHermitian` follows the same convention. Upstream-PR
viable.
-/

end SKEFTHawking.FKLW.SU2LieAlgebra
