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

/- **The full Cramer-rule linear-independence theorem
`tracelessSkewHermitian_lin_indep_of_pauliDet_ne_zero` is deferred to a
follow-on session.** It requires careful destructuring of the 3-tuple
Pauli-coord output + Cramer's-rule algebra; planned via `Matrix.det`
machinery rather than ad-hoc nlinarith. Substrate via `matrixToPauliCoords`
linearity (Layer F.3) + `pauliDet` (above) is in place. -/

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
