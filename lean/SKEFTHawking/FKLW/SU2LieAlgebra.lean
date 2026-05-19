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

/-! ## §4. Module summary

`SU2LieAlgebra.lean` (Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-A,
session 35): foundational Lie algebra substrate for the upstream-IFT
path to Fibonacci density.

**Shipped (zero new axioms)**:

  - **§1**: `Matrix.IsSkewHermitian` predicate + closure under add/neg/zero.
  - **§2**: `tracelessSkewHermitian (n : Type*) [Fintype n]` as ℝ-submodule
    of `Matrix n n ℂ`. The real Lie algebra 𝔰𝔲(n).
  - **§3**: `paulI_x`, `paulI_y`, `paulI_z` (the three i·σ_k generators
    of 𝔰𝔲(2)) + skew-Hermicity + tracelessness + membership lemmas.

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
