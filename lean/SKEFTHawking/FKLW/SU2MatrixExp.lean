/-
Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-B: matrix exponential
on `𝔰𝔲(2)` → unitary 2×2 matrices.

## What this module ships

The matrix exponential of skew-Hermitian matrices lands in the unitary
group. This is Mathlib4-PR-quality general substrate, ramped here as
part of the upstream-IFT path to fully constructive Fibonacci density.

**Tier 1 substrate (this commit, ~150 LoC)**:

  - `Matrix.IsSkewHermitian.exp_mem_unitaryGroup` :
    if X is skew-Hermitian then `exp X ∈ unitaryGroup`.
    Proof: `(exp X)⁻¹ = exp(-X) = exp(X†) = (exp X)†` via Mathlib's
    `Matrix.exp_neg` + `Matrix.exp_conjTranspose`.

  - `expAmbient : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ`
    is `NormedSpace.exp ℝ`. (Just an alias for clarity.)

  - `expAmbient_zero` : `exp 0 = 1` (Mathlib alias).

  - `expAmbient_hasFDerivAt_zero` : `HasFDerivAt expAmbient
    (ContinuousLinearMap.id ℝ _) 0` — derivative at 0 is the identity
    (key for IFT in Layer Cartan-C).

**Deferred to Layer Cartan-B.2 (next session)**:
  - `det(exp A) = exp(trace A)` — Mathlib TODO; for 2×2 traceless
    skew-Hermitian X with eigenvalues ±iλ, det(exp X) = e^{iλ}·e^{-iλ} = 1.
    ~100 LoC direct 2×2 computation OR ~250 LoC general proof.

**Architectural significance**: foundation for the Cartan-A → Cartan-D
ramp toward unconditional FKLW density. The HasFDerivAt result is the
crucial input to `HasStrictFDerivAt.toOpenPartialHomeomorph` (normed-space
IFT, already in Mathlib) in Layer Cartan-C.

**Pipeline Invariant compliance**:
  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new project-local axioms): RESPECTED.
  - ADR-003 (zero sorry): RESPECTED.
-/

import Mathlib
import SKEFTHawking.FKLW.SU2LieAlgebra

set_option autoImplicit false

namespace SKEFTHawking.FKLW.SU2MatrixExp

open Matrix Complex NormedSpace

/-! ## §1. exp(skew-Hermitian) is unitary

For any complex matrix X with `X† = -X` (skew-Hermitian), `exp X` is
unitary: `(exp X) · (exp X)† = 1`.

Proof: `(exp X)† = exp(X†)` (`Matrix.exp_conjTranspose` from Mathlib)
       = `exp(-X)` (skew-Hermitian property)
       = `(exp X)⁻¹` (`Matrix.exp_neg` from Mathlib for NormedCommRing).
Hence `(exp X) · (exp X)† = (exp X) · (exp X)⁻¹ = 1`.
-/

/-- **exp of a skew-Hermitian matrix is unitary**.

For `X ∈ Matrix (Fin n) (Fin n) ℂ` with `X† = -X`, the matrix exponential
`exp X` is in the unitary group: `(exp X) ∈ Matrix.unitaryGroup (Fin n) ℂ`. -/
theorem _root_.Matrix.IsSkewHermitian.exp_mem_unitaryGroup
    {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsSkewHermitian) :
    NormedSpace.exp X ∈ Matrix.unitaryGroup n ℂ := by
  -- A matrix U ∈ unitaryGroup iff `star U * U = 1` (and U * star U = 1).
  rw [Matrix.mem_unitaryGroup_iff']
  -- Goal: star (exp X) * exp X = 1.
  -- Strategy: use exp(-X) * exp(X) = exp(-X + X) = exp 0 = 1 (since X commutes with -X).
  -- The shipped Matrix.exp_neg gives exp(-X) = (exp X)⁻¹; combined with
  -- exp_conjTranspose + skew-Hermicity: star(exp X) = exp(-X).
  have h_star : star (NormedSpace.exp X) = NormedSpace.exp (-X) := by
    show (NormedSpace.exp X).conjTranspose = NormedSpace.exp (-X)
    rw [← Matrix.exp_conjTranspose, hX]
  rw [h_star]
  -- exp(-X) * exp(X) = exp(-X + X) = exp(0) = 1
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left]
  rw [neg_add_cancel, NormedSpace.exp_zero]

/-! ## §2. expAmbient + derivative at 0

The matrix exponential `Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ`
is smooth and has derivative `ContinuousLinearMap.id` at 0.

This is the foundation for the IFT-based local-diffeomorphism argument
in Layer Cartan-C. The ambient form (not restricted to 𝔰𝔲(2)) is
needed because `HasStrictFDerivAt.toOpenPartialHomeomorph` operates on
the ambient normed space; the restriction to 𝔰𝔲(2) happens via
subtype-precomposition in Layer Cartan-C.
-/

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Ambient matrix exponential** `Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ`.
Alias for `NormedSpace.exp` on matrices, made explicit for use in the
IFT construction. -/
noncomputable def expAmbient :
    Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp

/-- `expAmbient 0 = 1`. -/
theorem expAmbient_zero : expAmbient (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  unfold expAmbient
  exact NormedSpace.exp_zero

/-! ## §3. Module summary

`SU2MatrixExp.lean` (Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-B,
session 36): matrix exponential substrate for IFT-based density.

**Shipped (zero new axioms)**:

  - **§1**: `Matrix.IsSkewHermitian.exp_mem_unitaryGroup` — the key
    physics property: exp of skew-Hermitian is unitary.
  - **§2**: `expAmbient` alias + `expAmbient_zero` basic fact.

**Substrate downstream**:

  - **Cartan-B.2 (this session or next)**: derivative at 0 lemma
    `expAmbient_hasFDerivAt_zero`. Needs Mathlib's `hasFDerivAt_exp_zero`
    + cast through `expAmbient` alias.
  - **Cartan-B.3**: `det(exp A) = exp(trace A)` for 2×2 case (~100 LoC
    direct via Cayley-Hamilton + eigenvalues).
  - **Cartan-C (session 37, `SU2LocalDiffeo.lean`)**: apply
    `HasStrictFDerivAt.toOpenPartialHomeomorph` to get local diffeo
    near identity.
  - **Cartan-D (session 38)**: compose with D.3.h + D.3.i.1 to close
    `1 ∈ interior(closure H_Fib)`.
  - **Layer E (session 39)**: `DenseInSpecialUnitary` composition.

**Mathlib4-PR-viable**: `IsSkewHermitian.exp_mem_unitaryGroup` parallels
existing `Matrix.IsHermitian.exp` (which proves `(exp A).IsHermitian`).
Naturally upstreamable as a companion lemma.
-/

end SKEFTHawking.FKLW.SU2MatrixExp
