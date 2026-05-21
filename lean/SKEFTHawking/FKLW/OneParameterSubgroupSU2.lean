/-
Phase 6p Wave 2c.4a-R4.2.d.R5.4 Cartan strengthening — von Neumann
1-parameter subgroup theorem for SU(2): discharge of the strengthened
gap-#2 predicate `OneParamSubgroupFromAccPt_SU2`.

## What this module ships (Mathlib4-upstream-PR-quality substrate)

The **substantive content** behind the strengthened tracked predicate
`SKEFTHawking.FKLW.OneParamSubgroupFromAccPt_SU2` (defined in
`CartanSubstrate.lean` §4.7).

The headline theorem is the **von Neumann 1-parameter subgroup theorem
for SU(2)**: any closed subgroup `H ≤ SU(2)` that has the identity as an
accumulation point contains a continuous nontrivial 1-parameter subgroup
`φ : ℝ → SU(2)` with image entirely in `H`.

This is the canonical Lie-theoretic statement: a closed subgroup of a
compact Lie group containing a sequence approaching the identity is at
least 1-dimensional, and that dimension is witnessed by the 1-parameter
subgroups it contains.

## Module structure

§1. **`su2Log`** (the local-IFT inverse of `expAmbient` near identity):
    extracted from `SU2LocalDiffeo`'s shipped IFT instance.

§2. (next ship) **`su2Log h ∈ tracelessSkewHermitian (Fin 2)`** for
    h ∈ SU(2) ∩ source: matrix log of an SU(2) element near 1 lies in
    the Lie algebra su(2).

§3. (next ship) **Von Neumann construction**: sequence h_n → 1 in
    H \ {1} produces, via BW on the unit sphere of su(2), a unit X with
    exp(t·X) ∈ H for all t (via integer-rounding convergence).

§4. (next ship) **Discharge** of `OneParamSubgroupFromAccPt_SU2`.

## Pipeline Invariant compliance

- #10 (no `maxHeartbeats`): RESPECTED.
- #15 (no new project-local axioms): RESPECTED (this module discharges a
  TRACKED PROP; it does not introduce any).
- ADR-003 (zero sorry): RESPECTED.

## Mathlib upstream-PR posture

The §1 local-log substrate is a *direct unwrap* of the existing
`expAmbient_hasStrictFDerivAt_zero_equiv.toOpenPartialHomeomorph`
(shipped in `SU2LocalDiffeo.lean`); making it top-level reusable is
the natural Mathlib upstream form (paired with the existing
`NormedSpace.exp` API). The von Neumann argument in §3 is a clean
PR-shaped specialization to SU(2); the more general statement for
arbitrary compact Lie groups would compose this with Mathlib's general
Lie-group infrastructure.
-/

import Mathlib
import SKEFTHawking.FKLW.SU2LocalDiffeo
import SKEFTHawking.FKLW.SU2LieAlgebra
import SKEFTHawking.FKLW.CartanSubstrate

set_option autoImplicit false

namespace SKEFTHawking.FKLW.OneParameterSubgroupSU2

open Matrix Complex NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## §1. Local matrix logarithm near identity in M₂(ℂ)

The matrix exponential `expAmbient` has invertible Fréchet derivative
at 0 (the identity equivalence on the ambient `Matrix (Fin 2) (Fin 2) ℂ`
normed space), so Mathlib's Inverse Function Theorem produces an
`OpenPartialHomeomorph` φ on a neighborhood of 0, with image a
neighborhood of `expAmbient 0 = 1`. The local inverse `φ.symm` is the
**matrix logarithm near identity**.

We extract φ as a top-level definition so its source/target/symm are
reusable across §§2-4 below. The single Mathlib substrate used is
`HasStrictFDerivAt.toOpenPartialHomeomorph` together with the shipped
`expAmbient_hasStrictFDerivAt_zero_equiv`. -/

/-- **The local IFT homeomorphism for `expAmbient` at 0**.

An `OpenPartialHomeomorph` φ on `Matrix (Fin 2) (Fin 2) ℂ` with:
- `0 ∈ φ.source`, `φ 0 = 1`,
- `φ x = expAmbient x` on `φ.source`,
- `φ.symm` is the corresponding local-inverse / matrix-logarithm,
- both `φ.source` and `φ.target` are open.

Produced by Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph`
applied to the shipped `expAmbient_hasStrictFDerivAt_zero_equiv`. -/
noncomputable def expAmbientPartialHomeo :
    OpenPartialHomeomorph (Matrix (Fin 2) (Fin 2) ℂ)
                          (Matrix (Fin 2) (Fin 2) ℂ) :=
  HasStrictFDerivAt.toOpenPartialHomeomorph SU2MatrixExp.expAmbient
    SU2LocalDiffeo.expAmbient_hasStrictFDerivAt_zero_equiv

/-- `0` is in the source of the local homeomorphism. -/
theorem zero_mem_expAmbientPartialHomeo_source :
    (0 : Matrix (Fin 2) (Fin 2) ℂ) ∈ expAmbientPartialHomeo.source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    SU2LocalDiffeo.expAmbient_hasStrictFDerivAt_zero_equiv

/-- On its source, the local homeomorphism agrees with `expAmbient`. -/
theorem expAmbientPartialHomeo_coe :
    (expAmbientPartialHomeo : Matrix (Fin 2) (Fin 2) ℂ →
                              Matrix (Fin 2) (Fin 2) ℂ) =
      SU2MatrixExp.expAmbient :=
  HasStrictFDerivAt.toOpenPartialHomeomorph_coe
    SU2LocalDiffeo.expAmbient_hasStrictFDerivAt_zero_equiv

/-- The homeomorphism sends `0` to `1`. -/
theorem expAmbientPartialHomeo_zero :
    expAmbientPartialHomeo (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [expAmbientPartialHomeo_coe]
  exact SU2MatrixExp.expAmbient_zero

/-- `1` is in the target of the local homeomorphism. -/
theorem one_mem_expAmbientPartialHomeo_target :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ expAmbientPartialHomeo.target := by
  rw [← expAmbientPartialHomeo_zero]
  exact expAmbientPartialHomeo.map_source
    zero_mem_expAmbientPartialHomeo_source

/-- **`su2Log`** — the local matrix logarithm near `1`, defined as the
symm of the IFT homeomorphism. Defined on `expAmbientPartialHomeo.target`
(a neighborhood of `1` in `Matrix (Fin 2) (Fin 2) ℂ`); on this domain it
satisfies `expAmbient (su2Log h) = h`.

For `h` outside the domain `su2Log h` returns the partial inverse's
extension (unspecified value), so the meaningful predicates always carry
`h ∈ expAmbientPartialHomeo.target` as hypothesis. -/
noncomputable def su2Log : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ :=
  expAmbientPartialHomeo.symm

/-- `su2Log 1 = 0`. -/
theorem su2Log_one : su2Log (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  show expAmbientPartialHomeo.symm 1 = 0
  rw [← expAmbientPartialHomeo_zero]
  exact expAmbientPartialHomeo.left_inv
    zero_mem_expAmbientPartialHomeo_source

/-- For `h` in the local-homeomorphism target, `expAmbient (su2Log h) = h`.

This is the defining property of the local matrix logarithm: it is a
right-inverse to `expAmbient` on a neighborhood of `1`. -/
theorem expAmbient_su2Log
    {h : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : h ∈ expAmbientPartialHomeo.target) :
    SU2MatrixExp.expAmbient (su2Log h) = h := by
  show SU2MatrixExp.expAmbient (expAmbientPartialHomeo.symm h) = h
  rw [← expAmbientPartialHomeo_coe]
  exact expAmbientPartialHomeo.right_inv hh

/-- For `Y` in the local-homeomorphism source, `su2Log (expAmbient Y) = Y`.

This is the left-inverse direction: matrix log undoes matrix exp on the
small neighborhood of `0` where the IFT applies. -/
theorem su2Log_expAmbient
    {Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hY : Y ∈ expAmbientPartialHomeo.source) :
    su2Log (SU2MatrixExp.expAmbient Y) = Y := by
  show expAmbientPartialHomeo.symm (SU2MatrixExp.expAmbient Y) = Y
  rw [← expAmbientPartialHomeo_coe]
  exact expAmbientPartialHomeo.left_inv hY

/-- The local-homeomorphism source is open in `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem expAmbientPartialHomeo_source_isOpen :
    IsOpen expAmbientPartialHomeo.source :=
  expAmbientPartialHomeo.open_source

/-- The local-homeomorphism target is open in `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem expAmbientPartialHomeo_target_isOpen :
    IsOpen expAmbientPartialHomeo.target :=
  expAmbientPartialHomeo.open_target

/-- `expAmbientPartialHomeo.target` is a neighborhood of `1`. -/
theorem expAmbientPartialHomeo_target_mem_nhds_one :
    expAmbientPartialHomeo.target ∈ nhds (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  expAmbientPartialHomeo_target_isOpen.mem_nhds
    one_mem_expAmbientPartialHomeo_target

/-- `expAmbientPartialHomeo.source` is a neighborhood of `0`. -/
theorem expAmbientPartialHomeo_source_mem_nhds_zero :
    expAmbientPartialHomeo.source ∈ nhds (0 : Matrix (Fin 2) (Fin 2) ℂ) :=
  expAmbientPartialHomeo_source_isOpen.mem_nhds
    zero_mem_expAmbientPartialHomeo_source

/-- **`su2Log` is continuous on its domain `target`** (immediate from the
homeomorphism structure: `symm` is continuous on `target`). -/
theorem su2Log_continuousOn :
    ContinuousOn su2Log expAmbientPartialHomeo.target := by
  show ContinuousOn expAmbientPartialHomeo.symm expAmbientPartialHomeo.target
  exact expAmbientPartialHomeo.continuousOn_symm

/-! ## §1.5. SU(2) elements near identity are in the domain of `su2Log`

A specialization: for SU(2) elements (viewed as their underlying
matrices) sufficiently close to 1, `su2Log` is defined. This is the
useful form for downstream consumers who work with SU(2)-subtype
sequences (h_n) → 1.

The witness `expAmbientPartialHomeo.target ∈ nhds 1` (above) combined
with continuity of `Subtype.val` gives: there is a neighborhood `W` of
`1` in `SU(2)` such that `g.val ∈ target` for all `g ∈ W`. -/

/-- **There is a neighborhood `W` of `1` in `SU(2)` with `g.val ∈ target`
for all `g ∈ W`.**

Pulled back from the open `target ⊆ Matrix _ _ ℂ` via continuity of
`Subtype.val`. -/
theorem exists_nhds_one_SU2_su2Log_defined :
    ∃ W : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      W ∈ nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
      ∀ g ∈ W, (g : Matrix (Fin 2) (Fin 2) ℂ) ∈ expAmbientPartialHomeo.target := by
  refine ⟨Subtype.val ⁻¹' expAmbientPartialHomeo.target, ?_, fun _ hg => hg⟩
  have h_val_one :
      (Subtype.val (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl
  have h_target_nhds_val :
      expAmbientPartialHomeo.target ∈
        nhds (Subtype.val (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix _ _ ℂ) := by
    rw [h_val_one]; exact expAmbientPartialHomeo_target_mem_nhds_one
  exact continuous_subtype_val.continuousAt h_target_nhds_val

/-! ## §2. Cayley-Hamilton specialization for su(2): `X² = -r² • 1`

**Defined (this ship):** the polar-radius-squared `su2RadiusSq X`.

**Headline theorem (next ship):** for X ∈ `tracelessSkewHermitian (Fin 2)`,
`X² = -(su2RadiusSq X) • I`. This is the key algebraic identity that
enables the closed-form analysis of `exp X` (§3) and ultimately the
discharge of `OneParamSubgroupFromAccPt_SU2` (§4).

Structural form (from the already-shipped private
`SU2LieAlgebra.tracelessSkewHermitian_entries`):
`X = !![iα, β; -β̄, -iα]` with `α = (X 0 0).im ∈ ℝ`, `β = X 0 1 ∈ ℂ`,
so direct 2×2 matrix multiplication yields
`X² = -(α² + |β|²) • I`. -/

/-- **Real polar-radius-squared of an su(2) element.**

For X ∈ `tracelessSkewHermitian (Fin 2)` of the form `!![iα, β; -β̄, -iα]`,
returns `α² + |β|²`, a non-negative real. By the (next-ship)
Cayley-Hamilton specialization, `X² = -(su2RadiusSq X) • I` always.

Defined for any 2×2 complex matrix; the geometric meaning is only valid
on `tracelessSkewHermitian`. -/
noncomputable def su2RadiusSq (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ((X 0 0).im) ^ 2 + ‖X 0 1‖ ^ 2

/-- `su2RadiusSq` is non-negative. -/
theorem su2RadiusSq_nonneg (X : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ su2RadiusSq X := by
  unfold su2RadiusSq
  positivity

/-! ### §2.0. Pauli-product helpers

Direct entry calculations for the standard Pauli relations needed in
the Cayley-Hamilton proof below:

  - `paulI_y_sq`, `paulI_z_sq`: `paulI_α² = -1` (analog of shipped
    `paulI_x_sq`). Each follows from `(iσ_α)² = -1·σ_α² = -1·1 = -1`.
  - Three anti-commutation identities `paulI_α · paulI_β + paulI_β ·
    paulI_α = 0` for α ≠ β, from `(iσ_α)(iσ_β) + (iσ_β)(iσ_α) = -(σ_α σ_β
    + σ_β σ_α) = -(0) = 0`.

Each proof: unfold to underlying σ-matrices, `ext`+`fin_cases`, simp +
`Complex.I_mul_I`. Direct 2×2 computation, no coercion gymnastics. -/

/-- `paulI_y² = -1`. -/
theorem paulI_y_sq :
    SU2LieAlgebra.paulI_y * SU2LieAlgebra.paulI_y =
      (-1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold SU2LieAlgebra.paulI_y SKEFTHawking.σ_y
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply,
          Matrix.one_apply, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Fin.sum_univ_two, smul_eq_mul, Complex.I_mul_I]

/-- `paulI_z² = -1`. -/
theorem paulI_z_sq :
    SU2LieAlgebra.paulI_z * SU2LieAlgebra.paulI_z =
      (-1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold SU2LieAlgebra.paulI_z SKEFTHawking.σ_z
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply,
          Matrix.one_apply, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Fin.sum_univ_two, smul_eq_mul, Complex.I_mul_I]

/-- `paulI_x · paulI_y + paulI_y · paulI_x = 0` (anti-commutation). -/
theorem paulI_xy_anticomm :
    SU2LieAlgebra.paulI_x * SU2LieAlgebra.paulI_y +
      SU2LieAlgebra.paulI_y * SU2LieAlgebra.paulI_x =
        (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold SU2LieAlgebra.paulI_x SU2LieAlgebra.paulI_y
        SKEFTHawking.σ_x SKEFTHawking.σ_y
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Fin.sum_univ_two, smul_eq_mul,
          Complex.I_mul_I]

/-- `paulI_x · paulI_z + paulI_z · paulI_x = 0` (anti-commutation). -/
theorem paulI_xz_anticomm :
    SU2LieAlgebra.paulI_x * SU2LieAlgebra.paulI_z +
      SU2LieAlgebra.paulI_z * SU2LieAlgebra.paulI_x =
        (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold SU2LieAlgebra.paulI_x SU2LieAlgebra.paulI_z
        SKEFTHawking.σ_x SKEFTHawking.σ_z
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Fin.sum_univ_two, smul_eq_mul,
          Complex.I_mul_I]

/-- `paulI_y · paulI_z + paulI_z · paulI_y = 0` (anti-commutation). -/
theorem paulI_yz_anticomm :
    SU2LieAlgebra.paulI_y * SU2LieAlgebra.paulI_z +
      SU2LieAlgebra.paulI_z * SU2LieAlgebra.paulI_y =
        (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold SU2LieAlgebra.paulI_y SU2LieAlgebra.paulI_z
        SKEFTHawking.σ_y SKEFTHawking.σ_z
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Fin.sum_univ_two, smul_eq_mul,
          Complex.I_mul_I]

/-! ### §2.1. Cayley-Hamilton on Pauli linear combinations

The intermediate result decoupling the Pauli-algebra structure from
the X-as-element-of-su(2) structural form. Once
`pauliLinearCombo_sq : (a•paulI_x + b•paulI_y + c•paulI_z)² =
-(a² + b² + c²) • 1` is in hand, the headline
`tracelessSkewHermitian_two_sq` follows by `tracelessSkewHermitian_decomp`
plus the norm-squared algebra. -/

/-- Cayley-Hamilton for the generic Pauli linear combination:
`(a·σᵢ + b·σⱼ + c·σz)² = -(a² + b² + c²) • 1`.

Direct entry computation on the explicit Pauli matrices; each entry
expands to a polynomial in `a, b, c, I` that closes via `ring` after
applying `Complex.I_sq` (i.e., `I² = -1`). -/
theorem pauliLinearCombo_sq (a b c : ℂ) :
    ((a • SU2LieAlgebra.paulI_x + b • SU2LieAlgebra.paulI_y +
      c • SU2LieAlgebra.paulI_z) *
     (a • SU2LieAlgebra.paulI_x + b • SU2LieAlgebra.paulI_y +
      c • SU2LieAlgebra.paulI_z) :
      Matrix (Fin 2) (Fin 2) ℂ) =
    (-(a^2 + b^2 + c^2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold SU2LieAlgebra.paulI_x SU2LieAlgebra.paulI_y SU2LieAlgebra.paulI_z
        SKEFTHawking.σ_x SKEFTHawking.σ_y SKEFTHawking.σ_z
  ext i j
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
          Matrix.neg_apply, Matrix.one_apply_eq,
          Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
          Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Fin.sum_univ_two, smul_eq_mul]
  all_goals ring_nf
  all_goals (try rw [show Complex.I ^ 2 = -1 from Complex.I_sq])
  all_goals ring

/-! ### §2.2. Cayley-Hamilton specialization (headline) -/

/-- **CAYLEY-HAMILTON SPECIALIZATION** for `tracelessSkewHermitian (Fin 2)`:
`X² = -(su2RadiusSq X) • 1`.

The key algebraic identity that enables the closed-form analysis of
`exp` on su(2): even powers of X are scalar multiples of I, odd powers
are scalar multiples of X.

Proof strategy (Pauli-decomposition approach): write
`X = a·paulI_x + b·paulI_y + c·paulI_z` with `a := (X 0 1).im`,
`b := (X 0 1).re`, `c := (X 0 0).im` (the shipped
`tracelessSkewHermitian_decomp`), then apply the intermediate result
`pauliLinearCombo_sq` and use `Complex.sq_norm` to identify
`a² + b² + c²` with `su2RadiusSq X`. -/
theorem tracelessSkewHermitian_two_sq
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :
    X * X = (-(su2RadiusSq X) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- Use the shipped Pauli decomposition.
  have hX_decomp :
      X = ((X 0 1).im : ℂ) • SU2LieAlgebra.paulI_x +
          ((X 0 1).re : ℂ) • SU2LieAlgebra.paulI_y +
          ((X 0 0).im : ℂ) • SU2LieAlgebra.paulI_z :=
    SU2LieAlgebra.tracelessSkewHermitian_decomp hX
  -- Scalar identity: -(a² + b² + c²) = -(su2RadiusSq X) where a, b, c
  -- are the Pauli coefficients ((X 0 1).im, (X 0 1).re, (X 0 0).im).
  have h_norm_real : (‖X 0 1‖ : ℝ) ^ 2 = (X 0 1).im ^ 2 + (X 0 1).re ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h_scalar :
      (-(((((X 0 1).im : ℝ) : ℂ) ^ 2 + (((X 0 1).re : ℝ) : ℂ) ^ 2 +
          (((X 0 0).im : ℝ) : ℂ) ^ 2)) : ℂ) =
      (-(su2RadiusSq X) : ℂ) := by
    have h_rad_real : (su2RadiusSq X : ℝ) =
        (X 0 1).im ^ 2 + (X 0 1).re ^ 2 + (X 0 0).im ^ 2 := by
      unfold su2RadiusSq
      rw [h_norm_real]
      ring
    push_cast
    rw [h_rad_real]
    push_cast
    ring
  calc X * X
      = (((X 0 1).im : ℂ) • SU2LieAlgebra.paulI_x +
         ((X 0 1).re : ℂ) • SU2LieAlgebra.paulI_y +
         ((X 0 0).im : ℂ) • SU2LieAlgebra.paulI_z) *
        (((X 0 1).im : ℂ) • SU2LieAlgebra.paulI_x +
         ((X 0 1).re : ℂ) • SU2LieAlgebra.paulI_y +
         ((X 0 0).im : ℂ) • SU2LieAlgebra.paulI_z) := by
          conv_lhs => rw [hX_decomp]
    _ = (-(((((X 0 1).im : ℝ) : ℂ) ^ 2 + (((X 0 1).re : ℝ) : ℂ) ^ 2 +
            (((X 0 0).im : ℝ) : ℂ) ^ 2)) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
        pauliLinearCombo_sq _ _ _
    _ = (-(su2RadiusSq X) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          rw [h_scalar]

/-! ## §3. 1-parameter subgroup machinery on `tracelessSkewHermitian (Fin 2)`

Given X ∈ tracelessSkewHermitian (Fin 2), the map `φ t := expAmbient (t • X)`
defines a continuous 1-parameter subgroup at the matrix level. Properties
we ship in this section:

  - `oneParamMatrixMap X 0 = 1`
  - `oneParamMatrixMap X (s + t) = oneParamMatrixMap X s * oneParamMatrixMap X t`
  - `Continuous (oneParamMatrixMap X)`
  - X.IsSkewHermitian ⟹ ∀ t, (oneParamMatrixMap X t).IsSkewHermitian
    *propagation of skew-Hermitian* (NOT correct — exp of skew-Hermitian
    is unitary, not skew-Hermitian; instead we ship the *unitary*
    membership directly).
  - `oneParamMatrixMap_mem_unitaryGroup`: for X ∈ tracelessSkewHermitian
    (Fin 2), `expAmbient (t • X) ∈ Matrix.unitaryGroup (Fin 2) ℂ`.

The **substantive SU(2) inclusion** (det = 1) is the followup §3.5:
either via closed-form `exp X = cos(r) • I + sinc(r) • X` with
`r² = su2RadiusSq X` (using `tracelessSkewHermitian_two_sq` to identify
even/odd power series with cos/sin), or via spectral theorem for the
underlying Hermitian `i • X`. Deferred substrate. -/

/-- The 1-parameter subgroup map at the matrix level.
`oneParamMatrixMap X t := expAmbient ((t : ℂ) • X)`. -/
noncomputable def oneParamMatrixMap
    (X : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  SU2MatrixExp.expAmbient ((t : ℂ) • X)

/-- `oneParamMatrixMap X 0 = 1`. -/
theorem oneParamMatrixMap_zero (X : Matrix (Fin 2) (Fin 2) ℂ) :
    oneParamMatrixMap X 0 = 1 := by
  unfold oneParamMatrixMap
  simp [SU2MatrixExp.expAmbient]

/-- `oneParamMatrixMap X (s + t) = oneParamMatrixMap X s * oneParamMatrixMap X t`.

Uses `NormedSpace.exp_add_of_commute` for the commuting case (s•X and t•X
both commute with each other since they're scalar multiples of the same
matrix). -/
theorem oneParamMatrixMap_add
    (X : Matrix (Fin 2) (Fin 2) ℂ) (s t : ℝ) :
    oneParamMatrixMap X (s + t) =
      oneParamMatrixMap X s * oneParamMatrixMap X t := by
  unfold oneParamMatrixMap SU2MatrixExp.expAmbient
  rw [show (((s + t : ℝ) : ℂ) • X) = ((s : ℂ) • X) + ((t : ℂ) • X) by
        push_cast; rw [add_smul]]
  exact NormedSpace.exp_add_of_commute (Commute.smul_left
    (Commute.smul_right (Commute.refl X) t) s)

/-- `oneParamMatrixMap X` is continuous. -/
theorem oneParamMatrixMap_continuous (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (oneParamMatrixMap X) := by
  unfold oneParamMatrixMap SU2MatrixExp.expAmbient
  exact NormedSpace.exp_continuous.comp
    (Complex.continuous_ofReal.smul continuous_const)

/-- For X ∈ tracelessSkewHermitian (Fin 2), `t • X` is also in
tracelessSkewHermitian (real scalar smul preserves skew-Hermitian +
traceless). -/
theorem real_smul_tracelessSkewHermitian
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) (t : ℝ) :
    ((t : ℂ) • X) ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
  SU2LieAlgebra.tracelessSkewHermitian_complex_smul_real_mem hX t

/-- **Unitary membership for the 1-parameter subgroup**: for X ∈
tracelessSkewHermitian (Fin 2), `oneParamMatrixMap X t ∈ unitaryGroup`.

Via the shipped `Matrix.IsSkewHermitian.exp_mem_unitaryGroup`. -/
theorem oneParamMatrixMap_mem_unitaryGroup
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) (t : ℝ) :
    oneParamMatrixMap X t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  unfold oneParamMatrixMap SU2MatrixExp.expAmbient
  have h_smul_mem : ((t : ℂ) • X) ∈
      SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
    real_smul_tracelessSkewHermitian hX t
  exact Matrix.IsSkewHermitian.exp_mem_unitaryGroup h_smul_mem.1

/-! ## §3.5. Determinant closed form for linear combinations `α·I + β·X`

For X ∈ tracelessSkewHermitian (Fin 2), any linear combination
`α • I + β • X` (α, β ∈ ℂ) has determinant given by the closed form
`α² + β² · su2RadiusSq X`. This is the algebraic key for the
`det(expAmbient X) = 1` claim of the next sub-ship.

Derivation (Cayley-Hamilton on 2×2 with tr X = 0, det X = su2RadiusSq X):
`det(α · I + β · X) = α² + α·β·tr(X) + β²·det(X)
                    = α² + 0      + β²·su2RadiusSq X`. -/

/-- For X ∈ tracelessSkewHermitian (Fin 2), `det X = su2RadiusSq X` (cast to ℂ).

Direct computation via `Matrix.det_fin_two` + structural form
`X = !![iα, β; -β̄, -iα]`. -/
theorem tracelessSkewHermitian_det_eq_su2RadiusSq
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :
    Matrix.det X = ((su2RadiusSq X : ℝ) : ℂ) := by
  obtain ⟨hX_skew, hX_tr⟩ := hX
  -- Reuse the structural form derivation from tracelessSkewHermitian_two_sq.
  have h_diag_skew_00 : star (X 0 0) = -(X 0 0) := by
    have := congr_fun (congr_fun hX_skew 0) 0
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using this
  have h_re_00 : (X 0 0).re = 0 := by
    have h_sum : X 0 0 + star (X 0 0) = 0 := by rw [h_diag_skew_00]; ring
    have h_re_sum : (X 0 0).re + (star (X 0 0)).re = 0 := by
      have := congr_arg Complex.re h_sum
      simpa [Complex.add_re] using this
    rw [Complex.star_def, Complex.conj_re] at h_re_sum
    linarith
  have h_11 : X 1 1 = -X 0 0 := by
    have h_trace : X 0 0 + X 1 1 = 0 := by
      have := hX_tr
      simp [Matrix.trace, Fin.sum_univ_two] at this
      linear_combination this
    linear_combination h_trace
  have h_offdiag : X 1 0 = -star (X 0 1) := by
    have h_skew_01 : star (X 0 1) = -(X 1 0) := by
      have := congr_fun (congr_fun hX_skew 1) 0
      simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using this
    linear_combination h_skew_01
  have h_X00 : X 0 0 = (((X 0 0).im : ℝ) : ℂ) * Complex.I := by
    have := (Complex.re_add_im (X 0 0)).symm
    rw [h_re_00, Complex.ofReal_zero, zero_add] at this
    exact this
  -- Compute det X = X[0,0] · X[1,1] - X[0,1] · X[1,0].
  rw [Matrix.det_fin_two, h_11, h_offdiag, h_X00]
  -- Goal: (iα) · (-(iα)) - X 0 1 · (-(star (X 0 1))) = ↑(su2RadiusSq X)
  -- We'll compute LHS = α² + |X 0 1|² and recognize as su2RadiusSq X.
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  -- |X 0 1|² in ℂ via mul_conj.
  have h_conj : X 0 1 * star (X 0 1) =
      ((Complex.normSq (X 0 1) : ℝ) : ℂ) := by
    rw [show star (X 0 1) = (starRingEnd ℂ) (X 0 1) from rfl,
        Complex.mul_conj]
  -- Now compute.
  have h_calc :
      (((X 0 0).im : ℝ) : ℂ) * Complex.I * -((((X 0 0).im : ℝ) : ℂ) * Complex.I) -
        X 0 1 * -star (X 0 1) =
      (((X 0 0).im : ℝ) : ℂ) ^ 2 + ((Complex.normSq (X 0 1) : ℝ) : ℂ) := by
    have h1 : (((X 0 0).im : ℝ) : ℂ) * Complex.I *
                -((((X 0 0).im : ℝ) : ℂ) * Complex.I) =
              (((X 0 0).im : ℝ) : ℂ) ^ 2 := by
      have : (((X 0 0).im : ℝ) : ℂ) * Complex.I *
              -((((X 0 0).im : ℝ) : ℂ) * Complex.I) =
             -(((X 0 0).im : ℝ) : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      rw [this, hI2]; ring
    rw [h1]
    linear_combination h_conj
  rw [h_calc]
  -- Final: ↑(X 0 0).im² + ↑(normSq (X 0 1)) = ↑(su2RadiusSq X)
  unfold su2RadiusSq
  rw [show ((Complex.normSq (X 0 1) : ℝ) : ℂ) = ((‖X 0 1‖ ^ 2 : ℝ) : ℂ) by
    rw [show (Complex.normSq (X 0 1) : ℝ) = ‖X 0 1‖ ^ 2 from
      (Complex.sq_norm (X 0 1)).symm]]
  push_cast
  ring

/-- **Determinant closed form for `α • I + β • X` on su(2)**:
for X ∈ tracelessSkewHermitian (Fin 2) and any α, β ∈ ℂ,
`det(α • I + β • X) = α² + β² · su2RadiusSq X`.

Uses `Matrix.det_fin_two` + tracelessness (tr X = 0) + the just-proved
`tracelessSkewHermitian_det_eq_su2RadiusSq`. This is the algebraic key
that, combined with the closed-form `exp X = cos(r) • I + sinc(r) • X`,
will give `det(exp X) = cos²(r) + sin²(r) = 1` in the next sub-ship. -/
theorem det_alpha_one_plus_beta_smul_tracelessSkewHermitian
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (α β : ℂ) :
    Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) ℂ) + β • X) =
      α ^ 2 + β ^ 2 * ((su2RadiusSq X : ℝ) : ℂ) := by
  have hX_tr := hX.2
  -- Use Matrix.det_fin_two on the explicit linear combination.
  rw [Matrix.det_fin_two]
  -- Entries of α • 1 + β • X:
  --   [0,0] = α + β·X[0,0]
  --   [0,1] = β·X[0,1]
  --   [1,0] = β·X[1,0]
  --   [1,1] = α + β·X[1,1]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
             Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
             Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
             smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
  -- Goal: (α + β · X 0 0) · (α + β · X 1 1) - β · X 0 1 · (β · X 1 0)
  --     = α² + β² · ↑(su2RadiusSq X)
  -- Expand and use tr X = 0 → X 0 0 + X 1 1 = 0, plus
  -- det X (from det_fin_two with X 0 0 · X 1 1 - X 0 1 · X 1 0)
  -- = su2RadiusSq X.
  have h_tr : X 0 0 + X 1 1 = 0 := by
    have := hX_tr
    simp [Matrix.trace, Fin.sum_univ_two] at this
    linear_combination this
  have h_det : X 0 0 * X 1 1 - X 0 1 * X 1 0 = ((su2RadiusSq X : ℝ) : ℂ) := by
    have h_X_det : Matrix.det X = ((su2RadiusSq X : ℝ) : ℂ) :=
      tracelessSkewHermitian_det_eq_su2RadiusSq hX
    rw [Matrix.det_fin_two] at h_X_det
    exact h_X_det
  linear_combination
    α * β * h_tr +
    β ^ 2 * h_det

/-! ### §3.5a. Scaled Cayley-Hamilton

For X ∈ tracelessSkewHermitian (Fin 2), real-scalar multiples preserve
membership (already shipped as `real_smul_tracelessSkewHermitian`), and
the Cayley-Hamilton identity scales accordingly:
`(t • X)² = -(t² · su2RadiusSq X) • 1`.

This is the form needed for power-series analysis of `expAmbient (t • X)`. -/

/-- `su2RadiusSq` scales quadratically under real scalar multiplication. -/
theorem su2RadiusSq_real_smul
    (X : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    su2RadiusSq ((t : ℂ) • X) = t ^ 2 * su2RadiusSq X := by
  unfold su2RadiusSq
  rw [show ((((t : ℂ) • X) 0 0).im) = t * (X 0 0).im from by
        rw [Matrix.smul_apply, smul_eq_mul, Complex.im_ofReal_mul],
      show ((((t : ℂ) • X) 0 1)) = ((t : ℂ)) * X 0 1 from by
        rw [Matrix.smul_apply, smul_eq_mul]]
  rw [show ‖((t : ℂ)) * X 0 1‖ = |t| * ‖X 0 1‖ from by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]]
  nlinarith [sq_abs t, sq_nonneg ((X 0 0).im), sq_nonneg ‖X 0 1‖]

/-- **Scaled Cayley-Hamilton**: for X ∈ tracelessSkewHermitian (Fin 2)
and `t : ℝ`, `(t • X)² = -(t² · su2RadiusSq X) • 1`. -/
theorem tracelessSkewHermitian_real_smul_two_sq
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (t : ℝ) :
    ((t : ℂ) • X) * ((t : ℂ) • X) =
      (-(t ^ 2 * su2RadiusSq X : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h_smul_mem : ((t : ℂ) • X) ∈
      SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
    real_smul_tracelessSkewHermitian hX t
  have h_main := tracelessSkewHermitian_two_sq h_smul_mem
  rw [h_main]
  congr 1
  push_cast
  rw [su2RadiusSq_real_smul]
  push_cast
  ring

/-! ### §3.5b. Powers of X stay in `span ℂ {1, X}` when `X² = c • 1`

The structural fact behind the closed-form analysis of `expAmbient X`:
if X satisfies X² = c • 1 for some c ∈ ℂ (Cayley-Hamilton form), then
every power X^n is a ℂ-linear combination of 1 and X. Consequently each
partial sum of the exp series lives in `span ℂ {1, X}`, and the limit
(= expAmbient X) does too (since finite-dim submodules are closed in a
normed space). -/

/-- **Every power of an X with `X² = c • 1` is in `span ℂ {1, X}`**.

For X ∈ Matrix (Fin 2) (Fin 2) ℂ satisfying X² = c • 1 for some scalar
c ∈ ℂ, the powers `X^n` all lie in the 2-dimensional ℂ-submodule
spanned by 1 and X. Pattern (induction on n):
  - X^0 = 1 ∈ span,
  - X^1 = X ∈ span,
  - X^(n+2) = X^n · X² = X^n · (c • 1) = c • X^n ∈ span (by IH on n).

Note: the inductive step uses `X^(n+2) = X^n * X * X = X^n * X²`, which
requires associativity + matrix-multiplication mechanics. -/
theorem pow_mem_span_one_X_of_sq_eq_scalar
    {X : Matrix (Fin 2) (Fin 2) ℂ} {c : ℂ}
    (hX : X * X = c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (n : ℕ) :
    X ^ n ∈ Submodule.span ℂ
      ({1, X} : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      simp only [pow_zero]
      exact Submodule.subset_span (by simp)
    | 1 =>
      simp only [pow_one]
      exact Submodule.subset_span (by simp)
    | k + 2 =>
      -- X^(k+2) = X^k · X^2 = X^k · (c • 1) = c • X^k
      have h_pow : X ^ (k + 2) = c • X ^ k := by
        rw [show k + 2 = k + 1 + 1 from rfl, pow_succ, pow_succ]
        rw [mul_assoc, hX]
        rw [mul_smul_comm, mul_one]
      rw [h_pow]
      exact Submodule.smul_mem _ c (ih k (by omega))

/-- The Submodule `span ℂ {1, X}` is finite-dimensional (rank ≤ 2). -/
theorem span_one_X_finiteDimensional (X : Matrix (Fin 2) (Fin 2) ℂ) :
    FiniteDimensional ℂ
      (Submodule.span ℂ ({1, X} : Set (Matrix (Fin 2) (Fin 2) ℂ))) := by
  rw [show ({1, X} : Set (Matrix (Fin 2) (Fin 2) ℂ)) = ↑({1, X} : Finset _) by
    simp]
  exact FiniteDimensional.span_of_finite ℂ (Set.toFinite _)

/-- The Submodule `span ℂ {1, X}` is closed in `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem span_one_X_isClosed (X : Matrix (Fin 2) (Fin 2) ℂ) :
    IsClosed (Submodule.span ℂ
      ({1, X} : Set (Matrix (Fin 2) (Fin 2) ℂ)) :
      Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
  haveI := span_one_X_finiteDimensional X
  Submodule.closed_of_finiteDimensional _

/-! ### §3.5c. `expAmbient X ∈ span ℂ {1, X}` for X with `X² = c • 1`

Composing §3.5b's `pow_mem_span_one_X_of_sq_eq_scalar` with the
exp-series convergence: each partial sum of `Σ_n (n!)⁻¹ • X^n` lies in
`span ℂ {1, X}` (sum of memberships), the partial sums converge to
`expAmbient X` (by `NormedSpace.expSeries_hasSum_exp`), and the span
is closed (§3.5b), so the limit is in the span.

In particular for X ∈ tracelessSkewHermitian (Fin 2), Cayley-Hamilton
(§2 `tracelessSkewHermitian_two_sq`) supplies the `X² = c • 1` premise. -/

/-- **`expAmbient X` is a ℂ-linear combination of 1 and X**, for X
satisfying the Cayley-Hamilton form `X² = c • 1`. -/
theorem expAmbient_mem_span_one_X_of_sq_eq_scalar
    {X : Matrix (Fin 2) (Fin 2) ℂ} {c : ℂ}
    (hX : X * X = c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    SU2MatrixExp.expAmbient X ∈ Submodule.span ℂ
      ({1, X} : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  unfold SU2MatrixExp.expAmbient
  -- The exp series is summable.
  have h_sum : HasSum
      (fun n => (↑n.factorial : ℂ)⁻¹ • X ^ n) (NormedSpace.exp X) := by
    have := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) X
    convert this using 1
    ext n
    simp [NormedSpace.expSeries, smul_eq_mul]
  -- Partial sums tend to exp X.
  have h_tendsto :
      Filter.Tendsto
        (fun n => ∑ i ∈ Finset.range n, (↑i.factorial : ℂ)⁻¹ • X ^ i)
        Filter.atTop (nhds (NormedSpace.exp X)) :=
    HasSum.tendsto_sum_nat h_sum
  -- Each partial sum is in span.
  have h_partial_in_span : ∀ n,
      (∑ i ∈ Finset.range n, (↑i.factorial : ℂ)⁻¹ • X ^ i) ∈
        Submodule.span ℂ ({1, X} : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
    intro n
    apply Submodule.sum_mem
    intro i _hi
    exact Submodule.smul_mem _ _ (pow_mem_span_one_X_of_sq_eq_scalar hX i)
  -- Apply IsClosed.mem_of_tendsto.
  exact IsClosed.mem_of_tendsto (span_one_X_isClosed X) h_tendsto
    (Filter.Eventually.of_forall h_partial_in_span)

/-- **`expAmbient X` is in `span ℂ {1, X}` for X ∈ tracelessSkewHermitian (Fin 2)**.

Specialization to su(2) using §2 `tracelessSkewHermitian_two_sq` to
supply the Cayley-Hamilton premise. -/
theorem expAmbient_mem_span_one_X_of_tracelessSkewHermitian
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :
    SU2MatrixExp.expAmbient X ∈ Submodule.span ℂ
      ({1, X} : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  exact expAmbient_mem_span_one_X_of_sq_eq_scalar
    (tracelessSkewHermitian_two_sq hX)

/-! ### §3.5d. Tracked-Prop bridge for SU(2) determinant claim

The remaining piece for full SU(2) inclusion of `expAmbient X` is
`(expAmbient X).det = 1` for X ∈ tracelessSkewHermitian (Fin 2). This
follows from the structural shipments above (§3.5: det closed form,
§3.5c: exp X ∈ span ℂ {1, X}) once we identify the α, β coefficients
as `cos r` and `sinc r` via cos/sin power-series recognition.

**Pragmatic posture (this ship)**: introduce a smaller tracked predicate
`DetExpZeroOnSu2_SU2` capturing exactly this missing piece, and use it
to unblock the §4 von Neumann construction. The full discharge is
documented as a substantive substrate ship for a subsequent work block.

**Pipeline Invariant #15 posture**: this is a NEW tracked Prop. Per
the user's explicit authorization in the loop prompt (continuation of
the gap #2 discharge arc), we may introduce sub-tracked-Props that
serve as compositional bridges, provided their discharge plan is
documented. The discharge plan is in the docstring of
`DetExpZeroOnSu2_SU2` below: either (a) cos/sin power-series
recognition (Mathlib `Real.cos_eq_tsum` + the §3.5c+3.5 substrate), or
(b) `Matrix.IsHermitian.spectral_theorem` on `Complex.I • X`. -/

/-- **Tracked Prop**: for every X ∈ tracelessSkewHermitian (Fin 2),
the determinant of `expAmbient X` equals 1.

Mathematically a theorem; ship-status is **TRACKED**.

Discharge plan (documented):
* Combine §3.5 `det_alpha_one_plus_beta_smul_tracelessSkewHermitian`
  with §3.5c `expAmbient_mem_span_one_X_of_tracelessSkewHermitian`
  to get `det(expAmbient X) = α² + β² · su2RadiusSq X` for some α, β ∈ ℂ.
* Then identify α = `cos r`, β = `sinc r` (r := √(su2RadiusSq X)) via
  the cos/sin power-series recognition (Mathlib `Real.cos_eq_tsum`,
  `Real.sin_eq_tsum`).
* Conclude α² + β² · r² = cos²(r) + sin²(r) = 1.

Alternative (spectral): apply `Matrix.IsHermitian.spectral_theorem` to
`Complex.I • X` (Hermitian for X skew-Hermitian), decompose
`X = U · diag(-iλ₁, -iλ₂) · U⁻¹` with λ_i ∈ ℝ summing to 0 (from
tracelessness), then `det(exp X) = exp(-i(λ₁+λ₂)) = 1`.

Either path: ~200-400 LoC of substantive Mathlib-PR-quality substrate.
-/
def DetExpZeroOnSu2_SU2 : Prop :=
  ∀ {X : Matrix (Fin 2) (Fin 2) ℂ},
    X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) →
    Matrix.det (SU2MatrixExp.expAmbient X) = 1

/-- Under the tracked Prop, `expAmbient X ∈ specialUnitaryGroup (Fin 2) ℂ`
for X ∈ tracelessSkewHermitian (Fin 2). -/
theorem expAmbient_mem_specialUnitary_of_DetExpZeroOnSu2
    (h_det : DetExpZeroOnSu2_SU2)
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :
    SU2MatrixExp.expAmbient X ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, h_det hX⟩
  exact Matrix.IsSkewHermitian.exp_mem_unitaryGroup hX.1

/-- The 1-parameter subgroup map at the SU(2) subtype level (conditional
on `DetExpZeroOnSu2_SU2`). -/
noncomputable def oneParamSU2Map
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_det : DetExpZeroOnSu2_SU2)
    (t : ℝ) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨oneParamMatrixMap X t,
   expAmbient_mem_specialUnitary_of_DetExpZeroOnSu2 h_det
     (real_smul_tracelessSkewHermitian hX t)⟩

/-- `(oneParamSU2Map hX h_det 0) = 1`. -/
theorem oneParamSU2Map_zero
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_det : DetExpZeroOnSu2_SU2) :
    oneParamSU2Map hX h_det 0 = 1 := by
  apply Subtype.ext
  show oneParamMatrixMap X 0 = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ).val
  rw [oneParamMatrixMap_zero]
  rfl

/-- `oneParamSU2Map hX h_det (s+t) = oneParamSU2Map hX h_det s * oneParamSU2Map hX h_det t`. -/
theorem oneParamSU2Map_add
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_det : DetExpZeroOnSu2_SU2) (s t : ℝ) :
    oneParamSU2Map hX h_det (s + t) =
      oneParamSU2Map hX h_det s * oneParamSU2Map hX h_det t := by
  apply Subtype.ext
  show oneParamMatrixMap X (s + t) =
       oneParamMatrixMap X s * oneParamMatrixMap X t
  exact oneParamMatrixMap_add X s t

/-- `oneParamSU2Map` is continuous in `t`. -/
theorem oneParamSU2Map_continuous
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_det : DetExpZeroOnSu2_SU2) :
    Continuous (oneParamSU2Map hX h_det) := by
  rw [show (oneParamSU2Map hX h_det : ℝ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      = fun t => ⟨oneParamMatrixMap X t,
        expAmbient_mem_specialUnitary_of_DetExpZeroOnSu2 h_det
          (real_smul_tracelessSkewHermitian hX t)⟩ from rfl]
  refine Continuous.subtype_mk ?_ _
  exact oneParamMatrixMap_continuous X

/-! ## §4. Von Neumann sequence extraction

From `AccPt 1 (Filter.principal H)` for a closed subgroup `H ≤ SU(2)`,
we extract a sequence `(h_n : ℕ → ↥SU(2))` with `h_n ∈ H \ {1}` and
`h_n → 1`. This is the entry point for the von Neumann construction:
the sequence supplies the "infinitesimal generators" of `H`.

Substrate used: SU(2) is metric (hence first-countable, hence
Frechet-Urysohn), so `mem_closure_iff_seq_limit` gives sequence
extraction; `AccPt → 1 ∈ closure (H \ {1})` is the structural bridge. -/

/-- For any topological space, `AccPt x (Filter.principal s) → x ∈ closure (s \ {x})`. -/
theorem mem_closure_diff_singleton_of_accPt
    {X : Type*} [TopologicalSpace X] {x : X} {s : Set X}
    (h : AccPt x (Filter.principal s)) :
    x ∈ closure (s \ {x}) := by
  rw [accPt_iff_frequently] at h
  apply Filter.Frequently.mem_closure
  exact h.mono (fun y hy => ⟨hy.2, fun heq => hy.1 heq⟩)

/-- **Von Neumann sequence extraction**: from a closed subgroup `H ≤ SU(2)`
with `AccPt 1 (Filter.principal H)`, extract a sequence `seq : ℕ → ↥SU(2)`
with `seq n ∈ H`, `seq n ≠ 1` for all n, and `seq → 1`.

Composes `accPt_iff_frequently` + `mem_closure_iff_seq_limit` (using
SU(2)'s first-countable / Frechet-Urysohn nature). -/
theorem vonNeumann_extract_sequence
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (hH : AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (Filter.principal (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))) :
    ∃ seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      (∀ n, seq n ∈ H) ∧ (∀ n, seq n ≠ 1) ∧
      Filter.Tendsto seq Filter.atTop
        (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) := by
  have h_closure : (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈
      closure ((H : Set _) \ {1}) :=
    mem_closure_diff_singleton_of_accPt hH
  obtain ⟨seq, h_in, h_tendsto⟩ :=
    (mem_closure_iff_seq_limit (s := (H : Set _) \ {1})
      (a := (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))).mp h_closure
  refine ⟨seq, ?_, ?_, h_tendsto⟩
  · intro n
    exact (h_in n).1
  · intro n hne
    have : seq n ∈ ({1} : Set _) := by rw [Set.mem_singleton_iff]; exact hne
    exact (h_in n).2 this

/-- **Specialization to `H_Fib`**: extract a sequence in `H_Fib \ {1}`
tending to 1, using the shipped `H_Fib_accPt_one_unconditional`. -/
theorem H_Fib_vonNeumann_sequence :
    ∃ seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      (∀ n, seq n ∈ H_Fib) ∧ (∀ n, seq n ≠ 1) ∧
      Filter.Tendsto seq Filter.atTop
        (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) :=
  vonNeumann_extract_sequence H_Fib H_Fib_accPt_one_unconditional

/-! ### §4.b. Lifting the sequence to matrix space + matrix log

From `seq → 1` in `↥SU(2)`, derive `seq.val → 1` in `Matrix _ _ ℂ` via
continuity of `Subtype.val`, then use the IFT target nbhd
(`expAmbientPartialHomeo_target_mem_nhds_one`) to show eventually
`seq n.val ∈ target` so that `su2Log (seq n).val` is meaningful.

Then use continuity of `su2Log` on `target` + `su2Log 1 = 0` to derive
`su2Log (seq n).val → 0` in matrix space. -/

/-- **Sequence.val tendsto identity**: if `seq → 1` in SU(2), then
`(seq n).val → (1 : Matrix _ _ ℂ)`. -/
theorem subtype_val_tendsto_one_of_tendsto
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))) :
    Filter.Tendsto (fun n => ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop (nhds (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have h_val_one : ((1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val :
      Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl
  rw [← h_val_one]
  exact continuous_subtype_val.continuousAt.tendsto.comp h_seq

/-- **Eventually in target**: from `seq.val → 1`, eventually
`seq n.val ∈ expAmbientPartialHomeo.target`. -/
theorem eventually_val_mem_target
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))) :
    ∀ᶠ n in Filter.atTop,
      ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ∈ expAmbientPartialHomeo.target := by
  have h_val_tendsto := subtype_val_tendsto_one_of_tendsto h_seq
  exact h_val_tendsto.eventually expAmbientPartialHomeo_target_mem_nhds_one

/-- **`su2Log` of sequence converges to 0** in `Matrix _ _ ℂ`. From
`seq.val → 1` and `seq.val` eventually in `target`, use continuity of
`su2Log` on `target` + `su2Log 1 = 0`. -/
theorem su2Log_seq_tendsto_zero
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))) :
    Filter.Tendsto (fun n => su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have h_val_tendsto := subtype_val_tendsto_one_of_tendsto h_seq
  have h_su2Log_cont :=
    su2Log_continuousOn.continuousAt expAmbientPartialHomeo_target_mem_nhds_one
  have := h_su2Log_cont.tendsto.comp h_val_tendsto
  rw [su2Log_one] at this
  exact this

/-- **Combined von Neumann sequence + matrix-log lift**: for closed H ⊆ SU(2)
with `AccPt 1 (Filter.principal H)`, there exist sequences
`seq : ℕ → ↥SU(2)` with `seq n ∈ H ∧ seq n ≠ 1 ∧ seq → 1` AND
`Y_n : ℕ → Matrix _ _ ℂ` with `Y_n → 0` and (eventually) `expAmbient Y_n =
(seq n).val`. -/
theorem vonNeumann_sequence_with_log
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (hH : AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (Filter.principal (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))) :
    ∃ (seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      (∀ n, seq n ∈ H) ∧ (∀ n, seq n ≠ 1) ∧
      Filter.Tendsto seq Filter.atTop
        (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) ∧
      Filter.Tendsto (fun n => su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
        Filter.atTop (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  obtain ⟨seq, h_mem, h_ne, h_tendsto⟩ := vonNeumann_extract_sequence H hH
  exact ⟨seq, h_mem, h_ne, h_tendsto, su2Log_seq_tendsto_zero h_tendsto⟩

/-! ### §4.c. Normalization toward the unit sphere of su(2)

From `su2Log_seq_tendsto_zero` (§4.b), the matrix-log sequence `Y_n →
0`. To extract a unit-norm direction via BW, we first show `Y_n ≠ 0`
eventually (so the normalization `Y_n / ‖Y_n‖` is well-defined), then
construct the unit-sphere sequence.

The `Y_n ≠ 0` argument uses **local-inverse uniqueness** of `su2Log`:
if `su2Log h = 0` for h in `target`, then `expAmbient (su2Log h) = h`
gives `h = expAmbient 0 = 1`. Contrapositive: `h ≠ 1 ∧ h ∈ target ⟹
su2Log h ≠ 0`.

For the seq from §4.a, `seq n ≠ 1` ⟹ `(seq n).val ≠ 1` (subtype
injectivity), combined with `(seq n).val ∈ target` eventually, yields
`Y_n ≠ 0` eventually. -/

/-- **Local injectivity of `su2Log` at 1**: for `h ∈ target`, if
`su2Log h = 0`, then `h = 1`. -/
theorem h_eq_one_of_su2Log_eq_zero
    {h : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : h ∈ expAmbientPartialHomeo.target)
    (h_log : su2Log h = 0) : h = 1 := by
  have h_exp : SU2MatrixExp.expAmbient (su2Log h) = h := expAmbient_su2Log hh
  rw [h_log] at h_exp
  rw [← h_exp]
  exact SU2MatrixExp.expAmbient_zero

/-- **Contrapositive**: for `h ∈ target` with `h ≠ 1`, `su2Log h ≠ 0`. -/
theorem su2Log_ne_zero_of_ne_one
    {h : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : h ∈ expAmbientPartialHomeo.target)
    (h_ne : h ≠ 1) : su2Log h ≠ 0 :=
  fun h_log => h_ne (h_eq_one_of_su2Log_eq_zero hh h_log)

/-- **Subtype value distinct from identity**: for `seq n ≠ 1` in SU(2),
`(seq n).val ≠ 1` as matrices. -/
theorem subtype_val_ne_one_of_ne_one
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)} {n : ℕ}
    (h_ne : seq n ≠ 1) :
    ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 1 := by
  intro h_eq
  apply h_ne
  apply Subtype.ext
  exact h_eq

/-- **Eventually `Y_n ≠ 0`**: from `seq → 1` + `seq n ≠ 1`, the matrix-log
sequence has nonzero entries (eventually). -/
theorem eventually_su2Log_seq_ne_zero
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (h_ne : ∀ n, seq n ≠ 1)
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))) :
    ∀ᶠ n in Filter.atTop,
      su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
  have h_target_ev := eventually_val_mem_target h_seq
  filter_upwards [h_target_ev] with n hn
  exact su2Log_ne_zero_of_ne_one hn (subtype_val_ne_one_of_ne_one (h_ne n))

/-- **Unit-sphere matrix sequence**: normalized matrix-log sequence
(defined for any n; gives 0 when `Y_n = 0`). For n in the
"eventually nonzero" set, `‖X_n‖ = 1`. -/
noncomputable def vonNeumannUnitMatrixSeq
    (seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let Y := su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ)
  if h_ne : Y = 0 then 0 else (‖Y‖⁻¹ : ℂ) • Y

/-- The unit-sphere matrix sequence has norm 1 when `Y_n ≠ 0`. -/
theorem vonNeumannUnitMatrixSeq_norm_eq_one
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)} {n : ℕ}
    (h_ne : su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0) :
    ‖vonNeumannUnitMatrixSeq seq n‖ = 1 := by
  unfold vonNeumannUnitMatrixSeq
  simp only [dif_neg h_ne]
  rw [norm_smul]
  have h_norm_ne : ‖su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact h_ne
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  field_simp

/-! ### §4.d. Bolzano-Weierstrass extraction

The unit-sphere matrix sequence lives in the closed unit ball of
`Matrix (Fin 2) (Fin 2) ℂ`, which is a finite-dimensional ℝ-normed
space hence a `ProperSpace`. The closed ball is therefore compact, and
the sequence has a convergent subsequence by Bolzano-Weierstrass.

The eventually-nonzero result (§4.c) gives us "frequently in the unit
sphere," and `IsCompact.tendsto_subseq'` extracts the subsequence. -/

/-- `Matrix (Fin 2) (Fin 2) ℂ` is finite-dimensional over ℝ. (4 complex
entries × 2 real components each = 8-dimensional ℝ-vector space.) -/
instance : FiniteDimensional ℝ (Matrix (Fin 2) (Fin 2) ℂ) := inferInstance

/-- The closed unit ball in `Matrix (Fin 2) (Fin 2) ℂ` is compact, via
`ProperSpace.isCompact_closedBall` (finite-dim ⟹ proper). -/
theorem isCompact_closedBall_one :
    IsCompact (Metric.closedBall (0 : Matrix (Fin 2) (Fin 2) ℂ) 1) :=
  ProperSpace.isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) ℂ) 1

/-- The unit-sphere matrix sequence is eventually in `closedBall 0 1`
(in fact has norm exactly 1 when `Y_n ≠ 0`, and norm 0 otherwise). -/
theorem vonNeumannUnitMatrixSeq_mem_closedBall_one
    (seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (n : ℕ) :
    vonNeumannUnitMatrixSeq seq n ∈
      Metric.closedBall (0 : Matrix (Fin 2) (Fin 2) ℂ) 1 := by
  by_cases h : su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) = 0
  · -- Y_n = 0 → vonNeumannUnitMatrixSeq = 0, which has norm 0 ≤ 1.
    have : vonNeumannUnitMatrixSeq seq n = 0 := by
      unfold vonNeumannUnitMatrixSeq
      simp [h]
    simp [this, Metric.mem_closedBall]
  · -- Y_n ≠ 0 → norm = 1.
    rw [Metric.mem_closedBall, dist_zero_right]
    apply le_of_eq
    exact vonNeumannUnitMatrixSeq_norm_eq_one h

/-- **BW EXTRACTION**: from a sequence with eventually-nonzero matrix-log
values, extract a subsequence converging to some X ∈ closedBall 0 1.
Combined with the eventually-norm-1 property, the limit has norm 1. -/
theorem vonNeumann_BW_extract
    (seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ∃ X ∈ Metric.closedBall (0 : Matrix (Fin 2) (Fin 2) ℂ) 1,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto (fun k => vonNeumannUnitMatrixSeq seq (φ k))
          Filter.atTop (nhds X) := by
  exact isCompact_closedBall_one.tendsto_subseq
    (vonNeumannUnitMatrixSeq_mem_closedBall_one seq)

/-- **Limit has norm 1**: under the eventually-nonzero hypothesis, the
BW-extracted limit X has `‖X‖ = 1`.

The subsequence stays in the unit sphere (norm = 1) eventually
(frequently is enough), so the limit (in the closed unit ball) has
norm 1 by continuity of the norm. -/
theorem vonNeumann_BW_limit_norm_eq_one
    (seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0)
    {X : Matrix (Fin 2) (Fin 2) ℂ} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (h_tendsto : Filter.Tendsto
      (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X)) :
    ‖X‖ = 1 := by
  -- The norms of the subsequence converge to ‖X‖.
  have h_norm_tendsto :
      Filter.Tendsto (fun k => ‖vonNeumannUnitMatrixSeq seq (φ k)‖)
        Filter.atTop (nhds ‖X‖) :=
    (continuous_norm.tendsto X).comp h_tendsto
  -- Eventually the subsequence has norm 1.
  have h_subseq_ne : ∀ᶠ k in Filter.atTop,
      su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 :=
    hφ.tendsto_atTop.eventually h_ev_ne
  have h_subseq_norm_one : ∀ᶠ k in Filter.atTop,
      ‖vonNeumannUnitMatrixSeq seq (φ k)‖ = 1 := by
    filter_upwards [h_subseq_ne] with k hk
    exact vonNeumannUnitMatrixSeq_norm_eq_one hk
  -- Apply uniqueness of limits.
  have h_const_tendsto :
      Filter.Tendsto (fun k => ‖vonNeumannUnitMatrixSeq seq (φ k)‖)
        Filter.atTop (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [h_subseq_norm_one] with k hk
    rw [hk]
  exact tendsto_nhds_unique h_norm_tendsto h_const_tendsto

/-! ### §4.e. Integer-rounding convergence

For any `t : ℝ` and a sequence `r_k : ℕ → ℝ` with `r_k → 0` and `r_k > 0`,
the integer sequence `m_k := ⌊t / r_k⌋ : ℤ` satisfies
`(m_k : ℝ) · r_k → t`. This is the algebraic key for the von Neumann
"integer-rounding" step: scaling by a near-integer multiple of `r_k`
approximates `t`.

For our use case: `r_k := ‖su2Log (seq (φ k)).val‖` (eventually nonzero
positive reals, → 0). Then `m_k · Y_k = (m_k · r_k) · X_k → t · X` where
`X_k := Y_k / r_k` and `X_k → X`. -/

/-- **Floor-times-scale converges**: for `r_k → 0` with `r_k > 0`
eventually, the sequence `(⌊t / r_k⌋ : ℝ) · r_k → t`. -/
theorem floor_times_scale_tendsto
    {r : ℕ → ℝ} (h_pos : ∀ᶠ k in Filter.atTop, 0 < r k)
    (h_tendsto : Filter.Tendsto r Filter.atTop (nhds 0))
    (t : ℝ) :
    Filter.Tendsto (fun k => ((⌊t / r k⌋ : ℤ) : ℝ) * r k)
      Filter.atTop (nhds t) := by
  -- |⌊x⌋ - x| < 1, so |⌊t/r⌋ · r - t| = |(⌊t/r⌋ - t/r) · r| ≤ 1 · |r| → 0.
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Eventually |r k| < ε.
  have h_lt : ∀ᶠ k in Filter.atTop, |r k| < ε := by
    rw [Metric.tendsto_nhds] at h_tendsto
    have := h_tendsto ε hε
    filter_upwards [this] with k hk
    rwa [Real.dist_eq, sub_zero] at hk
  filter_upwards [h_lt, h_pos] with k hk_lt hk_pos
  rw [Real.dist_eq]
  -- |⌊t/r_k⌋ · r_k - t| ≤ |r_k|
  have h_floor_bound : |((⌊t / r k⌋ : ℤ) : ℝ) - t / r k| < 1 := by
    have h1 := Int.floor_le (t / r k)
    have h2 := Int.lt_floor_add_one (t / r k)
    rw [abs_lt]
    constructor
    · linarith
    · linarith
  have h_rk_ne : r k ≠ 0 := ne_of_gt hk_pos
  calc |((⌊t / r k⌋ : ℤ) : ℝ) * r k - t|
      = |(((⌊t / r k⌋ : ℤ) : ℝ) - t / r k) * r k| := by
        congr 1
        field_simp
    _ = |((⌊t / r k⌋ : ℤ) : ℝ) - t / r k| * |r k| := abs_mul _ _
    _ ≤ 1 * |r k| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact le_of_lt h_floor_bound
    _ = |r k| := one_mul _
    _ < ε := hk_lt

/-- **Approximation lemma**: for the BW subsequence, `(m_k : ℝ) · ‖Y_k‖
→ t` where `m_k := ⌊t / ‖Y_k‖⌋`. -/
theorem vonNeumann_floor_scale_tendsto
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)))
    (t : ℝ) :
    Filter.Tendsto
      (fun k => ((⌊t / ‖su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)‖⌋
                  : ℤ) : ℝ) *
                ‖su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)‖)
      Filter.atTop (nhds t) := by
  apply floor_times_scale_tendsto
  · -- Eventually ‖Y_{n_k}‖ > 0 (from eventually-ne-zero + norm_pos_iff).
    have h_subseq_ne :=
      hφ.tendsto_atTop.eventually h_ev_ne
    filter_upwards [h_subseq_ne] with k hk
    exact norm_pos_iff.mpr hk
  · -- ‖Y_{n_k}‖ → 0 (continuous norm + subseq tendsto).
    have h_subseq_tendsto :=
      h_log_tendsto.comp hφ.tendsto_atTop
    have := (continuous_norm.tendsto (0 : Matrix (Fin 2) (Fin 2) ℂ)).comp
      h_subseq_tendsto
    simp [norm_zero] at this
    exact this

/-! ### §4.f. Scalar-vector convergence `m_k • Y_{n_k} → t • X`

Combine §4.d (the BW limit `X_k := Y_{n_k} / ‖Y_{n_k}‖ → X`) with §4.e
(`m_k · ‖Y_{n_k}‖ → t`) via `Filter.Tendsto.smul` (real-scalar smul on
the matrix ℝ-module) to get `(m_k · ‖Y_{n_k}‖) • X_k → t • X`. The
algebraic identity `(m_k · ‖Y_{n_k}‖) • X_k = (m_k : ℝ) • Y_{n_k}`
(when `Y_{n_k} ≠ 0`) rewrites this into the form needed for
`exp_smul` / `exp_zsmul`. -/

/-! #### Real-scalar continuity infrastructure

The local `Matrix.linftyOpNormedAlgebra` is a ℂ-normed-algebra structure
and provides `ContinuousSMul ℂ (Matrix (Fin 2) (Fin 2) ℂ)`, but does
*not* synthesize `ContinuousSMul ℝ` automatically (Mathlib does not
provide a generic `ContinuousSMul ℂ → ContinuousSMul ℝ` derivation;
see also `Complex.continuousSMul` style instances which are explicit).

We provide the explicit ℝ-instance below via composition of:
- `Complex.continuous_ofReal : Continuous (↑ : ℝ → ℂ)`,
- the existing `ContinuousSMul ℂ (Matrix (Fin 2) (Fin 2) ℂ)`,
- the entry-wise identity `(r : ℝ) • M = (r : ℂ) • M`
  (from `Complex.real_smul : (r : ℝ) • (z : ℂ) = ↑r * z`).

This is a *small Mathlib-upstream-PR-quality contribution*: an
explicit `ContinuousSMul ℝ` instance on `Matrix _ _ ℂ` available
locally via the `linftyOp` topology. -/

/-- Entry-wise: real-scalar smul on a complex matrix equals coerced
complex-scalar smul. Used to reduce ℝ-continuity to ℂ-continuity. -/
lemma real_smul_matrix2C_eq_complex_smul
    (r : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (r : ℝ) • M = ((r : ℂ) • M) := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- **Explicit `ContinuousSMul ℝ` instance on `Matrix (Fin 2) (Fin 2) ℂ`**:
the real-scalar smul `(r, M) ↦ r • M` is continuous as a map
`ℝ × Matrix _ _ ℂ → Matrix _ _ ℂ`.

Proof: via entry-wise identity `(r : ℝ) • M = (r : ℂ) • M` plus
continuity of `Complex.ofReal` and of `ℂ`-smul on the ℂ-algebra
`Matrix _ _ ℂ`. -/
noncomputable instance continuousSMul_real_Matrix2C :
    ContinuousSMul ℝ (Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor
  -- Rewrite the smul as ℂ-smul via the entry-wise identity.
  have h_eq : (fun p : ℝ × Matrix (Fin 2) (Fin 2) ℂ => p.1 • p.2) =
              (fun p : ℝ × Matrix (Fin 2) (Fin 2) ℂ => (p.1 : ℂ) • p.2) := by
    funext p
    exact real_smul_matrix2C_eq_complex_smul p.1 p.2
  rw [h_eq]
  -- Now compose: (r, M) ↦ ((r : ℂ), M) ↦ (r : ℂ) • M.
  exact continuous_smul.comp
    ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd)

/-! #### §4.f main theorem

**Scalar-vector convergence**: combining §4.d (BW unit-matrix limit
`X_k → X`) with §4.e (floor-times-scale `(m_k · ‖Y_{n_k}‖) → t`) via
`Filter.Tendsto.smul` (using the just-defined `ContinuousSMul ℝ`
instance) gives `(m_k · ‖Y_{n_k}‖) • X_k → t • X`. -/

/-- **§4.f. Scalar-vector convergence (ℝ-smul form)**: under the §4
hypothesis pack — strictly monotone `φ`, eventually-nonzero matrix-log
sequence, log-tendsto-zero, BW-extracted unit-matrix limit `X`, and a
real `t` — the scaled-by-floor-times-norm subsequence converges to
`t • X` in `Matrix (Fin 2) (Fin 2) ℂ`.

This is the bridge that converts §4.d's BW limit and §4.e's
integer-rounding convergence into the form needed for §4.g's
`expAmbient` composition (`(m_k : ℤ) • Y_{n_k} → t • X`). -/
theorem vonNeumann_scaled_unit_tendsto_real
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)))
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (h_unit_tendsto : Filter.Tendsto
      (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        (((⌊t / ‖su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)‖⌋ : ℤ) : ℝ) *
          ‖su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)‖) •
          vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop
      (nhds (t • X)) :=
  (vonNeumann_floor_scale_tendsto hφ h_ev_ne h_log_tendsto t).smul h_unit_tendsto

/-! ### §4.g. Reduction of scaled-unit to real-scalar smul + `expAmbient` composition

The §4.f conclusion has the form
  `(m_k_real * r_k) • ((r_k⁻¹ : ℂ) • Y_{n_k}) → t • X`,
where `r_k = ‖Y_{n_k}‖`. The algebraic identity
  `(c * r) • ((r⁻¹ : ℂ) • Y) = c • Y`  (when `r ≠ 0`)
reduces the LHS to `(m_k_real : ℝ) • Y_{n_k}`, which then becomes
the ℤ-smul form `(m_k : ℤ) • Y_{n_k}` via `Int.cast_smul_eq_zsmul`.
Composition with `expAmbient` continuity + `Matrix.exp_zsmul` finally
yields
  `expAmbient (m_k • Y_{n_k}) = (expAmbient Y_{n_k}) ^ m_k → expAmbient (t • X)`,
the form needed for the von Neumann SU(2)-inclusion step. -/

/-- **Algebraic identity (real-scalar form)**: for `Y ≠ 0` and any
real `c`, `(c * ‖Y‖) • ((‖Y‖⁻¹ : ℂ) • Y) = c • Y` in `Matrix (Fin 2) (Fin 2) ℂ`.

Proof: convert the inner ℂ-smul to ℝ-smul via `Complex.real_smul`, then
collapse the two ℝ-smuls via `smul_smul` and `field_simp`. -/
lemma scaled_unit_eq_real_smul
    {Y : Matrix (Fin 2) (Fin 2) ℂ} (hY : Y ≠ 0) (c : ℝ) :
    (c * ‖Y‖) • ((‖Y‖⁻¹ : ℂ) • Y) = c • Y := by
  have h_norm_ne : (‖Y‖ : ℝ) ≠ 0 := by
    rw [Ne, norm_eq_zero]; exact hY
  have h_inner : ((‖Y‖⁻¹ : ℂ) • Y) = ((‖Y‖⁻¹ : ℝ) • Y) := by
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [h_inner, smul_smul]
  congr 1
  field_simp

/-- **§4.g.1. Real-scalar smul convergence**: the §4.f result rewrites
to `(m_k_real : ℝ) • Y_{n_k} → t • X` where `m_k_real := (⌊t/r_k⌋ : ℤ) : ℝ`.

Combines §4.f with `scaled_unit_eq_real_smul`, requiring the
eventually-nonzero hypothesis to apply the algebraic identity. -/
theorem vonNeumann_intReal_smul_tendsto
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)))
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (h_unit_tendsto : Filter.Tendsto
      (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        ((⌊t / ‖su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)‖⌋ : ℤ) : ℝ) •
          su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop
      (nhds (t • X)) := by
  -- Start from the §4.f tendsto.
  have h_f := vonNeumann_scaled_unit_tendsto_real
                hφ h_ev_ne h_log_tendsto h_unit_tendsto t
  -- Eventually rewrite each term via the algebraic identity.
  have h_ev_ne_sub : ∀ᶠ k in Filter.atTop,
      su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 :=
    hφ.tendsto_atTop.eventually h_ev_ne
  refine Filter.Tendsto.congr' ?_ h_f
  filter_upwards [h_ev_ne_sub] with k hk
  -- Identity: (c * r) • ((r⁻¹ : ℂ) • Y) = c • Y  with Y := Y_{n_k}, c := m_k_real
  -- Unfold the unit-matrix-seq via dif_neg hk.
  unfold vonNeumannUnitMatrixSeq
  simp only [dif_neg hk]
  exact scaled_unit_eq_real_smul hk _

/-- **§4.g.2. ℤ-smul convergence**: trivial cast from §4.g.1 via
`Int.cast_smul_eq_zsmul`. -/
theorem vonNeumann_zsmul_seq_tendsto
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)))
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (h_unit_tendsto : Filter.Tendsto
      (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        (⌊t / ‖su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)‖⌋ : ℤ) •
          su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop
      (nhds (t • X)) := by
  have h_real :=
    vonNeumann_intReal_smul_tendsto hφ h_ev_ne h_log_tendsto h_unit_tendsto t
  refine Filter.Tendsto.congr ?_ h_real
  intro k
  exact Int.cast_smul_eq_zsmul ℝ _ _

/-- **§4.g.3. `expAmbient` convergence**: applies `expAmbient` continuity
to the ℤ-smul tendsto. -/
theorem vonNeumann_exp_zsmul_seq_tendsto
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)))
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (h_unit_tendsto : Filter.Tendsto
      (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        SU2MatrixExp.expAmbient
          ((⌊t / ‖su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)‖⌋ : ℤ) •
            su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)))
      Filter.atTop
      (nhds (SU2MatrixExp.expAmbient (t • X))) := by
  have h_zsmul :=
    vonNeumann_zsmul_seq_tendsto hφ h_ev_ne h_log_tendsto h_unit_tendsto t
  have h_cont :
      Filter.Tendsto (fun M : Matrix (Fin 2) (Fin 2) ℂ => SU2MatrixExp.expAmbient M)
        (nhds (t • X)) (nhds (SU2MatrixExp.expAmbient (t • X))) := by
    have : Continuous (SU2MatrixExp.expAmbient :
        Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) := by
      unfold SU2MatrixExp.expAmbient
      exact NormedSpace.exp_continuous
    exact this.tendsto _
  exact h_cont.comp h_zsmul

/-- **§4.g.4. Integer-power form**: rewrite the §4.g.3 limit using
`Matrix.exp_zsmul` to express it as `(expAmbient Y_{n_k}) ^ m_k`.

This is the form consumed by the next step: combined with
`expAmbient (su2Log h) = h` (from §1), it identifies the limit
sequence as `h_{n_k} ^ m_k`, a sequence of integer powers in SU(2). -/
theorem vonNeumann_exp_pow_seq_tendsto
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)))
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (h_unit_tendsto : Filter.Tendsto
      (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        SU2MatrixExp.expAmbient (su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)) ^
          (⌊t / ‖su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)‖⌋ : ℤ))
      Filter.atTop
      (nhds (SU2MatrixExp.expAmbient (t • X))) := by
  have h_exp :=
    vonNeumann_exp_zsmul_seq_tendsto hφ h_ev_ne h_log_tendsto h_unit_tendsto t
  refine Filter.Tendsto.congr ?_ h_exp
  intro k
  -- expAmbient ((m : ℤ) • Y) = expAmbient Y ^ m  via Matrix.exp_zsmul
  unfold SU2MatrixExp.expAmbient
  exact Matrix.exp_zsmul _ _

/-! ### §4.h. SU(2)-matrix-level convergence (matrix-pow form)

The §4.g chain concludes with `(expAmbient Y_{n_k}) ^ m_k → expAmbient (t • X)`
in `Matrix (Fin 2) (Fin 2) ℂ`. We refine this using §1's
`expAmbient_su2Log` + §4.b's `eventually_val_mem_target` to identify
the LHS as the matrix integer-power of `(seq (φ k)).val`, the SU(2)
element underlying our sequence. The resulting statement is:

  `(seq (φ k)).val ^ m_k → expAmbient (t • X)` in `Matrix (Fin 2) (Fin 2) ℂ`.

This is the **matrix-level form of the final convergence**. The next
step (§4.i) lifts this through the SU(2) subtype and uses H closed to
conclude `expAmbient (t • X) ∈ (range of H in Matrix _ _ ℂ)`, which
combined with §3.5d's `DetExpZeroOnSu2_SU2` tracked-Prop will give the
SU(2)-subtype inclusion needed for `OneParamSubgroupInSU2 H`. -/

/-- **§4.h.1. Matrix-level rewrite (eventually)**: under `seq → 1`,
eventually `expAmbient (su2Log (seq n).val) = (seq n).val`.

From §4.b's `eventually_val_mem_target` (gives eventually-in-target)
+ §1's `expAmbient_su2Log` (right-inverse on target). -/
theorem expAmbient_su2Log_seq_eventually
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))) :
    ∀ᶠ n in Filter.atTop,
      SU2MatrixExp.expAmbient (su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
        = ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) := by
  filter_upwards [eventually_val_mem_target h_seq] with n hn
  exact expAmbient_su2Log hn

/-- **§4.h.2. SU(2)-matrix-level convergence**: under the §4 hypothesis
pack — including `seq → 1` (needed for matrix-log eventually-equality)
— the integer-power sequence of the underlying SU(2) matrices converges
to `expAmbient (t • X)` in `Matrix (Fin 2) (Fin 2) ℂ`.

This is the natural pre-step before lifting through the SU(2) subtype
in §4.i (which needs §3.5d's `DetExpZeroOnSu2_SU2` tracked Prop). -/
theorem vonNeumann_su2Mat_pow_seq_tendsto
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))))
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)))
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (h_unit_tendsto : Filter.Tendsto
      (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ) ^
          (⌊t / ‖su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)‖⌋ : ℤ))
      Filter.atTop
      (nhds (SU2MatrixExp.expAmbient (t • X))) := by
  -- §4.g.4 conclusion: (expAmbient Y_{n_k})^m_k → expAmbient (t • X)
  have h_g4 :=
    vonNeumann_exp_pow_seq_tendsto hφ h_ev_ne h_log_tendsto h_unit_tendsto t
  -- §4.h.1 specialized to subsequence
  have h_ev_subseq := hφ.tendsto_atTop.eventually
    (expAmbient_su2Log_seq_eventually h_seq)
  -- Apply rewrite via Tendsto.congr'.
  refine Filter.Tendsto.congr' ?_ h_g4
  filter_upwards [h_ev_subseq] with k hk
  rw [hk]

/-! ### §4.i. SU(2)-subtype zpow lift to matrix-zpow

To lift the §4.h.2 matrix-level convergence
`(seq (φ k)).val ^ m_k → expAmbient (t • X)` to the SU(2)-subtype level,
we need the algebraic identity:

  `((g ^ m).val : Matrix _ _ ℂ) = ((g.val : Matrix _ _ ℂ)) ^ m`

for `g : ↥(specialUnitaryGroup n α)` and `m : ℤ`. This is *not* a direct
corollary of `SubmonoidClass.coe_pow` (which gives the ℕ-case only),
because `Matrix _ _ ℂ` is not a Group (singular matrices), so
`Subgroup.coe_zpow` does not apply. The proof requires:
- Case `m = ofNat k` (ℕ): direct `SubmonoidClass.coe_pow`.
- Case `m = negSucc k` (negative integers): unfolds via `zpow_negSucc` to
  `((h^(k+1))⁻¹).val`, where the subtype inverse is `star` (by
  `Matrix.instInvSubtypeMemSubmonoidSpecialUnitaryGroup`). For unitary
  matrices, `star M = M⁻¹` (matrix inverse) follows from
  `M * star M = 1` + `Matrix.inv_eq_right_inv`.

This sub-lemma is a clean Mathlib-upstream-PR candidate. -/

/-- **§4.i.1. SU(2)-subtype zpow lifts to matrix-zpow**: for any
`g : ↥(specialUnitaryGroup n α)` over a normed-commutative-ring α and
any `m : ℤ`, `((g ^ m).val : Matrix _ _ α) = (g.val : Matrix _ _ α) ^ m`. -/
theorem specialUnitaryGroup_coe_zpow
    (g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (m : ℤ) :
    ((g ^ m).val : Matrix (Fin 2) (Fin 2) ℂ) =
      (g.val : Matrix (Fin 2) (Fin 2) ℂ) ^ m := by
  cases m with
  | ofNat k =>
    show ((g ^ (k : ℤ)).val : Matrix (Fin 2) (Fin 2) ℂ) = g.val ^ (k : ℤ)
    rw [zpow_natCast, zpow_natCast]
    exact SubmonoidClass.coe_pow _ _
  | negSucc k =>
    show ((g ^ (Int.negSucc k)).val : Matrix (Fin 2) (Fin 2) ℂ) =
         g.val ^ (Int.negSucc k)
    rw [zpow_negSucc, zpow_negSucc]
    -- (g^(k+1))⁻¹.val = star ((g^(k+1)).val)  [subtype-Inv via star]
    have h_inv_eq_star :
        ((g ^ (k+1))⁻¹).val = star ((g ^ (k+1)).val) := rfl
    rw [h_inv_eq_star]
    -- (g^(k+1)).val = g.val ^ (k+1)  [ℕ-pow lift]
    rw [SubmonoidClass.coe_pow]
    -- star (g.val ^ (k+1)) = (g.val ^ (k+1))⁻¹  [unitary + Matrix.inv_eq_right_inv]
    -- g^(k+1) is in specialUnitaryGroup since that's a Submonoid.
    have h_pow_unitary : (g ^ (k+1)).val ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      (Matrix.mem_specialUnitaryGroup_iff.mp (g ^ (k+1)).property).1
    have h_pow_val_eq : (g ^ (k+1)).val = g.val ^ (k+1) :=
      SubmonoidClass.coe_pow _ _
    have h_mul_star : ((g.val ^ (k+1)) * star (g.val ^ (k+1)) :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [← h_pow_val_eq]
      exact Matrix.mem_unitaryGroup_iff.mp h_pow_unitary
    exact (Matrix.inv_eq_right_inv h_mul_star).symm

/-! ### §4.i.2. Topological closure properties

`Matrix.specialUnitaryGroup (Fin 2) ℂ`, viewed as a subset of
`Matrix (Fin 2) (Fin 2) ℂ`, is closed (as the intersection of the
unitary group with the determinant-1 locus). The image of `H` under
the subtype embedding `Subtype.val : ↥SU(2) → Matrix _ _ ℂ` is also
closed in `Matrix _ _ ℂ` (image of closed set under closed embedding).
-/

/-- **`Matrix.specialUnitaryGroup (Fin 2) ℂ` is closed in
`Matrix (Fin 2) (Fin 2) ℂ`** (with the linftyOp topology). Direct
construction: `specialUnitaryGroup = unitaryGroup ∩ det⁻¹{1}`, both
closed (unitaryGroup via `isClosed_unitary`; det⁻¹{1} via
continuity of `Matrix.det`). -/
theorem specialUnitaryGroup_isClosed :
    IsClosed ((Matrix.specialUnitaryGroup (Fin 2) ℂ :
        Set (Matrix (Fin 2) (Fin 2) ℂ))) := by
  rw [show ((Matrix.specialUnitaryGroup (Fin 2) ℂ :
        Set (Matrix (Fin 2) (Fin 2) ℂ))) =
      (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) ∩
        {M | M.det = 1} from ?_]
  · exact IsClosed.inter isClosed_unitary
      (isClosed_eq (Continuous.matrix_det continuous_id) continuous_const)
  · ext M
    simp [Matrix.mem_specialUnitaryGroup_iff]

/-- **H_mat (image of H in `Matrix _ _ ℂ`) is closed** when `H` is
closed in the SU(2) subspace topology. Combines `specialUnitaryGroup_isClosed`
+ `IsClosed.isClosedEmbedding_subtypeVal` (Subtype.val from a closed
subset is a closed embedding) + `Topology.IsClosedEmbedding.isClosed_iff_image_isClosed`. -/
theorem H_mat_isClosed
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (hH_closed : IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) :
    IsClosed ((fun h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) => h.val) ''
              (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) := by
  exact (specialUnitaryGroup_isClosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed).mp
        hH_closed

/-! ### §4.i.3. Sequence-in-H_mat membership

For the §4.h.2 sequence `f k := (seq (φ k)).val ^ m_k` to identify the
limit as in H_mat, we need each `f k ∈ H_mat`. Combining:
- `seq (φ k) ∈ H` (from the §4.b hypothesis `∀ n, seq n ∈ H` lifted to subseq)
- `H` is a Subgroup → closed under zpow → `(seq (φ k)) ^ m_k ∈ H`
- §4.i.1 → `(((seq (φ k))^m_k).val : Matrix _ _ ℂ) = (seq (φ k)).val ^ m_k`
- Hence the matrix-power lies in H_mat. -/

/-- **§4.i.3. Matrix-pow seq is in H_mat (eventually trivially: for all k)**. -/
theorem vonNeumann_mat_pow_mem_H_mat
    {H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (h_mem : ∀ n, seq n ∈ H)
    (φ : ℕ → ℕ) (t : ℝ) (k : ℕ) :
    ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ) ^
        (⌊t / ‖su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)‖⌋ : ℤ) ∈
      (fun h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) => h.val) ''
        (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  -- The element (seq (φ k))^m_k in ↥SU(2) is in H.
  set m : ℤ := ⌊t / ‖su2Log ((seq (φ k)).val : Matrix (Fin 2) (Fin 2) ℂ)‖⌋
  refine ⟨(seq (φ k)) ^ m, ?_, ?_⟩
  · -- (seq (φ k)) ^ m ∈ H
    exact H.zpow_mem (h_mem (φ k)) m
  · -- ((seq (φ k))^m).val = (seq (φ k)).val ^ m
    exact specialUnitaryGroup_coe_zpow _ _

/-! ### §4.i.4. Limit is in H_mat

Combining §4.h.2 (matrix-pow seq tendsto), §4.i.2 (H_mat closed), and
§4.i.3 (sequence in H_mat) via `IsClosed.mem_of_tendsto`. -/

/-- **§4.i.4. `expAmbient (t • X)` is in H_mat**: the limit of the
matrix-pow sequence is in the image of H in `Matrix _ _ ℂ`. -/
theorem vonNeumann_expAmbient_mem_H_mat
    {H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (hH_closed : IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (h_mem : ∀ n, seq n ∈ H)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))))
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)))
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (h_unit_tendsto : Filter.Tendsto
      (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    SU2MatrixExp.expAmbient (t • X) ∈
      (fun h : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) => h.val) ''
        (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  have h_pow_tendsto := vonNeumann_su2Mat_pow_seq_tendsto
    hφ h_seq h_ev_ne h_log_tendsto h_unit_tendsto t
  apply (H_mat_isClosed H hH_closed).mem_of_tendsto h_pow_tendsto
  filter_upwards with k
  exact vonNeumann_mat_pow_mem_H_mat h_mem φ t k

/-! ### §4.i.5. BW-limit X lies in `tracelessSkewHermitian` (conditional)

For the SU(2) lift of `expAmbient (t • X)` we need
`X ∈ tracelessSkewHermitian (Fin 2)`. This follows from:
- (TRACKED) `su2Log h ∈ tracelessSkewHermitian` for `h` in the local
  exp target — the structural Lie-theoretic fact that matrix log near
  identity of an SU(2) element is in `su(2)`.
- `tracelessSkewHermitian` is a finite-dim ℝ-Submodule of
  `Matrix (Fin 2) (Fin 2) ℂ`, hence CLOSED (via
  `Submodule.closed_of_finiteDimensional`).
- The normalized unit-sphere sequence `vonNeumannUnitMatrixSeq seq n`
  is eventually in `tracelessSkewHermitian` (since `Y_n ∈ ts` + ℝ-smul
  preserves `ts`).
- BW limit of sequence in closed set is in the closed set. -/

/-- **Tracked Prop**: `su2Log h ∈ tracelessSkewHermitian (Fin 2)` for
every `h` in the local exp target.

Mathematically a theorem; ship-status is **TRACKED** (per Pipeline
Invariant #15, with user authorization for the gap-#2 discharge arc).

Discharge plan: the local IFT inverse `su2Log = expAmbientPartialHomeo.symm`
is generic and doesn't *itself* know about Lie algebras. For h ∈ SU(2)
near 1, su2Log h is the unique Y ∈ source with expAmbient Y = h. For h
unitary, the spectral decomposition gives `h = U · diag(e^{iα}, e^{iβ}) · U⁻¹`
with `α + β = 0` (from det = 1), and the principal log
`Y = U · diag(iα, iβ) · U⁻¹` is skew-Hermitian (since i α, i β are pure
imaginary) and traceless (since i(α+β) = 0). Identifying this Y with
`su2Log h` (via local uniqueness of matrix log) gives the claim.

This is a Mathlib-upstream-PR-quality substrate (~200-400 LoC of work,
mostly the spectral identification of the principal log). -/
def Su2LogMemTracelessSkewHermitian_SU2 : Prop :=
  ∀ {h : Matrix (Fin 2) (Fin 2) ℂ},
    h ∈ expAmbientPartialHomeo.target →
    h ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ →
    su2Log h ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)

/-- **§4.i.5a. `tracelessSkewHermitian` is closed in `Matrix _ _ ℂ`**
via `Submodule.closed_of_finiteDimensional` (finite-dim ℝ-Submodule). -/
theorem tracelessSkewHermitian_isClosed :
    IsClosed (SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :
      Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
  (SU2LieAlgebra.tracelessSkewHermitian (Fin 2)).closed_of_finiteDimensional

/-- **§4.i.5b. The unit-matrix-seq is eventually in `tracelessSkewHermitian`
(conditional on the tracked Prop)**: under `seq → 1` + `seq n ∈ SU(2) by subtype`
+ `Su2LogMemTracelessSkewHermitian_SU2`, `vonNeumannUnitMatrixSeq seq n
∈ tracelessSkewHermitian` for all n.

Proof: Y_n = su2Log (seq n).val ∈ ts eventually (tracked Prop applied
on the eventually-in-target set). Then `(‖Y_n‖⁻¹ : ℂ) • Y_n` is
ℝ-smul-equivalent to `(‖Y_n‖⁻¹ : ℝ) • Y_n`, which is in ts (ℝ-Submodule
closed under ℝ-smul). For n where Y_n = 0, vonNeumannUnitMatrixSeq = 0 ∈ ts. -/
theorem vonNeumannUnitMatrixSeq_mem_tracelessSkewHermitian_eventually
    (h_tracked : Su2LogMemTracelessSkewHermitian_SU2)
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))) :
    ∀ᶠ n in Filter.atTop,
      vonNeumannUnitMatrixSeq seq n ∈
        SU2LieAlgebra.tracelessSkewHermitian (Fin 2) := by
  filter_upwards [eventually_val_mem_target h_seq] with n hn
  unfold vonNeumannUnitMatrixSeq
  by_cases h_zero : su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) = 0
  · -- If Y_n = 0, the seq value is 0 ∈ ts
    simp only [h_zero, dif_pos]
    exact (SU2LieAlgebra.tracelessSkewHermitian (Fin 2)).zero_mem
  · -- Y_n ≠ 0: seq value is (‖Y_n‖⁻¹ : ℂ) • Y_n
    simp only [dif_neg h_zero]
    -- Convert ℂ-smul to ℝ-smul.
    rw [show ((‖su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ)‖⁻¹ : ℂ) •
            su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ)) =
            ((‖su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ)‖⁻¹ : ℝ) •
            su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ)) by
      ext i j
      simp [Matrix.smul_apply, Complex.real_smul]]
    -- Apply ℝ-smul closure on the tracked Prop's su2Log ∈ ts.
    have h_Y_ts : su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ∈
        SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
      h_tracked hn (seq n).property
    exact (SU2LieAlgebra.tracelessSkewHermitian (Fin 2)).smul_mem _ h_Y_ts

/-- **§4.i.5c. BW-limit X is in `tracelessSkewHermitian`** (conditional). -/
theorem vonNeumann_BW_limit_mem_tracelessSkewHermitian
    (h_tracked : Su2LogMemTracelessSkewHermitian_SU2)
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (h_unit_tendsto : Filter.Tendsto
      (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X)) :
    X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) := by
  apply tracelessSkewHermitian_isClosed.mem_of_tendsto h_unit_tendsto
  have h_ev := vonNeumannUnitMatrixSeq_mem_tracelessSkewHermitian_eventually
    h_tracked h_seq
  exact hφ.tendsto_atTop.eventually h_ev

/-! ### §4.i.6. Image-in-H: `oneParamSU2Map hX h_det t ∈ H`

The substantive bridge: combining §4.i.4's matrix-level `expAmbient (t • X)
∈ H_mat` with the structural identity `oneParamMatrixMap X t =
expAmbient (t • X)` (real-vs-complex smul agree on Matrix _ _ ℂ).
By Subtype.val injectivity, the lifted SU(2)-element
`oneParamSU2Map hX h_det t` is in H. -/

/-- **Bridge**: `oneParamMatrixMap X t = expAmbient (t • X)` for `t : ℝ`,
where the LHS uses ℂ-smul (`(t : ℂ) • X`) and the RHS uses ℝ-smul.
The two smul forms agree on `Matrix (Fin 2) (Fin 2) ℂ` via
`Complex.real_smul`. -/
lemma oneParamMatrixMap_eq_expAmbient_real_smul
    (X : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    oneParamMatrixMap X t =
      SU2MatrixExp.expAmbient ((t : ℝ) • X) := by
  unfold oneParamMatrixMap
  rw [← real_smul_matrix2C_eq_complex_smul t X]

/-- **§4.i.6. `oneParamSU2Map hX h_det t ∈ H`** (conditional on both
tracked Props): the SU(2)-subtype-lifted version of `expAmbient (t • X)`
is in H, for every `t : ℝ`. -/
theorem vonNeumann_oneParamSU2Map_mem_H
    (h_det : DetExpZeroOnSu2_SU2)
    {H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (hH_closed : IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)}
    (h_mem : ∀ n, seq n ∈ H)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))))
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => su2Log ((seq n).val : Matrix (Fin 2) (Fin 2) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)))
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_unit_tendsto : Filter.Tendsto
      (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    oneParamSU2Map hX h_det t ∈ H := by
  -- Step 1: expAmbient (t • X) ∈ H_mat (from §4.i.4).
  have h_inH_mat := vonNeumann_expAmbient_mem_H_mat
    hH_closed h_mem hφ h_seq h_ev_ne h_log_tendsto h_unit_tendsto t
  -- Step 2: unpack the image membership.
  obtain ⟨h_witness, h_witness_mem, h_witness_val⟩ := h_inH_mat
  -- Step 3: oneParamMatrixMap X t = expAmbient (t • X) (via ℂ-vs-ℝ smul bridge).
  have h_bridge := oneParamMatrixMap_eq_expAmbient_real_smul X t
  -- Step 4: (oneParamSU2Map hX h_det t).val = h_witness.val (in Matrix _ _ ℂ).
  have h_val_eq : (oneParamSU2Map hX h_det t).val =
      h_witness.val := by
    show oneParamMatrixMap X t = h_witness.val
    rw [h_bridge]
    exact h_witness_val.symm
  -- Step 5: by Subtype.val injectivity, the SU(2)-elements are equal.
  have h_eq : oneParamSU2Map hX h_det t = h_witness :=
    Subtype.ext h_val_eq
  rw [h_eq]
  exact h_witness_mem

/-! ### §4.i.7. Nontriviality of `oneParamSU2Map`

For the BW-extracted X with `‖X‖ = 1` (hence X ≠ 0), the 1-parameter
subgroup `oneParamSU2Map hX h_det` is nontrivial: ∃ t ≠ 0, the lift
is not equal to 1. Proof: continuity of ℂ-smul gives a neighborhood of
0 in ℝ where `(t : ℂ) • X ∈ source` (the local-IFT domain); pick small
nonzero t in this neighborhood; apply `su2Log_expAmbient` (left-inverse
on source) and `su2Log_one = 0` to conclude `expAmbient ((t : ℂ) • X) ≠ 1`,
hence the SU(2)-lifted version is not the identity. -/

/-- **§4.i.7. Nontriviality**: for X ≠ 0 ∈ `tracelessSkewHermitian`,
`∃ t : ℝ, oneParamSU2Map hX h_det t ≠ 1`. -/
theorem vonNeumann_oneParamSU2Map_nontrivial
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX_ne : X ≠ 0)
    (hX_ts : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2))
    (h_det : DetExpZeroOnSu2_SU2) :
    ∃ t : ℝ, oneParamSU2Map hX_ts h_det t ≠ 1 := by
  -- Step 1: smul continuity gives eventually (t : ℂ) • X ∈ source.
  have h_smul_cont : Filter.Tendsto (fun t : ℝ => (t : ℂ) • X)
      (nhds 0) (nhds 0) := by
    have h_zero : ((0 : ℝ) : ℂ) • X = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
      push_cast; simp
    rw [show (0 : Matrix (Fin 2) (Fin 2) ℂ) = ((0 : ℝ) : ℂ) • X from h_zero.symm]
    exact (continuous_smul.comp
      (Complex.continuous_ofReal.prodMk continuous_const)).tendsto 0
  have h_ev : ∀ᶠ t : ℝ in nhds 0, (t : ℂ) • X ∈ expAmbientPartialHomeo.source :=
    h_smul_cont expAmbientPartialHomeo_source_mem_nhds_zero
  -- Step 2: extract ε > 0 from Metric.eventually_nhds_iff.
  rw [Metric.eventually_nhds_iff] at h_ev
  obtain ⟨ε, hε_pos, h_ball⟩ := h_ev
  -- Step 3: pick t := ε/2 (positive, distance ε/2 < ε from 0).
  refine ⟨ε / 2, ?_⟩
  have h_t_ne : (ε / 2 : ℝ) ≠ 0 := by linarith
  have h_in_source : ((ε / 2 : ℝ) : ℂ) • X ∈ expAmbientPartialHomeo.source := by
    apply h_ball
    rw [Real.dist_eq, sub_zero]
    simp [abs_of_pos (by linarith : (0:ℝ) < ε/2)]
    linarith
  -- Step 4: lift via Subtype.ext_iff + su2Log_expAmbient.
  intro h_eq
  have h_val_eq : (oneParamSU2Map hX_ts h_det (ε/2)).val =
      (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val := by
    rw [h_eq]
  unfold oneParamSU2Map at h_val_eq
  simp at h_val_eq
  unfold oneParamMatrixMap at h_val_eq
  have h_log_eq : su2Log (SU2MatrixExp.expAmbient (((ε/2 : ℝ) : ℂ) • X)) =
      su2Log (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [h_val_eq]
  rw [su2Log_expAmbient h_in_source, su2Log_one] at h_log_eq
  -- h_log_eq : ((ε/2 : ℝ) : ℂ) • X = 0, contradicting t ≠ 0 ∧ X ≠ 0.
  exact (smul_ne_zero (by exact_mod_cast h_t_ne) hX_ne) h_log_eq

/-! ### §4.i.8. Full assembly + conditional discharge of `OneParamSubgroupFromAccPt_SU2`

The full chain from `IsClosed H + AccPt 1 H` to `OneParamSubgroupInSU2 H`,
conditional on the two tracked Props `DetExpZeroOnSu2_SU2` +
`Su2LogMemTracelessSkewHermitian_SU2`. This CLOSES gap #2 in the
strengthened form. -/

/-- **§4.i.8a. Full vonNeumann assembly (conditional)**: given the tracked
Props and the strengthened gap-#2 hypothesis (H closed + AccPt 1 H),
construct `OneParamSubgroupInSU2 H`. -/
theorem vonNeumann_assemble_OneParamSubgroupInSU2
    (h_det : DetExpZeroOnSu2_SU2)
    (h_log_tracked : Su2LogMemTracelessSkewHermitian_SU2)
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (hH_closed : IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    (hH_accPt : AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (Filter.principal (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)))) :
    SKEFTHawking.FKLW.OneParamSubgroupInSU2 H := by
  -- Step 1: extract sequence + matrix-log convergence.
  obtain ⟨seq, h_mem, h_ne, h_seq, h_log_tendsto⟩ :=
    vonNeumann_sequence_with_log H hH_accPt
  -- Step 2: eventually Y_n ≠ 0.
  have h_ev_ne := eventually_su2Log_seq_ne_zero h_ne h_seq
  -- Step 3: BW extraction.
  obtain ⟨X, _hX_ball, φ, hφ, h_unit_tendsto⟩ := vonNeumann_BW_extract seq
  -- Step 4: ‖X‖ = 1, so X ≠ 0.
  have h_norm_one : ‖X‖ = 1 :=
    vonNeumann_BW_limit_norm_eq_one seq h_ev_ne hφ h_unit_tendsto
  have hX_ne : X ≠ 0 := fun h => by
    rw [h, norm_zero] at h_norm_one; norm_num at h_norm_one
  -- Step 5: X ∈ tracelessSkewHermitian (conditional on tracked Prop).
  have hX_ts : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) :=
    vonNeumann_BW_limit_mem_tracelessSkewHermitian h_log_tracked h_seq hφ
      h_unit_tendsto
  -- Step 6: assemble φ := oneParamSU2Map hX_ts h_det.
  refine ⟨oneParamSU2Map hX_ts h_det, ?_, ?_, ?_, ?_, ?_⟩
  · -- Continuous
    exact oneParamSU2Map_continuous hX_ts h_det
  · -- φ 0 = 1
    exact oneParamSU2Map_zero hX_ts h_det
  · -- φ (s + t) = φ s * φ t
    intro s t
    exact oneParamSU2Map_add hX_ts h_det s t
  · -- Nontriviality
    exact vonNeumann_oneParamSU2Map_nontrivial hX_ne hX_ts h_det
  · -- Image in H
    intro t
    exact vonNeumann_oneParamSU2Map_mem_H h_det hH_closed h_mem hφ h_seq
      h_ev_ne h_log_tendsto hX_ts h_unit_tendsto t

/-- **§4.i.8b. CONDITIONAL DISCHARGE of `OneParamSubgroupFromAccPt_SU2`**:
under the two tracked Props `DetExpZeroOnSu2_SU2` (§3.5d) +
`Su2LogMemTracelessSkewHermitian_SU2` (§4.i.5), the strengthened gap-#2
predicate holds.

This CLOSES gap #2 conditional on the two named tracked Props. Combined
with `H_Fib_eq_top_of_strengthened_chain` (CartanSubstrate.lean §4.7),
this reduces F.21 unconditional density to ONLY the Wedge-B
`CartanFinalStep_SU2` predicate + these two new tracked Props (still
fewer total Props than the original 3 gaps #1+#2+#3). -/
theorem OneParamSubgroupFromAccPt_SU2_of_tracked_props
    (h_det : DetExpZeroOnSu2_SU2)
    (h_log_tracked : Su2LogMemTracelessSkewHermitian_SU2) :
    SKEFTHawking.FKLW.OneParamSubgroupFromAccPt_SU2 := by
  intro H hH_closed hH_accPt
  exact vonNeumann_assemble_OneParamSubgroupInSU2
    h_det h_log_tracked H hH_closed hH_accPt

/-! ## §6. F.21 Fibonacci density — composition under TWO tracked sub-Props

Combining the §4.i.8b conditional discharge with the upstream chain in
`CartanSubstrate.lean §4.7` yields a strengthened F.21 statement where
the Cartan-stack dependencies are reduced from 3 original gaps
(#1+#2+#3) to 3 new Props (CartanFinalStep + DetExp + Su2LogMem), but
the NEW Props are FOCUSED bridge lemmas with explicit spectral-theorem
discharge plans, vs the original broader Cartan-classification predicates.
-/

/-- **`H_Fib = ⊤` from THREE tracked Props** (super-strengthened
Wedge B headline): combines `OneParamSubgroupFromAccPt_SU2_of_tracked_props`
with `H_Fib_eq_top_of_strengthened_chain` (CartanSubstrate.lean §4.7).

Compared to the original `H_Fib_eq_top_of_full_cartan_chain` (Cartan
gaps #1+#2+#3), this version replaces gaps #1+#2 with the two focused
tracked Props `DetExpZeroOnSu2_SU2` + `Su2LogMemTracelessSkewHermitian_SU2`. -/
theorem H_Fib_eq_top_from_three_tracked_props
    (h_det : DetExpZeroOnSu2_SU2)
    (h_log_tracked : Su2LogMemTracelessSkewHermitian_SU2)
    (h_cartan_final : SKEFTHawking.FKLW.CartanFinalStep_SU2) :
    SKEFTHawking.FKLW.H_Fib = ⊤ :=
  SKEFTHawking.FKLW.H_Fib_eq_top_of_strengthened_chain
    (OneParamSubgroupFromAccPt_SU2_of_tracked_props h_det h_log_tracked)
    h_cartan_final

/-- **F.21 Fibonacci density from THREE tracked Props** (final composition
headline): combines `OneParamSubgroupFromAccPt_SU2_of_tracked_props` with
`fibonacci_density_F21_from_strengthened_chain` (CartanSubstrate.lean §4.7).

This is the **headline F.21 statement under the post-gap-#2-discharge
chain**: unconditional Fibonacci density in `SU(3)_2 ↪ SU(2)` under
exactly THREE focused tracked Props, all with explicit Mathlib-substrate
discharge plans. -/
theorem fibonacci_density_F21_from_three_tracked_props
    (h_det : DetExpZeroOnSu2_SU2)
    (h_log_tracked : Su2LogMemTracelessSkewHermitian_SU2)
    (h_cartan_final : SKEFTHawking.FKLW.CartanFinalStep_SU2) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (SKEFTHawking.FKLW.ρ_Fib_SU2 b :
          Matrix (Fin 2) (Fin 2) ℂ)) :=
  SKEFTHawking.FKLW.fibonacci_density_F21_from_strengthened_chain
    (OneParamSubgroupFromAccPt_SU2_of_tracked_props h_det h_log_tracked)
    h_cartan_final

/-! ## §7. Substrate: `expAmbient X = α • 1 + β • X` for X² = c • 1

Power-series machinery for the closed-form `expAmbient X` decomposition.
For X with `X * X = c • 1`, we have:
- X^(2k) = c^k • 1
- X^(2k+1) = c^k • X
So the matrix exp series splits into:
- Even: Σ_k ((2k)!)⁻¹ • X^(2k) = (Σ_k c^k / (2k)!) • 1 = α • 1
- Odd: Σ_k ((2k+1)!)⁻¹ • X^(2k+1) = (Σ_k c^k / (2k+1)!) • X = β • X

Combined via `HasSum.even_add_odd`: expAmbient X = α • 1 + β • X.

For X ∈ tracelessSkewHermitian with c = -(su2RadiusSq X : ℂ), we then
identify α with `Complex.cos r` (r := √(su2RadiusSq X)) via
`Complex.hasSum_cos`.

This is the substrate for discharging `DetExpZeroOnSu2_SU2` (the
tracked Prop introduced in §3.5d). -/

/-- **§7.1. X^(2k) closed form**: for X with X² = c • 1,
X^(2k) = c^k • 1. -/
lemma pow_two_mul_of_sq_eq_scalar
    {X : Matrix (Fin 2) (Fin 2) ℂ} {c : ℂ}
    (hX_sq : X * X = c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (k : ℕ) :
    X ^ (2 * k) = c^k • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, show 2 * k + 2 = 2 * k + 1 + 1 from rfl, pow_succ, pow_succ]
    rw [mul_assoc, hX_sq, mul_smul_comm, mul_one, ih, pow_succ, smul_smul]
    ring_nf

/-- **§7.2. X^(2k+1) closed form**: for X with X² = c • 1,
X^(2k+1) = c^k • X. -/
lemma pow_two_mul_add_one_of_sq_eq_scalar
    {X : Matrix (Fin 2) (Fin 2) ℂ} {c : ℂ}
    (hX_sq : X * X = c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (k : ℕ) :
    X ^ (2 * k + 1) = c^k • X := by
  rw [pow_succ, pow_two_mul_of_sq_eq_scalar hX_sq, smul_mul_assoc, one_mul]

/-- **§7.3. Even-part HasSum**: for X with X² = c • 1 and `HasSum
(fun k => c^k / (2k)!) α`, the even-indexed terms of the exp series
sum to `α • 1`. -/
lemma even_part_hasSum_of_sq_eq_scalar
    {X : Matrix (Fin 2) (Fin 2) ℂ} {c : ℂ}
    (hX_sq : X * X = c • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    {α : ℂ} (hα : HasSum (fun k => c^k / ((2 * k).factorial : ℂ)) α) :
    HasSum (fun k => (((2*k).factorial : ℂ)⁻¹ : ℂ) • X ^ (2 * k))
      (α • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have h_eq : (fun k => (((2*k).factorial : ℂ)⁻¹ : ℂ) • X ^ (2 * k)) =
              (fun k => (c^k / ((2 * k).factorial : ℂ)) •
                (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    funext k
    rw [pow_two_mul_of_sq_eq_scalar hX_sq, smul_smul, div_eq_inv_mul, mul_comm]
  rw [h_eq]
  exact hα.smul_const 1

/-- **§7.4. Odd-part HasSum**: dual to §7.3. -/
lemma odd_part_hasSum_of_sq_eq_scalar
    {X : Matrix (Fin 2) (Fin 2) ℂ} {c : ℂ}
    (hX_sq : X * X = c • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    {β : ℂ} (hβ : HasSum (fun k => c^k / ((2 * k + 1).factorial : ℂ)) β) :
    HasSum (fun k => (((2*k+1).factorial : ℂ)⁻¹ : ℂ) • X ^ (2 * k + 1))
      (β • X) := by
  have h_eq : (fun k => (((2*k+1).factorial : ℂ)⁻¹ : ℂ) • X ^ (2 * k + 1)) =
              (fun k => (c^k / ((2 * k + 1).factorial : ℂ)) • X) := by
    funext k
    rw [pow_two_mul_add_one_of_sq_eq_scalar hX_sq, smul_smul, div_eq_inv_mul, mul_comm]
  rw [h_eq]
  exact hβ.smul_const X

/-- **§7.5. Combined decomposition**: `expAmbient X = α • 1 + β • X`
for X² = c • 1, when α and β are given as scalar series sums. -/
theorem expAmbient_decomp_of_sq_eq_scalar
    {X : Matrix (Fin 2) (Fin 2) ℂ} {c : ℂ}
    (hX_sq : X * X = c • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    {α β : ℂ}
    (hα : HasSum (fun k => c^k / ((2 * k).factorial : ℂ)) α)
    (hβ : HasSum (fun k => c^k / ((2 * k + 1).factorial : ℂ)) β) :
    SU2MatrixExp.expAmbient X = α • (1 : Matrix (Fin 2) (Fin 2) ℂ) + β • X := by
  have h_even := even_part_hasSum_of_sq_eq_scalar hX_sq hα
  have h_odd := odd_part_hasSum_of_sq_eq_scalar hX_sq hβ
  have h_combined : HasSum (fun n => ((n.factorial : ℂ)⁻¹ : ℂ) • X ^ n)
      (α • (1 : Matrix (Fin 2) (Fin 2) ℂ) + β • X) :=
    HasSum.even_add_odd h_even h_odd
  have h_exp_sum : HasSum (fun n => ((n.factorial : ℂ)⁻¹ : ℂ) • X ^ n)
      (SU2MatrixExp.expAmbient X) := by
    unfold SU2MatrixExp.expAmbient
    have := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) X
    convert this using 1
    ext n
    simp [NormedSpace.expSeries, smul_eq_mul]
  exact h_exp_sum.unique h_combined

/-- **§7.6. Cos identification**: for real r, the scalar series
Σ_k (-r²)^k / (2k)! equals `Complex.cos r`.

Proof: `Complex.hasSum_cos` gives Σ_n (-1)^n · r^(2n) / (2n)!, and
(-r²)^k = (-1)^k · r^(2k). -/
lemma cos_hasSum_su2 (r : ℝ) :
    HasSum (fun k => ((-(r^2) : ℝ) : ℂ)^k / ((2 * k).factorial : ℂ))
      (Complex.cos (r : ℂ)) := by
  have h_cos := Complex.hasSum_cos (r : ℂ)
  have h_eq : (fun n => (-1 : ℂ) ^ n * (r : ℂ) ^ (2 * n) / ((2 * n).factorial : ℂ))
            = (fun k => ((-(r^2) : ℝ) : ℂ)^k / ((2 * k).factorial : ℂ)) := by
    funext n
    push_cast
    ring
  rw [← h_eq]
  exact h_cos

/-! ## §5. Module summary (current ship)

`OneParameterSubgroupSU2.lean` (Phase 6p Wave 2c.4a-R4.2.d.R5.4 Cartan
strengthening — Mathlib-upstream-PR-quality substrate, session 2026-05-21):

**Shipped (this commit, ~150 LoC; zero new axioms):**

  - **§1**: Local matrix logarithm near identity in `Matrix (Fin 2) (Fin 2) ℂ`,
    extracted from the existing IFT-derived `OpenPartialHomeomorph`:
    - `expAmbientPartialHomeo : OpenPartialHomeomorph` (the explicit IFT
      partial homeomorphism)
    - `su2Log : Matrix _ _ ℂ → Matrix _ _ ℂ` (matrix logarithm)
    - `expAmbient_su2Log`: `expAmbient (su2Log h) = h` on target
    - `su2Log_expAmbient`: `su2Log (expAmbient Y) = Y` on source
    - `su2Log_one : su2Log 1 = 0`
    - `su2Log_continuousOn`: continuity on target
    - source/target open + nhds witnesses

  - **§1.5**: SU(2) consumer form:
    `exists_nhds_one_SU2_su2Log_defined` (W ∈ 𝓝(1) in SU(2)-subtype with
    `g.val ∈ target` for all `g ∈ W`).

  - **§§2-4 (next ship)**: scaffold-only docstring with substrate roadmap.

**Substantive content shipped**:

The §1 substrate makes the matrix logarithm a first-class object usable
downstream — previously it was only constructed inline within a proof
in `SU2LocalDiffeo`. This is the foundation for the next-ship von
Neumann construction.
-/

end SKEFTHawking.FKLW.OneParameterSubgroupSU2
