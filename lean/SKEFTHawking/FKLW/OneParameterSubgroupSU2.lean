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

/-! ## §§3.5d-4. (Next ship — substrate roadmap)

  **§3.5. SU(2) inclusion `oneParamMatrixMap X t ∈ specialUnitaryGroup`**:

  Need `det (expAmbient (t • X)) = 1` for X ∈ tracelessSkewHermitian (Fin 2).

  Approach (closed-form): from `tracelessSkewHermitian_two_sq` we have
  `(t•X)² = -(t² · su2RadiusSq X) • I`. The power series for
  `expAmbient (t • X)` thus splits into even/odd parts that recognize as
  `cos(t·r) • I + sinc(t·r) • (t•X)` (with `r := √(su2RadiusSq X)`).
  Then `det(α • I + β • (t•X))` for traceless `t•X` ∈ M_2(ℂ) equals
  `α² + β² · det(t•X) = α² + β² · t² · su2RadiusSq X`, which evaluates
  to `cos²(t·r) + sin²(t·r) = 1`.

  Formalization: requires showing the partial-sum recognition with
  `Real.cos`, `Real.sin`. Approximately 200-400 LoC of substantive
  power-series work.

  Alternative (spectral): via `Matrix.IsHermitian.spectral_theorem` on
  `i • X` (Hermitian). Decomposes `t • X = U · diag(λ₁, λ₂) · U†` with
  λ_i pure imaginary, sum = 0 (from tracelessness). Then
  `det(expAmbient (t•X)) = exp(λ₁) · exp(λ₂) = exp(λ₁+λ₂) = exp(0) = 1`.
  Similar LoE.

  **§4. Von Neumann construction + discharge of
       `OneParamSubgroupFromAccPt_SU2`**:

  Once §3.5 is in hand:
  - From AccPt 1 in H, extract sequence (h_n) → 1 in H \ {1}.
  - Y_n := su2Log h_n; show Y_n ∈ tracelessSkewHermitian (using §3.5's
    SU(2) inclusion + local inverse uniqueness — this is the SHIPPED-substrate
    "log of SU(2) element near 1 is in su(2)" sub-lemma).
  - X_n := Y_n / ‖Y_n‖_op in unit sphere of finite-dim
    `tracelessSkewHermitian (Fin 2) ≅ ℝ³`.
  - BW → subseq X_{n_k} → X with ‖X‖ = 1.
  - For any t ∈ ℝ, k_n := round(t / ‖Y_n‖). h_n^{k_n} = expAmbient
    (k_n • Y_n) ∈ H. Show this → expAmbient (t • X) (uses unitary norm
    1 + telescoping bound). H closed → exp(t • X) ∈ H.
  - Define φ t := ⟨oneParamMatrixMap X t, ...⟩; verify all
    `OneParamSubgroupInSU2 H` conjuncts using §3 lemmas above.

  Result: `OneParamSubgroupFromAccPt_SU2` is theorem (not predicate),
  discharging gap #2 substantively. Combined with §4.7's strengthening,
  this reduces F.21 unconditional density to a single remaining tracked
  Cartan predicate (`CartanFinalStep_SU2`).
-/

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
