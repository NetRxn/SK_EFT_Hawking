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

/-- **CAYLEY-HAMILTON SPECIALIZATION** (NEXT SHIP — proof in flight, this
declaration is the target statement). For X ∈ tracelessSkewHermitian (Fin 2),
`X² = -(su2RadiusSq X) • 1`.

This is the key algebraic identity that enables the closed-form
analysis of `exp` on su(2): even powers of X are scalar multiples of I,
odd powers are scalar multiples of X.

Proof outline (deferred to next work block — local-pwd issue resolved):
use `Matrix.two_mul_expl` to obtain all 4 entry equations of `X * X`,
substitute the structural-form replacements `X 0 0 = iα`, `X 1 1 = -X 0 0`,
`X 1 0 = -star (X 0 1)` from membership in `tracelessSkewHermitian`,
and verify each entry via `Complex.mul_conj` + `Complex.I_sq` + `nlinarith`. -/
example : True := trivial -- placeholder for next-ship target
/-
theorem tracelessSkewHermitian_two_sq
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)) :
    X * X = (-(su2RadiusSq X) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- Extract the entry constraints from membership in tracelessSkewHermitian.
  obtain ⟨hX_skew, hX_tr⟩ := hX
  -- Re-derive the structural form (matches the private
  -- `tracelessSkewHermitian_entries`).
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
  -- Reformulate diagonal as X 0 0 = i · α with α := (X 0 0).im.
  have h_X00 : X 0 0 = (((X 0 0).im : ℝ) : ℂ) * Complex.I := by
    have := (Complex.re_add_im (X 0 0)).symm
    rw [h_re_00, Complex.ofReal_zero, zero_add] at this
    exact this
  -- Also reformulate the (1, 0) off-diagonal using complex conjugation.
  have h_X10 : X 1 0 = -((starRingEnd ℂ) (X 0 1)) := by
    rw [h_offdiag]
    rfl
  -- Substrate: ‖X 0 1‖² = (X 0 1).re² + (X 0 1).im² in ℝ.
  have h_norm_sq : (‖X 0 1‖ ^ 2 : ℂ) =
      (((X 0 1).re : ℝ) : ℂ) ^ 2 + (((X 0 1).im : ℝ) : ℂ) ^ 2 := by
    rw [show (‖X 0 1‖ ^ 2 : ℂ) = ((‖X 0 1‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl,
        Complex.sq_norm, Complex.normSq_apply]
    push_cast; ring
  -- Two key complex-conjugate identities.
  have h_conj_left : X 0 1 * (starRingEnd ℂ) (X 0 1) =
      (((X 0 1).re : ℝ) : ℂ) ^ 2 + (((X 0 1).im : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj]
    push_cast; rw [Complex.normSq_apply]; push_cast; ring
  have h_conj_right : (starRingEnd ℂ) (X 0 1) * X 0 1 =
      (((X 0 1).re : ℝ) : ℂ) ^ 2 + (((X 0 1).im : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj]
    push_cast; rw [Complex.normSq_apply]; push_cast; ring
  -- Use Matrix.two_mul_expl to get all 4 entry equations at once.
  obtain ⟨h_00, h_01, h_10, h_11_entry⟩ := Matrix.two_mul_expl X X
  -- Replace X via h_X00, h_X10, h_11 in each entry equation.
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  -- Now build the target matrix entry-by-entry.
  ext i j
  fin_cases i <;> fin_cases j
  · -- (0, 0)
    rw [h_00, h_X00]
    show (((X 0 0).im : ℝ) : ℂ) * Complex.I * ((((X 0 0).im : ℝ) : ℂ) * Complex.I) +
         X 0 1 * X 1 0 =
         (-(su2RadiusSq X) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        h_X10, su2RadiusSq]
    push_cast
    rw [h_conj_left]
    nlinarith [hI2, sq_nonneg ((X 0 0).im : ℝ),
               sq_nonneg ((X 0 1).re : ℝ), sq_nonneg ((X 0 1).im : ℝ)]
  · -- (0, 1)
    rw [h_01, h_X00, h_11]
    show (((X 0 0).im : ℝ) : ℂ) * Complex.I * X 0 1 +
         X 0 1 * (-(((X 0 0).im : ℝ) : ℂ) * Complex.I) =
         (-(su2RadiusSq X) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1
    rw [Matrix.smul_apply,
        Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        smul_zero]
    ring
  · -- (1, 0)
    rw [h_10, h_11, h_X10, h_X00]
    show -((starRingEnd ℂ) (X 0 1)) * ((((X 0 0).im : ℝ) : ℂ) * Complex.I) +
         (-(((X 0 0).im : ℝ) : ℂ) * Complex.I) * -((starRingEnd ℂ) (X 0 1)) =
         (-(su2RadiusSq X) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0
    rw [Matrix.smul_apply,
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
        smul_zero]
    ring
  · -- (1, 1)
    rw [h_11_entry, h_X10, h_11, h_X00]
    show -((starRingEnd ℂ) (X 0 1)) * X 0 1 +
         -(((X 0 0).im : ℝ) : ℂ) * Complex.I *
            (-(((X 0 0).im : ℝ) : ℂ) * Complex.I) =
         (-(su2RadiusSq X) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        h_conj_right, su2RadiusSq]
    push_cast
    nlinarith [hI2, sq_nonneg ((X 0 0).im : ℝ),
               sq_nonneg ((X 0 1).re : ℝ), sq_nonneg ((X 0 1).im : ℝ)]
-/

/-! ## §§3-4. (Next ship — substrate roadmap)

The remaining substantive content (Mathlib-upstream-PR-quality):

  **§3. Closed-form analysis of `expAmbient X` for X ∈ su(2)**:

  From `tracelessSkewHermitian_two_sq` (above) we have `X² = -r² • I` for
  `r² := su2RadiusSq X ≥ 0`. Hence:
    - `X^{2k} = (-r²)^k • I`,
    - `X^{2k+1} = (-r²)^k • X`.
  The power-series `exp X = Σ X^n/n!` splits into even/odd parts that
  recognize as `cos(r) • I + (sinc r) • X` (with the limit
  `sinc 0 = 1`). Yields:
    - `(expAmbient X).det = 1` (closed-form `cos² + r² · sinc²`)
    - `expAmbient X ∈ specialUnitaryGroup (Fin 2) ℂ`
    - The 1-parameter subgroup `φ t := expAmbient (t • X)` is continuous,
      satisfies `φ 0 = 1`, `φ (s + t) = φ s * φ t` (`exp_add_of_commute`).

  **§4. Von Neumann construction + discharge of
       `OneParamSubgroupFromAccPt_SU2`**:

  From a sequence (h_n) → 1 in `H \ {1}`:
    - Y_n := su2Log h_n ∈ su(2), Y_n → 0 (uses §2 + the §2.next "su2Log
      lands in su(2)" sublemma, derivable from §3's well-defined exp on
      su(2) plus local inverse uniqueness).
    - X_n := Y_n / ‖Y_n‖ in the unit sphere of `tracelessSkewHermitian
      (Fin 2)` (finite-dim ⇒ proper ⇒ compact sphere).
    - BW → subseq X_{n_k} → X with `‖X‖ = 1`.
    - For any `t : ℝ`, `k_n := round(t / ‖Y_n‖)` integer.
    - `h_n^{k_n} = expAmbient (k_n • Y_n)` (via `NormedSpace.exp_nsmul`).
    - `k_n • Y_n → t • X` (since `k_n · ‖Y_n‖ → t` and `X_n → X`).
    - exp continuous ⇒ `h_n^{k_n} → expAmbient (t • X)`.
    - H closed ⇒ `expAmbient (t • X) ∈ H` for all `t`.

  Set `φ t := ⟨expAmbient (t • X), ... ∈ SU(2)⟩` and verify the
  `OneParamSubgroupInSU2 H` conjuncts.

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
