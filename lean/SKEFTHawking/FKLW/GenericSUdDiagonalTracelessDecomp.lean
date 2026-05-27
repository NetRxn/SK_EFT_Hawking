/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 substrate — Rank-2 unitary-image balanced commutator at SU(d)

For ANY rank-2 Hermitian-traceless `H ∈ Matrix (Fin d) (Fin d) ℂ` arising as
`H = U · σ_z(i, j) · U*` for some `U ∈ SU(d)` and `i ≠ j ∈ Fin d`, the
balanced commutator equation

  F · G - G · F = -iθ · H

is discharged by `F = U · √(θ/2)·σ_y(i,j) · U*` and `G = U · √(θ/2)·σ_x(i,j) · U*`.

**Composition pattern**: Session 11's σ_z-pattern balanced commutator at SU(d)
+ Session 13's unitary conjugation invariance + Session 13's Hermitian/trace
preservation under SU(d) conjugation.

## Substantive content shipped

  * `balanced_commutator_unitary_image_sigmaZ_pattern_SUd_algebraic` — the
    algebraic balanced-commutator structure (Hermitian × 2, traceless × 2,
    commutator identity) is preserved under SU(d) conjugation.

## Norm-bridging caveat

The norm-bound conjunct `‖F‖_linftyOp ≤ √(θ/2)` is NOT automatically preserved
under unitary conjugation since `Matrix.linftyOpNorm` is not unitary-invariant.
The spectral norm IS unitary-invariant, with the d-dependent bridge
`‖A‖_linftyOp ≤ √d · ‖A‖_spectral`. The norm-bridging substrate ships
separately; this module ships the algebraic content.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 substrate (rank-2 unitary-
image case — the simplest non-trivial generalization beyond d = 2; arbitrary-
rank Aharonov-Arad construction with counterterms ships separately).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorTwoBlock
import SKEFTHawking.FKLW.GenericSUdBalancedCommutatorConjugation

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Rank-2 unitary-image discharge (algebraic conjuncts)

Composes Session 11's σ_z-pattern balanced commutator + Session 13's
unitary conjugation invariance. -/

/-- **Rank-2 unitary-image balanced commutator at SU(d)** (algebraic
content; norm bounds omitted — see norm-bridging caveat).

For `U ∈ SU(d)`, `i ≠ j ∈ Fin d`, `θ ∈ [0, 1]`, define
  F := U · √(θ/2)·σ_y(i, j) · U*
  G := U · √(θ/2)·σ_x(i, j) · U*
  H := U · σ_z(i, j) · U*
Then F, G are Hermitian + traceless and `F·G - G·F = -iθ · H`.

**Composition**: `balanced_commutator_sigmaZ_pattern_SUd` (Session 11) gives
the inner structure for `H̃ = σ_z(i, j)`; `unitary_conjugation_balanced_commutator_structure`
(Session 13) transports it under conjugation to `H = U · H̃ · U*`. -/
theorem balanced_commutator_unitary_image_sigmaZ_pattern_SUd_algebraic
    {d : ℕ} {i j : Fin d} (h_ne : i ≠ j)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    let c : ℂ := (Real.sqrt (θ/2) : ℂ)
    let F : Matrix (Fin d) (Fin d) ℂ := U.val * (c • sigmaYBlock i j) * star U.val
    let G : Matrix (Fin d) (Fin d) ℂ := U.val * (c • sigmaXBlock i j) * star U.val
    let H : Matrix (Fin d) (Fin d) ℂ := U.val * sigmaZBlock i j * star U.val
    F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
    F * G - G * F = -((θ : ℂ) * Complex.I) • H := by
  -- Extract Session 11's structure for the inner case H̃ = σ_z(i, j).
  have h_inner := balanced_commutator_sigmaZ_pattern_SUd h_ne θ hθ_nn hθ_le_one
  obtain ⟨h_F_herm, h_G_herm, h_F_tr, h_G_tr, _, _, h_comm⟩ := h_inner
  -- Apply Session 13's composite invariance under U-conjugation.
  exact unitary_conjugation_balanced_commutator_structure U
    (((Real.sqrt (θ/2) : ℝ) : ℂ) • sigmaYBlock i j)
    (((Real.sqrt (θ/2) : ℝ) : ℂ) • sigmaXBlock i j)
    (sigmaZBlock i j) θ h_F_herm h_G_herm h_F_tr h_G_tr h_comm

/-! ## 2. Hermitian rank-2 characterization

The rank-2 unitary-image `H = U · σ_z(i, j) · U*` is Hermitian and
traceless by construction (Session 13's `unitary_conjugation_isHermitian`
+ `unitary_conjugation_traceless`). -/

/-- **Rank-2 unitary-image is Hermitian**: for `U ∈ SU(d)` and `i, j ∈ Fin d`,
`(U · σ_z(i, j) · U*).IsHermitian`. -/
theorem unitary_image_sigmaZ_isHermitian {d : ℕ} (i j : Fin d)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    (U.val * sigmaZBlock i j * star U.val).IsHermitian :=
  unitary_conjugation_isHermitian U (sigmaZBlock i j) (sigmaZBlock_isHermitian i j)

/-- **Rank-2 unitary-image is traceless**: for `i ≠ j` and `U ∈ SU(d)`,
`(U · σ_z(i, j) · U*).trace = 0`. -/
theorem unitary_image_sigmaZ_traceless {d : ℕ} {i j : Fin d} (h_ne : i ≠ j)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    (U.val * sigmaZBlock i j * star U.val).trace = 0 :=
  unitary_conjugation_traceless U (sigmaZBlock i j) (sigmaZBlock_trace h_ne)

/-! ## 3. Combined Hermitian-traceless witness

For any rank-2 unitary image of σ_z(i, j), the resulting H is a Hermitian-
traceless witness in SU(d). -/

/-- **Rank-2 unitary-image is Hermitian-traceless**: combined statement. -/
theorem unitary_image_sigmaZ_isHermitian_and_traceless {d : ℕ} {i j : Fin d}
    (h_ne : i ≠ j) (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    (U.val * sigmaZBlock i j * star U.val).IsHermitian ∧
    (U.val * sigmaZBlock i j * star U.val).trace = 0 :=
  ⟨unitary_image_sigmaZ_isHermitian i j U,
   unitary_image_sigmaZ_traceless h_ne U⟩

/-! ## 4. Rank-2-unitary-image balanced commutator predicate

A predicate-level encoding of the rank-2 unitary-image case: for all `(i, j, U)`
defining a rank-2 H = U·σ_z(i,j)·U*, there exist F, G discharging the
algebraic balanced commutator structure. Discharged UNCONDITIONALLY via §1. -/

/-- **Rank-2 unitary-image balanced commutator predicate at SU(d)**.

The algebraic content of the SU(d) balanced commutator theorem (Phase 6y S.3)
restricted to the rank-2 unitary-image case: for every `(i, j) ∈ Fin d`
with `i ≠ j` and every `U ∈ SU(d)`, the target `H = U · σ_z(i, j) · U*`
admits Hermitian-traceless F, G satisfying `F·G − G·F = −iθ·H` for any
`θ ∈ [0, 1]`.

This is the **predicate form** of the Session 14 ship; downstream consumers
needing the rank-2-unitary-image case (which covers ALL Hermitian-traceless
H with eigenvalue spectrum `(+1, -1, 0, ..., 0)`) can invoke this predicate
directly. The general arbitrary-rank case requires the Aharonov-Arad
counterterm construction (ships separately).

**Norm-bridging note**: the bound `‖F‖ ≤ √(θ/2)` is NOT included since the
linftyOp norm is not unitary-conjugation-invariant. With the d-dependent
norm-bridge `‖U·M·U*‖_linftyOp ≤ √d · ‖M‖_linftyOp`, a `√d`-loose
strengthening of this predicate is possible. -/
def BalancedCommutator_SUd_rank2_unitary_image (d : ℕ) : Prop :=
  ∀ (i j : Fin d) (_h_ne : i ≠ j)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (θ : ℝ) (_hθ_nn : 0 ≤ θ) (_hθ_le_one : θ ≤ 1),
    ∃ (F G : Matrix (Fin d) (Fin d) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧
      F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) •
        (U.val * sigmaZBlock i j * star U.val)

/-- **UNCONDITIONAL discharge of `BalancedCommutator_SUd_rank2_unitary_image d`**
for any `d : ℕ`.

Witness: `F := U·√(θ/2)·σ_y(i,j)·U*`, `G := U·√(θ/2)·σ_x(i,j)·U*`. The 5
conjuncts (Hermitian × 2, traceless × 2, commutator identity) discharge via
`balanced_commutator_unitary_image_sigmaZ_pattern_SUd_algebraic` (§1). -/
theorem BalancedCommutator_SUd_rank2_unitary_image_holds (d : ℕ) :
    BalancedCommutator_SUd_rank2_unitary_image d := by
  intro i j h_ne U θ hθ_nn hθ_le_one
  refine ⟨U.val * (((Real.sqrt (θ/2) : ℝ) : ℂ) • sigmaYBlock i j) * star U.val,
          U.val * (((Real.sqrt (θ/2) : ℝ) : ℂ) • sigmaXBlock i j) * star U.val, ?_⟩
  exact balanced_commutator_unitary_image_sigmaZ_pattern_SUd_algebraic h_ne U θ hθ_nn hθ_le_one

/-! ### Worked examples at d = 2, d = 4, d = 8 -/

/-- **Example**: `BalancedCommutator_SUd_rank2_unitary_image 2` holds
(single-qubit SU(2) baseline). -/
example : BalancedCommutator_SUd_rank2_unitary_image 2 :=
  BalancedCommutator_SUd_rank2_unitary_image_holds 2

/-- **Example**: `BalancedCommutator_SUd_rank2_unitary_image 4` holds
(two-qubit SU(4); Phase 6y T-A1′ target). -/
example : BalancedCommutator_SUd_rank2_unitary_image 4 :=
  BalancedCommutator_SUd_rank2_unitary_image_holds 4

/-- **Example**: `BalancedCommutator_SUd_rank2_unitary_image 8` holds
(three-qubit SU(8); Phase 6y T-A2′ target). -/
example : BalancedCommutator_SUd_rank2_unitary_image 8 :=
  BalancedCommutator_SUd_rank2_unitary_image_holds 8

end SKEFTHawking.FKLW.GenericSUd
