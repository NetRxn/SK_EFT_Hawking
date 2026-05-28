/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness substrate — exp commutes with the per-ion embedding

Packages each per-ion Kronecker embedding `A ↦ kronSU4 A 1` (= `A ⊗ I`, ion 1) and
`B ↦ kronSU4 1 B` (= `I ⊗ B`, ion 2) as a **continuous `RingHom`** on the matrix algebras, and
applies Mathlib's `map_exp` (continuous ring homs commute with `NormedSpace.exp`) to obtain

  `kronSU4 (exp X) 1 = exp (kronSU4 X 1)`   and   `kronSU4 1 (exp X) = exp (kronSU4 1 X)`.

Consequence (used by the witness `hX_flow`): for a per-ion 𝔰𝔲(2) tangent `x` (skew-Hermitian,
traceless), the SU(4) one-parameter subgroup is `exp(t • kronSU4 x 1) = kronSU4 (exp (t•x)) 1`,
the embedded image of the SU(2) one-parameter subgroup — which lands in `H_of_G(trappedIon)` by
the per-ion containment.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness substrate
(exp/embedding commute → per-ion tangent flow lines). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4IonEmbed

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Additive / zero structure of `kronSU4 · 1` and `kronSU4 1 ·` -/

theorem kronSU4_zero_right_one : kronSU4 (0 : Matrix (Fin 2) (Fin 2) ℂ) 1 = 0 := by
  have h : Matrix.kronecker (0 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 :=
    Matrix.zero_kronecker 1
  unfold kronSU4; rw [h]; simp

theorem kronSU4_add_right_one (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4 (A + B) 1 = kronSU4 A 1 + kronSU4 B 1 := by
  have h : Matrix.kronecker (A + B) (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.kronecker A 1 + Matrix.kronecker B 1 := Matrix.add_kronecker A B 1
  unfold kronSU4; rw [h]; ext i j; simp [Matrix.submatrix_apply]

theorem kronSU4_zero_left_one : kronSU4 (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 = 0 := by
  have h : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 :=
    Matrix.kronecker_zero 1
  unfold kronSU4; rw [h]; simp

theorem kronSU4_add_left_one (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4 1 (A + B) = kronSU4 1 A + kronSU4 1 B := by
  have h : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (A + B) =
      Matrix.kronecker 1 A + Matrix.kronecker 1 B := Matrix.kronecker_add 1 A B
  unfold kronSU4; rw [h]; ext i j; simp [Matrix.submatrix_apply]

/-! ## 2. Per-ion embeddings as `RingHom`s on the matrix algebras -/

/-- The ion-1 matrix embedding `A ↦ kronSU4 A 1` (= `A ⊗ I`) as a `RingHom`. -/
noncomputable def ion1MatRingHom :
    Matrix (Fin 2) (Fin 2) ℂ →+* Matrix (Fin 4) (Fin 4) ℂ where
  toFun A := kronSU4 A 1
  map_one' := kronSU4_one
  map_mul' := kronSU4_ion1_mul
  map_zero' := kronSU4_zero_right_one
  map_add' := kronSU4_add_right_one

/-- The ion-2 matrix embedding `B ↦ kronSU4 1 B` (= `I ⊗ B`) as a `RingHom`. -/
noncomputable def ion2MatRingHom :
    Matrix (Fin 2) (Fin 2) ℂ →+* Matrix (Fin 4) (Fin 4) ℂ where
  toFun B := kronSU4 1 B
  map_one' := kronSU4_one
  map_mul' := kronSU4_ion2_mul
  map_zero' := kronSU4_zero_left_one
  map_add' := kronSU4_add_left_one

/-! ## 3. exp/embedding commute -/

/-- **exp commutes with the ion-1 embedding**: `kronSU4 (exp X) 1 = exp (kronSU4 X 1)`. -/
theorem kronSU4_exp_right_one (X : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4 (NormedSpace.exp X) 1 = NormedSpace.exp (kronSU4 X 1) :=
  NormedSpace.map_exp ion1MatRingHom continuous_kronSU4_right_one X

/-- **exp commutes with the ion-2 embedding**: `kronSU4 1 (exp X) = exp (kronSU4 1 X)`. -/
theorem kronSU4_exp_left_one (X : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU4 1 (NormedSpace.exp X) = NormedSpace.exp (kronSU4 1 X) :=
  NormedSpace.map_exp ion2MatRingHom continuous_kronSU4_left_one X

end SKEFTHawking.FKLW.TrappedIonSU4
