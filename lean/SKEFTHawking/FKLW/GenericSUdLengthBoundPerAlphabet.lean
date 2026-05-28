/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Per-alphabet length-bound specializations at SU(4) + SU(8)

Applies Session 53's parametric SU(d) length-bound framework
(`skApproxC_generic_sud_length_le_skLength_sud_param`) to the per-alphabet
generating sets at SU(4) (trapped-ion) and SU(8) (Clifford+CCZ).

Instantiates `WordLengthFreeGroupLike` for each per-alphabet GS via
Mathlib's `FreeGroup.norm_mul_le` + `FreeGroup.norm_inv_eq`, exposing
the per-alphabet wordLength = `(h_eq ▸ w : FreeGroup α).toWord.length`.

## Substantive content shipped

  * `freeGroup_wordLength_su4` — wordLength function for trapped-ion SU(4)
  * `freeGroup_wordLength_su4_isFreeGroupLike` — submultiplicativity bundle
  * `freeGroup_wordLength_su8` — wordLength function for Clifford+CCZ SU(8)
  * `freeGroup_wordLength_su8_isFreeGroupLike` — submultiplicativity bundle
  * Per-alphabet length-bound theorems wrapping
    `skApproxC_generic_sud_length_le_skLength_sud_param`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track T-A1′" + §"Track T-A2′" — per-alphabet length-bound
specializations (substrate for the T-X.5 F#4-compliant headlines).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdConcreteWordLengthBound
import SKEFTHawking.FKLW.TrappedIonGeneratingSetSU4Full
import SKEFTHawking.FKLW.CliffordCCZGeneratingSetSU8Full
import Mathlib.GroupTheory.FreeGroup.Reduce

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Trapped-ion SU(4) instantiation -/

/-- **Word-length function for trapped-ion SU(4)**: since
`(trappedIonGeneratingSetSU4 N hN).W = FreeGroup (Fin (4 + 2*N))`
definitionally (`rfl`), this is just `toWord.length`. -/
noncomputable def freeGroup_wordLength_su4 (N : ℕ) (hN : 0 < N) :
    (SKEFTHawking.FKLW.TrappedIonSU4.trappedIonGeneratingSetSU4 N hN).W → ℕ :=
  fun w => (w : FreeGroup (Fin (4 + 2 * N))).toWord.length

/-- **Submultiplicativity bundle for trapped-ion SU(4) wordLength**.

Via Mathlib's `FreeGroup.norm_mul_le` + `FreeGroup.norm_inv_eq`. The
underlying word type is definitionally `FreeGroup (Fin (4 + 2*N))`. -/
theorem freeGroup_wordLength_su4_isFreeGroupLike (N : ℕ) (hN : 0 < N) :
    WordLengthFreeGroupLike
      (SKEFTHawking.FKLW.TrappedIonSU4.trappedIonGeneratingSetSU4 N hN)
      (freeGroup_wordLength_su4 N hN) where
  mul_le := fun w₁ w₂ => FreeGroup.norm_mul_le _ _
  inv_eq := fun w => FreeGroup.norm_inv_eq

/-! ## 2. Clifford+CCZ SU(8) instantiation -/

/-- **Word-length function for Clifford+CCZ SU(8)**: since
`cliffordCCZGeneratingSetSU8.W = FreeGroup (Fin 10)` definitionally,
this is just `toWord.length`. -/
noncomputable def freeGroup_wordLength_su8 :
    (SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZGeneratingSetSU8).W → ℕ :=
  fun w => (w : FreeGroup (Fin 10)).toWord.length

/-- **Submultiplicativity bundle for Clifford+CCZ SU(8) wordLength**. -/
theorem freeGroup_wordLength_su8_isFreeGroupLike :
    WordLengthFreeGroupLike
      SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZGeneratingSetSU8
      freeGroup_wordLength_su8 where
  mul_le := by
    intro w₁ w₂
    unfold freeGroup_wordLength_su8
    exact FreeGroup.norm_mul_le _ _
  inv_eq := by
    intro w
    unfold freeGroup_wordLength_su8
    exact FreeGroup.norm_inv_eq

/-! ## 3. Per-alphabet length-bound theorems -/

/-- **Length-bound theorem for trapped-ion SU(4)** (per-alphabet wrapper).

Given a length-bounded base finder `baseFinder` (satisfying
`BaseFinder_length_bounded_sud_param N₀ freeGroup_wordLength_su4 baseFinder`),
the level-n SU(4) Dawson-Nielsen output has FreeGroup word-length bounded
by `skLength_sud N₀ 0 n`. -/
theorem trappedIonSU4_length_le_skLength_sud (N : ℕ) (hN : 0 < N)
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ) →
      (SKEFTHawking.FKLW.TrappedIonSU4.trappedIonGeneratingSetSU4 N hN).W)
    (h_det_pred : ExpIsud_det_eq_one_predicate 4)
    (N₀ : ℝ) (hN₀_nn : 0 ≤ N₀)
    (h_bf_length : BaseFinder_length_bounded_sud_param N₀
      (freeGroup_wordLength_su4 N hN) baseFinder)
    (n_lvl : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin 4) ℂ)) :
    (freeGroup_wordLength_su4 N hN
        (skApproxC_generic_sud
          (SKEFTHawking.FKLW.TrappedIonSU4.trappedIonGeneratingSetSU4 N hN)
          baseFinder h_det_pred n_lvl U) : ℝ) ≤
      skLength_sud N₀ 0 n_lvl :=
  skApproxC_generic_sud_length_le_skLength_sud_param
    (SKEFTHawking.FKLW.TrappedIonSU4.trappedIonGeneratingSetSU4 N hN)
    (freeGroup_wordLength_su4 N hN)
    (freeGroup_wordLength_su4_isFreeGroupLike N hN)
    baseFinder h_det_pred N₀ hN₀_nn h_bf_length n_lvl U

/-- **Length-bound theorem for Clifford+CCZ SU(8)** (per-alphabet wrapper). -/
theorem cliffordCCZSU8_length_le_skLength_sud
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) →
      (SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZGeneratingSetSU8).W)
    (h_det_pred : ExpIsud_det_eq_one_predicate 8)
    (N₀ : ℝ) (hN₀_nn : 0 ≤ N₀)
    (h_bf_length : BaseFinder_length_bounded_sud_param N₀
      freeGroup_wordLength_su8 baseFinder)
    (n_lvl : ℕ) (U : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
    (freeGroup_wordLength_su8
        (skApproxC_generic_sud
          SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZGeneratingSetSU8
          baseFinder h_det_pred n_lvl U) : ℝ) ≤
      skLength_sud N₀ 0 n_lvl :=
  skApproxC_generic_sud_length_le_skLength_sud_param
    SKEFTHawking.FKLW.CliffordCCZSU8.cliffordCCZGeneratingSetSU8
    freeGroup_wordLength_su8
    freeGroup_wordLength_su8_isFreeGroupLike
    baseFinder h_det_pred N₀ hN₀_nn h_bf_length n_lvl U

end SKEFTHawking.FKLW.GenericSUd
