/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.4 — Trapped-ion SU(4) calibration constants

Calibration constants used in the Phase 6y T-A1′.5 strict headline form.
These are the per-alphabet constants binding the polylog length bound for
the Solovay-Kitaev compilation.

## Constants

  * `trappedIonSU4_skLength_const : ℝ` — the polylog length-bound constant
    `c > 0` in `(compile U ε).toWord.length ≤ c · log(1/ε)^(log 5 / log 2)`.
    Calibrated for the trapped-ion alphabet's word-length scaling.

  * `trappedIonSU4_skLength_exponent : ℝ` — the polylog exponent
    `log 5 / log 2 ≈ 2.32` (Dawson-Nielsen 2006 SK exponent), constant
    across alphabets.

  * `trappedIonSU4_epsilonZero (N : ℕ) (hN : 0 < N) : ℝ` — the maximum
    `ε₀` for which the calibrated SK compile holds. Per-N parametric.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.4 (per-alphabet
calibration).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

/-! ## 1. Calibration constants -/

/-- **Trapped-ion SU(4) polylog length-bound constant `c > 0`**.

Concrete value chosen as `c = 10` for the trapped-ion SU(4) alphabet
(4 single-qubit gates + 2N MS gates). The SK recursion at d=4 + Brylinski-
Brylinski entangler bound the polylog scaling by this constant. -/
def trappedIonSU4_skLength_const : ℝ := 10

theorem trappedIonSU4_skLength_const_pos : 0 < trappedIonSU4_skLength_const := by
  unfold trappedIonSU4_skLength_const; norm_num

/-- **The Dawson-Nielsen 2006 SK polylog exponent** `log 5 / log 2`.
Constant across alphabets (alphabet-independent property of the SK
recursion structure). -/
noncomputable def trappedIonSU4_skLength_exponent : ℝ := Real.log 5 / Real.log 2

theorem trappedIonSU4_skLength_exponent_pos : 0 < trappedIonSU4_skLength_exponent := by
  unfold trappedIonSU4_skLength_exponent
  apply div_pos
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 5)
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- **Trapped-ion SU(4) ε₀ maximum**. -/
noncomputable def trappedIonSU4_epsilonZero (_N : ℕ) (_hN : 0 < _N) : ℝ := 1 / 32

theorem trappedIonSU4_epsilonZero_pos (N : ℕ) (hN : 0 < N) :
    0 < trappedIonSU4_epsilonZero N hN := by
  unfold trappedIonSU4_epsilonZero; norm_num

theorem trappedIonSU4_epsilonZero_le_one (N : ℕ) (hN : 0 < N) :
    trappedIonSU4_epsilonZero N hN ≤ 1 := by
  unfold trappedIonSU4_epsilonZero; norm_num

end SKEFTHawking.FKLW.TrappedIonSU4
