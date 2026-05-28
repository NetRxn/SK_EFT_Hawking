/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.4 — Clifford+CCZ SU(8) calibration constants

Calibration constants used in the Phase 6y T-A2′.5 strict headline form.
Mirrors `TrappedIonSU4Calibration.lean` at d=8.

## Constants

  * `cliffordCCZSU8_skLength_const : ℝ` — polylog length-bound constant.
  * `cliffordCCZSU8_skLength_exponent : ℝ` — Dawson-Nielsen `log 5 / log (3 / 2) ≈ 3.97`.
  * `cliffordCCZSU8_epsilonZero : ℝ` — maximum ε₀.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.4 (calibration).

-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

/-! ## 1. Calibration constants -/

/-- **Clifford+CCZ SU(8) polylog length-bound constant `c > 0`**. -/
def cliffordCCZSU8_skLength_const : ℝ := 20

theorem cliffordCCZSU8_skLength_const_pos : 0 < cliffordCCZSU8_skLength_const := by
  unfold cliffordCCZSU8_skLength_const; norm_num

/-- **The Dawson-Nielsen 2006 SK polylog exponent** `log 5 / log (3 / 2) ≈ 3.97`
(arXiv:quant-ph/0505030 §3.3: 5× word-length growth per level + ε^(3/2) error
contraction ⟹ `c = log 5 / log (3/2)`). -/
noncomputable def cliffordCCZSU8_skLength_exponent : ℝ := Real.log 5 / Real.log (3 / 2)

theorem cliffordCCZSU8_skLength_exponent_pos : 0 < cliffordCCZSU8_skLength_exponent := by
  unfold cliffordCCZSU8_skLength_exponent
  apply div_pos
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 5)
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)

/-- **Clifford+CCZ SU(8) ε₀ maximum**. -/
noncomputable def cliffordCCZSU8_epsilonZero : ℝ := 1 / 64

theorem cliffordCCZSU8_epsilonZero_pos : 0 < cliffordCCZSU8_epsilonZero := by
  unfold cliffordCCZSU8_epsilonZero; norm_num

theorem cliffordCCZSU8_epsilonZero_le_one : cliffordCCZSU8_epsilonZero ≤ 1 := by
  unfold cliffordCCZSU8_epsilonZero; norm_num

end SKEFTHawking.FKLW.CliffordCCZSU8
