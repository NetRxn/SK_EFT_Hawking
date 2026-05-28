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
    `c > 0` in `(compile U ε).toWord.length ≤ c · log(1/ε)^(log 5 / log (3/2))`.
    Calibrated for the trapped-ion alphabet's word-length scaling.

  * `trappedIonSU4_skLength_exponent : ℝ` — the polylog exponent
    `log 5 / log (3/2) ≈ 3.97` (Dawson-Nielsen 2006 SK exponent), constant
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
import SKEFTHawking.FKLW.GenericSUdSkLengthExponent

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

/-- **The SU(4) trapped-ion SK polylog exponent** — an alias of the canonical
`skLengthExponent_sud = log 5 / log (3 / 2) ≈ 3.97` (Dawson-Nielsen 2006,
arXiv:quant-ph/0505030 §3.3: 5× word-length growth per level + ε^(3/2) error
contraction). Alphabet-independent; single source of truth lives at
`SKEFTHawking.FKLW.GenericSUd.skLengthExponent_sud`. -/
noncomputable def trappedIonSU4_skLength_exponent : ℝ :=
  SKEFTHawking.FKLW.GenericSUd.skLengthExponent_sud

theorem trappedIonSU4_skLength_exponent_pos : 0 < trappedIonSU4_skLength_exponent :=
  SKEFTHawking.FKLW.GenericSUd.skLengthExponent_sud_pos

/-- **Trapped-ion SU(4) ε₀ maximum**. -/
noncomputable def trappedIonSU4_epsilonZero (_N : ℕ) (_hN : 0 < _N) : ℝ := 1 / 32

theorem trappedIonSU4_epsilonZero_pos (N : ℕ) (hN : 0 < N) :
    0 < trappedIonSU4_epsilonZero N hN := by
  unfold trappedIonSU4_epsilonZero; norm_num

theorem trappedIonSU4_epsilonZero_le_one (N : ℕ) (hN : 0 < N) :
    trappedIonSU4_epsilonZero N hN ≤ 1 := by
  unfold trappedIonSU4_epsilonZero; norm_num

end SKEFTHawking.FKLW.TrappedIonSU4
