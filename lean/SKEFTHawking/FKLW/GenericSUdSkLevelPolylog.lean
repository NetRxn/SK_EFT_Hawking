/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) polylog-level chooser

The **SU(d) generic generalization of `skLevel_polylog`** (Phase 6u Wave 4
SU(2) `SolovayKitaevRecursion.skLevel_polylog`, specialized to
`K_compose = 1024`).

For SU(d) generic K and ε₀_sud parameters, defines the polylog level
chooser:

  `skLevel_polylog_sud K ε := ⌈log(log(1/(K²·ε)) / log 4) / log(3/2)⌉₊`

Plus the spec predicate `SkLevelPolylog_sud_spec K ε₀_sud` capturing the
substantive content `∀ ε ∈ (0, ε₀_sud], ε_seq K (2·ε₀_sud) (skLevel_polylog_sud K ε) ≤ ε`.

The substantive discharge of `SkLevelPolylog_sud_spec` (analog of SU(2)
~110-LoC `skLevel_polylog_spec`) ships in follow-on sessions; depends on
a calibration condition `K² · 2·ε₀_sud ≤ 1/4` (cf SU(2)
`K_compose² · 2·ε₀ = 1/4`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — SU(d) polylog level
chooser (3rd of 4 substantive ingredients enumerated in Session 45's
headline cascade).

-/

import Mathlib
import SKEFTHawking.FKLW.EpsilonSeq

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

/-! ## 1. The SU(d) polylog level chooser -/

/-- **The SU(d) polylog level chooser**: returns `n` such that
`ε_seq K (2·ε₀_sud) n ≤ ε` for ε in the valid range.

Defined as
  `⌈log(log(1/(K²·ε)) / log 4) / log(3/2)⌉₊`.

For the valid-range spec ε ∈ (0, ε₀_sud], the calibration condition
`K² · 2·ε₀_sud ≤ 1/4` (cf SU(2) `K_compose² · 2·ε₀ = 1/4`) ensures
`log(1/(K²·ε)) ≥ log 4`, hence the argument is well-defined.

Mirrors SU(2)'s `skLevel_polylog` definitionally; the only difference is
parameterization by `K` instead of the hard-coded `K_compose`. -/
noncomputable def skLevel_polylog_sud (K ε : ℝ) : ℕ :=
  ⌈Real.log (Real.log (1 / (K^2 * ε)) / Real.log 4) /
    Real.log (3 / 2)⌉₊

/-! ## 2. The spec predicate -/

/-- **The spec predicate for `skLevel_polylog_sud`**.

Captures `∀ ε > 0 ε ≤ ε₀_sud, ε_seq K (2·ε₀_sud) (skLevel_polylog_sud K ε) ≤ ε`.

Substantive discharge (analog of SU(2) `skLevel_polylog_spec` ~110-LoC
proof) requires the calibration condition `K² · 2·ε₀_sud ≤ 1/4` and the
ε_seq closed-form expression. Ships in follow-on sessions. -/
def SkLevelPolylog_sud_spec (K ε₀_sud : ℝ) : Prop :=
  ∀ (ε : ℝ), 0 < ε → ε ≤ ε₀_sud →
    SKEFTHawking.FKLW.EpsilonSeq.ε_seq K (2 * ε₀_sud)
      (skLevel_polylog_sud K ε) ≤ ε

end SKEFTHawking.FKLW.GenericSUd
