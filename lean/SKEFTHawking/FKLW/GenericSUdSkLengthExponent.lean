/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Canonical SU(d) Solovay-Kitaev word-length exponent

Defines the SU(d) Solovay-Kitaev word-length exponent used by the
length-bound discharge and by the trapped-ion and Clifford+CCZ calibration
aliases. Some headline statements spell out the same logarithm ratio.

## The value

`skLengthExponent_sud := Real.log 5 / Real.log (3 / 2) ≈ 3.97` — the canonical
Dawson-Nielsen exponent (Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006),
81–95). The author preprint arXiv:quant-ph/0505030v2 gives the length bound
in §3 (Analysis), Eq. (8), p. 7, and extends it to fixed dimension in §5.1,
p. 11, with dimension-dependent constants and base lookup construction cost.
It arises from 5× word-length growth per level and superlinear error contraction
of order 3/2. The project's `SkApproxCSuperQuadraticBound_generic_sud_concrete_holds`
proves the error bound. Up to the base constants and integer rounding of the
depth, `n(ε) = log_{3/2} log(1/ε)` and `L(ε) = 5^{n(ε)} = (log(1/ε))^{log 5 / log(3/2)}`.
Equation (9) gives the separate classical runtime exponent `log 3 / log(3/2) ≈ 2.71`
when pointers are used to reuse subsequences, excluding finite-precision costs.

This exponent is definitionally equal to the SU(2) substrate's
`SKEFTHawking.FKLW.SolovayKitaevLengthBound.skLengthExponent` because the two
definitions use the same real logarithm ratio. The level chooser
`skLevel_polylog_sud` uses the denominator `Real.log (3 / 2)` to set the
recursion depth.

## Provenance note (2026-05-28)

A 2026-05-27 first-pass ship (commit 866396e) hardcoded this exponent as
`Real.log 5 / Real.log 2 ≈ 2.32` in the SU(d) headline forms, mis-attributing it
to Dawson-Nielsen. That value is unachievable for the project's ε^(3/2)
recursion (it would require quadratic ε² contraction, which is not proven). The
value was corrected project-wide and this module was introduced to provide
a named exponent for the SU(d) length bounds.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

/-- **The canonical SU(d) Solovay-Kitaev word-length polylog exponent**
`log 5 / log (3 / 2) ≈ 3.97` (Dawson-Nielsen, arXiv:quant-ph/0505030v2,
§3 (Analysis), Eq. (8), p. 7 and §5.1, p. 11). It comes from 5× word-length
growth per level and order-3/2 error contraction. The trapped-ion and
Clifford+CCZ calibration aliases use this definition. It is definitionally
equal to the SU(2) `SolovayKitaevLengthBound.skLengthExponent`. -/
noncomputable def skLengthExponent_sud : ℝ := Real.log 5 / Real.log (3 / 2)

/-- The canonical SU(d) SK length exponent is positive (`log 5 > 0`, `log (3/2) > 0`). -/
lemma skLengthExponent_sud_pos : 0 < skLengthExponent_sud := by
  unfold skLengthExponent_sud
  apply div_pos
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 5)
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)

end SKEFTHawking.FKLW.GenericSUd
