/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Canonical SU(d) Solovay-Kitaev word-length exponent

Single source of truth for the SU(d) Solovay-Kitaev word-length polylog
exponent, so the value cannot drift across the (many) headline / cascade /
calibration modules that reference it.

## The value

`skLengthExponent_sud := Real.log 5 / Real.log (3 / 2) ≈ 3.97` — the canonical
Dawson-Nielsen exponent (Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006),
81–95; arXiv:quant-ph/0505030, §3.3). It arises from solving the joint SK
recursion:
  * length recurrence `L(n+1) = 5 · L(n)` (5× word-length growth per level), and
  * error recurrence `ε(n+1) = ε(n)^(3/2)` (the super-quadratic contraction the
    project's `SkApproxCSuperQuadraticBound_generic_sud_concrete_holds` proves),
giving `n(ε) = log_{3/2} log(1/ε)` and `L(ε) = 5^{n(ε)} = (log(1/ε))^{log 5 / log(3/2)}`.

This is **definitionally equal** to the SU(2) substrate's
`SKEFTHawking.FKLW.SolovayKitaevLengthBound.skLengthExponent` (same literal),
to the base used by the level chooser `skLevel_polylog_sud` (`Real.log (3 / 2)`),
and to the value stated in the public README and the Phase 6u roadmap.

## Provenance note (2026-05-28)

A 2026-05-27 first-pass ship (commit 866396e) hardcoded this exponent as
`Real.log 5 / Real.log 2 ≈ 2.32` in the SU(d) headline forms, mis-attributing it
to Dawson-Nielsen. That value is unachievable for the project's ε^(3/2)
recursion (it would require quadratic ε² contraction, which is not proven). The
value was corrected project-wide and this module was introduced so every SU(d)
SK length-exponent reference resolves to one definition.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

/-- **The canonical SU(d) Solovay-Kitaev word-length polylog exponent**
`log 5 / log (3 / 2) ≈ 3.97` (Dawson-Nielsen 2006, arXiv:quant-ph/0505030 §3.3):
5× word-length growth per level + ε^(3/2) error contraction. Single source of
truth — all SU(d) headline / cascade / calibration modules reference this
definition so the value cannot drift. Definitionally equal to the SU(2)
`SolovayKitaevLengthBound.skLengthExponent`. -/
noncomputable def skLengthExponent_sud : ℝ := Real.log 5 / Real.log (3 / 2)

/-- The canonical SU(d) SK length exponent is positive (`log 5 > 0`, `log (3/2) > 0`). -/
lemma skLengthExponent_sud_pos : 0 < skLengthExponent_sud := by
  unfold skLengthExponent_sud
  apply div_pos
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 5)
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)

end SKEFTHawking.FKLW.GenericSUd
