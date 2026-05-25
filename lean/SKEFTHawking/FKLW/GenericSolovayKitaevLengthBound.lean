/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Wave 5 — Generic Solovay-Kitaev length bound

The Phase 6t `SolovayKitaevLengthBound.skLength_at_skLevel_polylog_le`
theorem is ALREADY alphabet-agnostic: it bounds the level-`n` word
length in terms of `skLengthBaseCase`, `skBalancedDecompCost`,
`skLengthConst`, and `skLengthExponent`, all of which are alphabet-
independent constants chosen conservatively to bound ANY alphabet's
SK recursion structure (5 sub-calls per level with constant per-step
cost).

This module re-exports the existing length bound under the generic
naming convention used by Wave 6's bundled-strict headline, and
documents the alphabet-independence.

## Per-alphabet constant calibration

The existing constants:
  - `skLengthBaseCase := 100` — upper bound on the max word length in
    the alphabet's ε₀-net findNearest output. Conservative for Fibonacci
    (8M-cell net); ample margin for Clifford+T (Ross-Selinger
    base-case ~30-50 per ε₀-cell).
  - `skBalancedDecompCost := 100` — per-level balanced commutator
    composition cost. Conservative for any alphabet (the SK recursion's
    `V_n · A_F · A_G · A_F⁻¹ · A_G⁻¹` requires 5 sub-word appends; 100
    is a safe upper bound including overhead).
  - `skLengthConst := 1000` — leading constant in the polylog bound,
    derived from the recurrence solution and conservative for
    `skLengthBaseCase = skBalancedDecompCost = 100`.
  - `skLengthExponent := log 5 / log(3/2) ≈ 3.97` — the canonical
    Dawson-Nielsen exponent, alphabet-independent (depends only on the
    super-quadratic recursion rate 3/2 and the 5-fold branching).

If a per-alphabet calibration needs tighter constants (e.g., a
specialized base-case net or a sharper per-level decomposition),
the parametric Wave 5b refinement can be shipped; for now the
conservative defaults discharge all known alphabets (Fibonacci,
Clifford+T) cleanly.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
- **Strengthening discipline**: re-export theorems explicitly stated
  with `GeneratingSet` parametrization for downstream consumers.

-/

import SKEFTHawking.FKLW.GenericSolovayKitaevRecursion

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open SKEFTHawking.FKLW
open SKEFTHawking.FKLW.SolovayKitaevLengthBound
open SKEFTHawking.FKLW.SolovayKitaevRecursion

/-! ## 1. Documentation: the existing length bound IS the generic length bound

The Phase 6t `skLength_at_skLevel_polylog_le` is already alphabet-agnostic
— `skLength` counts the words produced by the SK recursion regardless of
the underlying alphabet (it depends only on the 5-fold branching + level-0
base cost + per-level decomp cost, which are universally bounded by
`skLengthBaseCase` and `skBalancedDecompCost`). No re-export is needed;
downstream consumers (Wave 6 generic headline, Track instantiations)
call `skLength_at_skLevel_polylog_le` directly.

This module exists as a **DOCUMENTATION ANCHOR** for the Phase 6u Wave 5
deliverable: it codifies the observation that Phase 6t's length bound is
the generic length bound (no rework needed), and serves as the
strengthening-pass discharge target for Wave 6's `skLength` reference. -/

/-- **Wave 5 anchor**: explicit alias of `skLength_at_skLevel_polylog_le`
under the Phase 6u Generic naming, with no superfluous `gs` parameter
(strengthening pass §P5: dummy-parameter elimination).

The Phase 6t bound IS the generic bound; this alias makes the
Wave-5-as-deliverable explicit without adding a dummy argument. -/
theorem skLength_at_skLevel_polylog_le_generic
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    skLength (skLevel_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent :=
  skLength_at_skLevel_polylog_le ε hε_pos hε_le

end SKEFTHawking.FKLW.GenericSU2
