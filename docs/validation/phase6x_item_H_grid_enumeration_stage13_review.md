# Phase 6x Item H — Ross-Selinger upright grid enumeration — Stage 13 review

**Date:** 2026-05-30  **Verdict:** ✅ **GREEN** (0 findings at any severity)
**Reviewer:** fresh-context adversarial agent (read-only), per Wave Execution Pipeline Stage 13.

## Scope reviewed

`lean/SKEFTHawking/FKLW/RossSelinger/GridEnum.lean` + `scripts/grid_enum_pygridsynth_xval.py`
(commit `01e0653`) — the Ross-Selinger 2014 §5 Thm 2 upright grid enumeration (the combinatorial
grid solver): `gridSolutions1D`/`_mem_iff`/`_card_le` (1-D), `gridSolutions2D`/`_mem_iff`/`_card`
(the `ℤ[ω]=ℤ[√2][i]` product), and the pygridsynth `solve_ODGP` cross-validation harness.

## Findings: NONE

1. **`gridSolutions1D_mem_iff` is a genuine two-directional soundness AND completeness equivalence.**
   The four `div_le_iff₀`/`le_div_iff₀` + `nlinarith` bridges (hA–hD) are math-verified; the
   `Int.ceil_le`/`Int.le_floor`/`max_le_iff`/`le_min_iff` chain (`hn`) unpacks the `n`-range into
   exactly the four real bounds (`tauto` is a pure reordering, no conjunct dropped); the soundness
   `→` uses only the `n`-range (m-range correctly derived); the completeness `←` genuinely derives
   BOTH the `m`-range (from `lo+lo' ≤ 2m ≤ hi+hi'` by addition `nlinarith`) and the `n`-range.
   Non-vacuous (4851 solutions across the xval suite).
2. **`gridSolutions1D_card_le`** is a real `O(width·width')`-style bound (`card_biUnion_le` +
   per-`m` `card_image_le`), not vacuous.
3. **2-D solver** `gridSolutions2D`/`_mem_iff`/`_card`: the correct `×ˢ` product of two 1-D solves;
   `_mem_iff` = `Finset.mem_product` + two 1-D mem_iffs = the genuine conjunction of the real-part
   and imaginary-part 1-D grid problems.
4. **Axiom hygiene**: `lean_verify` on all three headline theorems returns exactly `{propext,
   Classical.choice, Quot.sound}` — no `native_decide`, no `sorryAx`, no new axiom; no `sorry`/
   `maxHeartbeats`/`axiom` in source. Invariants #10, #15 respected.
5. **pygridsynth cross-val methodology**: ran clean (**180/180 boxes, 4851 solutions, exact set
   match**). The Python `lean_grid1d` is a faithful verbatim port of the Lean enumeration; the
   reference `solve_ODGP(I,J)` is genuinely the same 1-D grid problem (exact mpmath arithmetic,
   matching coordinate + closed-interval conventions); the comparison is **set equality** (catches
   spurious AND missing); boxes are non-degenerate (179/180 non-empty). The reviewer's own
   **mutation test** (floor↔ceil swap on the `n`-lower bound) mismatched all 180 boxes — the
   `assert n_match == n_total` provably discriminates correct from incorrect enumeration (not a no-op).
6. **Honest-scope framing**: docstrings correctly scope to the UPRIGHT case and explicitly defer the
   Step-operator `O(log(1/M))`-per-solution refinement and general-convex regions; no overclaim.
7. **Compile gate / private leaks**: `lean_diagnostic_messages` zero items; `GridEnum` imported into
   the library root; no private-repo identifiers in either file.

## Disposition

GREEN — ship as-is. `gridSolutions1D_mem_iff` is a genuine sound-and-complete equivalence
(independently math-verified), kernel-pure, zero-sorry, no heartbeat overrides; the pygridsynth
cross-validation is a real, independent (exact-arithmetic) corroboration over a non-vacuous suite
with set-equality matching and a provably-discriminating pass assertion. Build clean (8988 jobs);
counts 9797 theorems / 0 axioms / 0 sorry / 739 modules; `axiom_closure_allowlist` + `counts_fresh`
+ `graph_integrity` PASS.
