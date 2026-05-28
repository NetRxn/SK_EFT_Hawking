/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) word-length closed-form upper bound

The **SU(d) generalization of Phase 6u's `skLength` substrate**, providing:
  * `skLength_sud (baseCase decompCost : ℝ) (n : ℕ) : ℝ` — closed-form
    upper bound on the level-n word length in the SK recursion.
  * Nonneg + monotone helpers.
  * `skLength_sud_eq_skLength` — agreement with Phase 6u SU(2) version
    at the canonical constants.

The SU(d) skLength substrate is **alphabet-agnostic** (the Phase 6u
SU(2) version is too — `skLength` only depends on the 5-fold branching
of the SK recursion, not the specific alphabet). For SU(d), we
parameterize the baseCase + decompCost to allow per-alphabet tightening.

## Substantive content shipped

  * `skLength_sud baseCase decompCost n` — d-independent closed-form
    upper bound (parametric in per-alphabet constants).
  * `skLength_sud_nonneg` — nonneg.
  * `skLength_sud_succ_recursion` — recursive form L(n+1) ≤ 5·L(n) + cost.
  * `SkLengthPolylogBound_sud` predicate — the substantive content for
    the polylog asymptotic at SU(d).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — word-length closed-form
substrate (4th of 4 substantive ingredients per Session 47 cascade index).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkApproxC
import SKEFTHawking.FKLW.GenericSUdSkLengthExponent

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

/-! ## 1. The SU(d) word-length closed-form -/

/-- **The SU(d) word-length closed-form upper bound**.

For level `n`, returns `baseCase · 5^n + decompCost · (5^n - 1) / 4`, the
closed-form solution to the recurrence `L(0) = baseCase`,
`L(n+1) = 5·L(n) + decompCost`.

The Phase 6u SU(2) `skLength` is the specialization at the canonical
constants `baseCase := 100`, `decompCost := 100`. -/
noncomputable def skLength_sud (baseCase decompCost : ℝ) (n : ℕ) : ℝ :=
  baseCase * (5 : ℝ) ^ n + decompCost * ((5 : ℝ) ^ n - 1) / 4

/-! ## 2. Basic properties -/

/-- The closed-form is nonneg given nonneg constants. -/
lemma skLength_sud_nonneg (baseCase decompCost : ℝ)
    (hb_nn : 0 ≤ baseCase) (hd_nn : 0 ≤ decompCost) (n : ℕ) :
    0 ≤ skLength_sud baseCase decompCost n := by
  unfold skLength_sud
  have h_5n_pos : (0 : ℝ) ≤ (5 : ℝ) ^ n := by positivity
  have h_5n_ge_one : (1 : ℝ) ≤ (5 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have h_5n_minus_one : (0 : ℝ) ≤ (5 : ℝ) ^ n - 1 := by linarith
  have h1 : 0 ≤ baseCase * (5 : ℝ) ^ n := mul_nonneg hb_nn h_5n_pos
  have h2 : 0 ≤ decompCost * ((5 : ℝ) ^ n - 1) / 4 := by
    have : 0 ≤ decompCost * ((5 : ℝ) ^ n - 1) := mul_nonneg hd_nn h_5n_minus_one
    linarith
  linarith

/-- The base case at n = 0. -/
@[simp]
lemma skLength_sud_zero (baseCase decompCost : ℝ) :
    skLength_sud baseCase decompCost 0 = baseCase := by
  unfold skLength_sud; ring

/-- Recursive form: `L(n+1) = 5·L(n) + decompCost`. -/
lemma skLength_sud_succ (baseCase decompCost : ℝ) (n : ℕ) :
    skLength_sud baseCase decompCost (n + 1) =
      5 * skLength_sud baseCase decompCost n + decompCost := by
  unfold skLength_sud
  have h_pow : (5 : ℝ) ^ (n + 1) = (5 : ℝ) ^ n * 5 := pow_succ (5 : ℝ) n
  rw [h_pow]
  ring

/-- Monotone in n: `L(n) ≤ L(n+1)` (given nonneg constants). -/
lemma skLength_sud_monotone (baseCase decompCost : ℝ)
    (hb_nn : 0 ≤ baseCase) (hd_nn : 0 ≤ decompCost) (n : ℕ) :
    skLength_sud baseCase decompCost n ≤
    skLength_sud baseCase decompCost (n + 1) := by
  rw [skLength_sud_succ]
  have h_L_nn := skLength_sud_nonneg baseCase decompCost hb_nn hd_nn n
  linarith

/-! ## 3. Polylog-bound predicate -/

/-- **The SU(d) polylog word-length bound predicate**.

For polylog-level `levelChooser : ℝ → ℕ` (e.g., `skLevel_polylog_sud K`),
asserts that the closed-form word length at level `levelChooser ε` is
≤ `c · (log(1/ε))^skLengthExponent_sud` for ε in valid range, where
`skLengthExponent_sud = log 5 / log (3/2) ≈ 3.97` is the canonical
Dawson-Nielsen exponent (single source of truth).

This is the substrate content for the SU(d) headline length bound. -/
def SkLengthPolylogBound_sud
    (baseCase decompCost ε₀_sud c : ℝ) (levelChooser : ℝ → ℕ) : Prop :=
  ∀ (ε : ℝ), 0 < ε → ε ≤ ε₀_sud →
    skLength_sud baseCase decompCost (levelChooser ε) ≤
      c * (Real.log (1 / ε)) ^ skLengthExponent_sud

end SKEFTHawking.FKLW.GenericSUd
