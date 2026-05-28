/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.6 — Generic SU(d) bundled-strict headline form

The **target shape** of Phase 6y's generic SU(d) Solovay-Kitaev
quantitative headline. The full UNCONDITIONAL form requires composing
the Phase 6y S.2 chain (S.2f Trotter sum + S.2g final discharge) +
S.3 (dnStepFG_sud) + S.4 (Y_h Lipschitz d-dependent) + S.5 (generic
SU(d) discharge); this module ships the **statement form** as a
predicate that downstream consumers can dispatch via closure-density
witnesses + the future S.2g unconditional discharge.

The headline includes BOTH conjuncts mandated by the Phase 6x M.4
inheritance discipline (failure-mode-#4 guardrail):
  * **Error bound**: `‖compile U ε - U‖ ≤ ε`
  * **Concrete word-length conjunct**: `(compile U ε).toWord.length ≤ <polylog>`

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 (headline statement).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdClosureDenseWitness

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The Phase 6y S.6 generic bundled-strict headline shape

For a `GeneratingSet d` with closure-density witness, the Phase 6y
Solovay-Kitaev compilation provides a quantitative density predicate:

  `∀ U ∈ SU(d), ∀ ε ∈ (0, ε₀], ∃ word ∈ gs.W,
      ‖(gs.ρ_hom word).val - U.val‖ ≤ ε ∧
      word.toWord.length ≤ polylog (1 / ε)`

The "polylog" bound has the standard form
`c · (log (1/ε)) ^ (log 5 / log (3/2))` with the canonical Dawson-Nielsen
exponent `log 5 / log (3/2) ≈ 3.97` (arXiv:quant-ph/0505030 §3.3).

This module ships the **predicate** `SolovayKitaevHeadline_SUd` capturing
this shape; the substantive discharge ships via composition with S.2g
+ S.3 + S.5 in follow-up commits. -/

/-- **The Phase 6y S.6 generic bundled-strict headline predicate**.

For a `GeneratingSet d gs`, asserts that the alphabet admits a
SK-style compilation `compile : ↥SU(d) → ℝ → gs.W` such that for any
target `U ∈ SU(d)` and any precision `ε ∈ (0, ε₀]`:
  * error bound: `‖(gs.ρ_hom (compile U ε)).val - U.val‖ ≤ ε`
  * word-length bound: `(compile U ε).toWord.length ≤ polylog_bound ε`

where `polylog_bound ε := c · (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))`
for some constant `c > 0` (Dawson-Nielsen 2006 exponent).

For `gs.W = FreeGroup α`, `word.toWord.length` is the abstract free-group
word length (`FreeGroup.toWord` then `List.length`).

When `gs.W` is a `FreeGroup`, this matches Phase 6x M.4's M.4-inheritance
form (error + concrete word-length, both at the SAME algorithmic compile
level). -/
def SolovayKitaevHeadline_FreeGroup_SUd {d : ℕ} {α : Type} [DecidableEq α]
    (gs : GeneratingSet d) (h_eq : gs.W = FreeGroup α) : Prop :=
  ∃ (ε₀ : ℝ) (c : ℝ) (compile : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) → ℝ → gs.W),
    0 < ε₀ ∧ 0 < c ∧
    ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
      (ε : ℝ) (_hε_pos : 0 < ε) (_hε_le : ε ≤ ε₀),
      -- Error bound at compile level.
      ‖((gs.ρ_hom (compile U ε) : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ) -
        (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ε ∧
      -- Word-length bound at compile level (polylog).
      -- Cast compile U ε from gs.W to FreeGroup α via h_eq, take toWord.length.
      ((h_eq ▸ compile U ε : FreeGroup α).toWord.length : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))

/-! ## 2. Specialization for the Phase 6y target instances

The Phase 6y T-A1′.5 and T-A2′.5 headlines specialize to this form at:
  * **T-A1′.5**: `gs = trappedIonGeneratingSetSU4`, `α = Fin (4 + 2*N)` for
    discrete grid resolution N (4 single-qubit tokens + 2N MS grid tokens).
  * **T-A2′.5**: `gs = cliffordCCZGeneratingSetSU8`, `α = Fin 4` (H_q1, H_q2,
    H_q3, CCZ_SU).
  * **S.6 (this module)**: generic `gs : GeneratingSet d` form. -/

/-- **The d-generic headline predicate** (without `FreeGroup α` specialization).

Variant of `SolovayKitaevHeadline_FreeGroup_SUd` that doesn't assume the
specific structure of `gs.W` (no `FreeGroup` requirement). The
word-length bound becomes an abstract `wordLength : gs.W → ℕ` parameter
(consumer-supplied). -/
def SolovayKitaevHeadline_SUd {d : ℕ}
    (gs : GeneratingSet d) (wordLength : gs.W → ℕ) : Prop :=
  ∃ (ε₀ : ℝ) (c : ℝ) (compile : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) → ℝ → gs.W),
    0 < ε₀ ∧ 0 < c ∧
    ∀ (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
      (ε : ℝ) (_hε_pos : 0 < ε) (_hε_le : ε ≤ ε₀),
      ‖((gs.ρ_hom (compile U ε) : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ) -
        (U : Matrix (Fin d) (Fin d) ℂ)‖ ≤ ε ∧
      (wordLength (compile U ε) : ℝ) ≤
        c * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))

end SKEFTHawking.FKLW.GenericSUd
