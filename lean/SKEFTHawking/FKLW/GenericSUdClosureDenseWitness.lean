/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2-consumer — Generic SU(d) `ClosureDenseWitness`

d-parametric lift of Phase 6u's `GenericClosureDenseWitness` to SU(d).
Carries the tangent + flow-line data needed to dispatch
`CartanFinalStep_SUd_v4_holds` (S.2g) into `H_of_G gs = ⊤`.

## Mathematical content

A `ClosureDenseWitness gs` (for `gs : GeneratingSet d`) carries:

  * Finite `n` of traceless skew-Hermitian tangents `X : Fin n → Matrix (Fin d) (Fin d) ℂ`
  * Spanning condition: every traceless skew-Hermitian Y is an
    ℝ-linear combination of the `X i`.
  * Flow-line containment: `exp(ℝ • X i) ⊆ H_of_G gs` for all `i`.

This matches the hypothesis-form of `CartanFinalStep_SUd_v4 d`
(Phase 6y S.2a predicate), so dispatch is direct.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" — consumer substrate for S.2.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdGeneratingSet
import SKEFTHawking.FKLW.GenericSUdCartanPredicate
import SKEFTHawking.FKLW.SU2LieAlgebra

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The d-generic `ClosureDenseWitness` structure -/

/-- **Generic SU(d) closure-density witness** for a `GeneratingSet d`.

Bundles a spanning collection of `n` traceless skew-Hermitian tangents
`X : Fin n → Matrix (Fin d) (Fin d) ℂ` together with their full
1-parameter flow-line containment in `H_of_G gs`. Matches the
hypothesis-form of the Phase 6y S.2a predicate `CartanFinalStep_SUd_v4`.

For Phase 6y Track T-A1′.2 (SU(4) trapped-ion): consumers construct
the witness from MS(θ) + per-ion 1Q closure-density at SU(4).
For Phase 6y Track T-A2′.2 (SU(8) Clifford+CCZ): from the Aaronson-
Gottesman 2004 universality of Clifford+CCZ at SU(2^n). -/
structure ClosureDenseWitness {d : ℕ} (gs : GeneratingSet d) : Type where
  /-- Number of tangents. -/
  n : ℕ
  /-- The tangent collection. -/
  X : Fin n → Matrix (Fin d) (Fin d) ℂ
  /-- Each tangent is traceless skew-Hermitian (in 𝔰𝔲(d)). -/
  hX_in_sud : ∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0
  /-- The ℝ-span of the tangents covers all of 𝔰𝔲(d). -/
  hX_spans : ∀ Y : Matrix (Fin d) (Fin d) ℂ,
    Y.IsSkewHermitian → Y.trace = 0 →
    ∃ c : Fin n → ℝ, Y = ∑ i, ((c i : ℝ) : ℂ) • X i
  /-- Each tangent's 1-parameter flow line is in `H_of_G gs`. -/
  hX_flow : ∀ i, ∀ t : ℝ,
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
      M ∈ H_of_G gs ∧ M.val = NormedSpace.exp (((t : ℝ) : ℂ) • X i)

/-! ## 2. Dispatch to `H_of_G gs = ⊤`

Conditional on `CartanFinalStep_SUd_v4 d` (Phase 6y S.2 predicate),
a `ClosureDenseWitness gs` discharges `H_of_G gs = ⊤`. -/

/-- **Conditional dispatch**: a `ClosureDenseWitness` discharges
`H_of_G gs = ⊤` if the SU(d) Cartan-final-step v4 holds.

The full unconditional discharge ships when `CartanFinalStep_SUd_v4_holds`
(Phase 6y S.2g) is composed in. -/
theorem H_of_G_eq_top_of_witness_conditional {d : ℕ} {gs : GeneratingSet d}
    (w : ClosureDenseWitness gs)
    (h_cartan : CartanFinalStep_SUd_v4 d) :
    H_of_G gs = ⊤ := by
  apply h_cartan (H_of_G gs) (H_of_G_isClosed gs)
  exact ⟨w.n, w.X, w.hX_in_sud, w.hX_spans, w.hX_flow⟩

/-! ## 3. Summary

This module ships the `ClosureDenseWitness gs` structure + the
conditional dispatch `H_of_G_eq_top_of_witness_conditional` that
turns a witness into `H_of_G gs = ⊤` modulo the SU(d) Cartan v4
predicate. The full unconditional density chain `gs admits witness
⟹ ρ_hom.range is dense in SU(d)` ships in a follow-up once
`CartanFinalStep_SUd_v4_holds` (S.2g) is composed in. -/

end SKEFTHawking.FKLW.GenericSUd
