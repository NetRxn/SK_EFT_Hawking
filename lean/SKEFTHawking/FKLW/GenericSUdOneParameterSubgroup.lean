/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 2b — SU(d) von-Neumann 1-parameter-subgroup theorem (construction)

The SU(d) generalization of `FKLW/OneParameterSubgroupSU2.lean`'s von-Neumann theorem: a closed subgroup
`H ≤ SU(d)` with `1` as an accumulation point contains a continuous nontrivial 1-parameter subgroup
`t ↦ exp(t • X)` (`X ∈ 𝔰𝔲(d)`, `X ≠ 0`) with image in `H`. Built on the existing `GenericSUd` matrix-log
local diffeo (`GenericSUdLocalDiffeoRestriction`, `GenericSUdMatrixLogTraceless`) rather than re-deriving
the SU(2) `su2Log`/`expAmbient` apparatus.

This is the engine that turns the Phase-6z seed's accumulation-point witness
(`CliffordCCZSU8.seedSU8_accPt_one`, Wave 2a) into the first continuous flow `exp(t•X₀) ∈ H_of_G`
(Wave 2). The flow is then spread to a spanning collection by Clifford conjugation (Wave 4) and fed to
`CartanFinalStep_SUd_v4` (Wave 5).

Increment 1 (this commit): **sequence extraction** — from `1 ∈ AccPt H` produce `seq : ℕ → SU(d)` in
`H \ {1}` with `seq n → 1`. The proof is pure topology (first-countable), ported verbatim from the SU(2)
`vonNeumann_extract_sequence`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6z provenance

Phase 6z Wave 2b (SU(d) von-Neumann 1-parameter subgroup). 2026-05-28.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

/-- A point that is an accumulation point of `s` lies in the closure of `s \ {x}`. (Generic topology.) -/
theorem mem_closure_diff_singleton_of_accPt {X : Type*} [TopologicalSpace X] {s : Set X} {x : X}
    (hx : AccPt x (Filter.principal s)) : x ∈ closure (s \ {x}) := by
  rw [accPt_iff_frequently] at hx
  apply Filter.Frequently.mem_closure
  exact hx.mono (fun y hy => ⟨hy.2, fun heq => hy.1 heq⟩)

/-- **Von-Neumann sequence extraction (SU(d)).** From `1 ∈ AccPt H` extract a sequence in `H \ {1}`
converging to `1`. Pure-topology port of the SU(2) `vonNeumann_extract_sequence`. -/
theorem vonNeumann_extract_sequence {d : ℕ}
    [FrechetUrysohnSpace ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)]
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (hH : AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
      (Filter.principal (H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))) :
    ∃ seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
      (∀ n, seq n ∈ H) ∧ (∀ n, seq n ≠ 1) ∧
      Filter.Tendsto seq Filter.atTop
        (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))) := by
  have h_closure : (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) ∈
      closure ((H : Set _) \ {1}) :=
    mem_closure_diff_singleton_of_accPt hH
  obtain ⟨seq, h_in, h_tendsto⟩ :=
    (mem_closure_iff_seq_limit (s := (H : Set _) \ {1})
      (a := (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))).mp h_closure
  refine ⟨seq, fun n => (h_in n).1, ?_, h_tendsto⟩
  intro n hne
  exact (h_in n).2 (by rw [Set.mem_singleton_iff]; exact hne)

/-! ## Remaining increments (the von-Neumann analytic core — next builds)

Built on the existing `GenericSUd` matrix-log local diffeo
(`GenericSUdLocalDiffeoRestriction.matrixLog_expAmbient_on_su_d` /
`expAmbient_matrixLog_on_SUd`, `GenericSUdMatrixLogTraceless.matrixLog_in_su_d_on_nhd_one`):

  * **inc 2 — `matrixLog (seq n) → 0`:** the extracted sequence's matrix logs tend to `0`
    (continuity of `matrixLog` at `1` + `seq.val → 1`; mirror SU(2) `su2Log_seq_tendsto_zero`).
  * **inc 3 — BW on the 𝔰𝔲(d) unit sphere:** `X n := matrixLog (seq n) / ‖matrixLog (seq n)‖` lies on
    the compact unit sphere of the finite-dim `𝔰𝔲(d)`; extract a convergent subsequence `X (φ k) → X`,
    `‖X‖ = 1`, `X ∈ 𝔰𝔲(d)`.
  * **inc 4 — integer-rounding convergence:** for each `t`, with `m k := ⌊t / ‖matrixLog (seq (φ k))‖⌋`,
    `(seq (φ k)) ^ (m k) = exp (m k • matrixLog (seq (φ k))) → exp (t • X)`; since each is in `H`
    (subgroup) and `H` is closed, `exp (t • X) ∈ H`. (Mirror SU(2) §3.)
  * **inc 5 — main theorem:** assemble `1 ∈ AccPt H → ∃ X ∈ 𝔰𝔲(d), X ≠ 0 ∧ ∀ t, exp (t • X) ∈ H`.

Each is a port of the corresponding SU(2) lemma in `OneParameterSubgroupSU2.lean` with `su2Log` replaced
by the `GenericSUd` `matrixLog`. This is the genuine analytic core (multi-session). -/

end SKEFTHawking.FKLW.GenericSUd
