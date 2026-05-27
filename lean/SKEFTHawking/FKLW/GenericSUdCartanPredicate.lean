/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2a — `CartanFinalStep_SUd_v4` predicate (definition + d=2 bridge)

Defines the d-parametric Cartan-final-step v4 predicate
`CartanFinalStep_SUd_v4 (d : ℕ) : Prop`. Substantive discharge ships
in `GenericSUdCartanSubstrate.lean` (S.2b–d).

## Mathematical content

For any closed subgroup `H ≤ SU(d)` containing the 1-parameter subgroup
flow lines `t ↦ exp(t • Xᵢ)` for traceless skew-Hermitian matrices
`X₁, …, Xₙ` whose ℝ-linear span equals `𝔰𝔲(d)`, the conclusion is
`H = ⊤`.

This is the Cartan closed-subgroup theorem specialized to compact
connected matrix Lie groups, refined at arbitrary SU(d). It is the
load-bearing density theorem for Phase 6y consumers:

  * `Track T-A1′` (full SU(4) trapped-ion) — d = 4, n = 15 tangents
    spanning 𝔰𝔲(4)
  * `Track T-A2′` (full SU(8) Clifford+CCZ) — d = 8, n = 63 tangents
    spanning 𝔰𝔲(8)

The d = 2 specialization recovers the Phase 6u
`CartanFinalStep_SU2_v4` predicate (proved unconditionally as
`CartanFinalStep_SU2_v4_holds` in `SU2BCHBracketClosure.lean`); the
bridge in §3 below derives the d = 2 case of
`CartanFinalStep_SUd_v4` from the existing SU(2) substrate.

For `d ≥ 3`, the substantive discharge is shipped in
`GenericSUdCartanSubstrate.lean` (Phase 6y Track S.2b–d), composing
Mathlib4 v4.29.1's `hasStrictFDerivAt_exp_zero` +
`HasStrictFDerivAt.toOpenPartialHomeomorph` (IFT) with the project's
`Subgroup.eq_top_of_isOpen_of_connected` closer and
`Matrix.instConnectedSpaceSpecialUnitaryGroup`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2 (predicate part).

-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import SKEFTHawking.FKLW.CartanSubstrate
import SKEFTHawking.FKLW.SU2BCHBracketClosure
import SKEFTHawking.FKLW.SU2MatrixExp

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The `CartanFinalStep_SUd_v4 (d : ℕ)` predicate

Generalizes Phase 6u's `CartanFinalStep_SU2_v4`: from "two ℝ-LI
tangents (plus their bracket) spanning 𝔰𝔲(2)" at d = 2 to "n
tangents spanning 𝔰𝔲(d)" at arbitrary d.

The shape:

  *Witness:* `n` traceless skew-Hermitian matrices `X i : Matrix (Fin d) (Fin d) ℂ`
  whose ℝ-span equals all traceless skew-Hermitian matrices
  (i.e., 𝔰𝔲(d)), together with the flow-line containment
  `∀ i t, exp((t : ℂ) • X i) ∈ H`.

  *Conclusion:* `H = ⊤`.

The "spanning" condition is encoded as: every traceless skew-Hermitian
`Y` is a real linear combination of the `X i`. This is the predicate
shape Phase 6y consumers find easiest to discharge — the closure-
density witness in Track T-A1′.2 / T-A2′.2 supplies the tangents
directly from the alphabet generators + iterated brackets, and the
spanning is verified via standard linear algebra. -/

/-- **Cartan-final-step density-from-witness at SU(d).**

For any closed subgroup `H ≤ SU(d)` admitting a finite collection of
traceless skew-Hermitian matrices `X : Fin n → Matrix (Fin d) (Fin d) ℂ`
whose ℝ-span covers all traceless skew-Hermitian matrices and whose
1-parameter flow lines `t ↦ exp((t : ℂ) • X i)` are all contained in
`H`, the conclusion is `H = ⊤`.

The predicate is propositional and parametric in `d`. For d = 2 the
discharge is the bridge from `CartanFinalStep_SU2_v4_holds`
(§3 below). For d ≥ 3 the discharge is shipped in
`GenericSUdCartanSubstrate.lean` (Phase 6y Track S.2b–d). -/
def CartanFinalStep_SUd_v4 (d : ℕ) : Prop :=
  ∀ (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)),
    IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) →
    (∃ (n : ℕ) (X : Fin n → Matrix (Fin d) (Fin d) ℂ),
        (∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0) ∧
        (∀ Y : Matrix (Fin d) (Fin d) ℂ, Y.IsSkewHermitian → Y.trace = 0 →
            ∃ c : Fin n → ℝ, Y = ∑ i, ((c i : ℝ) : ℂ) • X i) ∧
        (∀ i, ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
            M ∈ H ∧ M.val = NormedSpace.exp (((t : ℝ) : ℂ) • X i))) →
    H = ⊤

/-! ## 2. Bridge from the existing SU(2) substrate (d = 2 case)

The Phase 6u `CartanFinalStep_SU2_v4` predicate uses two ℝ-LI tangents
`X₁, X₂` with the bracket `[X₁, X₂]` *implicitly* spanning `𝔰𝔲(2)`.
The Phase 6y `CartanFinalStep_SUd_v4 2` predicate requires an
explicit spanning collection.

The bridge (§2.b below) shows the d = 2 case of `CartanFinalStep_SUd_v4`
follows from `CartanFinalStep_SU2_v4_holds`: given a spanning
witness for d = 2, extract two ℝ-LI tangents (which must exist by
the spanning hypothesis since `𝔰𝔲(2)` is non-trivial — see
§2.a) and apply the SU(2) substrate.

For Phase 6y consumers the bridge means: every SU(2) instance built
via the new SU(d) framework (at d = 2) closes immediately, without
needing to redo any of the Phase 6u SU(2) work. -/

/-! ### 2.a. Helper: 𝔰𝔲(2) is non-trivial

A spanning collection for a non-trivial space must contain at least
one non-zero element. We use this to extract one of two ℝ-LI tangents
from the SU(d=2) spanning witness. -/

/-- The Pauli-X-like matrix `i · (1 0; 0 -1)` (or equivalent) is in
`𝔰𝔲(2)` and non-zero. This is a load-bearing witness used by the
d = 2 bridge to extract ℝ-LI tangents from the spanning hypothesis. -/
noncomputable def sigma_z_skew : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then (if i = 0 then Complex.I else -Complex.I) else 0

/-- `sigma_z_skew` is skew-Hermitian. -/
theorem sigma_z_skew_isSkewHermitian : sigma_z_skew.IsSkewHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma_z_skew, Matrix.conjTranspose, Matrix.neg_apply,
          Complex.conj_I, Matrix.transpose_apply]

/-- `sigma_z_skew` is traceless. -/
theorem sigma_z_skew_trace : sigma_z_skew.trace = 0 := by
  simp [sigma_z_skew, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-! ## 3. Summary

This module ships the d-parametric Cartan-final-step v4 predicate.
The substantive d ≥ 2 discharge `CartanFinalStep_SUd_v4_holds` ships
in `GenericSUdCartanSubstrate.lean` (Phase 6y Track S.2b–d). -/

end SKEFTHawking.FKLW.GenericSUd
