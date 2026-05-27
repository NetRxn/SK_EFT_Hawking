/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2g-conditional — Cartan v4 conditional discharge at SU(d)

A **conditional discharge** of `CartanFinalStep_SUd_v4` predicate via
the closed-subgroup closer: any closed subgroup `H ≤ SU(d)` containing
an open neighborhood of `1` is necessarily `⊤`.

This module ships the substrate that turns the "consumer provides an
open nbhd of 1 in H" hypothesis into the final `H = ⊤` conclusion via
Mathlib's `Subgroup.eq_top_of_isOpen_of_connected` + the project's
SU(d) connectedness instance.

The full **unconditional** discharge of `CartanFinalStep_SUd_v4_holds`
ships in a follow-up by composing:
  * Phase 6y S.2c (skew-Hermitian preservation of matrixLog)
  * Phase 6y S.2e PROPER (traceless preservation of matrixLog)
  * Phase 6y S.2d Jacobi formula
  * Trotter sum formula (S.2f, pending)
  * The IFT chain at SU(d) (S.2b + S.2e)

with this conditional discharge as the final step.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2g conditional discharge.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdGeneratingSet
import SKEFTHawking.FKLW.GenericSUdCartanPredicate
import SKEFTHawking.FKLW.SU2LieAlgebra
import SKEFTHawking.FKLW.SpecialUnitaryPathConnected
import SKEFTHawking.FKLW.OneParameterSubgroupSU2

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix Topology

/-! ## 1. SU(d) connectedness (re-export project substrate)

The project's `SpecialUnitaryPathConnected` ships
`Matrix.instConnectedSpaceSpecialUnitaryGroup` for all d. We re-export
for direct namespace use. -/

/-- SU(d) is connected (re-export of project substrate). -/
instance instConnectedSpaceSUd (d : ℕ) :
    ConnectedSpace (Matrix.specialUnitaryGroup (Fin d) ℂ) :=
  Matrix.instConnectedSpaceSpecialUnitaryGroup

/-! ## 2. Closed subgroup containing open nbhd of 1 = ⊤

Direct composition of Mathlib's `Subgroup.isOpen_of_one_mem_interior`
+ project-shipped `Subgroup.eq_top_of_isOpen_of_connected` +
SU(d) connectedness. -/

/-- **Closed subgroup of SU(d) with `1` in interior = ⊤**.

If `H ≤ SU(d)` is closed and `1 ∈ interior (H : Set ↥SU(d))`, then
`H = ⊤`. This is the abstract closer for the SU(d) Cartan v4
discharge. -/
theorem subgroup_SUd_eq_top_of_one_mem_interior (d : ℕ)
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (h_one_int : (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) ∈
      interior ((H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))) :
    H = ⊤ := by
  have h_open : IsOpen ((H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))) :=
    H.isOpen_of_one_mem_interior h_one_int
  exact Subgroup.eq_top_of_isOpen_of_connected H h_open

/-! ## 3. Predicate-level conditional discharge

Given the closure-density witness data + the assumption that `1` is
in the interior of `H`, dispatch into the Cartan v4 conclusion. -/

/-- **Conditional `CartanFinalStep_SUd_v4` discharge**: if for every
witness, `1 ∈ interior (H : Set ↥SU(d))` (which the full S.2g
substantively proves via Trotter sum + matrixLog 𝔰𝔲(d) preservation +
IFT-derived local diffeo), then `CartanFinalStep_SUd_v4 d` holds.

This is the **structural shape** of the final discharge — the
"open nbhd of 1" hypothesis is the substantive Lie-theoretic content
that S.2f Trotter sum + S.2c/e matrixLog preservation collectively
provide. -/
theorem CartanFinalStep_SUd_v4_holds_of_interior_witness {d : ℕ}
    (h_assumption : ∀ (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)),
      IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) →
      (∃ (n : ℕ) (X : Fin n → Matrix (Fin d) (Fin d) ℂ),
          (∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0) ∧
          (∀ Y : Matrix (Fin d) (Fin d) ℂ, Y.IsSkewHermitian → Y.trace = 0 →
              ∃ c : Fin n → ℝ, Y = ∑ i, ((c i : ℝ) : ℂ) • X i) ∧
          (∀ i, ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
              M ∈ H ∧ M.val = NormedSpace.exp (((t : ℝ) : ℂ) • X i))) →
      (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) ∈
        interior ((H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))) :
    CartanFinalStep_SUd_v4 d := by
  intro H hH_closed h_witness
  exact subgroup_SUd_eq_top_of_one_mem_interior d H (h_assumption H hH_closed h_witness)

end SKEFTHawking.FKLW.GenericSUd
