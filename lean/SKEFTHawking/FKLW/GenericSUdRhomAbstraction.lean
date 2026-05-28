/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — SU(d) ρ_hom MonoidHom abstraction lemmas

The SU(d) analogs of the SU(2) alphabet-agnostic `ρ_hom_mul_val` /
`ρ_hom_inv_val` / `ρ_hom_groupCommutator_val`. These push the generating-set
representation `gs.ρ_hom : W →* specialUnitaryGroup (Fin d) ℂ` through to the
matrix level:

  * `(gs.ρ_hom (a·b)).val = (gs.ρ_hom a).val · (gs.ρ_hom b).val`
  * `(gs.ρ_hom a⁻¹).val = ((gs.ρ_hom a).val)⁻¹`
  * `(gs.ρ_hom (a·b·a⁻¹·b⁻¹)).val = groupCommutator (gs.ρ_hom a).val (gs.ρ_hom b).val`

These are direct consequences of `gs.ρ_hom` being a `MonoidHom` plus the
`specialUnitaryGroup (Fin d) ℂ` subtype mult/inv coercions. They are the
alphabet-agnostic MonoidHom abstractions the super-quad main induction is
parameterized over (the SU(2) discharge uses the `Fin 2` versions throughout
its `ρ(sk(n+1) U) = V_n · gC(ρsk A_F, ρsk A_G)` composition identity).

## Substantive content shipped

  * `SUd_subtype_inv_val_eq_matrix_inv` — group inverse coerces to matrix inverse.
  * `ρ_hom_sud_mul_val`, `ρ_hom_sud_inv_val`, `ρ_hom_sud_groupCommutator_val`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — SU(d) ρ_hom abstractions
(super-quad main induction MonoidHom substrate).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdGeneratingSet
import SKEFTHawking.FKLW.GroupCommutator

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix
open SKEFTHawking.FKLW.GroupCommutator

/-- **SU(d) subtype-group inverse equals matrix inverse**: for
`A : ↥(specialUnitaryGroup (Fin d) ℂ)`, the underlying matrix of the group
inverse `A⁻¹` equals the matrix nonsing inverse of `A.val`. Dimension-generic
lift of SU(2)'s `SU2_subtype_inv_val_eq_matrix_inv`. -/
lemma SUd_subtype_inv_val_eq_matrix_inv {d : ℕ}
    (A : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    ((A⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) =
      ((A : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ)⁻¹ := by
  have h_mul : A * A⁻¹ = 1 := mul_inv_cancel A
  have h_mul_val : (A : Matrix (Fin d) (Fin d) ℂ) *
      ((A⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ) = 1 := by
    have h_eq : ((A * A⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
              Matrix (Fin d) (Fin d) ℂ) =
           (A : Matrix (Fin d) (Fin d) ℂ) *
             ((A⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
                Matrix (Fin d) (Fin d) ℂ) := rfl
    rw [← h_eq, h_mul]
    rfl
  exact (Matrix.inv_eq_right_inv h_mul_val).symm

/-- **`gs.ρ_hom` multiplicativity at the matrix level** (SU(d)). -/
lemma ρ_hom_sud_mul_val {d : ℕ} (gs : GeneratingSet d) (a b : gs.W) :
    ((gs.ρ_hom (a * b) : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) =
      ((gs.ρ_hom a : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ) *
      ((gs.ρ_hom b : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ) := by
  rw [map_mul]
  rfl

/-- **`gs.ρ_hom` inverse at the matrix level** (SU(d)). -/
lemma ρ_hom_sud_inv_val {d : ℕ} (gs : GeneratingSet d) (a : gs.W) :
    ((gs.ρ_hom a⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) =
      ((gs.ρ_hom a : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ)⁻¹ := by
  rw [map_inv]
  exact SUd_subtype_inv_val_eq_matrix_inv _

/-- **`gs.ρ_hom` of group commutator at the matrix level** (SU(d)). -/
lemma ρ_hom_sud_groupCommutator_val {d : ℕ} (gs : GeneratingSet d) (a b : gs.W) :
    ((gs.ρ_hom (a * b * a⁻¹ * b⁻¹) :
        ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) =
      groupCommutator
        ((gs.ρ_hom a : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
            Matrix (Fin d) (Fin d) ℂ)
        ((gs.ρ_hom b : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
            Matrix (Fin d) (Fin d) ℂ) := by
  unfold groupCommutator
  rw [ρ_hom_sud_mul_val, ρ_hom_sud_mul_val, ρ_hom_sud_mul_val,
      ρ_hom_sud_inv_val, ρ_hom_sud_inv_val]

end SKEFTHawking.FKLW.GenericSUd
