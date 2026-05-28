/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Bounded-form (F, G) existence at the dnStep level

Composes Session 33's spectral extraction (`Matrix.IsHermitian.spectral_theorem`)
with Session 37's bounded-form discharge
(`symmetric_balanced_commutator_hermitian_via_spectral_bounded`) to give,
for any Hermitian-traceless H with `θ := ‖H‖ ∈ (0, 1]`, the existence of
balanced-commutator witnesses F, G with EXPLICIT linftyOp norm bounds
`‖F‖ ≤ (n+2)² · ‖F_inner‖` (and mirror for G).

This is the substantive substrate for the super-quad bound's F/G-norm
ingredient: the missing piece is bounding `‖F_inner‖` (the inner
diagonal-case witness) in terms of `θ`, which requires the spectral
partial-sum analysis (follow-on). With that, `‖F‖ ≤ (n+2)² · K_inner · √(θ/2)`,
discharging `DnStepFG_sud_F_norm_bound_predicate` at `K_F = (n+2)² · K_inner`.

## Substantive content shipped

  * `balanced_commutator_bounded_of_hermitian` — for any Hermitian-traceless
    H and θ ∈ [0, 1], ∃ F G F_inner G_inner with the balanced commutator
    identity + Hermitian + traceless + `‖F‖ ≤ (n+2)²·‖F_inner‖` + mirror.
    Unconditional in H (extracts spectral decomp internally).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — bounded-form (F, G)
existence at dnStep level (super-quad bound F/G-norm substrate).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdHermitianDischargeBounded

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **Bounded-form balanced commutator from Hermitian H** (unconditional in H).

For any Hermitian-traceless `H : Matrix (Fin (n+2)) (Fin (n+2)) ℂ` and
`θ ∈ [0, 1]`, there exist F, G, F_inner, G_inner with:
  * F, G Hermitian + traceless
  * `F · G − G · F = -(θ·i) • H`
  * `‖F‖ ≤ (n+2)² · ‖F_inner‖` and `‖G‖ ≤ (n+2)² · ‖G_inner‖`

Composes Mathlib's spectral theorem (extract eigenvectorUnitary +
eigenvalues from H) with Session 37's
`symmetric_balanced_commutator_hermitian_via_spectral_bounded`.

This is the UNCONDITIONAL-in-H version of Session 37 (which required the
spectral decomposition as input). -/
theorem balanced_commutator_bounded_of_hermitian {n : ℕ}
    (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (h_herm : H.IsHermitian) (h_tr : H.trace = 0)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G F_inner G_inner : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H ∧
      ‖F‖ ≤ ((n + 2 : ℕ) : ℝ)^2 * ‖F_inner‖ ∧
      ‖G‖ ≤ ((n + 2 : ℕ) : ℝ)^2 * ‖G_inner‖ := by
  -- Extract spectral decomposition from Mathlib (as in Session 33).
  have h_spec : H = h_herm.eigenvectorUnitary.val *
      Matrix.diagonal (fun k => ((h_herm.eigenvalues k : ℝ) : ℂ)) *
      star h_herm.eigenvectorUnitary.val := by
    have h_st := h_herm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h_st
    convert h_st
  -- Apply Session 37's bounded form.
  obtain ⟨F, G, F_inner, G_inner, hF_herm, hG_herm, hF_tr, hG_tr, hcomm,
      hF_norm, hG_norm, _, _⟩ :=
    symmetric_balanced_commutator_hermitian_via_spectral_bounded H h_tr
      h_herm.eigenvectorUnitary h_herm.eigenvalues h_spec θ hθ_nn hθ_le_one
  exact ⟨F, G, F_inner, G_inner, hF_herm, hG_herm, hF_tr, hG_tr, hcomm,
    hF_norm, hG_norm⟩

end SKEFTHawking.FKLW.GenericSUd
