/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.3 d≥3 PROPER — Unconditional Hermitian discharge

For ANY Hermitian-traceless `H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ`,

  `∃ F G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ,
    F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
    F * G - G * F = -((θ : ℂ) * Complex.I) • H`

for any θ ∈ [0, 1].

This is the **UNCONDITIONAL FULL S.3 d≥3 PROPER discharge**: combines
Session 32's spectral-lift form with Mathlib's
`Matrix.IsHermitian.spectral_theorem` (which extracts the eigenvector
unitary and eigenvalues from any Hermitian matrix).

## Substantive content shipped

  * `symmetric_balanced_commutator_hermitian_unconditional` — the full
    S.3 d≥3 PROPER discharge for ANY Hermitian-traceless H.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.3 d≥3 PROPER — UNCONDITIONAL.
This is the substantive completion of Track S keystone.

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSpectralLift

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## UNCONDITIONAL discharge for ANY Hermitian H -/

/-- **UNCONDITIONAL FULL S.3 d≥3 PROPER discharge**: for ANY
Hermitian-traceless `H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ` and any
`θ ∈ [0, 1]`, there exist Hermitian-traceless F, G such that

  `F · G - G · F = -((θ : ℂ) · Complex.I) • H`.

Proof: extract (U, a) from H via Mathlib's `Matrix.IsHermitian.spectral_theorem`
(`U := h_herm.eigenvectorUnitary`, `a := h_herm.eigenvalues`), then apply
Session 32's `symmetric_balanced_commutator_hermitian_via_spectral`.

The spectral theorem in Mathlib gives the form
`H = (Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜)) U (diag (RCLike.ofReal ∘ eigenvalues))`,
which unfolds via `Unitary.conjStarAlgAut_apply` to
`U.val · diag(a coerced) · star U.val` — matching S32's hypothesis. -/
theorem symmetric_balanced_commutator_hermitian_unconditional {n : ℕ}
    (H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
    (h_herm : H.IsHermitian) (h_tr : H.trace = 0)
    (θ : ℝ) (hθ_nn : 0 ≤ θ) (hθ_le_one : θ ≤ 1) :
    ∃ (F G : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ),
      F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = -((θ : ℂ) * Complex.I) • H := by
  -- Extract spectral decomposition from Mathlib.
  have h_spec : H = h_herm.eigenvectorUnitary.val *
      Matrix.diagonal (fun k => ((h_herm.eigenvalues k : ℝ) : ℂ)) *
      star h_herm.eigenvectorUnitary.val := by
    have h_st := h_herm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h_st
    convert h_st
  -- Apply Session 32.
  exact symmetric_balanced_commutator_hermitian_via_spectral H h_tr
    h_herm.eigenvectorUnitary h_herm.eigenvalues h_spec θ hθ_nn hθ_le_one

end SKEFTHawking.FKLW.GenericSUd
