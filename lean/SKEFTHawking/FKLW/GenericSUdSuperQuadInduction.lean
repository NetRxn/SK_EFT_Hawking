/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S — Super-quad main induction (assembly)

The (B) ingredient: discharge of `SkApproxCSuperQuadraticBound_generic_sud`
(Session 44 predicate) — the SU(d) analog of SU(2)'s
`SkApproxCSuperQuadraticBound_generic_holds`
(`GenericSolovayKitaevRecursionDischarge.lean` lines 468-1181).

This module assembles the recursion induction from the per-step ingredients
shipped in Sessions 79-88:
  * F/G-norm bound (Session 82, `dnStepFG_sud_F_norm_le`)
  * commutator identity + invalid-zero (Session 83)
  * exp(-[F,G]) = Δ (Session 84)
  * expIsud near-identity norm bounds (Session 85)
  * group-commutator cubic remainder (Session 86, `≤ 320·δ³`)
  * ρ_hom MonoidHom abstractions (Session 87)
  * `groupCommutator_stability_nearIdentity` (already dimension-generic)
  * ε_seq monotonicity + the bumped `K_compose_sud = 1024·d^16` calibration
    (Session 88)

The induction proceeds in stages (shipped incrementally):
  1. **Base case** (this module): level-0 error ≤ `ε_seq K (2·ε₀) 0 = 2·ε₀`.
  2. Regime lemmas (θ ≤ 1, δ_lie ≤ 1 from `ε_n ≤ 2·ε₀_sud`).
  3. `valid_branch_K_chain_le_K_compose_sud_numeric` (the numeric K-chain).
  4. Inductive step (valid + invalid branches).
  5. The full induction `SkApproxCSuperQuadraticBound_generic_sud_holds`.

## Substantive content shipped (this session)

  * `skApproxC_generic_sud_zero_error_bound` — base case of the induction.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.6 — super-quad main induction
assembly (the (B) ingredient; base case).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdSkApproxC
import SKEFTHawking.FKLW.GenericSUdDnStepFGNormBound
import SKEFTHawking.FKLW.EpsilonSeq

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## Numeric-chain prep: polynomial bound on the F/G-norm constant K_F -/

/-- `0 ≤ dnStepFG_sud_K_F n`. -/
lemma dnStepFG_sud_K_F_nonneg (n : ℕ) : 0 ≤ dnStepFG_sud_K_F n := by
  unfold dnStepFG_sud_K_F
  positivity

/-- **Polynomial bound on K_F**: `dnStepFG_sud_K_F n = (n+2)²·(n+1)·√(n+2) ≤ (n+2)⁴`.

Tames the awkward `√(n+2)` factor to a clean polynomial d-power for the
super-quad numeric chain: `(n+1)·√(n+2) ≤ (n+2)·(n+2) = (n+2)²` (since
`n+1 ≤ n+2` and `√(n+2) ≤ n+2`), so `K_F ≤ (n+2)²·(n+2)² = (n+2)⁴`. -/
lemma dnStepFG_sud_K_F_le (n : ℕ) : dnStepFG_sud_K_F n ≤ ((n : ℝ) + 2)^4 := by
  unfold dnStepFG_sud_K_F
  have h_cast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [h_cast]
  have h_sqrt_le : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ) + 2 by positivity)
    have hs_nn := Real.sqrt_nonneg ((n:ℝ) + 2)
    nlinarith [hs, hs_nn, sq_nonneg (Real.sqrt ((n:ℝ) + 2) - 1),
      (by positivity : (0:ℝ) ≤ (n:ℝ))]
  rw [show ((n:ℝ) + 2)^4 = ((n:ℝ) + 2)^2 * (((n:ℝ) + 2) * ((n:ℝ) + 2)) from by ring]
  gcongr
  norm_num

/-- **Base case of the super-quad induction**: the level-0 approximation
`skApproxC_generic_sud … 0 U = baseFinder U` is within
`ε_seq K (2·ε₀) 0 = 2·ε₀` of `U`, given the base finder's ε₀-net property.

SU(d) analog of SU(2)'s `skApproxC_generic_zero_error_bound`. -/
lemma skApproxC_generic_sud_zero_error_bound {m : ℕ}
    (gs : GeneratingSet (m + 2))
    (baseFinder : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ) → gs.W)
    (h_det_pred : ExpIsud_det_eq_one_predicate (m + 2))
    (K ε₀ : ℝ)
    (h_baseFinder : BaseFinder_approximates_within_sud gs baseFinder (2 * ε₀))
    (U : ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
    ‖((gs.ρ_hom (skApproxC_generic_sud gs baseFinder h_det_pred 0 U) :
          ↥(Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ)) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) -
        (U : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)‖ ≤
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K (2 * ε₀) 0 := by
  rw [SKEFTHawking.FKLW.EpsilonSeq.ε_seq_zero, skApproxC_generic_sud_zero]
  exact (h_baseFinder U).le

end SKEFTHawking.FKLW.GenericSUd
