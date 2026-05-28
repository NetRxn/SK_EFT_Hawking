/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y literal Clifford+CCZ strengthening — the irrational-angle seed `g = CCZ·(H⊗H⊗H)`

The *faithful* literal Clifford+CCZ headline (CCZ as the essential non-Clifford resource, no `T`)
needs a continuous one-parameter subgroup in the closure of the discrete group `⟨H,S,CNOT,CCZ⟩`.
Since every literal generator is finite-order, the first such flow is seeded by an **infinite-order**
element with an irrational eigen-angle. Per the Phase-6y DR spike
(`Lit-Search/Phase-6y/Phase 6y · T-A2′ — Clifford+CCZ Seed Element.md`):

  `g := CCZ · (H ⊗ H ⊗ H)`  has  `tr(g) = 1/√2`.

A finite-order unitary has all eigenvalues roots of unity, so `tr` would be a sum of roots of unity,
hence an algebraic integer. `1/√2 ∉ 𝒪_ℚ̄` (its `ℚ(√2)` norm is `−1/2 ∉ ℤ`), so `g` has infinite order
and some eigen-angle is `∉ π·ℚ` (Kronecker). This module ships **Phase A.1: the seed + `tr(g)=1/√2`**
via the clean route `tr(CCZ·K) = tr(K) − 2·K₇₇`, with `tr(K) = (tr H)³ = 0` (`kronSU8_trace`) and
`K₇₇ = (H₁₁)³`. The irrationality proof (Phase B) and the closure→one-parameter-subgroup lift
(Phase C, the Kronecker–Weyl piece — pending a proof-sketch sub-spike) follow.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y provenance

Phase 6y T-A2′ literal-Clifford+CCZ strengthening, Phase A.1 (seed element + trace). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8Tangents
import SKEFTHawking.FKLW.CliffordCCZAlphabet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix Complex SKEFTHawking.FKLW.CliffordCCZ SKEFTHawking.FKLW.TrappedIonSU4

/-- Raw (textbook) Hadamard `H = (1/√2)·[[1,1],[1,-1]]` — `det = −1`, real orthogonal. -/
noncomputable def litHadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Real.sqrt 2 : ℂ) • !![1, 1; 1, -1]

/-- `tr H = 0`. -/
theorem litHadamard_trace : litHadamard.trace = 0 := by
  simp [litHadamard, Matrix.trace_fin_two]

/-- The `(1,1)` entry `H₁₁ = -1/√2`. -/
theorem litHadamard_apply_1_1 : litHadamard 1 1 = -(1 / Real.sqrt 2 : ℂ) := by
  simp [litHadamard]

/-- **The literal seed** `g = CCZ · (H⊗H⊗H)` (Toffoli–Hadamard; real orthogonal, `det = −1`). -/
noncomputable def litSeed : Matrix (Fin 8) (Fin 8) ℂ :=
  CCZ_mat * kronSU8 litHadamard litHadamard litHadamard

/-- `tr(H⊗H⊗H) = (tr H)³ = 0`. -/
theorem kron_litHadamard_trace :
    (kronSU8 litHadamard litHadamard litHadamard).trace = 0 := by
  rw [kronSU8_trace, litHadamard_trace]; ring

/-- Diagonal-times-matrix trace split: `tr(CCZ·K) = tr K − 2·K₇₇`. -/
theorem trace_CCZ_mul (K : Matrix (Fin 8) (Fin 8) ℂ) :
    (CCZ_mat * K).trace = K.trace - 2 * K (7 : Fin 8) (7 : Fin 8) := by
  rw [CCZ_mat]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Fin.sum_univ_eight, Fin.sum_univ_eight]
  norm_num [Fin.ext_iff]
  ring

/-- The `|111⟩` diagonal entry `(H⊗H⊗H)₇₇ = (H₁₁)³`. -/
theorem kron_litHadamard_apply_7_7 :
    (kronSU8 litHadamard litHadamard litHadamard) (7 : Fin 8) (7 : Fin 8)
      = (litHadamard 1 1) ^ 3 := by
  unfold kronSU8 kronSU2SU4 kronSU4
  simp [Matrix.submatrix_apply, Matrix.reindex_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    finProdFinEquiv, Fin.divNat, Fin.modNat]
  ring

/-- **The seed trace** `tr(g) = 1/√2` — the obstruction to `g = CCZ·(H⊗H⊗H)` being finite-order
(a sum of roots of unity equal to `1/√2 ∉ 𝒪_ℚ̄`). -/
theorem litSeed_trace : litSeed.trace = (1 / Real.sqrt 2 : ℂ) := by
  have hsqrt : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    exact_mod_cast h
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  unfold litSeed
  rw [trace_CCZ_mul, kron_litHadamard_trace, kron_litHadamard_apply_7_7, litHadamard_apply_1_1,
    show (-(1 / (Real.sqrt 2 : ℂ))) ^ 3
        = -(1 / ((Real.sqrt 2 : ℂ) ^ 2 * (Real.sqrt 2 : ℂ))) by ring, hsqrt]
  field_simp
  ring

end SKEFTHawking.FKLW.CliffordCCZSU8
