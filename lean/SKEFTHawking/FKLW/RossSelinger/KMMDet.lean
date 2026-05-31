/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — determinant of a Clifford+T-realizable matrix

KMM Theorem 1 (arXiv:1206.5236) characterizes the Clifford+T-realizable `2×2`
unitaries over `ZOmegaSqrt2` as exactly those of determinant `ω^k`. This file ships
the forward half: every realizable matrix has determinant `ωS^k` for some `k`. Each
gate's determinant is a power of `ωS = of ω` (`decide`); `det` is multiplicative
(`Matrix.det_mul`), so the word's determinant is `ωS^(Σ exponents)`.

This is the foundation for the M-structure form `M = [[x, −ωᵏȳ],[y, ωᵏx̄]]/√2^m`
(`col1` determined by `col0` + the `ω^k` determinant), feeding the `μ ≤ 3 ⟹ kSO3 ≤ 3`
bridge and the Clifford base via a bounded `decide`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only, finite `decide`).
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.KMM
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2
open scoped Matrix

set_option maxRecDepth 4000 in
/-- **Each gate's determinant is a power of `ωS`** (kernel-checked). -/
theorem det_gateMatrix_eq_omega_pow (g : CliffordTGate) :
    ∃ k : ℕ, Matrix.det (gateMatrix g) = ωS ^ k := by
  cases g
  · exact ⟨4, by rw [Matrix.det_fin_two]; decide⟩
  · exact ⟨2, by rw [Matrix.det_fin_two]; decide⟩
  · exact ⟨1, by rw [Matrix.det_fin_two]; decide⟩
  · exact ⟨4, by rw [Matrix.det_fin_two]; decide⟩
  · exact ⟨4, by rw [Matrix.det_fin_two]; decide⟩
  · exact ⟨4, by rw [Matrix.det_fin_two]; decide⟩
  · exact ⟨0, by rw [Matrix.det_fin_two]; decide⟩
  · exact ⟨2, by rw [Matrix.det_fin_two]; decide⟩

/-- **`det` of a realizable matrix is `ωS^k`** (KMM Theorem 1, forward half): the
determinant is multiplicative over the gate word, and each gate contributes a power
of `ωS`. -/
theorem det_realizable_eq_omega_pow {M : Mat2} (h : IsCliffordTRealizable M) :
    ∃ k : ℕ, Matrix.det M = ωS ^ k := by
  obtain ⟨gs, rfl⟩ := h
  induction gs with
  | nil => exact ⟨0, by rw [interp_nil, Matrix.det_one, pow_zero]⟩
  | cons g gs ih =>
      obtain ⟨kg, hkg⟩ := det_gateMatrix_eq_omega_pow g
      obtain ⟨k, hk⟩ := ih
      refine ⟨kg + k, ?_⟩
      rw [interp_cons, show (gateMatrix g * interp gs).det
          = (gateMatrix g).det * (interp gs).det from Matrix.det_mul _ _, hkg, hk, ← pow_add]

end KMM

end SKEFTHawking.RossSelinger
