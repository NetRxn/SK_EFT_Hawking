/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the KMM Theorem 1 column structure

KMM Theorem 1 (arXiv:1206.5236) characterizes a Clifford+T-realizable `2×2`
unitary `M` over `ZOmegaSqrt2` by the *column-1-from-column-0* form

  `M = [[x, −ωᵏ·x̄_c], [y, ωᵏ·x̄]] / √2^m`,

i.e. the second column is determined by the first column (via the conjugate)
and the determinant `ωᵏ`. This file ships that structural identity at the
entry level:

  * `M 1 1 = ωᵏ · conj (M 0 0)`  (the `(1,1)` entry),
  * `M 0 1 = −(ωᵏ · conj (M 1 0))`  (the `(0,1)` entry),

for the same `k` with `det M = ωᵏ` (`KMMDet.det_realizable_eq_omega_pow`).

## Proof

The uniform algebraic route is `det • M† = adjugate M` (valid even when
`M 0 0 = 0`, no case split): from `M† M = 1` one extracts the column-0 entry
equations

  * `h00 : conj(M₀₀)·M₀₀ + conj(M₁₀)·M₁₀ = 1`,
  * `h01 : conj(M₀₀)·M₀₁ + conj(M₁₀)·M₁₁ = 0`,

and with `hdet : M₀₀·M₁₁ − M₀₁·M₁₀ = ωᵏ` the two target entries fall out by
`linear_combination` (each a pure commutative-ring identity in the atoms
`{M i j, conj (M i j), ωᵏ}`). The `(1,1)` entry uses
`conj(M₀₀)·hdet − M₁₁·h00 + M₁₀·h01`; the `(0,1)` entry uses
`−conj(M₁₀)·hdet + M₀₀·h01 − M₀₁·h00`.

This is the foundation for the `μ ≤ 3 ⟹ kSO3 ≤ 3` bridge and the Clifford
base (`kSO3 = 0 ⟹ Clifford ≤ 6`): with column 1 determined by column 0, the
whole matrix is fixed by a bounded `(x, y, k, m)` integer tuple, turning the
`∀`-over-realizable-`M` discharges into bounded `native_decide` enumerations.

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §3, Theorem 1.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.KMMDet
import SKEFTHawking.FKLW.RossSelinger.UnitaryT
import SKEFTHawking.FKLW.RossSelinger.UnitaryClosure
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2
open scoped Matrix

/-- **KMM Theorem 1 column structure** (forward half): for a Clifford+T-realizable
`M`, column 1 is determined by column 0 and the determinant `ωᵏ`:
`M 1 1 = ωᵏ · conj (M 0 0)` and `M 0 1 = −(ωᵏ · conj (M 1 0))`, with the same `k`
as `det M = ωᵏ`. Proved via the uniform `det • M† = adjugate M` identity (no
case split on `M 0 0 = 0`); each entry is a `linear_combination` of the column-0
unitarity equations and the determinant equation. -/
theorem realizable_col1 {M : Mat2} (h : IsCliffordTRealizable M) :
    ∃ k : ℕ, M 0 1 = -(ωS ^ k * conj (M 1 0)) ∧ M 1 1 = ωS ^ k * conj (M 0 0) := by
  obtain ⟨k, hdet⟩ := det_realizable_eq_omega_pow h
  have hu : IsUnitaryT M := by obtain ⟨gs, rfl⟩ := h; exact interp_isUnitaryT gs
  have hdet2 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = ωS ^ k := by
    rw [← Matrix.det_fin_two]; exact hdet
  have h00 : conj (M 0 0) * M 0 0 + conj (M 1 0) * M 1 0 = 1 := by
    have h' := congrFun (congrFun hu 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_two, adjoint_apply, adjoint_apply,
      Matrix.one_apply_eq] at h'
  have h01 : conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1 = 0 := by
    have h' := congrFun (congrFun hu 0) 1
    rwa [Matrix.mul_apply, Fin.sum_univ_two, adjoint_apply, adjoint_apply,
      Matrix.one_apply_ne (by decide)] at h'
  -- The factor-vanishing helpers (`linear_combination`'s `ring1` closer fails to
  -- synthesize `IsRightCancelAdd` on this quotient ring, so the combination is
  -- assembled manually: `ring` proves the polynomial identity, then each
  -- hypothesis-factor is rewritten to `0`).
  have e1 : M 0 0 * M 1 1 - M 0 1 * M 1 0 - ωS ^ k = 0 := by rw [hdet2]; ring
  have e3 : conj (M 0 0) * M 0 0 + conj (M 1 0) * M 1 0 - 1 = 0 := by rw [h00]; ring
  refine ⟨k, ?_, ?_⟩
  · refine sub_eq_zero.mp ?_
    have key : M 0 1 - (-(ωS ^ k * conj (M 1 0)))
        = (-(conj (M 1 0))) * (M 0 0 * M 1 1 - M 0 1 * M 1 0 - ωS ^ k)
          + (M 0 0) * (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1)
          - (M 0 1) * (conj (M 0 0) * M 0 0 + conj (M 1 0) * M 1 0 - 1) := by ring
    rw [key, e1, h01, e3]; ring
  · refine sub_eq_zero.mp ?_
    have key : M 1 1 - ωS ^ k * conj (M 0 0)
        = (conj (M 0 0)) * (M 0 0 * M 1 1 - M 0 1 * M 1 0 - ωS ^ k)
          - (M 1 1) * (conj (M 0 0) * M 0 0 + conj (M 1 0) * M 1 0 - 1)
          + (M 1 0) * (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) := by ring
    rw [key, e1, e3, h01]; ring

end KMM

end SKEFTHawking.RossSelinger
