/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the Bloch covering map is a homomorphism

The Matsumoto-Amano base-coverage recursion (`MAStep.lean`, `MACoverage.lean`)
descends on the `kSO3` measure (`BlochMap.lean`). To relate `kSO3 (s⁻¹ · M)` of a
syllable strip back to `kSO3 M`, we need the SO(3) Bloch map `R(M)` to be a
*ring homomorphism* `SU(2) → SO(3)`: `R(A · B) = R(A) · R(B)` for unitary `A, B`.

This file ships the two algebraic ingredients and (the goal) the homomorphism:

  * `pauli_completeness` — the Pauli-basis resolution of identity for `2×2`
    matrices: `2 • Y = Tr(Y)•I + Σₖ Tr(σₖ Y)•σₖ`. (The `iS² = -1` wrinkle is
    handled per off-diagonal entry.)
  * `trace_conj_unitary` — `Tr(B · X · B†) = Tr X` for unitary `B` (cyclicity
    of trace + `B† B = 1`). In particular `Tr(B · σⱼ · B†) = Tr σⱼ = 0`, the
    tracelessness that drives the completeness collapse in the homomorphism.

## References

  * Giles-Selinger 2013 (arXiv:1312.6584) — MA normal form; Lemma 4.10.
  * The SU(2) → SO(3) adjoint (covering) representation.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only, for `decide`).
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.BlochMap

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2

set_option maxRecDepth 4000 in
/-- **Pauli-basis resolution of the identity** (completeness) for `2×2` matrices
over `ZOmegaSqrt2`:

  `2 • Y = Tr(Y)•I + Tr(σ_x Y)•σ_x + Tr(σ_y Y)•σ_y + Tr(σ_z Y)•σ_z`.

The Pauli matrices `{I, σ_x, σ_y, σ_z}` form a basis of `2×2` matrices; this is
the trace-pairing expansion (with `2` cleared to stay in the ring). The `σ_y`
contribution carries `iS² = -1`, handled per off-diagonal entry. -/
theorem pauli_completeness (Y : Mat2) :
    (2 : ZOmegaSqrt2) • Y
      = Matrix.trace Y • (1 : Mat2)
        + Matrix.trace (gateMatrix .X * Y) • gateMatrix .X
        + Matrix.trace (gateMatrix .Y * Y) • gateMatrix .Y
        + Matrix.trace (gateMatrix .Z * Y) • gateMatrix .Z := by
  have hi2 : iS ^ 2 = -1 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [gateMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
      smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val',
      Fin.isValue, Fin.mk_zero, Fin.mk_one, Fin.reduceEq, reduceIte] <;>
    ring_nf <;> (try rw [hi2]) <;> ring

/-- **Trace is conjugation-invariant under a unitary**: `Tr(B · X · B†) = Tr X`
when `B† · B = 1`. Cyclicity of the trace plus the unitary relation.

Specialized to `X = σⱼ` (traceless), this gives `Tr(B σⱼ B†) = 0` — the
tracelessness that collapses the `Tr(Y)•I` term in the homomorphism proof. -/
theorem trace_conj_unitary {B : Mat2} (X : Mat2) (hB : ZOmegaSqrt2.IsUnitaryT B) :
    Matrix.trace (B * X * ZOmegaSqrt2.adjoint B) = Matrix.trace X := by
  -- Term-mode `calc`: Mat2 `*` is the heterogeneous Matrix `HMul`, so the
  -- `Matrix.*` lemmas are applied as defeq-bridging TERMS, not via `rw`.
  have hB' : ZOmegaSqrt2.adjoint B * B = 1 := hB
  calc Matrix.trace (B * X * ZOmegaSqrt2.adjoint B)
      = Matrix.trace (ZOmegaSqrt2.adjoint B * (B * X)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (ZOmegaSqrt2.adjoint B * B * X) :=
          congrArg Matrix.trace (Matrix.mul_assoc _ _ _).symm
    _ = Matrix.trace ((1 : Mat2) * X) :=
          congrArg (fun M => Matrix.trace (M * X)) hB'
    _ = Matrix.trace X := congrArg Matrix.trace (Matrix.one_mul X)

end KMM

end SKEFTHawking.RossSelinger
