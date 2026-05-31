/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — Clifford+T-realizable ⟹ unitary

The `μ`-decrease step (`MuDecrease.lean`) needs the matrices in the `kmmReduce`
recursion to be unitary (so `chooseReductionMu_succeeds`/`mu_decrease` apply). The
recursion preserves `IsCliffordTRealizable` (`reduceStep` left-multiplies by gate
matrices), so it suffices that **every Clifford+T-realizable matrix is unitary**.

This file proves `isUnitaryT_of_isCliffordTRealizable` from the conjugate-transpose
anti-homomorphism `adjoint (M·N) = adjoint N · adjoint M`, the unitarity of each
gate matrix (kernel `decide`), and closure of `IsUnitaryT` under product and at `1`.

## Note on the Matrix `*` instance

`Mat2`'s `*` resolves to `Matrix`'s heterogeneous `HMul` (not the `Monoid.mul`), so
the generic `mul_assoc`/`mul_one`/`one_mul` rewrite lemmas do NOT syntactically
match — but `Matrix.mul_assoc`/`Matrix.one_mul` apply as *terms* (defeq bridges the
instances). `IsUnitaryT.mul` is therefore proved term-mode (`calc` + `congrArg`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected (kernel-pure; the gate-unitarity
  `decide` is kernel, not `native_decide`).

-/

import SKEFTHawking.FKLW.RossSelinger.UnitaryT

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmegaSqrt2

/-- **`adjoint 1 = 1`** (the conjugate transpose of the identity is the identity). -/
theorem adjoint_one : adjoint (1 : Mat2) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- **Conjugate transpose is a (multiplicative) anti-homomorphism**:
`adjoint (M·N) = adjoint N · adjoint M`. Entrywise via `conj_add`/`conj_mul`. -/
theorem adjoint_mul (M N : Mat2) : adjoint (M * N) = adjoint N * adjoint M := by
  ext i j
  simp only [adjoint_apply, Matrix.mul_apply, Fin.sum_univ_two, conj_add, conj_mul]
  ring

/-- **The identity is unitary**. -/
theorem IsUnitaryT.one : IsUnitaryT (1 : Mat2) := by
  unfold IsUnitaryT
  rw [adjoint_one]
  exact Matrix.one_mul 1

/-- **Unitarity is closed under product**: `adjoint(M·N)·(M·N) = adjoint N ·
(adjoint M · M) · N = adjoint N · N = 1`. Proved term-mode (`Matrix.mul_assoc`/
`Matrix.one_mul` as terms) because `Mat2`'s `*` is the heterogeneous `HMul`. -/
theorem IsUnitaryT.mul {M N : Mat2} (hM : IsUnitaryT M) (hN : IsUnitaryT N) :
    IsUnitaryT (M * N) := by
  unfold IsUnitaryT at hM hN ⊢
  rw [adjoint_mul]
  calc adjoint N * adjoint M * (M * N)
      = adjoint N * (adjoint M * (M * N)) := Matrix.mul_assoc _ _ _
    _ = adjoint N * (adjoint M * M * N) := congrArg (adjoint N * ·) (Matrix.mul_assoc _ _ _).symm
    _ = adjoint N * (1 * N) := congrArg (adjoint N * ·) (congrArg (· * N) hM)
    _ = adjoint N * N := congrArg (adjoint N * ·) (Matrix.one_mul N)
    _ = 1 := hN

/-- **Every Clifford+T gate matrix is unitary** (kernel `decide` per gate). -/
theorem gateMatrix_isUnitaryT (g : CliffordTGate) : IsUnitaryT (CliffordTGate.gateMatrix g) := by
  cases g <;> (unfold IsUnitaryT; decide)

/-- **Every gate-sequence interpretation is unitary** (induction: product of unitaries). -/
theorem interp_isUnitaryT (gs : List CliffordTGate) : IsUnitaryT (CliffordTGate.interp gs) := by
  induction gs with
  | nil => rw [CliffordTGate.interp_nil]; exact IsUnitaryT.one
  | cons g gs ih => rw [CliffordTGate.interp_cons]; exact IsUnitaryT.mul (gateMatrix_isUnitaryT g) ih

/-- **Clifford+T-realizable ⟹ unitary**: the fuel-sufficiency precondition for the
`kmmReduce` recursion (`reduceStep` preserves realizability, hence unitarity). -/
theorem isUnitaryT_of_isCliffordTRealizable {M : Mat2} (h : KMM.IsCliffordTRealizable M) :
    IsUnitaryT M := by
  obtain ⟨gs, hgs⟩ := h
  rw [← hgs]
  exact interp_isUnitaryT gs

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
