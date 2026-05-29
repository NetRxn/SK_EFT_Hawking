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
import SKEFTHawking.FKLW.RossSelinger.UnitaryClosure

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

set_option maxRecDepth 8000 in
/-- **Bloch completeness on a unitary**: for unitary `B`,

  `B · σⱼ · B† = ∑ₖ blochEntry B k j • σₖ`.

The Pauli-basis expansion of the adjoint action `σⱼ ↦ B σⱼ B†`. Proof:
`Y := B σⱼ B†` is traceless (`trace_conj_unitary` + `Tr σⱼ = 0`), so
`pauli_completeness` collapses to `2•Y = ∑ₖ Tr(σₖ Y)•σₖ`; matching `2·blochEntry`
coefficients (`2·half = 1`) and cancelling the `2•` (via `half•`) gives the claim.
This is the engine of the Bloch homomorphism. -/
theorem bloch_completeness_unitary {B : Mat2} (hB : ZOmegaSqrt2.IsUnitaryT B) (j : Fin 3) :
    B * pauliMat j * ZOmegaSqrt2.adjoint B = ∑ k : Fin 3, blochEntry B k j • pauliMat k := by
  set Y := B * pauliMat j * ZOmegaSqrt2.adjoint B with hYdef
  have hY0 : Matrix.trace Y = 0 := by
    rw [hYdef, trace_conj_unitary (pauliMat j) hB]; fin_cases j <;> decide
  have hbe : ∀ k : Fin 3, blochEntry B k j = half * Matrix.trace (pauliMat k * Y) := by
    intro k
    have harg : pauliMat k * B * pauliMat j * ZOmegaSqrt2.adjoint B = pauliMat k * Y := by
      rw [hYdef]; ext x y; simp only [Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [blochEntry, harg]
  have hc := pauli_completeness Y
  rw [hY0, zero_smul, zero_add] at hc
  have h2half : (2 : ZOmegaSqrt2) * half = 1 := by decide
  have cancel : ∀ Z : Mat2, half • ((2 : ZOmegaSqrt2) • Z) = Z := by
    intro Z; rw [smul_smul, mul_comm, h2half, one_smul]
  have key : (2 : ZOmegaSqrt2) • Y
      = (2 : ZOmegaSqrt2) • (∑ k : Fin 3, blochEntry B k j • pauliMat k) := by
    rw [hc, Finset.smul_sum, Fin.sum_univ_three]
    simp only [hbe, smul_smul, ← mul_assoc, h2half, one_mul, pauliMat]
  calc Y = half • ((2 : ZOmegaSqrt2) • Y) := (cancel Y).symm
    _ = half • ((2 : ZOmegaSqrt2) • (∑ k : Fin 3, blochEntry B k j • pauliMat k)) := by rw [key]
    _ = ∑ k : Fin 3, blochEntry B k j • pauliMat k := cancel _

set_option maxRecDepth 8000 in
/-- **The Bloch map is a homomorphism** `SU(2) → SO(3)` (for unitary right factor):

  `blochEntry (A · B) i j = ∑ₖ blochEntry A i k · blochEntry B k j`,

i.e. `R(A·B) = R(A)·R(B)`. Proof: reassociate `σᵢ(AB)σⱼ(AB)† = σᵢ A (Bσⱼ B†) A†`
(via `adjoint_mul`), expand `Bσⱼ B†` by `bloch_completeness_unitary`, distribute the
sum/scalars through the product and trace, and recognize `blochEntry A i k`.

This is the structural fact that lets the Matsumoto-Amano recursion relate
`kSO3 (s⁻¹·M) = kSO3 (adjoint(syl s) · M)` to `kSO3 M`. -/
theorem bloch_hom {A B : Mat2} (hB : ZOmegaSqrt2.IsUnitaryT B) (i j : Fin 3) :
    blochEntry (A * B) i j = ∑ k : Fin 3, blochEntry A i k * blochEntry B k j := by
  have harg2 : pauliMat i * (A * B) * pauliMat j * ZOmegaSqrt2.adjoint (A * B)
      = pauliMat i * A * (B * pauliMat j * ZOmegaSqrt2.adjoint B) * ZOmegaSqrt2.adjoint A := by
    rw [ZOmegaSqrt2.adjoint_mul]; ext x y; simp only [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have hdist : pauliMat i * A * (∑ k : Fin 3, blochEntry B k j • pauliMat k) * ZOmegaSqrt2.adjoint A
      = ∑ k : Fin 3, blochEntry B k j • (pauliMat i * A * pauliMat k * ZOmegaSqrt2.adjoint A) := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, smul_eq_mul]
    ring
  rw [blochEntry, harg2, bloch_completeness_unitary hB j, hdist, Matrix.trace_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.trace_smul, smul_eq_mul]
  conv_rhs => rw [blochEntry]
  ring

end KMM

end SKEFTHawking.RossSelinger
