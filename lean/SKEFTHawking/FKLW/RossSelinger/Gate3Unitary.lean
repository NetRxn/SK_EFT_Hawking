/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 37) — unitarity of three-qubit words + the ℂ-norm transport

The ∀U headline composes three approximate z-rotation words; the error propagates through the
composition only because each word is **norm-preserving** (the intermediate states leave the
ancilla-initialized subspace, so the triangle-inequality steps need unitarity). This file supplies
that layer:

  * `adjoint8` / `IsUnitary8` — the ring-level conjugate-transpose and unitarity at dim 8;
    **every `Gate3` generator is unitary** (one kernel reduction over the 30-element `Fintype`),
    hence every word (`interp3_unitary`).
  * `toComplexMat8` — the entrywise `ℤ[ω][1/√2] → ℂ` embedding; it intertwines `adjoint8` with the
    conjugate transpose (`toComplex_conj`), so **embedded words are ℂ-unitary**
    (`toComplexMat8_interp3_unitary`).
  * `sumNormSq` — the squared ℓ²-norm `Σ normSq (x i)` on ℂ⁸ (handrolled; avoids `PiLp` friction);
    **embedded words preserve it** (`sumNormSq_mulVec_interp3`) — the norm-preservation the ∀U
    composition consumes.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` — generator unitarity is one kernel reduction (`decide +kernel`, top level).
-/

import SKEFTHawking.FKLW.RossSelinger.KMMZRotationHeadline

set_option autoImplicit false

open scoped Matrix

namespace SKEFTHawking.RossSelinger

/-! ### Fintype instances for the gate alphabets -/

instance : Fintype CliffordTGate where
  elems := ⟨([.H, .S, .T, .X, .Y, .Z, .id, .omega] : List CliffordTGate), by decide⟩
  complete := fun x => by cases x <;> decide

instance : Fintype Gate3 where
  elems := ⟨([.onSys .H, .onSys .S, .onSys .T, .onSys .X, .onSys .Y, .onSys .Z, .onSys .id,
    .onSys .omega, .onA1 .H, .onA1 .S, .onA1 .T, .onA1 .X, .onA1 .Y, .onA1 .Z, .onA1 .id,
    .onA1 .omega, .onA2 .H, .onA2 .S, .onA2 .T, .onA2 .X, .onA2 .Y, .onA2 .Z, .onA2 .id,
    .onA2 .omega, .cxsa, .cxsb, .cxab, .cxba, .cxas, .cxbs] : List Gate3), by decide⟩
  complete := fun x => by
    cases x <;> first | decide | (rename_i c; cases c <;> decide)

namespace ZOmegaSqrt2

/-- `conj` distributes over finite sums. -/
theorem conj_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ZOmegaSqrt2) :
    conj (∑ i ∈ s, f i) = ∑ i ∈ s, conj (f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, conj_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, conj_add, ih]

end ZOmegaSqrt2

namespace Gate3

open ZOmegaSqrt2

/-! ### Ring-level unitarity at dim 8 -/

/-- The conjugate transpose over `ℤ[ω][1/√2]` at dim 8. -/
def adjoint8 (M : Mat8) : Mat8 := fun i j => conj (M j i)

/-- Ring-level unitarity: `M† · M = 1`. -/
def IsUnitary8 (M : Mat8) : Prop := adjoint8 M * M = 1

instance (M : Mat8) : Decidable (IsUnitary8 M) := by unfold IsUnitary8; infer_instance

/-- **Every generator is unitary** — one kernel reduction over the 30-element alphabet. -/
theorem gateMatrix3_unitary : ∀ g : Gate3, IsUnitary8 (gateMatrix3 g) := by decide +kernel

/-- The adjoint is multiplicative-reversing: `(M·N)† = N†·M†`. -/
theorem adjoint8_mul (M N : Mat8) : adjoint8 (M * N) = adjoint8 N * adjoint8 M := by
  funext i j
  show conj ((M * N) j i) = (adjoint8 N * adjoint8 M) i j
  rw [Matrix.mul_apply, Matrix.mul_apply, ZOmegaSqrt2.conj_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show conj (M j k * N k i) = conj (N k i) * conj (M j k)
  rw [conj_mul]
  ring

theorem adjoint8_one : adjoint8 (1 : Mat8) = 1 := by decide

/-- **Every word is unitary** (ring level). -/
theorem interp3_unitary (w : List Gate3) : IsUnitary8 (interp3 w) := by
  induction w with
  | nil =>
    show adjoint8 (1 : Mat8) * 1 = 1
    rw [adjoint8_one]
    exact Matrix.one_mul 1
  | cons g gs ih =>
    show adjoint8 (gateMatrix3 g * interp3 gs) * (gateMatrix3 g * interp3 gs) = 1
    rw [adjoint8_mul]
    calc adjoint8 (interp3 gs) * adjoint8 (gateMatrix3 g) * (gateMatrix3 g * interp3 gs)
        = adjoint8 (interp3 gs) *
            (adjoint8 (gateMatrix3 g) * (gateMatrix3 g * interp3 gs)) := Matrix.mul_assoc _ _ _
      _ = adjoint8 (interp3 gs) *
            (adjoint8 (gateMatrix3 g) * gateMatrix3 g * interp3 gs) :=
          congrArg (adjoint8 (interp3 gs) * ·) (Matrix.mul_assoc _ _ _).symm
      _ = adjoint8 (interp3 gs) * ((1 : Mat8) * interp3 gs) :=
          congrArg (adjoint8 (interp3 gs) * ·)
            (congrArg (· * interp3 gs) (gateMatrix3_unitary g))
      _ = adjoint8 (interp3 gs) * interp3 gs :=
          congrArg (adjoint8 (interp3 gs) * ·) (one_mul _)
      _ = 1 := ih

/-! ### The ℂ-embedding at dim 8 -/

/-- The entrywise `ℤ[ω][1/√2] → ℂ` embedding at dim 8. -/
noncomputable def toComplexMat8 (M : Mat8) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  ZOmegaSqrt2.toComplex.mapMatrix M

theorem toComplexMat8_mul (M N : Mat8) :
    toComplexMat8 (M * N) = toComplexMat8 M * toComplexMat8 N :=
  map_mul (RingHom.mapMatrix ZOmegaSqrt2.toComplex) M N

theorem toComplexMat8_one : toComplexMat8 (1 : Mat8) = 1 :=
  map_one (RingHom.mapMatrix ZOmegaSqrt2.toComplex)

/-- The embedding intertwines `adjoint8` with the complex conjugate transpose. -/
theorem toComplexMat8_adjoint8 (M : Mat8) :
    toComplexMat8 (adjoint8 M) = (toComplexMat8 M)ᴴ := by
  funext i j
  show ZOmegaSqrt2.toComplex (conj (M j i)) = star (ZOmegaSqrt2.toComplex (M j i))
  exact ZOmegaSqrt2.toComplex_conj (M j i)

/-- **Embedded words are ℂ-unitary**: `(W_ℂ)ᴴ · W_ℂ = 1`. -/
theorem toComplexMat8_interp3_unitary (w : List Gate3) :
    (toComplexMat8 (interp3 w))ᴴ * toComplexMat8 (interp3 w) = 1 := by
  rw [← toComplexMat8_adjoint8, ← toComplexMat8_mul, interp3_unitary w, toComplexMat8_one]

/-! ### Squared ℓ²-norm preservation -/

/-- The squared ℓ²-norm on ℂ-vectors over the 8-dimensional register. -/
noncomputable def sumNormSq (x : Fin 2 × Fin 2 × Fin 2 → ℂ) : ℝ :=
  ∑ i, Complex.normSq (x i)

/-- A ℂ-unitary matrix preserves the squared ℓ²-norm of `mulVec`. -/
theorem sumNormSq_mulVec_of_unitary
    {U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ}
    (hU : Uᴴ * U = 1) (x : Fin 2 × Fin 2 × Fin 2 → ℂ) :
    sumNormSq (U.mulVec x) = sumNormSq x := by
  have hdot : ∀ y : Fin 2 × Fin 2 × Fin 2 → ℂ, star y ⬝ᵥ y = (sumNormSq y : ℂ) := by
    intro y
    rw [sumNormSq, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show star (y i) * y i = (Complex.normSq (y i) : ℂ)
    rw [show star (y i) = (starRingEnd ℂ) (y i) from rfl, mul_comm, Complex.mul_conj]
  have key : star (U.mulVec x) ⬝ᵥ U.mulVec x = star x ⬝ᵥ x := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
      Matrix.vecMul_one]
  have hfinal := (hdot (U.mulVec x)).symm.trans (key.trans (hdot x))
  exact_mod_cast hfinal

/-- **Embedded words preserve the squared ℓ²-norm** — the norm-preservation the ∀U composition
consumes. -/
theorem sumNormSq_mulVec_interp3 (w : List Gate3) (x : Fin 2 × Fin 2 × Fin 2 → ℂ) :
    sumNormSq ((toComplexMat8 (interp3 w)).mulVec x) = sumNormSq x :=
  sumNormSq_mulVec_of_unitary (toComplexMat8_interp3_unitary w) x

end Gate3
end SKEFTHawking.RossSelinger
