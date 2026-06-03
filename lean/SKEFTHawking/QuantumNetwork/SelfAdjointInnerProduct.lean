import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Real Frobenius inner product on self-adjoint matrices (Phase 6AI — diamond-SDP linchpin, brick 1)

The single object the diamond-norm SDP strong-duality argument is gated on: a genuine real
`InnerProductSpace ℝ` on the self-adjoint matrices `selfAdjoint (Matrix (Fin d) (Fin d) ℂ)`, with the
Frobenius / Hilbert–Schmidt inner product `⟪A, B⟫ = Re tr(A·B)` (real because `A,B` are Hermitian).
Mathlib's matrix inner products are `𝕜`-valued and PSD-weighted, so this is built from
`InnerProductSpace.ofCore`. With this instance the cone-duality engine
(`ProperCone.hyperplane_separation`, `geometric_hahn_banach_compact_closed`) applies to the
self-adjoint matrix space, unblocking the SDP zero-gap proof.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {d : ℕ}

/-- The real Frobenius inner-product core on self-adjoint complex matrices: `⟪A,B⟫ = Re tr(A·B)`.
Symmetry is trace cyclicity; positivity/definiteness come from `Aᴴ A ⪰ 0` and
`tr(AᴴA) = 0 ↔ A = 0`. -/
noncomputable instance selfAdjointCore :
    InnerProductSpace.Core ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) where
  inner A B := ((A.1 * B.1).trace).re
  conj_inner_symm A B := by simp only [RCLike.conj_to_real]; rw [Matrix.trace_mul_comm]
  re_inner_nonneg A := by
    have h : A.1ᴴ = A.1 := A.2
    have := (Matrix.posSemidef_conjTranspose_mul_self A.1).trace_nonneg
    rw [h] at this; simpa using (Complex.le_def.mp this).1
  add_left A B C := by simp [Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  smul_left A B r := by
    simp only [selfAdjoint.val_smul, Matrix.smul_mul, Matrix.trace_smul, RCLike.conj_to_real]
    exact Complex.smul_re r _
  definite A h := by
    have hh : A.1ᴴ = A.1 := A.2
    have hps : (A.1ᴴ * A.1).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A.1
    have htr : (A.1ᴴ * A.1).trace = 0 := by
      rw [hh]; refine Complex.ext (by simpa using h) ?_
      have := (Complex.le_def.mp hps.trace_nonneg).2; rw [hh] at this; simpa using this.symm
    exact Subtype.ext (Matrix.conjTranspose_mul_self_eq_zero.mp (hps.trace_eq_zero_iff.mp htr))

/-- The norm induced by the Frobenius inner product on self-adjoint matrices. -/
noncomputable instance selfAdjointNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :=
  (selfAdjointCore (d := d)).toNormedAddCommGroup

/-- **The real Frobenius `InnerProductSpace ℝ` on self-adjoint matrices** (the 6AI linchpin). -/
noncomputable instance selfAdjointInnerProductSpace :
    InnerProductSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :=
  InnerProductSpace.ofCore inferInstance

/-- The inner product unfolds to the real part of the trace of the product: `⟪A,B⟫ = Re tr(A·B)`. -/
theorem selfAdjoint_inner_eq (A B : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :
    (inner ℝ A B : ℝ) = ((A.1 * B.1).trace).re := rfl

end SKEFTHawking.QuantumNetwork
