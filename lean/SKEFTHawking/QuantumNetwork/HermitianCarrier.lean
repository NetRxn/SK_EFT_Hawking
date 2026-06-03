import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Diamond-SDP carrier: a single-topology Hilbert space of self-adjoint matrices (Phase 6AI)

The diamond-norm SDP strong-duality argument needs the cone-separation engine
(`ProperCone.relative_hyperplane_separation`, `geometric_hahn_banach_compact_closed`), which
requires `ContinuousSMul ℝ` / `CompleteSpace` / `LocallyConvexSpace` on the carrier. Building the
real Frobenius `InnerProductSpace ℝ` directly on the *subtype* `selfAdjoint (Matrix ι ι ℂ)`
(`SelfAdjointInnerProduct.lean`) creates a **topology instance diamond** — the unconditional
`instTopologicalSpaceSubtype` competes with the `InnerProductSpace.ofCore` metric topology, and the
three instances above fail to synthesize.

The fix is a **fresh one-field structure** `HermCarrier ι` (no inherited subtype topology), carrying
the Frobenius inner product `⟪A,B⟫ = Re tr(A·B)` via `InnerProductSpace.ofCore`. Because the carrier
is a fresh type, `ofCore` provides the *only* topology, so `ContinuousSMul`/`LocallyConvexSpace`
follow from the `NormedSpace`, and `CompleteSpace` follows once finite-dimensionality is supplied —
all verified to resolve. This unblocks the SDP zero-gap (`≥`) direction of `diamondDist_eq_choiSDP`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The diamond-SDP carrier**: a fresh one-field wrapper around the self-adjoint matrices, so the
Frobenius `InnerProductSpace ℝ` topology is the *only* topology (no subtype-topology diamond). -/
structure HermCarrier (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The underlying self-adjoint matrix. -/
  toSA : selfAdjoint (Matrix ι ι ℂ)

namespace HermCarrier

/-- The carrier is in bijection with the self-adjoint matrices. -/
def equivSA : HermCarrier ι ≃ selfAdjoint (Matrix ι ι ℂ) :=
  ⟨toSA, mk, fun _ => rfl, fun _ => rfl⟩

noncomputable instance : AddCommGroup (HermCarrier ι) := equivSA.addCommGroup
noncomputable instance : Module ℝ (HermCarrier ι) := equivSA.module ℝ

@[simp] theorem add_toSA (A B : HermCarrier ι) : (A + B).toSA = A.toSA + B.toSA := rfl
@[simp] theorem smul_toSA (r : ℝ) (A : HermCarrier ι) : (r • A).toSA = r • A.toSA := rfl
@[simp] theorem zero_toSA : (0 : HermCarrier ι).toSA = 0 := rfl

/-- The real Frobenius inner-product core on the carrier: `⟪A,B⟫ = Re tr(A·B)`. -/
noncomputable instance core : InnerProductSpace.Core ℝ (HermCarrier ι) where
  inner A B := ((A.toSA.1 * B.toSA.1).trace).re
  conj_inner_symm A B := by simp only [RCLike.conj_to_real]; rw [Matrix.trace_mul_comm]
  re_inner_nonneg A := by
    have h : A.toSA.1ᴴ = A.toSA.1 := A.toSA.2
    have := (Matrix.posSemidef_conjTranspose_mul_self A.toSA.1).trace_nonneg
    rw [h] at this; simpa using (Complex.le_def.mp this).1
  add_left A B C := by
    show (((A.toSA.1 + B.toSA.1) * C.toSA.1).trace).re = _
    simp [Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  smul_left A B r := by
    simp only [smul_toSA, selfAdjoint.val_smul, smul_mul_assoc, Matrix.trace, Matrix.diag_apply,
      Matrix.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, starRingEnd_apply, star_trivial, Complex.re_sum]
    rw [Finset.mul_sum]
  definite A h := by
    have hh : A.toSA.1ᴴ = A.toSA.1 := A.toSA.2
    have hps : (A.toSA.1ᴴ * A.toSA.1).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A.toSA.1
    have htr : (A.toSA.1ᴴ * A.toSA.1).trace = 0 := by
      rw [hh]; refine Complex.ext (by simpa using h) ?_
      have := (Complex.le_def.mp hps.trace_nonneg).2; rw [hh] at this; simpa using this.symm
    have hA0 : A.toSA = 0 :=
      Subtype.ext (Matrix.conjTranspose_mul_self_eq_zero.mp (hps.trace_eq_zero_iff.mp htr))
    exact equivSA.injective (hA0.trans zero_toSA.symm)

noncomputable instance : NormedAddCommGroup (HermCarrier ι) := (core (ι := ι)).toNormedAddCommGroup
noncomputable instance : InnerProductSpace ℝ (HermCarrier ι) := InnerProductSpace.ofCore inferInstance

/-- The inner product unfolds to `Re tr(A·B)`. -/
theorem inner_eq (A B : HermCarrier ι) :
    (inner ℝ A B : ℝ) = ((A.toSA.1 * B.toSA.1).trace).re := rfl

-- The topology diamond is gone: the separation-engine instances now resolve on the fresh carrier
-- (without `FiniteDimensional`, which is only needed for `CompleteSpace` at the Farkas step).
example : ContinuousSMul ℝ (HermCarrier ι) := inferInstance
example : LocallyConvexSpace ℝ (HermCarrier ι) := inferInstance

end HermCarrier

end SKEFTHawking.QuantumNetwork
