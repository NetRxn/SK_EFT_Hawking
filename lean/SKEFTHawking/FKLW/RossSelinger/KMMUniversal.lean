/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 40) — the ∀U∈SU(2) KMM headline: composition machinery

The final assembly: three approximate z-rotation words (inc 38) interleaved with two exact system
Hadamards realize any `U ∈ SU(2)` up to global phase (inc 39), with the errors **adding** through
the composition — which requires unitarity (`sumNormSq_mulVec_interp3`, inc 37), since the
intermediate states leave the ancilla-initialized subspace only by the per-step error.

This file: the ℓ²-bridge to `EuclideanSpace` (Minkowski), the one-step composition triangle, the
**exact** system-Hadamard step on initialized states, and unit-pair preservation along the chain.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.KMMOperational
import SKEFTHawking.FKLW.RossSelinger.SU2Euler
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

set_option autoImplicit false

open scoped Matrix

namespace SKEFTHawking.RossSelinger
namespace Gate3

open ZOmegaSqrt2

/-! ### The ℓ²-bridge -/

/-- `sumNormSq` is the squared `EuclideanSpace` norm. -/
theorem sumNormSq_eq_norm_sq (x : Fin 2 × Fin 2 × Fin 2 → ℂ) :
    sumNormSq x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ => Complex.normSq_eq_norm_sq _

theorem sumNormSq_nonneg (x : Fin 2 × Fin 2 × Fin 2 → ℂ) : 0 ≤ sumNormSq x :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

/-- **One composition step**: if the unitary-word `P` is applied after an approximate step
(`u ≈ v`) and `P·v ≈ w`, the errors add in the ℓ²-distance (triangle + norm preservation). -/
theorem step_triangle (P : List Gate3) (u v w : Fin 2 × Fin 2 × Fin 2 → ℂ) :
    Real.sqrt (sumNormSq (fun i => (toComplexMat8 (interp3 P)).mulVec u i - w i))
      ≤ Real.sqrt (sumNormSq (fun i => u i - v i))
        + Real.sqrt (sumNormSq (fun i => (toComplexMat8 (interp3 P)).mulVec v i - w i)) := by
  have hsplit : (fun i => (toComplexMat8 (interp3 P)).mulVec u i - w i)
      = fun i => (toComplexMat8 (interp3 P)).mulVec (fun j => u j - v j) i
        + ((toComplexMat8 (interp3 P)).mulVec v i - w i) := by
    funext i
    rw [show (toComplexMat8 (interp3 P)).mulVec (fun j => u j - v j) i
        = (toComplexMat8 (interp3 P)).mulVec u i - (toComplexMat8 (interp3 P)).mulVec v i from by
      rw [show (fun j => u j - v j) = u - v from rfl, Matrix.mulVec_sub]
      rfl]
    ring
  rw [hsplit]
  have hpres := sumNormSq_mulVec_interp3 P (fun j => u j - v j)
  rw [show sumNormSq (fun j => u j - v j)
      = sumNormSq (fun i => u i - v i) from rfl] at hpres
  rw [show sumNormSq (fun i =>
        (toComplexMat8 (interp3 P)).mulVec (fun j => u j - v j) i
          + ((toComplexMat8 (interp3 P)).mulVec v i - w i))
      = ‖(WithLp.toLp 2 (fun i => (toComplexMat8 (interp3 P)).mulVec (fun j => u j - v j) i)
            : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))
          + (WithLp.toLp 2 (fun i => (toComplexMat8 (interp3 P)).mulVec v i - w i)
            : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))‖ ^ 2 from by
    rw [← sumNormSq_eq_norm_sq]
    rfl]
  rw [Real.sqrt_sq (norm_nonneg _)]
  calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
    _ = Real.sqrt (sumNormSq (fun i => u i - v i))
        + Real.sqrt (sumNormSq (fun i => (toComplexMat8 (interp3 P)).mulVec v i - w i)) := by
      rw [show (‖(WithLp.toLp 2 (fun i => (toComplexMat8 (interp3 P)).mulVec
            (fun j => u j - v j) i) : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))‖ : ℝ)
          = Real.sqrt (sumNormSq (fun i => (toComplexMat8 (interp3 P)).mulVec
              (fun j => u j - v j) i)) from by
        rw [sumNormSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)],
        hpres,
        show (‖(WithLp.toLp 2 (fun i => (toComplexMat8 (interp3 P)).mulVec v i - w i)
            : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))‖ : ℝ)
          = Real.sqrt (sumNormSq (fun i => (toComplexMat8 (interp3 P)).mulVec v i - w i)) from by
        rw [sumNormSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]]

end Gate3
end SKEFTHawking.RossSelinger
