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

/-! ### The exact system-Hadamard step and pair-norm preservation -/

/-- The system Hadamard acts **exactly** on initialized states:
`H_s · (ψ ⊗ |00⟩) = (Hψ) ⊗ |00⟩`. -/
theorem sysH_step (α' β' : ℂ) :
    (toComplexMat8 (gateMatrix3 (.onSys .H))).mulVec (initState α' β')
      = initState (((Real.sqrt 2)⁻¹ : ℂ) * (α' + β')) (((Real.sqrt 2)⁻¹ : ℂ) * (α' - β')) := by
  have hcases : ∀ i : Fin 2 × Fin 2 × Fin 2, i = (0, 0, 0) ∨ i = (0, 0, 1) ∨ i = (0, 1, 0) ∨
      i = (0, 1, 1) ∨ i = (1, 0, 0) ∨ i = (1, 0, 1) ∨ i = (1, 1, 0) ∨ i = (1, 1, 1) := by decide
  have hentry : ∀ (s p s' p'), toComplexMat8 (gateMatrix3 (.onSys .H)) (s, p) (s', p')
      = ZOmegaSqrt2.toComplex (CliffordTGate.gateMatrix .H s s' * (1 : Mat4) p p') := fun _ _ _ _ =>
    rfl
  have hone : ∀ p : Fin 2 × Fin 2, p ≠ ((0 : Fin 2), (0 : Fin 2)) →
      ∀ z : ZOmegaSqrt2, ZOmegaSqrt2.toComplex (z * (1 : Mat4) p ((0 : Fin 2), (0 : Fin 2))) = 0 :=
    fun p hp z => by rw [Matrix.one_apply_ne hp, mul_zero, map_zero]
  have hHcol : ∀ s : Fin 2, ∀ z : ZOmegaSqrt2,
      ZOmegaSqrt2.toComplex (z * (1 : Mat4) ((0 : Fin 2), (0 : Fin 2))
        ((0 : Fin 2), (0 : Fin 2))) = ZOmegaSqrt2.toComplex z := fun s z => by
    rw [Matrix.one_apply_eq, mul_one]
  funext i
  rw [show initState α' β' = (fun j => if j = ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2)) then α'
      else if j = ((1 : Fin 2), (0 : Fin 2), (0 : Fin 2)) then β' else 0) from rfl,
    mulVec_two_support _ (by decide)]
  have hinv := toComplex_invSqrt2
  rcases hcases i with h | h | h | h | h | h | h | h <;> subst h <;> rw [hentry, hentry]
  · rw [hHcol 0, hHcol 0,
      show CliffordTGate.gateMatrix .H 0 0 = ZOmegaSqrt2.invSqrt2 from rfl,
      show CliffordTGate.gateMatrix .H 0 1 = ZOmegaSqrt2.invSqrt2 from rfl, hinv,
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2))
        = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β') from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 2)) = 0 from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 2)) = 0 from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 2)) = 0 from rfl]
    ring
  · rw [hHcol 1, hHcol 1,
      show CliffordTGate.gateMatrix .H 1 0 = ZOmegaSqrt2.invSqrt2 from rfl,
      show CliffordTGate.gateMatrix .H 1 1 = -ZOmegaSqrt2.invSqrt2 from rfl, map_neg, hinv,
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 2))
        = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' - β') from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 2)) = 0 from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 2)) = 0 from rfl]
    ring
  · rw [hone _ (by decide), hone _ (by decide),
      show initState ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (α' + β')) ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (α' - β')) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2)) = 0 from rfl]
    ring

/-- `Λ`-steps preserve the system-pair norm. -/
theorem pair_norm_lam (φ : ℝ) (α' β' : ℂ) :
    Complex.normSq α' + Complex.normSq (β' * Complex.exp ((φ : ℂ) * Complex.I))
      = Complex.normSq α' + Complex.normSq β' := by
  rw [Complex.normSq_mul, show Complex.normSq (Complex.exp ((φ : ℂ) * Complex.I)) = 1 from by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num]
  ring

/-- `H`-steps preserve the system-pair norm (the `ℂ`-parallelogram law). -/
theorem pair_norm_h (α' β' : ℂ) :
    Complex.normSq (((Real.sqrt 2)⁻¹ : ℂ) * (α' + β'))
      + Complex.normSq (((Real.sqrt 2)⁻¹ : ℂ) * (α' - β'))
      = Complex.normSq α' + Complex.normSq β' := by
  rw [Complex.normSq_mul, Complex.normSq_mul,
    show Complex.normSq (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = 1 / 2 from by
      rw [Complex.normSq_inv, Complex.normSq_ofReal,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num]
  have hpar : Complex.normSq (α' + β') + Complex.normSq (α' - β')
      = 2 * (Complex.normSq α' + Complex.normSq β') := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im]
    ring
  linarith

end Gate3
end SKEFTHawking.RossSelinger
