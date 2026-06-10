import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Row-sum → L²-operator-norm bridge (Phase 6AP, Wave 3b)

The hypothesis-form norm bridge: if every row of `A` has ℓ¹-sum at most `C`, then

  `‖A‖_{L²op} ≤ √(card m) · C`.

Per row, Cauchy–Schwarz-free: `|(Ax)ᵢ| ≤ (∑ⱼ|aᵢⱼ|)·‖x‖ ≤ C·‖x‖` (each coordinate of an
ℓ² vector is bounded by its norm), then `‖Ax‖² = ∑ᵢ|(Ax)ᵢ|² ≤ card·C²·‖x‖²`.

Stated with the row-sum hypothesis EXPLICIT (`∀ i, ∑ j, ‖A i j‖ ≤ C`) rather than against
the `linftyOpNorm` instance, so the lemma composes with files elaborated under either
matrix-norm instance without notation collision — in particular it converts the Clifford+T
compiler's L∞-operator-norm error (`Matrix.linfty_opNorm_def` exposes exactly this row-sum
form) into the L²-operator-norm input of the diamond AKN bound (`UnitaryDiamond.lean`).

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork.MatrixNormBridge

open scoped Matrix Matrix.Norms.L2Operator
open WithLp

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Each coordinate of an ℓ² vector is bounded by its norm: `‖x j‖ ≤ ‖x‖`. -/
lemma coord_norm_le (x : EuclideanSpace ℂ n) (j : n) : ‖x.ofLp j‖ ≤ ‖x‖ := by
  have hsq : ‖x.ofLp j‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (f := fun k => ‖x.ofLp k‖ ^ 2)
      (fun k _ => by positivity) (Finset.mem_univ j)
  nlinarith [norm_nonneg (x.ofLp j), norm_nonneg x]

/-- **Row-sum → L²-opnorm bridge:** if every row ℓ¹-sum of `A` is at most `C`, then
`‖A‖_{L²op} ≤ √(card m) · C`. -/
theorem l2_opNorm_le_sqrt_card_mul_of_rowSum_le (A : Matrix m n ℂ) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, ∑ j, ‖A i j‖ ≤ C) :
    ‖A‖ ≤ Real.sqrt (Fintype.card m) * C := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  show ‖(toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℂ m)‖ ≤ Real.sqrt (Fintype.card m) * C * ‖x‖
  -- per-row bound: ‖(Ax)ᵢ‖ ≤ C·‖x‖
  have hrow : ∀ i, ‖(A *ᵥ x.ofLp) i‖ ≤ C * ‖x‖ := by
    intro i
    calc ‖∑ j, A i j * x.ofLp j‖
        ≤ ∑ j, ‖A i j * x.ofLp j‖ := norm_sum_le _ _
      _ = ∑ j, ‖A i j‖ * ‖x.ofLp j‖ := by simp [norm_mul]
      _ ≤ ∑ j, ‖A i j‖ * ‖x‖ :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (coord_norm_le x j) (norm_nonneg _)
      _ = (∑ j, ‖A i j‖) * ‖x‖ := by rw [Finset.sum_mul]
      _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right (h i) (norm_nonneg _)
  -- squared form: ‖Ax‖² ≤ card·(C‖x‖)²
  have hsq : ‖(toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℂ m)‖ ^ 2
      ≤ (Fintype.card m : ℝ) * (C * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hbound : ∀ i : m, ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := fun i => by
      have := hrow i
      nlinarith [norm_nonneg ((A *ᵥ x.ofLp) i)]
    calc ∑ i : m, ‖(toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℂ m).ofLp i‖ ^ 2
        = ∑ i : m, ‖(A *ᵥ x.ofLp) i‖ ^ 2 := rfl
      _ ≤ ∑ _i : m, (C * ‖x‖) ^ 2 := Finset.sum_le_sum fun i _ => hbound i
      _ = (Fintype.card m : ℝ) * (C * ‖x‖) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- take square roots
  have hxnn : 0 ≤ C * ‖x‖ := by positivity
  have hT := norm_nonneg (toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℂ m)
  have hfin : ‖(toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℂ m)‖
      ≤ Real.sqrt ((Fintype.card m : ℝ) * (C * ‖x‖) ^ 2) := by
    rw [← Real.sqrt_sq hT]
    exact Real.sqrt_le_sqrt hsq
  calc ‖(toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℂ m)‖
      ≤ Real.sqrt ((Fintype.card m : ℝ) * (C * ‖x‖) ^ 2) := hfin
    _ = Real.sqrt (Fintype.card m) * (C * ‖x‖) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hxnn]
    _ = Real.sqrt (Fintype.card m) * C * ‖x‖ := by ring

end SKEFTHawking.QuantumNetwork.MatrixNormBridge
