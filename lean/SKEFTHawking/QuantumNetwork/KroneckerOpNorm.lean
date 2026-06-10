import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# `KroneckerOpNorm`: L²-operator-norm bound for `A ⊗ₖ I` (Phase 6AP, Wave 2)

For `A : Matrix m n 𝕜` (with `RCLike 𝕜`) and the identity matrix on a finite type `p`,
the L²-operator norm of the Kronecker product satisfies

  `‖A ⊗ₖ (1 : Matrix p p 𝕜)‖_op ≤ ‖A‖_op`.

This is the standard "attaching an ancilla register does not increase the operator norm"
fact (textbook; e.g. Watrous, *The Theory of Quantum Information*, §1.1/§3.3 background) —
the substrate step every diamond-norm comparison with an auxiliary system needs, and in
particular the ancilla-register step of the Aharonov–Kitaev–Nisan-style bound
`‖Φ_U − Φ_V‖_♦ ≤ 2‖U − V‖_op` (Phase 6AP W3). Absent from Mathlib (verified by search);
Mathlib-upstream candidate.

## Proof strategy

For `x ∈ EuclideanSpace 𝕜 (n × p)` the action of `A ⊗ₖ I` factors along the `p` axis:
`((A ⊗ₖ I) *ᵥ x) (i, k) = (A *ᵥ x_k) i` where `x_k := fun j => x (j, k)` is the `k`-th
column slice. By the per-column L²-opnorm bound (`Matrix.l2_opNorm_mulVec`):

  `‖(A ⊗ₖ 1) *ᵥ x‖² = ∑_k ‖A *ᵥ x_k‖² ≤ ∑_k ‖A‖²·‖x_k‖² = ‖A‖²·‖x‖²`.

Invariants: kernel-pure, zero sorry, no project-local axioms (#15), no `maxHeartbeats` (#10)
— the proof is decomposed into focused sub-lemmas.
-/

namespace SKEFTHawking.QuantumNetwork.KroneckerOpNorm

open scoped Matrix Kronecker Matrix.Norms.L2Operator
open WithLp

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-! ### Step 1: pointwise action of `A ⊗ₖ 1` -/

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The action of `A ⊗ₖ (1 : Matrix p p 𝕜)` on a vector indexed by `n × p`, evaluated at
    `(i, k)`, equals the action of `A` on the `k`-th column slice `fun j => x (j, k)`,
    evaluated at `i`. -/
lemma kronecker_one_mulVec_apply (A : Matrix m n 𝕜)
    (x : (n × p) → 𝕜) (i : m) (k : p) :
    ((A ⊗ₖ (1 : Matrix p p 𝕜)) *ᵥ x) (i, k)
      = (A *ᵥ (fun j => x (j, k))) i := by
  -- Both sides are `dotProduct` sums.
  show ((fun jl => (A ⊗ₖ (1 : Matrix p p 𝕜)) (i, k) jl) ⬝ᵥ x)
    = ((fun j => A i j) ⬝ᵥ (fun j => x (j, k)))
  rw [show ((fun jl => (A ⊗ₖ (1 : Matrix p p 𝕜)) (i, k) jl) ⬝ᵥ x)
        = ∑ jl : n × p, (A ⊗ₖ (1 : Matrix p p 𝕜)) (i, k) jl * x jl from rfl]
  rw [show ((fun j => A i j) ⬝ᵥ (fun j => x (j, k))) = ∑ j : n, A i j * x (j, k) from rfl]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_eq_single k]
  · -- l = k case.
    rw [Matrix.kroneckerMap_apply]
    simp [Matrix.one_apply_eq]
  · -- l ≠ k case.
    intro l _ hlk
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hlk)]
    ring
  · intro h
    exact absurd (Finset.mem_univ k) h

/-! ### Step 2: column-slice norm-square decomposition -/

omit [DecidableEq n] [DecidableEq p] in
/-- Squared L² norm of an `EuclideanSpace 𝕜 (n × p)` vector decomposes as a nested sum:
    `‖x‖² = ∑_k ∑_j |x (j, k)|²`. -/
lemma euclideanSpace_norm_sq_factored (x : EuclideanSpace 𝕜 (n × p)) :
    ‖x‖ ^ 2 = ∑ k : p, ∑ j : n, ‖x.ofLp (j, k)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]

omit [Fintype p] [DecidableEq n] [DecidableEq p] in
/-- Squared L² norm of the column-slice `fun j => x (j, k)` viewed as an
    `EuclideanSpace 𝕜 n` (via `toLp`) equals `∑_j |x (j, k)|²`. -/
lemma col_slice_norm_sq (x : (n × p) → 𝕜) (k : p) :
    ‖(toLp 2 (fun j => x (j, k)) : EuclideanSpace 𝕜 n)‖ ^ 2 = ∑ j : n, ‖x (j, k)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

/-! ### Step 3: per-column L²-opnorm bound -/

omit [Fintype p] [DecidableEq m] [DecidableEq p] in
/-- For each column index `k`, `‖toLp 2 (A *ᵥ x_k)‖² ≤ ‖A‖² · ‖toLp 2 x_k‖²`, where
    `x_k := fun j => x (j, k)`. -/
lemma col_action_norm_sq_le (A : Matrix m n 𝕜) (x : (n × p) → 𝕜) (k : p) :
    ‖(toLp 2 (A *ᵥ (fun j => x (j, k))) : EuclideanSpace 𝕜 m)‖ ^ 2
      ≤ ‖A‖ ^ 2 * ‖(toLp 2 (fun j => x (j, k)) : EuclideanSpace 𝕜 n)‖ ^ 2 := by
  -- Use Matrix.l2_opNorm_mulVec on the column slice.
  have h_le : ‖(toLp 2 (A *ᵥ (fun j => x (j, k))) : EuclideanSpace 𝕜 m)‖
      ≤ ‖A‖ * ‖(toLp 2 (fun j => x (j, k)) : EuclideanSpace 𝕜 n)‖ := by
    have h_apply := Matrix.l2_opNorm_mulVec A
      (toLp 2 (fun j => x (j, k)) : EuclideanSpace 𝕜 n)
    -- Goal of h_apply: ‖(EuclideanSpace.equiv m 𝕜).symm (A *ᵥ ofLp _)‖ ≤ ‖A‖ * ‖_‖.
    -- ofLp (toLp 2 v) = v (def), so A *ᵥ ofLp _ = A *ᵥ v. The .symm wrap = toLp 2.
    convert h_apply using 1
  have h_lhs_nn : 0 ≤ ‖(toLp 2 (A *ᵥ (fun j => x (j, k))) : EuclideanSpace 𝕜 m)‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ‖A‖ * ‖(toLp 2 (fun j => x (j, k)) : EuclideanSpace 𝕜 n)‖ := by positivity
  nlinarith [h_le, h_lhs_nn, h_rhs_nn]

/-! ### Step 4: square of opnorm action equals nested sum of column actions -/

omit [DecidableEq m] in
/-- The squared norm `‖toEuclideanLin (A ⊗ₖ I) x‖²` decomposes as a sum over `k : p` of the
    squared norm of the per-column action `A *ᵥ x_k`. -/
lemma kronecker_one_action_norm_sq (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 (n × p)) :
    ‖((Matrix.toEuclideanLin (𝕜 := 𝕜) (m := m × p) (n := n × p)).trans
        LinearMap.toContinuousLinearMap) (A ⊗ₖ (1 : Matrix p p 𝕜)) x‖ ^ 2
      = ∑ k : p, ‖(toLp 2 (A *ᵥ (fun j => x.ofLp (j, k))) : EuclideanSpace 𝕜 m)‖ ^ 2 := by
  -- The action is toLp 2 ((A ⊗ₖ I) *ᵥ ofLp x) by toEuclideanLin_apply.
  show ‖toLp 2 ((A ⊗ₖ (1 : Matrix p p 𝕜)) *ᵥ x.ofLp)‖ ^ 2 = _
  rw [EuclideanSpace.norm_sq_eq]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Goal: ‖(toLp 2 ((A ⊗ I) *ᵥ x.ofLp)).ofLp (i, k)‖² = ‖(toLp 2 (A *ᵥ ...)).ofLp i‖².
  -- (toLp 2 v).ofLp = v definitionally, so reduce to entry-wise equality of mulVec.
  show ‖((A ⊗ₖ (1 : Matrix p p 𝕜)) *ᵥ x.ofLp) (i, k)‖ ^ 2
    = ‖(A *ᵥ (fun j => x.ofLp (j, k))) i‖ ^ 2
  rw [kronecker_one_mulVec_apply]

/-! ### Main result: `‖A ⊗ₖ I‖_op ≤ ‖A‖_op` -/

omit [DecidableEq m] in
/-- The L²-operator norm of `A ⊗ₖ (1 : Matrix p p 𝕜)` is at most `‖A‖_op`: attaching an
    identity ancilla register never increases the operator norm. The substrate step for
    diamond-norm comparisons with an auxiliary register (Phase 6AP W3). -/
theorem l2_opNorm_kronecker_one_le (A : Matrix m n 𝕜) :
    ‖A ⊗ₖ (1 : Matrix p p 𝕜)‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro x
  -- Strategy: bound the squared form, then take sqrt.
  have h_rhs_nn : 0 ≤ ‖A‖ * ‖x‖ := by positivity
  have h_lhs_nn : 0 ≤ ‖((Matrix.toEuclideanLin (𝕜 := 𝕜) (m := m × p) (n := n × p)).trans
      LinearMap.toContinuousLinearMap) (A ⊗ₖ (1 : Matrix p p 𝕜)) x‖ := norm_nonneg _
  rw [← Real.sqrt_sq h_rhs_nn, ← Real.sqrt_sq h_lhs_nn]
  refine Real.sqrt_le_sqrt ?_
  -- Squared LHS = ∑ k, ‖toLp 2 (A *ᵥ x_k)‖².
  rw [kronecker_one_action_norm_sq]
  -- Bound each term by ‖A‖² · ‖toLp 2 x_k‖² via per-column lemma.
  have h_per_col := fun k : p => col_action_norm_sq_le A x.ofLp k
  refine (Finset.sum_le_sum (fun k _ => h_per_col k)).trans ?_
  -- Pull constant ‖A‖² out: ∑ k, ‖A‖² · ‖x_k‖² = ‖A‖² · ∑ k, ‖x_k‖².
  rw [← Finset.mul_sum]
  -- ∑ k, ‖x_k‖² = ‖x‖² via euclideanSpace_norm_sq_factored.
  have h_sum_eq : ∑ k : p, ‖(toLp 2 (fun j => x.ofLp (j, k)) : EuclideanSpace 𝕜 n)‖ ^ 2
      = ∑ k : p, ∑ j : n, ‖x.ofLp (j, k)‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact col_slice_norm_sq x.ofLp k
  rw [h_sum_eq, ← euclideanSpace_norm_sq_factored]
  -- Final: ‖A‖² · ‖x‖² ≤ (‖A‖ · ‖x‖)² = ‖A‖² · ‖x‖² (equal).
  have h_sq : (‖A‖ * ‖x‖) ^ 2 = ‖A‖ ^ 2 * ‖x‖ ^ 2 := by ring
  rw [h_sq]

end SKEFTHawking.QuantumNetwork.KroneckerOpNorm
