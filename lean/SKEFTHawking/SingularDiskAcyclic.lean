import Mathlib
import SKEFTHawking.SingularHomotopyInvariance

/-!
# Acyclicity of the closed disk

The closed unit ball `Dⁿ ⊆ ℝⁿ` is star-convex about `0`, so the straight-line contraction
`H(x, t) = (1 - t) • x` (which stays in the ball, `‖(1 - t) • x‖ ≤ ‖x‖ ≤ 1`) makes it contractible:
`Hₖ(Dⁿ; ℤ/2) = 0` for `k ≥ 1`. The hemispheres of a sphere are disks, so this is an input to the
Mayer–Vietoris computation of sphere homology.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularHomotopyInvariance

namespace SKEFTHawking.SingularDiskAcyclic

/-- The closed unit ball `Dⁿ ⊆ ℝⁿ` as a topological space object. -/
abbrev Disk (n : ℕ) : TopCat := TopCat.of (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

variable {n : ℕ}

/-- The contraction stays in the disk: `(1 - t) • x` has norm `≤ ‖x‖ ≤ 1`. -/
theorem smul_mem_disk (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) (t : unitInterval) :
    (1 - (t : ℝ)) • (x : EuclideanSpace ℝ (Fin n)) ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [t.2.2] : (0 : ℝ) ≤ 1 - (t : ℝ))]
  have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
    have := x.2; rw [Metric.mem_closedBall, dist_zero_right] at this; exact this
  exact mul_le_one₀ (by linarith [t.2.1]) (norm_nonneg _) hx

/-- The **straight-line contraction** `H(x, t) = (1 - t) • x` of the disk to its center. -/
noncomputable def contraction : C(↑(Disk n) × unitInterval, ↑(Disk n)) where
  toFun p := ⟨(1 - (p.2 : ℝ)) • (p.1 : EuclideanSpace ℝ (Fin n)), smul_mem_disk p.1 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.smul ?_ (continuous_subtype_val.comp continuous_fst)) _
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd))

/-- The `t = 0` slice is the identity. -/
theorem slice_contraction_zero : slice (contraction (n := n)) 0 = ContinuousMap.id ↑(Disk n) := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  show (1 - ((0 : unitInterval) : ℝ)) • (x : EuclideanSpace ℝ (Fin n)) = (x : _)
  simp

/-- The `t = 1` slice is the constant map at the center `0`. -/
theorem slice_contraction_one :
    slice (contraction (n := n)) 1 = ContinuousMap.const ↑(Disk n) ⟨0, by simp⟩ := by
  refine ContinuousMap.ext fun x => Subtype.ext ?_
  show (1 - ((1 : unitInterval) : ℝ)) • (x : EuclideanSpace ℝ (Fin n)) = (0 : EuclideanSpace ℝ (Fin n))
  simp

/-- **`Dⁿ` is acyclic**: every cycle in degree `k + 1` is a boundary, so `Hₖ₊₁(Dⁿ; ℤ/2) = 0`. -/
theorem cycle_mem_boundaries (k : ℕ) (z : SingularChain (Disk n) (k + 1))
    (hz : chainBoundary (Disk n) k z = 0) :
    z ∈ boundaries (Disk n) (k + 1) :=
  cycle_mem_boundaries_of_contraction contraction ⟨0, by simp⟩ slice_contraction_zero
    slice_contraction_one z hz

end SKEFTHawking.SingularDiskAcyclic
