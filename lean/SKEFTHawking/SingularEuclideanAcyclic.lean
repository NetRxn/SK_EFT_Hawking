import Mathlib
import SKEFTHawking.SingularHomotopyInvariance

/-!
# Acyclicity of Euclidean space

`ℝⁿ` is contractible via the straight-line contraction `H(x, t) = (1 - t) • x` (to the origin), so
`Hₖ(ℝⁿ; ℤ/2) = 0` for `k ≥ 1`. This instantiates the abstract
`cycle_mem_boundaries_of_contraction` and is the base case for the sphere / local-homology
computations.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularHomotopyInvariance

namespace SKEFTHawking.SingularEuclideanAcyclic

/-- `ℝⁿ` as a topological space object. -/
abbrev Eucl (n : ℕ) : TopCat := TopCat.of (EuclideanSpace ℝ (Fin n))

/-- The **straight-line contraction** `H(x, t) = (1 - t) • x` of `ℝⁿ` to the origin. -/
noncomputable def contraction (n : ℕ) : C(↑(Eucl n) × unitInterval, ↑(Eucl n)) :=
  ⟨fun p => (1 - (p.2 : ℝ)) • p.1,
    (Continuous.smul (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
      continuous_fst)⟩

@[simp] theorem contraction_apply (n : ℕ) (x : ↑(Eucl n)) (t : unitInterval) :
    contraction n (x, t) = (1 - (t : ℝ)) • x := rfl

/-- The `t = 0` slice of the contraction is the identity (`(1 - 0) • x = x`). -/
theorem slice_contraction_zero (n : ℕ) : slice (contraction n) 0 = ContinuousMap.id ↑(Eucl n) := by
  refine ContinuousMap.ext fun x => ?_
  show (1 - ((0 : unitInterval) : ℝ)) • x = x
  simp

/-- The `t = 1` slice of the contraction is the constant map at the origin (`(1 - 1) • x = 0`). -/
theorem slice_contraction_one (n : ℕ) :
    slice (contraction n) 1 = ContinuousMap.const ↑(Eucl n) 0 := by
  refine ContinuousMap.ext fun x => ?_
  show (1 - ((1 : unitInterval) : ℝ)) • x = 0
  simp

/-- **`ℝⁿ` is acyclic**: every cycle in degree `k + 1` is a boundary, so `Hₖ₊₁(ℝⁿ; ℤ/2) = 0`. -/
theorem cycle_mem_boundaries (n k : ℕ) (z : SingularChain (Eucl n) (k + 1))
    (hz : chainBoundary (Eucl n) k z = 0) :
    z ∈ boundaries (Eucl n) (k + 1) :=
  cycle_mem_boundaries_of_contraction (contraction n) 0 (slice_contraction_zero n)
    (slice_contraction_one n) z hz

/-- **`ℝⁿ` is reduced-acyclic**: the augmentation `ε̄ : H₀(ℝⁿ) → ℤ/2` is injective (`H̃₀(ℝⁿ) = 0`),
since `ℝⁿ` is contractible. The base reduced-acyclic space for the bottom suspension. -/
theorem eucl_augH_injective (n : ℕ) : Function.Injective (SingularH0.augH (Eucl n)) :=
  augH_injective_of_contraction (contraction n) 0 (slice_contraction_zero n)
    (slice_contraction_one n)

end SKEFTHawking.SingularEuclideanAcyclic
