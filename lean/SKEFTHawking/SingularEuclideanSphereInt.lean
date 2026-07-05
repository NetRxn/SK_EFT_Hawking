import Mathlib
import SKEFTHawking.SingularHomotopyInvarianceInt
import SKEFTHawking.SingularEuclideanAcyclic

/-!
# Integral acyclicity of Euclidean space

`ℝⁿ` is contractible via the straight-line contraction `H(x, t) = (1 - t) • x` to the origin, so
`Hₖ(ℝⁿ; ℤ) = 0` for `k ≥ 1`. This is the integral mirror of `SingularEuclideanAcyclic` (which proves
the `ℤ/2` version); the contraction `contraction n` and its two endpoint slices
(`slice_contraction_zero/one`) are **reused verbatim** (they are coefficient-free continuous maps),
and the acyclicity now flows through the integral signed-prism engine
`SingularHomotopyInvarianceInt.cycle_mem_boundaries_of_contractionInt`.

The integral base case for the sphere / local-homology computations feeding the integral local
class `H₄(M|x; ℤ) ≅ ℤ`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularEuclideanAcyclic (Eucl contraction slice_contraction_zero slice_contraction_one)

namespace SKEFTHawking.SingularEuclideanAcyclicInt

/-- **`ℝⁿ` is integrally acyclic**: every cycle in degree `k + 1` is a boundary, so
`Hₖ₊₁(ℝⁿ; ℤ) = 0`. Reuses the mod-2 file's contraction (a coefficient-free continuous map) through
the integral signed-prism acyclicity engine. -/
theorem cycle_mem_boundariesInt (n k : ℕ) (z : SingularChainInt (Eucl n) (k + 1))
    (hz : chainBoundary (Eucl n) k z = 0) :
    z ∈ boundaries (Eucl n) (k + 1) :=
  SingularHomotopyInvarianceInt.cycle_mem_boundaries_of_contractionInt (contraction n) 0
    (slice_contraction_zero n) (slice_contraction_one n) z hz

end SKEFTHawking.SingularEuclideanAcyclicInt
