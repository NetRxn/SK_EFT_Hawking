import Mathlib
import SKEFTHawking.SingularHomotopyInvarianceInt
import SKEFTHawking.SingularFunctorialityInt
import SKEFTHawking.SingularEuclideanAcyclic
import SKEFTHawking.SingularPuncturedRetract

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

/-!
# Integral punctured-space deformation retract `ℝⁿ ∖ 0 ≃ Sⁿ⁻¹`

The punctured space `ℝⁿ ∖ 0` deformation-retracts onto the unit sphere `Sⁿ⁻¹` via
`normalize x = x/‖x‖`, a homotopy equivalence with inverse the inclusion `incl`. All the continuous
maps and slice identities are reused verbatim from `SingularPuncturedRetract` (coefficient-free); the
transport to integral homology now flows through
`SingularFunctorialityInt.Homology.mapInt_bijective_of_homotopyEquiv`.
-/

namespace SKEFTHawking.SingularPuncturedRetractInt

open SKEFTHawking.SingularPuncturedRetract
open SKEFTHawking.SingularFunctorialityInt

/-- **`normalize : ℝⁿ ∖ 0 → Sⁿ⁻¹` induces an isomorphism on `Hₖ₊₁(·; ℤ)`** — the punctured space
deformation-retracts onto the sphere. Integral mirror of `homology_map_normalize_bijective`. -/
theorem homology_mapInt_normalize_bijective (n k : ℕ) :
    Function.Bijective (Homology.mapInt (normalize (n := n)) (k + 1)) :=
  Homology.mapInt_bijective_of_homotopyEquiv normalize incl puncHomotopy slice_puncHomotopy_zero
    slice_puncHomotopy_one constHomotopy
    ((slice_constHomotopy 0).trans normalize_comp_incl.symm) (slice_constHomotopy 1) k

end SKEFTHawking.SingularPuncturedRetractInt
