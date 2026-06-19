import Mathlib
import SKEFTHawking.SingularDualityAdjoint
import SKEFTHawking.SingularRelativeCohomologyMV
import SKEFTHawking.SingularRelativeUC

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5b-mvadj) — the MV-map Kronecker adjunctions

The cohomology Mayer–Vietoris maps are Kronecker-adjoint to the homology MV maps (the directions flip):
  `⟨relCohomMvSum (α,β), w⟩_{U∩V} = ⟨α, ι w⟩_U + ⟨β, ι w⟩_V`     (`relCohomMvSum` ⊣ `relMvHomDiag`),
  `⟨relCohomMvDiag γ, (x,y)⟩ = ⟨γ, relMvHomSum (x,y)⟩_{U∪V}`     (`relCohomMvDiag` ⊣ `relMvHomSum`),
where `ι = relIncl …`. Both follow from the component adjunction
`SingularDualityAdjoint.relKroneckerH_relCohomRestrict'` + bilinearity of `relKroneckerH`. These are the
algebraic core of the **duality-transfer** route: combined with the homology MV exactness
(`SingularRelativeMV`) and the perfect Kronecker pairing (`SingularRelativeUC`, PD-4d), they carry
exactness to the cohomology side — `ker (relCohomMvSum) = annihilator (range relMvHomDiag)` is then a
finite-dimension-free consequence (the converse `range (relCohomMvDiag) = annihilator (ker relMvHomSum)`
uses finite-dimensionality, available for the induction's `Hᵏ(M|x)≅ℤ/2`-built pieces).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularRelativeCohomologyRestrict SKEFTHawking.SingularRelativeCohomologyMV
open SKEFTHawking.SingularDualityAdjoint SKEFTHawking.SingularRelativeUC

namespace SKEFTHawking.SingularDualityMVAdjoint

variable {M : TopCat}

/-- **`relCohomMvSum` is Kronecker-adjoint to `relMvHomDiag`**: pairing the MV sum of a cohomology pair
against a class `w ∈ Hₙ(M|A∩B)` is the pair paired against `relMvHomDiag w` (the two inclusions of `w`). -/
theorem relKroneckerH_relCohomMvSum {U V : Set ↑M} {N : ℕ}
    (α : RelativeCohomology U (N + 1)) (β : RelativeCohomology V (N + 1))
    (w : RelativeHomology (U ∩ V) (N + 1)) :
    relKroneckerH (U ∩ V) (relCohomMvSum U V (N + 1) (α, β)) w
      = relKroneckerH U α (relIncl Set.inter_subset_left (N + 1) w)
        + relKroneckerH V β (relIncl Set.inter_subset_right (N + 1) w) := by
  rw [relCohomMvSum_apply, map_add, LinearMap.add_apply,
    relKroneckerH_relCohomRestrict', relKroneckerH_relCohomRestrict']

/-- **`relCohomMvDiag` is Kronecker-adjoint to `relMvHomSum`**: pairing the MV diagonal of a class
`γ ∈ Hᵏ(M|A∪B)` against a homology pair `(x,y)` is `γ` paired against `relMvHomSum (x,y)`. -/
theorem relKroneckerH_relCohomMvDiag {U V : Set ↑M} {N : ℕ}
    (γ : RelativeCohomology (U ∪ V) (N + 1))
    (x : RelativeHomology U (N + 1)) (y : RelativeHomology V (N + 1)) :
    relKroneckerH U (relCohomMvDiag U V (N + 1) γ).1 x
        + relKroneckerH V (relCohomMvDiag U V (N + 1) γ).2 y
      = relKroneckerH (U ∪ V) γ (relMvHomSum U V (N + 1) (x, y)) := by
  rw [relCohomMvDiag_apply, relKroneckerH_relCohomRestrict', relKroneckerH_relCohomRestrict',
    relMvHomSum, LinearMap.coprod_apply, map_add]

/-- **`ker (relCohomMvSum)` is the annihilator of `range (relMvHomDiag)`** (finite-dimension-free): a
cohomology pair `(α, β)` is killed by the MV sum iff it pairs to `0` with every `relMvHomDiag w`. The
`⟸` is the perfect-pairing non-degeneracy (`relCohomology_eq_zero_of_relKroneckerH`, PD-4d); the `⟹` is
the MV-sum adjunction. The first half of the duality-transfer of the homology MV exactness to cohomology
(`range (relMvHomDiag) = ker (relMvHomSum)` then identifies this annihilator). -/
theorem mem_ker_relCohomMvSum_iff {U V : Set ↑M} {N : ℕ}
    (α : RelativeCohomology U (N + 1)) (β : RelativeCohomology V (N + 1)) :
    (α, β) ∈ LinearMap.ker (relCohomMvSum U V (N + 1)) ↔
      ∀ w : RelativeHomology (U ∩ V) (N + 1),
        relKroneckerH U α (relIncl Set.inter_subset_left (N + 1) w)
          + relKroneckerH V β (relIncl Set.inter_subset_right (N + 1) w) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h w
    rw [← relKroneckerH_relCohomMvSum, h, map_zero, LinearMap.zero_apply]
  · intro h
    refine relCohomology_eq_zero_of_relKroneckerH (U ∩ V) (relCohomMvSum U V (N + 1) (α, β))
      (fun w => ?_)
    rw [relKroneckerH_relCohomMvSum]
    exact h w

end SKEFTHawking.SingularDualityMVAdjoint
