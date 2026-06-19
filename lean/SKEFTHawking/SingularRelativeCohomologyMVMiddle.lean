import Mathlib
import SKEFTHawking.SingularDualityMVAdjoint
import SKEFTHawking.SingularDualityFinrank
import SKEFTHawking.SingularUniversalCoeff
import SKEFTHawking.SingularRelativeMV
import SKEFTHawking.SingularRelativeUCSurj

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5b-mid) — relative cohomology MV exactness at the middle

The middle exactness of the relative cohomology Mayer–Vietoris sequence,
  `Hᵏ(M|A∪B) --Δ--> Hᵏ(M|A) ⊕ Hᵏ(M|B) --Σ--> Hᵏ(M|A∩B)`,
i.e. `ker (relCohomMvSum) = range (relCohomMvDiag)`, obtained by **duality-transfer** from the homology
MV exactness (`SingularRelativeMV.relMv_exact_middle'`) through the perfect Kronecker pairing
(`SingularDualityFinrank`), with `Hₙ(M|A∪B)` finite-dimensional (supplied by the PD induction's
`Hⁿ(M|x)≅ℤ/2`-built pieces).

`⊇` is `relCohomMvSum_relCohomMvDiag` (`Σ∘Δ=0`). For `⊆`: given `(α,β) ∈ ker (relCohomMvSum)`, the
functional `F = ⟨α,·⟩ ⊕ ⟨β,·⟩` on `Hₙ(M|A)⊕Hₙ(M|B)` vanishes on `ker (relMvHomSum) = range (relMvHomDiag)`
(homology exactness + `mem_ker_relCohomMvSum_iff`), hence factors `F = g ∘ relMvHomSum`
(`exists_factor_of_ker_le_ker`); realize `g` as `⟨γ,·⟩` (`relKroneckerH_surjective`, finite-dim); then
`relCohomMvDiag γ = (α,β)` since both pair equally against every class (`relCohomology_eq_zero…`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularRelativeCohomologyRestrict SKEFTHawking.SingularRelativeCohomologyMV
open SKEFTHawking.SingularDualityAdjoint SKEFTHawking.SingularDualityMVAdjoint
open SKEFTHawking.SingularDualityFinrank SKEFTHawking.SingularRelativeUC
open SKEFTHawking.SingularUniversalCoeff SKEFTHawking.SingularRelativeUCSurj

namespace SKEFTHawking.SingularRelativeCohomologyMVMiddle

variable {M : TopCat}

/-- **`ker (relCohomMvSum) ≤ range (relCohomMvDiag)`** — the substantive half of cohomology MV middle
exactness, by duality-transfer (needs `IsOpen U`, `IsOpen V` for the homology exactness and
`Hₙ(M|A∪B)` finite-dimensional). -/
theorem ker_relCohomMvSum_le_range_relCohomMvDiag (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V)
    {N : ℕ}
    (α : RelativeCohomology U (N + 1)) (β : RelativeCohomology V (N + 1))
    (hαβ : (α, β) ∈ LinearMap.ker (relCohomMvSum U V (N + 1))) :
    (α, β) ∈ LinearMap.range (relCohomMvDiag U V (N + 1)) := by
  -- The functional `F (x,y) = ⟨α,x⟩ + ⟨β,y⟩` on `Hₙ(M|A) ⊕ Hₙ(M|B)`.
  set F : RelativeHomology U (N + 1) × RelativeHomology V (N + 1) →ₗ[ZMod 2] ZMod 2 :=
    (relKroneckerH U α).coprod (relKroneckerH V β) with hF
  -- `F` vanishes on `ker (relMvHomSum) = range (relMvHomDiag)`.
  have hker : LinearMap.ker (relMvHomSum U V (N + 1)) ≤ LinearMap.ker F := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    obtain ⟨w, rfl⟩ := (relMv_exact_middle' U V hU hV N p).mp hp
    show relKroneckerH U α (relMvHomDiag U V (N + 1) w).1
        + relKroneckerH V β (relMvHomDiag U V (N + 1) w).2 = 0
    exact (mem_ker_relCohomMvSum_iff α β).mp hαβ w
  -- Factor `F = g ∘ relMvHomSum`; realize `g = ⟨γ,·⟩`.
  obtain ⟨g, hg⟩ := exists_factor_of_ker_le_ker (relMvHomSum U V (N + 1)) F hker
  obtain ⟨γ, hγ⟩ := relKroneckerH_surjective_field (U ∪ V) g
  -- `⟨γ, relMvHomSum (x,y)⟩ = F (x,y) = ⟨α,x⟩ + ⟨β,y⟩`.
  have hpair : ∀ x y, relKroneckerH (U ∪ V) γ (relMvHomSum U V (N + 1) (x, y))
      = relKroneckerH U α x + relKroneckerH V β y := by
    intro x y
    have := LinearMap.congr_fun (hγ.symm ▸ hg) (x, y)
    simpa [hF] using this
  -- `relCohomMvDiag γ = (α, β)`: each restriction pairs equally against all classes.
  refine ⟨γ, Prod.ext ?_ ?_⟩
  · refine sub_eq_zero.mp (relCohomology_eq_zero_of_relKroneckerH U
      ((relCohomMvDiag U V (N + 1) γ).1 - α) (fun x => ?_))
    have hl : relMvHomSum U V (N + 1) (x, 0) = relIncl Set.subset_union_left (N + 1) x := by
      rw [relMvHomSum, LinearMap.coprod_apply, map_zero, add_zero]
    rw [map_sub, LinearMap.sub_apply, relCohomMvDiag_apply, relKroneckerH_relCohomRestrict',
      ← hl, hpair, map_zero, add_zero, sub_self]
  · refine sub_eq_zero.mp (relCohomology_eq_zero_of_relKroneckerH V
      ((relCohomMvDiag U V (N + 1) γ).2 - β) (fun y => ?_))
    have hr : relMvHomSum U V (N + 1) (0, y) = relIncl Set.subset_union_right (N + 1) y := by
      rw [relMvHomSum, LinearMap.coprod_apply, map_zero, zero_add]
    rw [map_sub, LinearMap.sub_apply, relCohomMvDiag_apply, relKroneckerH_relCohomRestrict',
      ← hr, hpair, map_zero, zero_add, sub_self]

/-- **Relative cohomology MV exactness at the middle** `Hᵏ(M|A) ⊕ Hᵏ(M|B)`:
`Function.Exact (relCohomMvDiag) (relCohomMvSum)`, i.e. `range Δ = ker Σ`. The duality-transfer of
`SingularRelativeMV.relMv_exact_middle'` (`IsOpen U/V`, `Hₙ(M|A∪B)` finite-dimensional). The middle term
of the cohomology MV long exact sequence — the top row of the Poincaré-duality `5`-lemma ladder. -/
theorem relCohomMv_exact_middle (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) {N : ℕ} :
    Function.Exact (relCohomMvDiag U V (N + 1)) (relCohomMvSum U V (N + 1)) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨α, β⟩ := p
    exact ker_relCohomMvSum_le_range_relCohomMvDiag U V hU hV α β hp
  · obtain ⟨q, rfl⟩ := hp
    rw [LinearMap.mem_ker, relCohomMvSum_relCohomMvDiag]

end SKEFTHawking.SingularRelativeCohomologyMVMiddle
