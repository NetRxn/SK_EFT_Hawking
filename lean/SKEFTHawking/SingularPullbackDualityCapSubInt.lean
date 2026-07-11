/-
# Phase 5q.H (E1 CSC-PD tower) — pullback-cochain naturality + legW-cap sub-form (integral, brick 6e-c-step1)

The three supporting bricks that let the seam-match `seamMatch_upperInt` reduce to its genuine-cap
skeleton (the mechanical step 1 of the core matching):
* `coboundary_pullbackCochainInt` — the sub-inclusion cochain pullback commutes with `δ`.
* `pullbackCochainInt_vanish_preimageInt` — the pullback of a rel-`T` cocycle vanishes on
  `val⁻¹T`-simplices of `sub W` (nested-inclusion range argument). Feeds `capInt_relCycle_isCycleInt` and
  the `capInt_subspaceChainInt_eq_zero` locality on the sub level.
* `pullbackDualityIntₗ_eq_sub_capInt` (sub-lemma A) — the `legW` cycle rep `pullbackDualityIntₗ z_K g_rep`
  IS a genuine cap `capInt (pullbackCochainInt W g_rep) (inclRangeEquiv.symm z_K)` at the `sub W` level, so
  the canonical cap-cover-partition (`exists_cap_cover_partitionInt`) applies and its `B`-part is a literal
  cap (whose boundary computes via `capInt_cocycle_chainMap`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCapChainInclInt
import SKEFTHawking.SingularLocalDualityKInt
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularCompactsInOpen

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularExcisionIsoInt (range_simplexIncl_subsetInt mem_subspaceChainsInt_of_support)
open SKEFTHawking.SingularCapChainInclInt (pullbackCochainInt capInt_chainIncl)
open SKEFTHawking.SingularLocalDualityKInt (pullbackDualityIntₗ chainIncl_pullbackDualityIntₗ)
open SKEFTHawking.SingularCompactsInOpen (CompactsIn)

namespace SKEFTHawking.SingularPullbackDualityCapSubInt

variable {X : TopCat}

/-- Cochain pullback commutes with coboundary (integral), from `simplexIncl_face`. -/
theorem coboundary_pullbackCochainInt {S : Set ↑X} (k : ℕ) (a : SingularCochainInt X k) :
    coboundary (sub S) k (pullbackCochainInt S k a)
      = pullbackCochainInt S (k + 1) (coboundary X k a) := by
  funext τ
  simp only [coboundary_apply, SKEFTHawking.SingularCapChainInclInt.pullbackCochainInt_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 2

/-- `pullbackCochainInt (A∪B)` of a rel-`T` cocycle `g_rep` vanishes on `val⁻¹T`-simplices of `sub W`
(integral): the nested inclusion lands the simplex range in `T`, where the rel cochain vanishes. -/
theorem pullbackCochainInt_vanish_preimageInt {W T : Set ↑X} (k : ℕ)
    (g_rep : LinearMap.ker (relCoboundaryIntₗ T k))
    (τ : (TopCat.toSSet.obj (sub (Subtype.val ⁻¹' T : Set ↑(sub W)))).obj
        (Opposite.op (SimplexCategory.mk k))) :
    pullbackCochainInt W k ((g_rep : relCochainsInt T k) : SingularCochainInt X k)
        (simplexIncl (Subtype.val ⁻¹' T : Set ↑(sub W)) k τ) = 0 := by
  show ((g_rep : relCochainsInt T k) : SingularCochainInt X k)
      (simplexIncl W k (simplexIncl (Subtype.val ⁻¹' T : Set ↑(sub W)) k τ)) = 0
  have hrange : Set.range (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk k))
      (simplexIncl W k (simplexIncl (Subtype.val ⁻¹' T : Set ↑(sub W)) k τ))) ⊆ T := by
    rw [SKEFTHawking.SingularExcisionIso.simplexIncl_range_subset_iff]
    exact range_simplexIncl_subsetInt (Subtype.val ⁻¹' T : Set ↑(sub W)) τ
  have hmem : Finsupp.single (simplexIncl W k (simplexIncl (Subtype.val ⁻¹' T : Set ↑(sub W)) k τ))
      (1 : ℤ) ∈ subspaceChainsInt T k :=
    mem_subspaceChainsInt_of_support (fun σ hσ => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hσ
      subst hσ; exact hrange)
  have := g_rep.1.2 _ hmem
  rwa [kronecker_single, one_mul] at this

/-- **Sub-lemma A**: the `legW` cycle rep `pullbackDualityIntₗ` is a genuine cap of the reflected
fundamental cycle `z_K'` at the `sub W` level. -/
theorem pullbackDualityIntₗ_eq_sub_capInt {k m : ℕ} {W : Set ↑X} (K : CompactsIn W)
    (z_K : SingularChainInt X (k + m + 1)) (hz_K : z_K ∈ subspaceChainsInt W (k + m + 1))
    (g_rep : LinearMap.ker (relCoboundaryIntₗ ((↑K.1 : Set ↑X)ᶜ) k)) :
    pullbackDualityIntₗ ((↑K.1 : Set ↑X)ᶜ) W z_K hz_K g_rep
      = capInt (m := m + 1) (pullbackCochainInt W k ((g_rep : relCochainsInt ((↑K.1 : Set ↑X)ᶜ) k) :
            SingularCochainInt X k))
          ((inclRangeEquiv W (k + m + 1)).symm ⟨z_K, hz_K⟩) := by
  apply chainIncl_injective W (m + 1)
  rw [chainIncl_pullbackDualityIntₗ, ← capInt_chainIncl]
  congr 1
  exact (chainIncl_inclRangeEquiv_symm W (k + m + 1) ⟨z_K, hz_K⟩).symm

end SKEFTHawking.SingularPullbackDualityCapSubInt
