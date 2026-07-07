/-
# Phase 5q.H (E1 CSC-PD tower) — integral cap-iso `capEquiv` assembly

Assembles the integral cap-with-`[M]` isomorphism `capEquivInt : Cohomology M k ≃ Homology M (m+1)`
(the `IntCapIso.capEquiv` field) from the completed pieces:
* `compactlySupportedTopEquivInt` (CSC-cohomology collapse onto ordinary cohomology, compact `M`);
* `fundamentalDuality_bijective_of_openDuality_univ_bijectiveInt` (the d1 ⊤-collapse bridge);
* `relativeDualityInt_empty_eq_capHInt` (the duality-over-`∅` = `capHInt` crux) transported across the
  colimit ⊤-stage by `relativeDualityInt_set_congr` (`(↑⊤)ᶜ = ∅`).

The payoff `fundamentalDualityInt_top_eq_capHInt` establishes `IntCapIso.capEquiv_apply` — the assembled
`D_univ` reads off as `capHInt · [M]`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCompactlySupportedTopInt
import SKEFTHawking.SingularFundamentalDualityTopInt
import SKEFTHawking.SingularDualityEmptyInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCohomologyColimitInt
open SKEFTHawking.SingularCompactlySupportedTopInt
open SKEFTHawking.SingularRelativeCohomologyEmptyInt
open SKEFTHawking.SingularDualityEmptyInt
open SKEFTHawking.SingularFundamentalDualityInt
open SKEFTHawking.SingularFundamentalDualityTopInt
open SKEFTHawking.SingularOpenDualityInt

namespace SKEFTHawking.SingularIntCapEquivAssembly

variable {X : TopCat}

/-- **Set-congruence of `relativeDualityInt`**: for `S = T`, the integral duality map over `S` is the
duality map over `T` precomposed with `relCohomSetCongrInt`. A `subst` of the set. Integral mirror of
`SingularRelativeDualityCongr.relativeDuality_set_congr`. -/
theorem relativeDualityInt_set_congr {S T : Set ↑X} (hST : S = T) (k m : ℕ)
    (z : SingularChainInt X (k + m + 1)) (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (ω : RelativeCohomologyInt S k) :
    relativeDualityInt S k m z hzS ω
      = relativeDualityInt T k m z (hST ▸ hzS) (relCohomSetCongrInt hST k ω) := by
  subst hST
  rfl

/-- **The assembled `D_M` reads off as `capHInt · [z]`** (forward form): on the CSC-cohomology of a
compact `M`, `fundamentalDualityInt k m z hz` equals `capHInt k m · [z]` transported by the collapse
`compactlySupportedTopEquivInt`. Chains the ⊤-stage `lift_of`, the `(↑⊤)ᶜ = ∅` set-congruence, and the
duality-over-`∅` crux `relativeDualityInt_empty_eq_capHInt`. -/
theorem fundamentalDualityInt_eq_capHInt_top {M : TopCat} [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (z : SingularChainInt M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (c : CompactlySupportedCohomologyInt (M := M) k) :
    fundamentalDualityInt k m z hz c
      = capHInt k m (compactlySupportedTopEquivInt k c) (Homology.mk M (k + m + 1) ⟨z, hz⟩) := by
  have hcT : (↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ = (∅ : Set ↑M) := by
    rw [TopologicalSpace.Compacts.coe_top, Set.compl_univ]
  obtain ⟨w, rfl⟩ := (SKEFTHawking.SingularDirectLimitTop.of_top_bijective
    (cohomGInt (M := M) k) (cohomFInt k)).surjective c
  have hlift : fundamentalDualityInt k m z hz
        (Module.DirectLimit.of ℤ (TopologicalSpace.Compacts ↑M) (cohomGInt k) (cohomFInt k) ⊤ w)
      = relativeDualityInt ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) k m z
          (by rw [hz]; exact Submodule.zero_mem _) w :=
    Module.DirectLimit.lift_of _ _ w
  have htop : compactlySupportedTopEquivInt k
        (Module.DirectLimit.of ℤ (TopologicalSpace.Compacts ↑M) (cohomGInt k) (cohomFInt k) ⊤ w)
      = relCohomologyEmptyEquivInt k (relCohomSetCongrInt hcT k w) := by
    simp only [compactlySupportedTopEquivInt]
    erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  rw [hlift, htop, relativeDualityInt_set_congr hcT k m z _ w,
    relativeDualityInt_empty_eq_capHInt]

/-- **The integral cap-with-`[z]` isomorphism** `Cohomology M k ≃ Homology M (m+1)`, given a bijective
`D_univ` (`openDuality univ`, from the pdWindow cover-induction). This is the `IntCapIso.capEquiv` field:
the CSC-cohomology collapse composed with the (bijective) fixed-target duality. -/
noncomputable def capEquivInt {M : TopCat} [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChainInt M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (hD : Function.Bijective ⇑(openDuality (k := k) (m := m) hop z hz)) :
    Cohomology M k ≃ₗ[ℤ] Homology M (m + 1) :=
  (compactlySupportedTopEquivInt k).symm.trans
    (LinearEquiv.ofBijective (fundamentalDualityInt k m z hz)
      (fundamentalDuality_bijective_of_openDuality_univ_bijectiveInt hop z hz hD))

/-- **`capEquivInt` is `capHInt · [z]`** — the `IntCapIso.capEquiv_apply` obligation: the assembled
cap-iso underlying map is the integral cap-with-`[z]`. -/
theorem capEquivInt_apply {M : TopCat} [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChainInt M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (hD : Function.Bijective ⇑(openDuality (k := k) (m := m) hop z hz))
    (a : Cohomology M k) :
    capEquivInt hop z hz hD a = capHInt k m a (Homology.mk M (k + m + 1) ⟨z, hz⟩) := by
  rw [capEquivInt, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    fundamentalDualityInt_eq_capHInt_top, LinearEquiv.apply_symm_apply]

end SKEFTHawking.SingularIntCapEquivAssembly
