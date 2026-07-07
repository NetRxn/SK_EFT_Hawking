/-
# Phase 5q.H (E1 CSC-PD tower) — d1 ⊤-collapse bridge: the ⊤-stage leg identities (integral)

The connecting lemmas that transfer `openDuality univ` bijectivity to the fixed-target
`fundamentalDualityInt`. Mirror of `SingularPDWindow.legW_top_eq_relativeDualityK` (:577) and
`relativeDuality_top_eq_map_legW` (:602): on a compact `M` the compactly-supported colimits collapse
onto their `⊤`-stage, whose `D_univ` leg (`legW ⊤`, at the per-stage cycle) agrees with the ambient
fundamental duality (at the global cycle `z`) up to the `univ`-inclusion pushforward — the cycle
mismatch is `fundCycleW_relHomologous`, absorbed by `relativeDualityKInt_cycle_compat_relB`. ℤ-diff:
the mod-2 `add_comm` (char 2 makes `−` symmetric) becomes an honest `neg_sub` sign-flip.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityInt
import SKEFTHawking.SingularFundamentalDualityInt
import SKEFTHawking.SingularFundamentalDualityBridgeInt
import SKEFTHawking.SingularConvexRadialBaseInt
import SKEFTHawking.SingularDirectLimitTop

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularOpenDualityCycleInt
open SKEFTHawking.SingularLocalDualityKInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCohomologyColimitInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularFundamentalDualityBridgeInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularConvexRadialBaseInt (mapChainInt_ambIncl)
open SKEFTHawking.SingularFundamentalDualityInt

namespace SKEFTHawking.SingularFundamentalDualityTopInt

/-- For compact `M`, `CompactsIn univ` has a top: the whole space as a compact (coefficient-free;
mirror of the local instance in `SingularPDWindow`). -/
noncomputable instance {M : TopCat} [CompactSpace ↑M] :
    OrderTop (SKEFTHawking.SingularCompactsInOpen.CompactsIn (Set.univ : Set ↑M)) where
  top := ⟨⊤, Set.subset_univ _⟩
  le_top _K := Subtype.coe_le_coe.mp le_top

/-- Fresh-budget helper: the `D_univ` `⊤`-leg with its per-stage cycle swapped for the ambient
`z` (`fundCycleW_relHomologous` through `relativeDualityKInt_cycle_compat_relB`). -/
private theorem legW_top_eq_relativeDualityKInt {M : TopCat} [T2Space ↑M] [CompactSpace ↑M]
    {k m : ℕ} (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChainInt M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (x : cohomGWInt (Set.univ : Set ↑M) k (⊤ : CompactsIn (Set.univ : Set ↑M))) :
    legW hop z hz (⊤ : CompactsIn (Set.univ : Set ↑M)) x
      = relativeDualityKInt ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ)
          (Set.univ : Set ↑M) k m z (mem_subspaceChainsInt_univ z)
          (by rw [hz]; exact Submodule.zero_mem _) x := by
  refine relativeDualityKInt_cycle_compat_relB _ _ _ _ _ _ ?_ ?_ x
  · rw [Set.biUnion_pair, interior_univ]
    exact Set.eq_univ_of_univ_subset (Set.subset_union_left)
  · rw [← neg_sub]
    exact Submodule.neg_mem _
      (fundCycleW_relHomologous hop z hz (⊤ : CompactsIn (Set.univ : Set ↑M)))

/-- **(d1b) The `⊤`-stage leg square** (integral): the fundamental-duality `⊤`-leg
(`relativeDualityInt` at the ambient cycle `z`) is the `univ`-inclusion pushforward of the `D_univ`
`⊤`-leg (`legW` at the per-stage `fundCycleW`) — the cycle mismatch is `fundCycleW_relHomologous`,
absorbed by `relativeDualityKInt_cycle_compat_relB` (through `legW_top_eq_relativeDualityKInt`). -/
theorem relativeDuality_top_eq_map_legWInt {M : TopCat} [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChainInt M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (x : cohomGWInt (Set.univ : Set ↑M) k (⊤ : CompactsIn (Set.univ : Set ↑M))) :
    relativeDualityInt ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) k m z
        (by rw [hz]; exact Submodule.zero_mem _) x
      = Homology.mapInt (ambIncl (Set.univ : Set ↑M)) (m + 1)
          (legW hop z hz (⊤ : CompactsIn (Set.univ : Set ↑M)) x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hchain : mapChainInt (ambIncl (Set.univ : Set ↑M)) (m + 1)
        (pullbackDualityIntₗ ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ)
          (Set.univ : Set ↑M) z (mem_subspaceChainsInt_univ z) a)
      = capInt a.1.1 z :=
    (congrFun (congrArg DFunLike.coe (mapChainInt_ambIncl (Set.univ : Set ↑M) (m + 1)))
      _).trans (chainIncl_pullbackDualityIntₗ
        ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) (Set.univ : Set ↑M)
        z (mem_subspaceChainsInt_univ z) a)
  exact (congrArg (fun t => Homology.mk M (m + 1) t) (Subtype.ext hchain.symm)).trans
    (congrArg (fun t => Homology.mapInt (ambIncl (Set.univ : Set ↑M)) (m + 1) t)
      (legW_top_eq_relativeDualityKInt hop z hz (Submodule.Quotient.mk a)).symm)

/-- **(d1a) The P-side colimit collapses onto its `⊤`-stage** (compact `M`): `of ⊤` is bijective. -/
theorem of_top_univ_bijectiveInt {M : TopCat} [CompactSpace ↑M] (k : ℕ) :
    Function.Bijective (Module.DirectLimit.of ℤ
      (CompactsIn (Set.univ : Set ↑M))
      (cohomGWInt (Set.univ : Set ↑M) k) (cohomFWInt (Set.univ : Set ↑M) k) ⊤) :=
  SKEFTHawking.SingularDirectLimitTop.of_top_bijective _ _

/-- **The `⊤`-stage leg of an injective `D_univ` is injective** — the P-side half of the W-d1
endpoint bridge. -/
theorem legW_top_injectiveInt {M : TopCat} [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z₀ : SingularChainInt M (k + m + 1)) (hz₀ : chainBoundary M (k + m) z₀ = 0)
    (hD : Function.Injective ⇑(openDuality (k := k) (m := m) hop z₀ hz₀)) :
    Function.Injective ⇑(legW hop z₀ hz₀ (⊤ : CompactsIn (Set.univ : Set ↑M))) := by
  intro a b hab
  have h1 : openDuality (k := k) (m := m) hop z₀ hz₀
        (Module.DirectLimit.of ℤ (CompactsIn (Set.univ : Set ↑M))
          (cohomGWInt (Set.univ : Set ↑M) k) (cohomFWInt (Set.univ : Set ↑M) k) ⊤ a)
      = openDuality (k := k) (m := m) hop z₀ hz₀
        (Module.DirectLimit.of ℤ (CompactsIn (Set.univ : Set ↑M))
          (cohomGWInt (Set.univ : Set ↑M) k) (cohomFWInt (Set.univ : Set ↑M) k) ⊤ b) := by
    rw [openDuality_of, openDuality_of]
    exact hab
  exact (of_top_univ_bijectiveInt k).injective (hD h1)

/-- **(d1c) W-d1: the fundamental duality is injective when `D_univ` is** — both colimits
collapse onto their `⊤`-stages, whose legs agree by the (d1b) square. -/
theorem fundamentalDuality_injective_of_openDuality_univ_injectiveInt {M : TopCat}
    [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChainInt M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (hD : Function.Injective ⇑(openDuality (k := k) (m := m) hop z hz)) :
    Function.Injective ⇑(fundamentalDualityInt k m z hz) := by
  have hleg := legW_top_injectiveInt hop z hz hD
  intro α β hαβ
  obtain ⟨x, rfl⟩ := (SKEFTHawking.SingularDirectLimitTop.of_top_bijective
    (cohomGInt (M := M) k) (cohomFInt k)).surjective α
  obtain ⟨y, rfl⟩ := (SKEFTHawking.SingularDirectLimitTop.of_top_bijective
    (cohomGInt (M := M) k) (cohomFInt k)).surjective β
  have hfac : ∀ w, fundamentalDualityInt k m z hz
        (Module.DirectLimit.of ℤ (TopologicalSpace.Compacts ↑M)
          (cohomGInt k) (cohomFInt k) ⊤ w)
      = relativeDualityInt ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) k m z
          (by rw [hz]; exact Submodule.zero_mem _) w := fun w =>
    Module.DirectLimit.lift_of _ _ w
  rw [hfac, hfac, relativeDuality_top_eq_map_legWInt hop z hz,
    relativeDuality_top_eq_map_legWInt hop z hz] at hαβ
  exact congrArg _ (hleg ((homology_map_ambIncl_univ_bijectiveInt (m + 1)).injective hαβ))

/-- **The BIJECTIVE W-d1 endpoint bridge** (integral): the fundamental duality is bijective when
`D_univ` is (the `⊤`-collapse square transfers surjectivity too). -/
theorem fundamentalDuality_bijective_of_openDuality_univ_bijectiveInt {M : TopCat}
    [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChainInt M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (hD : Function.Bijective ⇑(openDuality (k := k) (m := m) hop z hz)) :
    Function.Bijective ⇑(fundamentalDualityInt k m z hz) := by
  constructor
  · exact fundamentalDuality_injective_of_openDuality_univ_injectiveInt hop z hz hD.injective
  · intro y
    obtain ⟨y', hy'⟩ := (homology_map_ambIncl_univ_bijectiveInt (m + 1)).surjective y
    obtain ⟨α, hα⟩ := hD.surjective y'
    obtain ⟨x, rfl⟩ := (of_top_univ_bijectiveInt (M := M) k).surjective α
    refine ⟨Module.DirectLimit.of ℤ (TopologicalSpace.Compacts ↑M)
      (cohomGInt k) (cohomFInt k) ⊤ x, ?_⟩
    have hfac : ∀ w, fundamentalDualityInt k m z hz
          (Module.DirectLimit.of ℤ (TopologicalSpace.Compacts ↑M)
            (cohomGInt k) (cohomFInt k) ⊤ w)
        = relativeDualityInt ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) k m z
            (by rw [hz]; exact Submodule.zero_mem _) w := fun w =>
      Module.DirectLimit.lift_of _ _ w
    rw [hfac x, relativeDuality_top_eq_map_legWInt hop z hz x]
    rw [show legW hop z hz (⊤ : CompactsIn (Set.univ : Set ↑M)) x
        = openDuality (k := k) (m := m) hop z hz
            (Module.DirectLimit.of ℤ (CompactsIn (Set.univ : Set ↑M))
              (cohomGWInt (Set.univ : Set ↑M) k) (cohomFWInt (Set.univ : Set ↑M) k) ⊤ x)
      from (openDuality_of hop z hz ⊤ x).symm]
    rw [hα, hy']

end SKEFTHawking.SingularFundamentalDualityTopInt
