import Mathlib
import SKEFTHawking.SingularMayerVietorisLES
import SKEFTHawking.SingularExcisionBot
import SKEFTHawking.SingularSubHomologyMV
import SKEFTHawking.SingularOpenDualityMVSquare

/-!
# Phase 5q.G (G1 PD-induction, D⁰-substrate) — the `H₀` Mayer–Vietoris middle exactness

The degree-0 companions of `excisionMap_homProj` and `mv_exact_middle` (both `H_{n+1}`-floored
in their generic forms). The chase mirrors the generic 1:1 at index `0` — every LES engine
(`homIncl`/`homProj`, both pair-LES exactness lemmas, `excisionEquiv` at relative degree `1`,
`seamHomologyEquiv`, the seam squares, `inclRA_connecting`, `mvHomSum_mvHomDiag`) is
index-generic; the excision-injectivity input is `excisionMap_injective₀`
(`SingularExcisionBot`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularExcisionBot
open SKEFTHawking.SingularSubHomologyMV

namespace SKEFTHawking.SingularMayerVietorisLESBot

variable {X : TopCat}

/-- Degree-0 companion of `excisionMap_homProj`. -/
theorem excisionMap_homProj₀ (A B : Set X) (v : Homology (sub B) 0) :
    excisionMap A B 0 (homProj (restr A B) 0 v)
      = homProj A 0 (homIncl B 0 v) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  show excisionMap A B 0 (homProj (restr A B) 0 (Homology.mk (sub B) 0 z))
      = homProj A 0 (homIncl B 0 (Homology.mk (sub B) 0 z))
  rw [homProj_mk, excisionMap_mk, homIncl_mk, homProj_mk]
  exact congrArg (RelativeHomology.mk A 0) (Subtype.ext (relChainIncl_mk A B 0 z))

/-- **The `H₀` Mayer–Vietoris middle exactness** (degree-0 companion of `mv_exact_middle`):
`Exact (mvHomDiag A B 0) (mvHomSum A B 0)`. -/
theorem mv_exact_middle₀ (A B : Set X)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) :
    Function.Exact (mvHomDiag A B 0) (mvHomSum A B 0) := by
  intro uv
  refine ⟨fun huv => ?_, fun hr => ?_⟩
  · obtain ⟨u, v⟩ := uv
    have hsum : homIncl A 0 u + homIncl B 0 v = 0 := by
      simpa only [mvHomSum, LinearMap.coprod_apply, Homology.map_ambIncl] using huv
    have h1 : homProj A 0 (homIncl B 0 v) = 0 := by
      have h := congrArg (homProj A 0) hsum
      rwa [map_add, homProj_homIncl, zero_add, map_zero] at h
    have h2 : homProj (restr A B) 0 v = 0 := by
      apply excisionMap_injective₀ A B hcov
      rw [excisionMap_homProj₀, map_zero]; exact h1
    obtain ⟨w'', hw''⟩ := (exact_homIncl_homProj (restr A B) 0 _).mp h2
    have h4 : homIncl A 0 (u + Homology.map (inclRA A B) 0 w'') = 0 := by
      rw [map_add, homIncl_inclRA, hw'']; exact hsum
    obtain ⟨c', hc'⟩ := (exact_connecting_homIncl A 0 _).mp h4
    obtain ⟨c'', hc''⟩ := (excisionEquiv A B 0 hcov).surjective c'
    have hu : Homology.map (inclRA A B) 0 (w'' + connecting (restr A B) 0 c'') = u := by
      rw [map_add, inclRA_connecting, show excisionMap A B (0 + 1) c'' = c' from hc'', hc',
        add_comm (Homology.map (inclRA A B) 0 w'') (u + Homology.map (inclRA A B) 0 w''),
        add_assoc, ZModModule.add_self, add_zero]
    refine ⟨seamHomologyEquiv A B 0 (w'' + connecting (restr A B) 0 c''), ?_⟩
    refine Prod.ext ?_ ?_
    · show Homology.map (subIncl (Set.inter_subset_left (s := A) (t := B))) 0
          (seamHomologyEquiv A B 0 (w'' + connecting (restr A B) 0 c'')) = u
      rw [map_subInclL_seam]; exact hu
    · show Homology.map (subIncl (Set.inter_subset_right (s := A) (t := B))) 0
          (seamHomologyEquiv A B 0 (w'' + connecting (restr A B) 0 c'')) = v
      rw [map_subInclR_seam, map_add, hw'', homIncl_connecting, add_zero]
  · obtain ⟨w, rfl⟩ := hr
    exact mvHomSum_mvHomDiag A B 0 w

/-- **The `H₀` subspace-MV middle exactness** (degree-0 companion of `subHom_exact_middle`):
`Exact (subHomDiag U V 0) (subHomSum U V 0)` — the seam transport of `mv_exact_middle₀`. This is
the `hg₁`-input of the D⁰ five-lemma ladder. -/
theorem subHom_exact_middle₀ {X : TopCat} (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) :
    Function.Exact (SingularOpenDualityMVSquare.subHomDiag U V 0)
      (SingularOpenDualityMVSquare.subHomSum U V 0) := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := seamI U V 0)
    (e₂ := (seamU U V 0).prodCongr (seamV U V 0))
    (e₃ := LinearEquiv.refl (ZMod 2) (Homology (sub (U ∪ V)) 0)) ?_ ?_
    (mv_exact_middle₀ (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V)
      (cover_preimage U V hU hV))
  · refine LinearMap.ext fun w => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.prodCongr_apply]
    exact diagSquare U V 0 w
  · refine LinearMap.ext fun p => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.refl_apply, LinearEquiv.prodCongr_apply]
    exact sumSquare U V 0 p

end SKEFTHawking.SingularMayerVietorisLESBot
