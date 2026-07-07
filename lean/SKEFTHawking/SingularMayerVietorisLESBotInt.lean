/-
# Phase 5q.H (E1 CSC-PD tower) — the integral `H₀` Mayer–Vietoris middle exactness

Integral (`ZMod 2 → ℤ`) mirror of the degree-0 slice of `SingularMayerVietorisLESBot`. The `H₀`-companions
of `excisionMap_homProjInt` and `mv_exact_middleInt` (both `H_{n+1}`-floored in their generic integral forms).

**The chase mirrors the GENERAL integral `mv_exact_middleInt` at degree 0 — NOT the mod-2 sum-based
degree-0.** Over ℤ, `mvHomSumInt` is an honest DIFFERENCE (`map(ambIncl A)∘fst − map(ambIncl B)∘snd`), so
the middle exactness runs `homIncl A u − homIncl B v = 0` and the combining witness is `u − mapInt(inclRAInt)
w''` (`abel`-closed), exactly as the general chase — with the two degree-0-specific inputs
`excisionMap_homProj₀Int` (here) and `excisionMap_injective₀Int` (`SingularExcisionBotInt`) swapped in for the
`n+1`-only generic versions.

`subHom_exact_middle₀Int` is the seam transport of `mv_exact_middle₀Int` (the `hg₁`-input of the integral PD
D⁰ five-lemma), mirroring the general `subHom_exact_middleInt` at degree 0.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularMayerVietorisLESInt
import SKEFTHawking.SingularExcisionBotInt
import SKEFTHawking.SingularSubHomologyMVInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.SingularSubHomologyMVInt
open SKEFTHawking.SingularOpenDualityMVSquareInt
open SKEFTHawking.SingularExcisionBotInt
open SKEFTHawking.SingularMayerVietorisLES (subIncl)
open SKEFTHawking.SingularSubHomologyMV (cover_preimage)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularMayerVietorisLESBotInt

variable {X : TopCat}

/-- Degree-0 companion of `excisionMap_homProjInt`. -/
theorem excisionMap_homProj₀Int (A B : Set ↑X) (v : Homology (sub B) 0) :
    excisionMapInt A B 0 (homProjInt (restr A B) 0 v)
      = homProjInt A 0 (homIncl B 0 v) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  show excisionMapInt A B 0 (homProjInt (restr A B) 0 (Homology.mk (sub B) 0 z))
      = homProjInt A 0 (homIncl B 0 (Homology.mk (sub B) 0 z))
  rw [homProjInt_mk, excisionMapInt_mk, homIncl_mk, homProjInt_mk]
  exact congrArg (RelHomologyInt.mk A 0) (Subtype.ext (relChainInclInt_mk A B 0 z))

/-- **The integral `H₀` Mayer–Vietoris middle exactness** (degree-0 companion of `mv_exact_middleInt`):
`Function.Exact (mvHomDiagInt A B 0) (mvHomSumInt A B 0)`. -/
theorem mv_exact_middle₀Int (A B : Set ↑X)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ) :
    Function.Exact (mvHomDiagInt A B 0) (mvHomSumInt A B 0) := by
  intro uv
  refine ⟨fun huv => ?_, fun hr => ?_⟩
  · obtain ⟨u, v⟩ := uv
    have hsum : homIncl A 0 u - homIncl B 0 v = 0 := by
      simpa only [mvHomSumInt_apply, Homology.mapInt_ambIncl] using huv
    have h1 : homProjInt A 0 (homIncl B 0 v) = 0 := by
      have h := congrArg (homProjInt A 0) hsum
      rw [map_sub, SingularSphereHomologyInt.homProjInt_homIncl, zero_sub, map_zero, neg_eq_zero] at h
      exact h
    have h2 : homProjInt (restr A B) 0 v = 0 := by
      apply excisionMap_injective₀Int A B hcov
      rw [excisionMap_homProj₀Int, map_zero]; exact h1
    obtain ⟨w'', hw''⟩ := (SingularSphereHomologyInt.exact_homIncl_homProjInt (restr A B) 0 _).mp h2
    have h4 : homIncl A 0 (u - Homology.mapInt (inclRAInt A B) 0 w'') = 0 := by
      rw [map_sub, homIncl_inclRAInt, hw'']; exact hsum
    obtain ⟨c', hc'⟩ := (SingularLocalHomologyInt.exact_connectingInt_homIncl A 0 _).mp h4
    obtain ⟨c'', hc''⟩ := (excisionEquivInt A B 0 hcov).surjective c'
    have hu : Homology.mapInt (inclRAInt A B) 0 (w'' + connectingInt (restr A B) 0 c'') = u := by
      rw [map_add, inclRA_connectingInt, show excisionMapInt A B 1 c'' = c' from hc'', hc']
      abel
    refine ⟨seamHomologyEquivInt A B 0 (w'' + connectingInt (restr A B) 0 c''), ?_⟩
    refine Prod.ext ?_ ?_
    · show Homology.mapInt (subIncl (Set.inter_subset_left (s := A) (t := B))) 0
          (seamHomologyEquivInt A B 0 (w'' + connectingInt (restr A B) 0 c'')) = u
      rw [map_subInclL_seamInt]; exact hu
    · show Homology.mapInt (subIncl (Set.inter_subset_right (s := A) (t := B))) 0
          (seamHomologyEquivInt A B 0 (w'' + connectingInt (restr A B) 0 c'')) = v
      rw [map_subInclR_seamInt, map_add, hw'', SingularLocalHomologyInt.homIncl_connectingInt, add_zero]
  · obtain ⟨w, rfl⟩ := hr
    exact mvHomSumInt_mvHomDiagInt A B 0 w

/-- **The integral `H₀` subspace-MV middle exactness** (`hg₁`-input of the D⁰ five-lemma):
`Function.Exact (subHomDiagInt U V 0) (subHomSumInt U V 0)` — the seam transport of `mv_exact_middle₀Int`. -/
theorem subHom_exact_middle₀Int (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) :
    Function.Exact (subHomDiagInt U V 0) (subHomSumInt U V 0) := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := seamI U V 0)
    (e₂ := (seamU U V 0).prodCongr (seamV U V 0))
    (e₃ := LinearEquiv.refl ℤ (Homology (sub (U ∪ V)) 0)) ?_ ?_
    (mv_exact_middle₀Int (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V)
      (cover_preimage U V hU hV))
  · refine LinearMap.ext fun w => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.prodCongr_apply]
    exact diagSquareInt U V 0 w
  · refine LinearMap.ext fun p => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.refl_apply, LinearEquiv.prodCongr_apply]
    exact sumSquareInt U V 0 p

end SKEFTHawking.SingularMayerVietorisLESBotInt
