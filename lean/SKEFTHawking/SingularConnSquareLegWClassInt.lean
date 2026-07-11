/-
# Phase 5q.H (E1 CSC-PD tower) — Route B, legW-on-subdivided-cap + explicit Brick B (integral, stage-1 sub-brick 3/3)

* `capInt_sub_singularSd_eq_boundary_explicitInt` — the second `∃`-free explicit-witness variant
  (of committed Brick B `capInt_sub_singularSd_mem_boundariesInt`): exposes the `W`-supported bounding
  chain the descent-bridge realizer needs.
* `legW_iterate_cap_class_eqInt` (Brick H) — `legW` evaluates on any subdivided-cap representative;
  rebuilt on the ℤ realizer `homology_eq_of_ambient_boundaryInt` (honest `−`) + `legW_mkInt` (rfl) +
  the explicit Brick B. Kernel-pure.
-/
import Mathlib
import SKEFTHawking.SingularConnSquareFactIDischargeInt
import SKEFTHawking.SingularOpenDualityInt
import SKEFTHawking.SingularLegWCapFormInt
import SKEFTHawking.SingularLocalDualityKInt
import SKEFTHawking.SingularHomologyDescentBridgeInt
import SKEFTHawking.SingularOpenDualityCycleInt
import SKEFTHawking.SingularCapSubdivCorrectionInt
import SKEFTHawking.SingularCapSupportInt
import SKEFTHawking.SingularSubdivisionInt
import SKEFTHawking.SingularExcisionIsoInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityInt (legW)
open SKEFTHawking.SingularLegWCapFormInt (legW_mkInt)
open SKEFTHawking.SingularLocalDualityKInt (pullbackDualityIntₗ chainIncl_pullbackDualityIntₗ)
open SKEFTHawking.SingularHomologyDescentBridgeInt (homology_eq_of_ambient_boundaryInt)
open SKEFTHawking.SingularOpenDualityCycleInt (fundCycleW fundCycleW_mem_W fundCycleW_boundary)
open SKEFTHawking.SingularCapSubdivCorrectionInt (capInt_sub_singularSd_iterate)
open SKEFTHawking.SingularCapSupportInt (capInt_mem_subspaceChainsInt)
open SKEFTHawking.SingularSubdivisionInt (singularSdInt iterHomotopyInt)
open SKEFTHawking.SingularExcisionIsoInt (iterHomotopyInt_mem_subspaceChainsInt)
open SKEFTHawking.SingularEuclideanCapIsoInt

namespace SKEFTHawking.SingularConnSquareCloseNCInt

variable {X : TopCat} [T2Space ↑X]

omit [T2Space ↑X] in
/-- **Explicit-witness Brick B** (integral). `capInt a z − capInt a (Sd^j z) = ∂((-1)^k • capInt a (Dⱼ z))`
with the bounding chain EXPLICIT (the committed `capInt_sub_singularSd_mem_boundariesInt` hides it under
`∈ boundaries`, blocking the `W`-support the descent-bridge realizer needs). ℤ analog of the mod-2
`cap_cocycle_singularSd_iterate_add_eq_boundary` (the `+`→`−`). -/
theorem capInt_sub_singularSd_eq_boundary_explicitInt {k m : ℕ} (S : Set ↑X)
    (a : SingularCochainInt X k) (ha : coboundary X k a = 0)
    (haS : ∀ τ, a (simplexIncl S k τ) = 0)
    (j : ℕ) (z : SingularChainInt X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m)) :
    capInt (m := m + 1) a z - capInt (m := m + 1) a ((⇑(singularSdInt X (k + m + 1)))^[j] z)
      = chainBoundary X (m + 1)
          ((-1 : ℤ) ^ k • capInt (m := m + 1 + 1) a (iterHomotopyInt X (k + m + 1) j z)) := by
  rw [capInt_sub_singularSd_iterate a j z,
    capInt_subspaceChainInt_eq_zero (m := m + 1) S a haS
      (iterHomotopyInt_mem_subspaceChainsInt hz j), add_zero]
  have hcm : chainBoundary X (m + 1)
        (capInt (m := m + 1 + 1) a (iterHomotopyInt X (k + m + 1) j z))
      = (-1 : ℤ) ^ k • capInt (m := m + 1) a
          (chainBoundary X (k + m + 1) (iterHomotopyInt X (k + m + 1) j z)) :=
    capInt_cocycle_chainMap (m := m + 1) a ha (iterHomotopyInt X (k + m + 1) j z)
  rw [map_smul, hcm, smul_smul, ← pow_add, ← two_mul, pow_mul,
    show ((-1 : ℤ) ^ 2) ^ k = 1 from by norm_num, one_smul]

/-- **`legW` evaluates on any subdivided-cap representative** (integral, Brick H). ℤ port of the mod-2
`SingularConnSquareCloseNC.legW_iterate_cap_class_eq`, rebuilt on the descent-bridge realizer
`homology_eq_of_ambient_boundaryInt` (honest `−`) + `legW_mkInt` (rfl) + explicit Brick B. -/
theorem legW_iterate_cap_class_eqInt {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : CompactsIn W) (a : LinearMap.ker (relCoboundaryIntₗ ((↑K.1 : Set ↑X)ᶜ) k))
    (μ : ℕ) (zsum : SingularChainInt (sub W) (m + 1)) (hcyc : zsum ∈ cycles (sub W) (m + 1))
    (hamb : chainIncl W (m + 1) zsum
      = capInt (m := m + 1) a.1.1 ((⇑(singularSdInt X (k + m + 1)))^[μ] (fundCycleW hW z₀ hz₀ K))) :
    legW hW z₀ hz₀ K (RelativeCohomologyInt.mk ((↑K.1 : Set ↑X)ᶜ) k a)
      = Homology.mk (sub W) (m + 1) ⟨zsum, hcyc⟩ := by
  have hgc : coboundary X k a.1.1 = 0 := by
    have hh := congrArg Subtype.val a.2
    simpa only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] using hh
  have havan : ∀ τ, a.1.1 (simplexIncl ((↑K.1 : Set ↑X)ᶜ) k τ) = 0 :=
    fun τ => relCochainInt_vanish ((↑K.1 : Set ↑X)ᶜ) a.1 τ
  rw [legW_mkInt hW z₀ hz₀ K a]
  refine homology_eq_of_ambient_boundaryInt _ _
    ((-1 : ℤ) ^ k • capInt (m := m + 1 + 1) a.1.1
      (iterHomotopyInt X (k + m + 1) μ (fundCycleW hW z₀ hz₀ K)))
    (Submodule.smul_mem _ _
      (capInt_mem_subspaceChainsInt (m := m + 1 + 1) W a.1.1
        (iterHomotopyInt_mem_subspaceChainsInt (fundCycleW_mem_W hW z₀ hz₀ K) μ))) ?_
  rw [chainIncl_pullbackDualityIntₗ, hamb]
  exact (capInt_sub_singularSd_eq_boundary_explicitInt ((↑K.1 : Set ↑X)ᶜ) a.1.1 hgc havan μ
    (fundCycleW hW z₀ hz₀ K) (fundCycleW_boundary hW z₀ hz₀ K)).symm

end SKEFTHawking.SingularConnSquareCloseNCInt
