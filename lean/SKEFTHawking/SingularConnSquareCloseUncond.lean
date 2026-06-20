import Mathlib
import SKEFTHawking.SingularConnSquareCloseChainMap

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — toward the UNCONDITIONAL connecting-square close

`SingularConnSquareCloseChainMap.subHomConnecting_openDuality_of_chainMatch` proves the per-`K`
Poincaré-duality connecting square taking the single explicit cross-cover cap-naturality pairing
`hmatch` as a hypothesis. Discharging `hmatch` reduces (via the seam transport
`kroneckerH_double_seam_symm` (RHS) + `kroneckerH_mk_mk` (LHS) + universal-coefficients
non-degeneracy) to a single explicit chain cap-Leibniz identity.

This file provides the **forward double-seam dual transport** `kroneckerH_double_seam` — the
`seamI ∘ seamHom`-forward analogue of `kroneckerH_double_seam_symm` — which is the LHS-side reduction
of that residual: it rewrites `⟨c, seamI (seamHom [zY])⟩` (the bottom-row connecting class paired against
a `sub (U∩V)`-cocycle `c`) to the chain pairing `⟨double-pullback c, zY⟩`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularConnSquareMatch
  SKEFTHawking.SingularConnSquareLHSLeg SKEFTHawking.SingularRelMvDeltaPartition
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularConnSquareLHS

namespace SKEFTHawking.SingularConnSquareCloseUncond

open SKEFTHawking.SingularMvDeltaPartition SKEFTHawking.SingularConnSquareLHSExplicit
  SKEFTHawking.SingularCoverPartitionExist SKEFTHawking.SingularConnSquareLHSPairing
  SKEFTHawking.SingularConnSquareMatchLHS SKEFTHawking.SingularConnSquareCloseM2
  SKEFTHawking.SingularLegWCapForm SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularRelCohomMvConnectingGeom SKEFTHawking.SingularConnSquareCloseFinal
  SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularSeamDualPairing
  SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularCapSubKDuality

open SKEFTHawking.SingularKroneckerFunctoriality (pullbackCochainMap pullbackCochainMap_mem_ker
  kroneckerH_Homology_map)

variable {X : TopCat} [T2Space ↑X]

omit [T2Space ↑X] in
/-- **Forward double-seam dual transport** (the `seamI ∘ seamHom`-forward analogue of
`SingularConnSquareCloseChainMap.kroneckerH_double_seam_symm`): pairing a `sub (U∩V)`-cocycle `c`
against `seamI (seamHom [zY])` for a `sub (restr (val⁻¹U) (val⁻¹V))`-cycle `zY` equals the chain-level
pairing of the double cochain-pullback of `c` (through `seamHomeo` then `subSeamHomeo`) against `zY`.
The forward-direction reduction of the LHS seam-class. -/
theorem kroneckerH_double_seam (U V : Set ↑X) (n : ℕ)
    (c : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) n))
    (zY : cycles (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n) :
    kroneckerH (X := sub (U ∩ V)) n (Submodule.Quotient.mk c)
        (seamI U V n
          (SingularMayerVietorisLES.seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))
            (Subtype.val ⁻¹' V) n
            (Homology.mk (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n zY)))
      = kronecker
          (pullbackCochainMap ⟨(SingularMayerVietorisLES.seamHomeo
              (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)),
              (SingularMayerVietorisLES.seamHomeo
                (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).continuous⟩ n
            (pullbackCochainMap ⟨(SingularSubHomologyMV.subSeamHomeo
                (Set.inter_subset_left.trans Set.subset_union_left)
                (fun _ : ↑(sub (U ∪ V)) => Iff.rfl)),
                (SingularSubHomologyMV.subSeamHomeo
                  (Set.inter_subset_left.trans Set.subset_union_left)
                  (fun _ : ↑(sub (U ∪ V)) => Iff.rfl)).continuous⟩ n c.1))
          zY.1 := by
  obtain ⟨zI, hzI'⟩ := Submodule.Quotient.mk_surjective _
    (SingularMayerVietorisLES.seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))
      (Subtype.val ⁻¹' V) n
      (Homology.mk (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n zY))
  have hzI : Homology.mk (sub ((Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) ∩ Subtype.val ⁻¹' V)) n zI
      = SingularMayerVietorisLES.seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))
          (Subtype.val ⁻¹' V) n
          (Homology.mk (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n zY) :=
    hzI'
  rw [seamI, ← hzI]
  erw [kroneckerH_subSeamEquiv (Set.inter_subset_left.trans Set.subset_union_left)
      (fun _ : ↑(sub (U ∪ V)) => Iff.rfl) n c zI]
  erw [hzI, kroneckerH_seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n
      ⟨pullbackCochainMap ⟨(SingularSubHomologyMV.subSeamHomeo
            (Set.inter_subset_left.trans Set.subset_union_left)
            (fun _ : ↑(sub (U ∪ V)) => Iff.rfl)),
          (SingularSubHomologyMV.subSeamHomeo
            (Set.inter_subset_left.trans Set.subset_union_left)
            (fun _ : ↑(sub (U ∪ V)) => Iff.rfl)).continuous⟩ n c.1,
        pullbackCochainMap_mem_ker _ n c⟩ zY,
    kroneckerH_mk_mk]
end SKEFTHawking.SingularConnSquareCloseUncond
