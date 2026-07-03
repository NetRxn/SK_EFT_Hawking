import Mathlib
import SKEFTHawking.SingularConnSquareCloseChainMap
import SKEFTHawking.SingularConnSquareCloseM2Gen
import SKEFTHawking.SingularOpenDualityBotLegdeltaCollapse

/-!
# Phase 5q.G (G1 PD-induction, brick B1c) — the BOTTOM `of_chainMatch₀` reducer

The bottom (`(H₁, H₀)`-pair) mirror of `subHomConnecting_openDuality_of_chainMatch`: the per-`K`
connecting square at homology degree `0` — LHS the MAIN-family `legW (m := 0)` (H₁-valued,
in-scheme), RHS the ₀-family `openDuality₀ ∘ legδ` — reduced to the single degree-`0` chain
pairing `hmatch₀`.

Degree simplification vs the original: at the bottom BOTH sides share the `z₀`-frame
(`N+1+0+1 = N+2`) — no `castChain` presentations anywhere. The seam/partition guts are the SAME
n-generic machinery (`exists_mvUnion_partition`, `mvConnecting_cover_partition`,
`kroneckerH_double_seam_symm`) instantiated at `n = 0`; the RHS collapse is B1a
(`openDuality₀_legδ_eq_legW₀`), the square-to-MV reduction is B1b
(`subHomConnecting_legW_eq_of_mvConnecting_gen` at `p = 0`), and the RHS-inner cap-class form is
the ₀-family's `relativeDualityK₀_mk` (via the local `legW₀_mk`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularMayerVietorisLES
  SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularPairLES
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularOpenDualityBot
  SKEFTHawking.SingularOpenDualityBotLegdeltaCollapse
  SKEFTHawking.SingularConnSquareCloseM2Gen SKEFTHawking.SingularConnSquareCloseChainMap
  SKEFTHawking.SingularKroneckerFunctoriality SKEFTHawking.SingularMvDeltaPartition
  SKEFTHawking.SingularCoverPartitionExist SKEFTHawking.SingularConnSquareLHSExplicit
  SKEFTHawking.SingularConnSquareCloseM2 SKEFTHawking.SingularLocalDualityKBot

namespace SKEFTHawking.SingularConnSquareCloseChainMapBot

variable {X : TopCat} [T2Space ↑X]

/-- **`legW₀` on a `Quotient.mk` is the `Homology.mk` of the bottom pulled-back duality chain**
(the ₀-analogue of `SingularLegWCapForm.legW_mk`, by `relativeDualityK₀_mk`). -/
theorem legW₀_mk {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (K : CompactsIn W) (a : LinearMap.ker (relCoboundaryₗ ((↑K.1 : Set ↑X)ᶜ) (k + 1))) :
    legW₀ hW z₀ hz₀ K (RelativeCohomology.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) a)
      = Homology.mk (sub W) 0
          ⟨SKEFTHawking.SingularLocalDualityKBot.pullbackDualityₗ₀ ((↑K.1 : Set ↑X)ᶜ) W
              (fundCycleW₀ hW z₀ hz₀ K) (fundCycleW₀_mem_W hW z₀ hz₀ K) a,
            Submodule.mem_top⟩ :=
  rfl

/-- **The per-`K` BOTTOM connecting square via the chain-map route**, reduced to the degree-`0`
cross-cover cap-naturality pairing `hmatch₀`. -/
theorem subHomConnecting_openDuality₀_of_chainMatch {N : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + 1 + 0 + 1)) (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K)
    (hmatch : ∀ (g_rep : LinearMap.ker (relCoboundaryₗ ((↑K.1 : Set ↑X)ᶜ) (N + 1)))
        (zc0 : cycles (sub (U ∪ V)) (0 + 1))
        (_hzc0 : Submodule.Quotient.mk zc0
          = SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := 0) (hU.union hV)
              z₀ hz₀ K (Submodule.Quotient.mk g_rep))
        (zA : SingularChain (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (0 + 1))
        (zB : SingularChain (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (0 + 1))
        (hcyc : chainIncl (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (0 + 1) zA
            + chainIncl (Subtype.val ⁻¹' V) (0 + 1) zB ∈ cycles (sub (U ∪ V)) (0 + 1))
        (_hpart : Homology.mk (sub (U ∪ V)) (0 + 1) zc0
          = Homology.mk (sub (U ∪ V)) (0 + 1) ⟨_, hcyc⟩)
        (a'rep : LinearMap.ker (coboundaryₗ
            (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) 0))
        (hzBmem : zB ∈ SingularPairLES.relCycleLift
            (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) 0)
        (σR_rep : LinearMap.ker (relCoboundaryₗ
            ((↑(SingularCSCMayerVietorisConnecting.infCompact U V
                (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)).1 : Set ↑X)ᶜ) (N + 2)))
        (_hσR : Submodule.Quotient.mk σR_rep
          = (SingularCompactlySupportedTop.relCohomSetCongr
              (show ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ
                    ∪ (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
                  = ((↑(SingularCSCMayerVietorisConnecting.infCompact U V
                      (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                      (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)).1 : Set ↑X)ᶜ)
                by rw [SingularCSCMayerVietorisConnecting.infCompact_coe, Set.compl_inter]) (N + 2))
            ((SingularRelativeCohomologyMVConnecting.relCohomMvConnecting
                ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ)
                ((↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
                (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
                (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
                N)
              ((SingularRelativeCohomologyRestrict.relCohomRestrict
                  (Set.inter_subset_inter subset_rfl subset_rfl) (N + 1))
                ((SingularCompactlySupportedTop.relCohomSetCongr
                    (by rw [SingularCSCMayerVietorisConnecting.legSplit_cover U V hU hV K,
                      Set.compl_union]) (N + 1)) (Submodule.Quotient.mk g_rep))))),
      kronecker a'rep.1
          (SingularPairLES.boundaryExtract
            (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) 0
            ⟨zB, hzBmem⟩)
        = kronecker
            (pullbackCochainMap ⟨(subSeamHomeo
                  (Set.inter_subset_left.trans Set.subset_union_left)
                  (fun _ : ↑(sub (U ∪ V)) => Iff.rfl)).symm,
                (subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
                  (fun _ : ↑(sub (U ∪ V)) => Iff.rfl)).symm.continuous⟩ 0
              (pullbackCochainMap ⟨(SingularMayerVietorisLES.seamHomeo
                  (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).symm,
                  (SingularMayerVietorisLES.seamHomeo
                    (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).symm.continuous⟩ 0
                a'rep.1))
            (SKEFTHawking.SingularLocalDualityKBot.pullbackDualityₗ₀
              ((↑(SingularCSCMayerVietorisConnecting.infCompact U V
                  (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                  (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)).1 : Set ↑X)ᶜ)
              (U ∩ V)
              (fundCycleW₀ (hU.inter hV) z₀ hz₀
                (SingularCSCMayerVietorisConnecting.infCompact U V
                  (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                  (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
              (fundCycleW₀_mem_W (hU.inter hV) z₀ hz₀ _) σR_rep)) :
    SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV 0
        (SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K g)
      = openDuality₀ (k := N + 1) (hU.inter hV) z₀ hz₀
          (SKEFTHawking.SingularCSCMayerVietorisConnecting.legδ U V hU hV N K g) := by
  rw [openDuality₀_legδ_eq_legW₀]
  apply subHomConnecting_legW_eq_of_mvConnecting_gen (k := N + 1) (p := 0) U V hU hV z₀ hz₀ K g
  obtain ⟨g_rep, rfl⟩ := Submodule.Quotient.mk_surjective _ g
  obtain ⟨zc0, hzc0⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := 0) (hU.union hV)
      z₀ hz₀ K (Submodule.Quotient.mk g_rep))
  obtain ⟨zA, zB, hcyc, hpart⟩ := exists_mvUnion_partition
    (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val) 0 zc0
    (mem_subspaceChains_preimage_union U V (0 + 1) zc0.1)
  refine mvConnecting_eq_seamRHS_of_partition U V hU hV 0 _ _ zA zB hcyc
    (by rw [← hzc0]; exact hpart) _ rfl ?_
  rw [mvConnecting_cover_partition]
  rw [← sub_eq_zero]
  apply SKEFTHawking.PoincareDualityConstruct.homology_eq_zero_of_kroneckerH 0
  intro a'
  rw [map_sub, sub_eq_zero]
  obtain ⟨a'rep, rfl⟩ := Submodule.Quotient.mk_surjective _ a'
  rw [show Homology.mk (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)))
        0 ⟨SingularPairLES.boundaryExtract
            (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) 0
            ⟨zB, zB_mem_relCycleLift _ _ 0 zA zB hcyc⟩,
          SingularPairLES.boundaryExtract_mem_cycles _ 0 _⟩
        = Submodule.Quotient.mk ⟨SingularPairLES.boundaryExtract
            (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) 0
            ⟨zB, zB_mem_relCycleLift _ _ 0 zA zB hcyc⟩,
          SingularPairLES.boundaryExtract_mem_cycles _ 0 _⟩ from rfl,
    kroneckerH_mk_mk]
  set J := SingularCSCMayerVietorisConnecting.infCompact U V
    (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
    (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K) with hJ
  obtain ⟨σR_rep, hσR⟩ := Submodule.Quotient.mk_surjective _
    ((SingularCompactlySupportedTop.relCohomSetCongr
        (show ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ
              ∪ (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
            = ((↑J.1 : Set ↑X)ᶜ)
          by rw [hJ, SingularCSCMayerVietorisConnecting.infCompact_coe, Set.compl_inter]) (N + 2))
      ((SingularRelativeCohomologyMVConnecting.relCohomMvConnecting
          ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ)
          ((↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
          (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
          (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
          N)
        ((SingularRelativeCohomologyRestrict.relCohomRestrict
            (Set.inter_subset_inter subset_rfl subset_rfl) (N + 1))
          ((SingularCompactlySupportedTop.relCohomSetCongr
              (by rw [SingularCSCMayerVietorisConnecting.legSplit_cover U V hU hV K, Set.compl_union])
              (N + 1)) (Submodule.Quotient.mk g_rep)))))
  rw [← hσR,
    show (Submodule.Quotient.mk σR_rep : RelativeCohomology ((↑J.1 : Set ↑X)ᶜ) (N + 2))
        = RelativeCohomology.mk ((↑J.1 : Set ↑X)ᶜ) (N + 2) σR_rep from rfl,
    legW₀_mk]
  rw [kroneckerH_double_seam_symm]
  exact hmatch g_rep zc0 hzc0 zA zB hcyc hpart a'rep
    (zB_mem_relCycleLift _ _ 0 zA zB hcyc) σR_rep hσR

end SKEFTHawking.SingularConnSquareCloseChainMapBot
