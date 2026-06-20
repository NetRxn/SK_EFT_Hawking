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

omit [T2Space ↑X] in
/-- **Subdivision-invariance of the cocycle pairing**: for a cocycle `a` and a cycle `c` (`∂c = 0`), the
Kronecker pairing is invariant under barycentric subdivision: `⟨a, Sdᵐ c⟩ = ⟨a, c⟩`. Since
`Sdᵐ c = c + ∂(Dₘ c)` for a cycle (`add_singularSd_iterate_eq_boundary`), the subdivision differs from `c`
by a boundary, which a cocycle annihilates (`⟨a, ∂h⟩ = ⟨δa, h⟩ = 0`). This is the chain-level tool that
lets a cover-partition obtained *after* subdivision be paired against the unsubdivided seam cocycle. -/
theorem kronecker_singularSd_iterate_cocycle {n : ℕ} (a : LinearMap.ker (coboundaryₗ X (n + 1)))
    (c : SingularChain X (n + 1)) (hc : chainBoundary X n c = 0) (m : ℕ) :
    kronecker a.1 ((⇑(SingularSubdivision.singularSd X (n + 1)))^[m] c) = kronecker a.1 c := by
  have h := SingularExcision.add_singularSd_iterate_eq_boundary hc m
  have hsd : (⇑(SingularSubdivision.singularSd X (n + 1)))^[m] c
      = c + chainBoundary X (n + 1) (SingularSubdivision.iterHomotopy X (n + 1) m c) := by
    conv_rhs => rw [← h]
    rw [← add_assoc, ZModModule.add_self, zero_add]
  have hδ : kronecker a.1 (chainBoundary X (n + 1)
      (SingularSubdivision.iterHomotopy X (n + 1) m c)) = 0 := by
    rw [← kronecker_coboundary_chainBoundary,
      show coboundary X (n + 1) a.1 = coboundaryₗ X (n + 1) a.1 from rfl, LinearMap.mem_ker.mp a.2,
      ← kroneckerₗ_apply, map_zero, LinearMap.zero_apply]
  rw [hsd, kronecker_add_right, hδ, add_zero]

/-- **The connecting-square close, reduced to the cross-realization homology-class equation.**
This carries the *entire* seam/duality descent of `hmatch` and leaves a single, geometrically clean
residual `hcore`: the bottom-row Mayer–Vietoris connecting realization `seamI (seamHom [∂zB])` of the
`V`-part seam boundary equals the per-`K` Poincaré-duality realization `D_J (σR) = [σR ⌢ z_J]` of the
cohomology-connecting cocycle, as classes in `H_{p+1}(sub (U∩V))`. This is materially cleaner than the
chain-level `hmatch` of `subHomConnecting_openDuality_of_chainMatch`: the messy double-cochain-pullback
seam transport (`kroneckerH_double_seam_symm`) is already discharged, so `hcore` is exactly the
**cross-realization compatibility** — provable from the shared fundamental cycle `z₀` via
`SingularOpenDualityCycle.relativeDualityK_cycle_compat_relB` plus the chain-level cap-Leibniz
cover-partition (with subdivision handled by `kronecker_singularSd_iterate_cocycle`). -/
theorem subHomConnecting_openDuality_of_crossRealization {N p : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K)
    (hcore : ∀ (g_rep : LinearMap.ker (relCoboundaryₗ ((↑K.1 : Set ↑X)ᶜ) (N + 1)))
        (zc0 : cycles (sub (U ∪ V)) (p + 1 + 1))
        (_hzc0 : Submodule.Quotient.mk zc0
          = SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := p + 1) (hU.union hV)
              (SingularOpenDualityMVConnSquare.castChain
                (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
              (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
              K (Submodule.Quotient.mk g_rep))
        (zA : SingularChain (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (p + 1 + 1))
        (zB : SingularChain (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (p + 1 + 1))
        (hcyc : chainIncl (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (p + 1 + 1) zA
            + chainIncl (Subtype.val ⁻¹' V) (p + 1 + 1) zB ∈ cycles (sub (U ∪ V)) (p + 1 + 1))
        (_hpart : Homology.mk (sub (U ∪ V)) (p + 1 + 1) zc0
          = Homology.mk (sub (U ∪ V)) (p + 1 + 1) ⟨_, hcyc⟩)
        (hzBmem : zB ∈ SingularPairLES.relCycleLift
            (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1))
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
      (seamI U V (p + 1))
          ((SingularMayerVietorisLES.seamHomologyEquiv
              (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) (p + 1))
            (Homology.mk (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)))
              (p + 1)
              ⟨SingularPairLES.boundaryExtract
                  (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
                  ⟨zB, hzBmem⟩,
                SingularPairLES.boundaryExtract_mem_cycles _ (p + 1) _⟩))
        = SingularLocalDualityK.relativeDualityK
            ((↑(SingularCSCMayerVietorisConnecting.infCompact U V
                (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)).1 : Set ↑X)ᶜ) (U ∩ V)
            (N + 2) p
            (SingularOpenDualityCycle.fundCycleW (hU.inter hV)
              (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
              (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
              (SingularCSCMayerVietorisConnecting.infCompact U V
                (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
            (SingularOpenDualityCycle.fundCycleW_mem_W (hU.inter hV) _ _ _)
            (SingularOpenDualityCycle.fundCycleW_boundary (hU.inter hV) _ _ _)
            (RelativeCohomology.mk _ (N + 2) σR_rep)) :
    SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV (p + 1)
        (SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := p + 1) (hU.union hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          K g)
      = SKEFTHawking.SingularOpenDuality.openDuality (k := N + 2) (m := p) (hU.inter hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          (SKEFTHawking.SingularCSCMayerVietorisConnecting.legδ U V hU hV N K g) := by
  apply SingularConnSquareCloseChainMap.subHomConnecting_openDuality_of_chainMatch hU hV z₀ hz₀ K g
  intro g_rep zc0 hzc0 zA zB hcyc hpart a'rep hzBmem σR_rep hσR
  -- The RHS cap chain is a `cycles (sub (U ∩ V)) (p+1)`.
  have hRHScyc : SingularLocalDualityK.pullbackDualityₗ
      ((↑(SingularCSCMayerVietorisConnecting.infCompact U V
          (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
          (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)).1 : Set ↑X)ᶜ) (U ∩ V)
      (SingularOpenDualityCycle.fundCycleW (hU.inter hV)
        (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
        (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
        (SingularCSCMayerVietorisConnecting.infCompact U V
          (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
          (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
      (SingularOpenDualityCycle.fundCycleW_mem_W (hU.inter hV) _ _ _) σR_rep
      ∈ cycles (sub (U ∩ V)) (p + 1) :=
    SingularLocalDualityK.pullbackDualityₗ_mem_cycles _ _ _ _
      (SingularOpenDualityCycle.fundCycleW_boundary (hU.inter hV) _ _ _) σR_rep
  -- Step 1: lift both sides to `kroneckerH (mk a'rep) (-)`, reducing to a class equation.
  rw [← kroneckerH_mk_mk a'rep ⟨SingularPairLES.boundaryExtract
        (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1) ⟨zB, hzBmem⟩,
      SingularPairLES.boundaryExtract_mem_cycles _ (p + 1) _⟩,
    ← SingularConnSquareCloseChainMap.kroneckerH_double_seam_symm U V (p + 1) a'rep ⟨_, hRHScyc⟩]
  refine congrArg (kroneckerH (p + 1) (Submodule.Quotient.mk a'rep)) ?_
  -- Convert the symm class equation to the forward form `seamI (seamHom [∂zB]) = D_J(σR)`.
  rw [LinearEquiv.eq_symm_apply, LinearEquiv.eq_symm_apply,
    show Homology.mk (sub (U ∩ V)) (p + 1)
        ⟨SingularLocalDualityK.pullbackDualityₗ _ (U ∩ V) _ _ σR_rep, hRHScyc⟩
      = SingularLocalDualityK.relativeDualityK _ (U ∩ V) (N + 2) p _ _
          (SingularOpenDualityCycle.fundCycleW_boundary (hU.inter hV) _ _ _)
          (RelativeCohomology.mk _ (N + 2) σR_rep)
      from (SingularLocalDualityK.relativeDualityK_mk _ _ (N + 2) p _ _ _ σR_rep).symm]
  exact hcore g_rep zc0 hzc0 zA zB hcyc hpart hzBmem σR_rep hσR

end SKEFTHawking.SingularConnSquareCloseUncond
