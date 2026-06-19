import Mathlib
import SKEFTHawking.SingularConnSquareLHS
import SKEFTHawking.SingularOpenDualityConnLegdeltaCollapse
import SKEFTHawking.SingularRelativeDualityKSetCongr
import SKEFTHawking.SingularMvDeltaPartition
import SKEFTHawking.SingularRelMvDeltaChain
import SKEFTHawking.SingularRightCapBoundary
import SKEFTHawking.SingularConnSquareRHSN2
import SKEFTHawking.PoincareDualityConstruct

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-M4) — the connecting-square hcore, reduced to MATCH M

The per-`K` cycle core `hcore` of the Poincaré-duality connecting square
(`subHomConnecting (legW K g) = openDuality (legδ K g)` in `Homology (sub(U∩V)) (p+1)`) is here
reduced, via the Kronecker-pairing universal-coefficients non-degeneracy
(`homology_eq_zero_of_kroneckerH`, pairing the difference against *all*
`a' : Cohomology (sub(U∩V)) (p+1)`) together with the two committed leg reductions
(`kroneckerH_subHomConnecting_legW` for the LHS; `openDuality_legδ_eq_legW` +
`kroneckerH_relativeDualityK_setCongr_relCohomMvConnecting_N2` for the RHS), to the single
relative-Kronecker **MATCH M**:

  `relKroneckerH ((↑K)ᶜ) g [chainIncl (b ⌢ʳ z_K)]`
    `= relKroneckerH (LUᶜ ∩ LVᶜ) (g↾) (relMvDelta LUᶜ LVᶜ [chainIncl (a' ⌢ʳ z'')])`

(`b` a cocycle rep of `absCohomConn a'`, `z_K`/`z''` the per-compact fundamental cycles of the common
ancestor `z₀`, `LU = legSplitU`, `LV = legSplitV`, `g↾` the cover-restricted `g`). `subHomConnecting_of_match`
discharges the colimit/leg machinery and presents the genuine remaining content (a shared cover-partition
of the fundamental cycle + cap-Leibniz) as the explicit hypothesis `hmatch`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularSubsetHomology SKEFTHawking.SingularSubHomologyMV
  SKEFTHawking.SingularCapChainIncl SKEFTHawking.SingularOpenDuality
  SKEFTHawking.SingularOpenDualityCycle SKEFTHawking.SingularConnSquareLHS
  SKEFTHawking.SingularConnSquareRHSAdjoint SKEFTHawking.SingularRelMvDeltaChain
  SKEFTHawking.SingularMvDeltaPartition SKEFTHawking.SingularCapSubKDuality
  SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularSubspaceChainsEquiv

namespace SKEFTHawking.SingularConnSquareMatch

variable {X : TopCat} [T2Space ↑X]

/-- **The connecting-square per-`K` cycle core, reduced to the relative-Kronecker MATCH M.** Given the
match `hmatch` (the genuine shared-cover-partition + cap-Leibniz content), `hcore` follows from the
universal-coefficients non-degeneracy of the Kronecker pairing and the two committed leg reductions. -/
theorem subHomConnecting_openDuality_of_match {N p : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V))
    (g : cohomGW (U ∪ V) (N + 1) K)
    (hmatch : ∀ (a'rep : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) (p + 1)))
        (b : LinearMap.ker (coboundaryₗ (sub (U ∪ V)) (p + 2))),
        Submodule.Quotient.mk b
          = SKEFTHawking.SingularSubHomologyMVCohomConn.absCohomConn U V hU hV p
              (Submodule.Quotient.mk a'rep) →
      relKroneckerH ((↑K.1 : Set ↑X)ᶜ) g
          (RelativeHomology.mk ((↑K.1 : Set ↑X)ᶜ) (N + 1)
            ⟨RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (N + 1)
                (chainIncl (U ∪ V) (N + 1) (rcap b.1
                  ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∪ V) (N + 1 + (p + 1) + 1)).symm
                    ⟨fundCycleW (hU.union hV)
                        (SingularOpenDualityMVConnSquare.castChain
                          (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
                        (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero
                          (by omega) (by omega) z₀ hz₀) K,
                      fundCycleW_mem_W (hU.union hV) _ _ _⟩))),
              chainIncl_rcap_mem_relCycles _ _
                (fundCycleW_boundary (hU.union hV) _ _ _) b⟩)
        = relKroneckerH
            ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ
              ∩ (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
            ((SingularRelativeCohomologyRestrict.relCohomRestrict
                (Set.inter_subset_inter subset_rfl subset_rfl) (N + 1))
              ((SingularCompactlySupportedTop.relCohomSetCongr
                  (by rw [SingularCSCMayerVietorisConnecting.legSplit_cover U V hU hV K,
                    Set.compl_union]) (N + 1) g)))
            (relMvDelta
              ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ)
              ((↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
              (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
              (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
              (N + 1)
              (RelativeHomology.mk
                ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ
                  ∪ (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ) (N + 2)
                ⟨RelativeChain.mk
                    ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ
                      ∪ (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ) (N + 2)
                    (chainIncl (U ∩ V) (N + 2) (rcap a'rep.1
                      ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 2 + p + 1)).symm
                        ⟨fundCycleW (hU.inter hV)
                            (SingularOpenDualityMVConnSquare.castChain
                              (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
                            (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero
                              (by omega) (by omega) z₀ hz₀)
                            (SingularCSCMayerVietorisConnecting.infCompact U V
                              (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                              (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)),
                          fundCycleW_mem_W (hU.inter hV) _ _ _⟩))),
                  chainIncl_rcap_mem_relCycles _ _
                    (by
                      have := fundCycleW_boundary (hU.inter hV)
                        (SingularOpenDualityMVConnSquare.castChain
                          (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
                        (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero
                          (by omega) (by omega) z₀ hz₀)
                        (SingularCSCMayerVietorisConnecting.infCompact U V
                          (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                          (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K))
                      rw [SingularCSCMayerVietorisConnecting.infCompact_coe, Set.compl_inter] at this
                      exact this)
                    a'rep⟩))) :
    SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV (p + 1)
        (SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := p + 1) (hU.union hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          K g)
      = openDuality (k := N + 2) (m := p) (hU.inter hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          (SKEFTHawking.SingularCSCMayerVietorisConnecting.legδ U V hU hV N K g) := by
  rw [← sub_eq_zero]
  apply SKEFTHawking.PoincareDualityConstruct.homology_eq_zero_of_kroneckerH (p + 1)
  intro a'
  rw [map_sub, sub_eq_zero]
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularSubHomologyMVCohomConn.absCohomConn U V hU hV p a')
  rw [kroneckerH_subHomConnecting_legW hU hV
    (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
    (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
    K g a' b hb]
  rw [SKEFTHawking.SingularOpenDualityConnLegdeltaCollapse.openDuality_legδ_eq_legW]
  obtain ⟨a'rep, rfl⟩ := Submodule.Quotient.mk_surjective _ a'
  rw [SKEFTHawking.SingularOpenDuality.legW]
  have hJL : ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ
        ∪ (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
      = ((↑(SingularCSCMayerVietorisConnecting.infCompact U V
            (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
            (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)).1 : Set ↑X)ᶜ) := by
    rw [SingularCSCMayerVietorisConnecting.infCompact_coe, Set.compl_inter]
  have hbdy := fundCycleW_boundary (hU.inter hV)
    (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
    (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
    (SingularCSCMayerVietorisConnecting.infCompact U V
      (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
      (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K))
  have hbdyUV : chainBoundary X (N + 2 + p) (fundCycleW (hU.inter hV)
      (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
      (SingularCSCMayerVietorisConnecting.infCompact U V
        (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
        (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
      ∈ subspaceChains ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ
          ∪ (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ) (N + 2 + p) := by
    rw [hJL]; exact hbdy
  have hRHS := SKEFTHawking.SingularConnSquareRHSN2.kroneckerH_relativeDualityK_setCongr_relCohomMvConnecting_N2
    (U' := (↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ)
    (V' := (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
    (K := U ∩ V)
    (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    hJL
    (fundCycleW (hU.inter hV)
      (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
      (SingularCSCMayerVietorisConnecting.infCompact U V
        (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
        (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
    (fundCycleW_mem_W (hU.inter hV) _ _ _)
    hbdyUV hbdy a'rep
    ((SingularRelativeCohomologyRestrict.relCohomRestrict
        (Set.inter_subset_inter subset_rfl subset_rfl) (N + 1))
      ((SingularCompactlySupportedTop.relCohomSetCongr
          (by rw [SingularCSCMayerVietorisConnecting.legSplit_cover U V hU hV K, Set.compl_union])
          (N + 1) g)))
  refine Eq.trans ?_ hRHS.symm
  exact hmatch a'rep b hb

end SKEFTHawking.SingularConnSquareMatch
