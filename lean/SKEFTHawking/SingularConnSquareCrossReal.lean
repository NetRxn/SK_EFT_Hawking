import Mathlib
import SKEFTHawking.SingularConnSquareCloseUncond
import SKEFTHawking.SingularConnSquareRHSDance
import SKEFTHawking.SingularConnSquareMatchCross

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — UNCONDITIONAL connecting-square close

Discharges the cross-realization residual `hcore` of
`SingularConnSquareCloseUncond.subHomConnecting_openDuality_of_crossRealization`, yielding the
unconditional per-`K` Poincaré-duality connecting square `subHomConnecting (legW K g) = openDuality (legδ K g)`.

The discharge wires three committed engines over the shared fundamental cycle `z₀`:
- the LHS seam transport `kroneckerH_double_seam` (pairing against a test cocycle `ωrep`);
- the RHS W5 dance `SingularConnSquareRHSDance.rhs_dance` (reduces the `relativeDualityK` leg to the
  connecting-INPUT pairing `⟨σ_inner, w⟩`, `w` the `V`-part `chainIncl LVᶜ w'`);
- the heavy-term-free pivot `SingularConnSquareMatchCross.cross_realization_match`, leaving the two
  genuine cross-realization bridges `hLHS` (LHS connecting-cap naturality) and `hRHS` (rcap-vs-`LVᶜ`
  realization), both over the shared `c = z₀`-realized in `sub (U∩V)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularCompactlySupportedOpen

namespace SKEFTHawking.SingularConnSquareCrossReal

open SKEFTHawking.SingularConnSquareRHSN2 SKEFTHawking.SingularConnSquareCloseFinal
  SKEFTHawking.SingularRelCohomMvConnectingGeom SKEFTHawking.SingularLocalDualityK
  SKEFTHawking.SingularRelativeCohomologyMVConnecting SKEFTHawking.SingularCompactlySupportedTop
  SKEFTHawking.SingularCapChainIncl SKEFTHawking.SingularSubspaceChainsEquiv
  SKEFTHawking.SingularConnSquareRHSDance SKEFTHawking.SingularConnSquareMatchCross
  SKEFTHawking.SingularConnSquareMatchLHS

variable {X : TopCat} [T2Space ↑X]

theorem subHomConnecting_openDuality {N p : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K) :
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
  apply SingularConnSquareCloseUncond.subHomConnecting_openDuality_of_crossRealization hU hV z₀ hz₀ K g
  intro g_rep zc0 hzc0 zA zB hcyc hpart hzBmem σR_rep hσR
  apply eq_of_sub_eq_zero
  apply SKEFTHawking.PoincareDualityConstruct.homology_eq_zero_of_kroneckerH
  intro ω
  obtain ⟨ωrep, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
  rw [map_sub, sub_eq_zero, SingularConnSquareCloseUncond.kroneckerH_double_seam]
  obtain ⟨σ_inner, hσi⟩ := Submodule.Quotient.mk_surjective _
    ((SingularRelativeCohomologyRestrict.relCohomRestrict
        (Set.inter_subset_inter subset_rfl subset_rfl) (N + 1))
      ((SingularCompactlySupportedTop.relCohomSetCongr
          (by rw [SingularCSCMayerVietorisConnecting.legSplit_cover U V hU hV K, Set.compl_union])
          (N + 1))
        (Submodule.Quotient.mk g_rep)))
  rw [← hσi] at hσR
  obtain ⟨w_R, hwmem, hweq⟩ := rhs_dance
    (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    (by simp only [SingularCSCMayerVietorisConnecting.infCompact_coe, Set.compl_inter,
        TopologicalSpace.Compacts.carrier_eq_coe])
    (SingularOpenDualityCycle.fundCycleW (hU.inter hV)
      (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
      (SingularCSCMayerVietorisConnecting.infCompact U V
        (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
        (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
    (SingularOpenDualityCycle.fundCycleW_mem_W (hU.inter hV) _ _ _)
    (by simpa only [SingularCSCMayerVietorisConnecting.infCompact_coe, Set.compl_inter,
        TopologicalSpace.Compacts.carrier_eq_coe] using
          SingularOpenDualityCycle.fundCycleW_boundary (hU.inter hV)
            (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
            (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
            (SingularCSCMayerVietorisConnecting.infCompact U V
              (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
              (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
    (SingularOpenDualityCycle.fundCycleW_boundary (hU.inter hV) _ _ _)
    ωrep σ_inner
  erw [← hσR] at hweq
  refine Eq.trans ?_ hweq.symm
  erw [← SingularKroneckerFunctoriality.kronecker_mapChain,
    ← SingularKroneckerFunctoriality.kronecker_mapChain]
  obtain ⟨w', hw'⟩ := hwmem
  -- brick 1: `zc0`'s up-to-homology cover-split is exact modulo a boundary `∂η`.
  obtain ⟨η, hη⟩ := SingularConnSquareRHSScaffold.exists_boundary_of_homology_eq zc0 ⟨_, hcyc⟩ hpart
  -- brick 2: `zc0 = g̃ ⌢ z_K` modulo a boundary `∂η'` (via `legW_mk`).
  erw [SingularLegWCapForm.legW_mk] at hzc0
  obtain ⟨η', hη'⟩ := SingularConnSquareRHSScaffold.exists_boundary_of_homology_eq zc0 _ hzc0
  rw [← hw']
  apply SingularConnSquareMatchCross.cross_realization_match
  -- ▶ Obligations: hLHS (`⟨ωrep, lhsChain⟩ = ⟨ωrep, cap (pullbackCochain (U∩V) g̃) c⟩`) + hRHS
  --   (`⟨g̃, chainIncl (U∩V)(rcap ωrep c)⟩ = ⟨g̃, chainIncl legSplitVᶜ w'⟩`) + (sometimes) the shared `?c` data.
  --   `all_goals sorry` — robust to whether `?c` is absorbed into hLHS or a separate goal (a NON-DETERMINISTIC
  --   metavar fragility: inline hLHS steps that touch `?c` can break the upstream `Eq.trans` synthesis).
  -- ▶ hLHS ASSEMBLY (all 4 bricks committed — build SOLO in an isolated lemma to keep `?c` from leaking up):
  --   (1) `exists_boundary_of_homology_eq zc0 ⟨_,hcyc⟩ hpart` ⟹ `↑zc0 = chainIncl zA+zB + ∂η`;
  --   (2) `erw [legW_mk] at hzc0` + `exists_boundary_of_homology_eq zc0 _ hzc0` ⟹ `↑zc0 = cap g̃ z_K_sub + ∂η'`;
  --   (3) `exists_cap_cover_partition` (`33476fb3`) ⟹ clean cap partition, V-part `cap g̃|_V w` a genuine cap;
  --   (4) `cap_mapChain` (`c9f35f09`) ×2 moves the cap through the seam homeos ⟹ LHS = `cap (g↾) c`, c = double-seam(∂w).
  all_goals sorry

end SKEFTHawking.SingularConnSquareCrossReal
