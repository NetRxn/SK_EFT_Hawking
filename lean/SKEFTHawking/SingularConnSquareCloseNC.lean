import Mathlib
import SKEFTHawking.SingularConnSquareMatch
import SKEFTHawking.SingularConnSquareLHS
import SKEFTHawking.SingularConnSquareLHSCover
import SKEFTHawking.SingularConnSquareCloseFinal
import SKEFTHawking.SingularConnSquareRHSPairing
import SKEFTHawking.SingularCapSubKDuality
import SKEFTHawking.SingularOpenDualityCycle
import SKEFTHawking.SingularHcrossClose
import SKEFTHawking.SingularCoverPartitionExist
import SKEFTHawking.SingularConnSquareLHSExplicit
import SKEFTHawking.SingularAbsCohomConnGeom
import SKEFTHawking.SingularConnSquareLHSRealize
import SKEFTHawking.SingularRelCohomSetCongrMk
import SKEFTHawking.SingularConnSquareMatchCross

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-NC) — non-circular connecting-square closure (WIP)

Closes the per-`K` Poincaré-duality connecting square `subHomConnecting (legW K g) = openDuality (legδ K g)`
by reducing it (via `SingularConnSquareMatch.subHomConnecting_openDuality_of_match`, which discharges all
leg/colimit machinery through Kronecker non-degeneracy) to the single relative-Kronecker **MATCH M**
`hmatch`, then closing `hmatch` via the **cup-form PAIRING route** (route B, 2026-06-22): both legs reduce
to `⟨grep ∪ a', z₀⟩` on the single shared `z₀` via `SingularConnSquareRHSPairing.pair_fund_eq_pair_z0`
(a cocycle `c = grep ∪ a'` vanishing on `C(Kᶜ)` pairs identically against `fund` and `z₀` when they are
rel-homologous). The hmem/excision gap is cap-form/class-altitude only; the pairing form sidesteps it
(`relKroneckerH_relMvDelta_pairing` is unconditional).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularConnSquareMatch
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularConnSquareLHS

namespace SKEFTHawking.SingularConnSquareCloseNC

variable {X : TopCat} [T2Space ↑X]

theorem subHomConnecting_openDuality {N p : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K) :
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
  -- ▶ ROUTE B (2026-06-22): reduce the whole connecting square to the single MATCH M `hmatch` via
  --   `_of_match` (it discharges leg/colimit machinery through Kronecker non-degeneracy), then close
  --   `hmatch` by the cup-form pairing route (both legs → ⟨grep∪a', z₀⟩ via `pair_fund_eq_pair_z0`).
  apply subHomConnecting_openDuality_of_match hU hV z₀ hz₀ K g
  intro a'rep b hb
  -- ▶ hmatch : `relKroneckerH g [chainIncl(rcap b fund_∪)] = relKroneckerH g↾ (relMvDelta[chainIncl(rcap a' fund_∩)])`.
  -- ▶ THE HMATCH (the clean `_of_match` output = the documented close-path (C) surface, TRACE:194–199):
  --   `relKroneckerH g [chainIncl(rcap b fund_∪)] = relKroneckerH σ (relMvDelta[chainIncl(rcap a'rep fund_∩)])`,
  --   `b` reps `absCohomConn a'rep` (`hb`), `σ = g↾`; both `fund = fundCycleW(castChain z₀)` of the SAME z₀.
  -- ▶ CLOSE (C) — the documented path (brick-1's ambient lowering was BELOW this surface; reverted 2026-06-22):
  --   • RHS V-part: `rhs_relMvDelta_rcap_eq_legVpart` (HcrossClose:120, bundles the cover-split, returns
  --     `hwcyc`) → `relKroneckerH σ [chainIncl(legSplitVᶜ) w']` → descend → `kronecker grep↾ (chainIncl w')`.
  --   • LHS V-part: `kroneckerH_subHomConnecting_legW` (LHS:40) → `⟨a', subHomConnecting(legW K g)⟩`, then
  --     `kroneckerH_subHomConnecting_seam` (LHSLeg:34, whnf carried abstractly) → `kronecker a'rep (seam zseam)`.
  --   • FINAL cross-space match `kronecker a'rep (seam zseam) = kronecker grep↾ (chainIncl(legSplitVᶜ) w')` —
  --     the two V-parts over the shared z₀, matched by the cup–cap core `kronecker_cap_eq_kronecker_rcap`
  --     (MatchLHS:73) + `chainIncl_rcap_cover_agree` + `relativeDualityK_cycle_compat_relB`. The genuine core.
  --   See LAB_NOTEBOOK.md (the complete (C) close-path map).
  -- ── (C) RHS V-part (whnf-free): `relMvDelta[chainIncl(rcap a'rep fund_∩)]` → the `legSplitVᶜ` V-part `w'`.
  have hbdRHS := SingularOpenDualityCycle.fundCycleW_boundary (hU.inter hV)
    (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 1 + 1 + p + 1 by omega) z₀)
    (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
    (SingularCSCMayerVietorisConnecting.infCompact U V
      (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
      (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K))
  rw [SingularCSCMayerVietorisConnecting.infCompact_coe, Set.compl_inter] at hbdRHS
  obtain ⟨w', hwcyc, hV⟩ := SingularHcrossClose.rhs_relMvDelta_rcap_eq_legVpart
    (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    _ (SingularOpenDualityCycle.fundCycleW_mem_W (hU.inter hV) _ _ _) a'rep
    (SingularCapSubKDuality.chainIncl_rcap_mem_relCycles _ _ hbdRHS a'rep)
  erw [hV]
  -- ── (C) LHS: realize the relative pairing as `⟨a', subHomConnecting(legW K g)⟩` (kroneckerH_subHomConnecting_legW).
  rw [← SingularConnSquareLHS.kroneckerH_subHomConnecting_legW (a' := Submodule.Quotient.mk a'rep) (hb := hb)]
  -- (C) LHS step (a): Kronecker adjunction `⟨a', subHomConnecting w⟩ = ⟨absCohomConn a', w⟩` — moves the
  --   connecting map off the homology side onto the (opaque, but cover-partitionable) absolute cohomology class.
  rw [← SingularSubHomologyMVCohomConn.kroneckerH_absCohomConn]
  -- (C) LHS step (b): `g : cohomGW = H(M|K)` is a quotient class; take a cocycle rep `grep` so that
  --   `legW_mk` can realize `legW K g` as the cap-with-fundamental-cycle `[pullbackDualityₗ … grep]`.
  obtain ⟨grep, rfl⟩ := Submodule.Quotient.mk_surjective _ g
  -- (C) LHS step (b cont.): realize `legW K (mk grep)` as the homology class of `grep ⌢ fundCycleW`
  --   (`pullbackDualityₗ`). `erw` (not `rw`): `legW_mk` wants the `RelativeCohomology.mk` spelling, defeq to
  --   the `Submodule.Quotient.mk` the rep-extraction produced.
  erw [SingularLegWCapForm.legW_mk]
  -- ▶ REMAINING (the genuine 5-day core): cover-split `grep ⌢ fundCycleW` by subdivision
  --   (`homology_mk_singularSd_iterate` → `exists_iterate_mvUnion`/`mem_subspaceChains_preimage_union`
  --   → `exists_chainIncl_partition_of_mem_mvUnionChains` ⇒ zA,zB), then `kroneckerH_absCohomConn_cover_partition`
  --   (whnf-dodge; z_seam ∃-bound) ⇒ `kronecker a'rep (seam ∂zB)`; then the FINAL cross-space match to the RHS
  --   V-part `chainIncl(legSplitVᶜ) w'` via `kronecker_cap_eq_kronecker_rcap` + `chainIncl_rcap_cover_agree`
  --   + `relativeDualityK_cycle_compat_relB` (both legs → ⟨grep ∪ a', z₀⟩ over the shared z₀).
  -- (C) LHS step (c): realize the cap-cycle's pairing as the seam V-part via the abstract-w shard
  --   `kroneckerH_absCohomConn_coverClass` — `_` for the cycle is assigned by `erw` STRUCTURALLY (no whnf;
  --   the shard does the cover-split + cover_partition internally over an abstract cycle `w`).
  obtain ⟨zseam, hLHS⟩ :=
    SingularConnSquareLHSRealize.kroneckerH_absCohomConn_coverClass U V hU ‹IsOpen V› p a'rep _
  erw [hLHS]
  -- (C) FINAL match — RHS bridge (cast-free path): `relKroneckerH_relCohomRestrict'` peels relCohomRestrict
  --   (→ relIncl on homology); `SingularRelativeMV.relIncl_mk` pushes relIncl THROUGH `mk` (no cast — the
  --   `relCohomSetCongr_relIncl_collapse` route makes a blocking `hSet ▸`, AVOID it); then handle
  --   relCohomSetCongr(mk grep) + `relKroneckerH_mk_mk` + `relKronecker_mk` ⟹ `kronecker grep (chainIncl
  --   legSplitVᶜ w')`. Then `apply SingularConnSquareMatchCross.cross_realization_match` (W=U∩V, gamb=grep,
  --   LVc=legSplitVᶜ, c = z₀-realized cap, ONCE) → hRHS (`chainIncl_rcap_cover_agree`) + hLHS (sub-lemma A core).
  rw [SingularDualityAdjoint.relKroneckerH_relCohomRestrict']  -- cast-FREE: relIncl onto homology, no `▸`
  erw [SingularRelativeMV.relIncl_mk]  -- push relIncl THROUGH mk (erw clears the LinearMap-coe that blocked rw)
  erw [SingularRelCohomSetCongrMk.relCohomSetCongr_mk]  -- collapse relCohomSetCongr ⟹ cohomology now `mk (h ▸ grep)`
  erw [SingularRelativePairing.relKroneckerH_mk_mk, SingularRelativePairing.relKronecker_mk]  -- ⟹ both sides `kronecker`
  simp only [SingularFunctoriality.mapChain_id]  -- RHS = `kronecker (h ▸ grep) (chainIncl legSplitVᶜ w')` — the cross-match shape
  sorry

end SKEFTHawking.SingularConnSquareCloseNC
