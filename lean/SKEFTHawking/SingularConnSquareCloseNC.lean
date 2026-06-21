import Mathlib
import SKEFTHawking.SingularConnSquareMatch
import SKEFTHawking.SingularConnSquareLHSLeg
import SKEFTHawking.SingularRelMvDeltaPartition
import SKEFTHawking.SingularConnSquareLHS
import SKEFTHawking.SingularLegWCapForm
import SKEFTHawking.SingularConnSquareLHSExplicit
import SKEFTHawking.SingularCoverPartitionExist
import SKEFTHawking.SingularConnSquareLHSPairing
import SKEFTHawking.SingularConnSquareMatchLHS
import SKEFTHawking.SingularConnSquareMatchCross
import SKEFTHawking.SingularConnSquareClose
import SKEFTHawking.SingularConnSquareCloseChainMap
import SKEFTHawking.SingularRelCohomMvConnectingGeom

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-NC) — non-circular connecting-square closure (WIP)
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularConnSquareMatch
  SKEFTHawking.SingularConnSquareLHSLeg SKEFTHawking.SingularRelMvDeltaPartition
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularConnSquareLHS

namespace SKEFTHawking.SingularConnSquareCloseNC

open SKEFTHawking.SingularMvDeltaPartition SKEFTHawking.SingularExcisionIso
  SKEFTHawking.SingularPairLES SKEFTHawking.SingularConnSquareLHSExplicit
  SKEFTHawking.SingularCoverPartitionExist SKEFTHawking.SingularMayerVietorisLES
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularKroneckerFunctoriality
  SKEFTHawking.SingularConnSquareLHSPairing SKEFTHawking.SingularConnSquareMatchLHS
  SKEFTHawking.SingularSubdivision SKEFTHawking.SingularRelativeMV

variable {X : TopCat} [T2Space ↑X]

/-- **RHS-descent (abstract, wall-free):** `relKroneckerH` of a `relCohomRestrict`-restricted cohomology
`mk g` against a relative homology class `[mk W]` descends to the ambient chain pairing of the restricted
cochain against `W`. Stated abstractly (no heavy seam term) so the `rfl`/`mk_mk` lemmas don't whnf-wall;
`rw`-applied at the heavy hmatch goal it substitutes the RHS without touching the LHS. -/
theorem relKroneckerH_relCohomRestrict_descent {Y : TopCat} {S T : Set ↑Y} (h : S ⊆ T) {N : ℕ}
    (g : LinearMap.ker (relCoboundaryₗ T (N + 1))) (W : SingularChain Y (N + 1))
    (hW : RelativeChain.mk S (N + 1) W ∈ relCycles S (N + 1)) :
    SingularRelativePairing.relKroneckerH S
        (SingularRelativeCohomologyRestrict.relCohomRestrict h (N + 1)
          (RelativeCohomology.mk T (N + 1) g))
        (RelativeHomology.mk S (N + 1) ⟨RelativeChain.mk S (N + 1) W, hW⟩)
      = kronecker (SingularRelativeCohomologyRestrict.relCocycleRestrict h (N + 1) g).1 W := by
  rw [SingularRelativeCohomologyRestrict.relCohomRestrict_mk,
    SingularRelativePairing.relKroneckerH_mk_mk, SingularRelativePairing.relKronecker_mk]

/-- **LHS-peel (abstract, wall-free):** strip the `Subtype.val` ker-coe off a doubly-pulled-back seam
cochain and peel both `pullbackCochainMap` homeos via `kronecker_mapChain` (reversed). Lands the LHS chain
pairing of `⟨seam²-dual f, h⟩` against a seam chain `z` as the ambient pairing of `f` against `z` pushed
forward through both homeos. Stated abstractly (no heavy seam term) so the `show`/`mapChain` rewrites don't
whnf-wall; `rw`-applied at the heavy hmatch goal it substitutes the LHS without touching the RHS. -/
theorem kronecker_coe_pullback2 {Y Z W : TopCat} (φ₂ : C(↑Y, ↑Z)) (φ₁ : C(↑Z, ↑W)) (n : ℕ)
    (f : SingularCochain W n)
    (h : pullbackCochainMap φ₂ n (pullbackCochainMap φ₁ n f) ∈ LinearMap.ker (coboundaryₗ Y n))
    (z : SingularChain Y n) :
    kronecker (↑(⟨pullbackCochainMap φ₂ n (pullbackCochainMap φ₁ n f), h⟩
        : LinearMap.ker (coboundaryₗ Y n))) z
      = kronecker f (mapChain φ₁ n (mapChain φ₂ n z)) := by
  show kronecker (pullbackCochainMap φ₂ n (pullbackCochainMap φ₁ n f)) z = _
  rw [← kronecker_mapChain, ← kronecker_mapChain]

/-- **Cocycle-pairing descends to homology** (the b4 descent): for a cocycle `a` and two cycles `x`, `y`
whose homology classes agree, the chain-level Kronecker pairings agree. The clean way to reduce the
hmatch seam-chain pairing `⟨a'rep, X⟩ = ⟨a'rep, Y⟩` to the seam homology-class equality `[X] = [Y]`
(`kroneckerH_mk_mk` + the class hypothesis); applying it to the goal auto-unifies `x := X`, `y := Y`. -/
theorem kronecker_eq_of_homology_eq {Y : TopCat} {n : ℕ}
    (a : LinearMap.ker (coboundaryₗ Y n)) {x y : SingularChain Y n}
    (hx : x ∈ cycles Y n) (hy : y ∈ cycles Y n)
    (hclass : (Submodule.Quotient.mk (⟨x, hx⟩ : cycles Y n) : Homology Y n)
      = Submodule.Quotient.mk ⟨y, hy⟩) :
    kronecker a.1 x = kronecker a.1 y := by
  rw [← kroneckerH_mk_mk a ⟨x, hx⟩, ← kroneckerH_mk_mk a ⟨y, hy⟩, hclass]

/-- **cap of the subdivision prism is a boundary** (a piece of the hclass witness `W`): for a cocycle
`a` and an absolute cycle `c`, `cap a c + cap a (Sdⁱ c) ∈ boundaries` — the cap of
`add_singularSd_iterate_eq_boundary` pushed through the cap chain map (`cap_cocycle_chainMap`).
Applies to `zc0 = legW = cap g · fundCycleW`, which is an *absolute* cycle (relativeDualityK). -/
theorem cap_add_singularSd_iterate_mem_boundaries {Y : TopCat} {k m : ℕ}
    (a : SingularCochain Y k) (ha : coboundaryₗ Y k a = 0)
    (c : SingularChain Y (k + m + 1)) (hc : chainBoundary Y (k + m) c = 0) (i : ℕ) :
    cap a c + cap a ((⇑(SingularSubdivision.singularSd Y (k + m + 1)))^[i] c)
      ∈ boundaries Y (m + 1) := by
  rw [← map_add, SingularExcision.add_singularSd_iterate_eq_boundary hc i]
  erw [← cap_cocycle_chainMap (m := m + 1) a ha]
  exact ⟨_, rfl⟩

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
  -- ▶ REDUCTION via `_of_chainMatch` (DR-aligned chain-map reframe, 2026-06-21). The RHS uses
  --   `relCohomMvConnecting` — which HAS a committed geometric δφ representative
  --   (`relCohomMvConnecting_eq_mk_coboundary_cochainSplit`), NOT the Kronecker-only `absCohomConn`
  --   that the abandoned `_of_hcup_linked` route required. The residual `hmatch` is the genuine
  --   cross-cover cap-naturality chain pairing, closed via the committed cap-Leibniz over the shared z₀
  --   (DR: `Formalizing "hcross"…md` — snake-lemma naturality under the cap-with-z₀ chain map).
  apply SingularConnSquareCloseChainMap.subHomConnecting_openDuality_of_chainMatch hU hV z₀ hz₀ K g
  intro g_rep zc0 hzc0 zA zB hcyc hpart a'rep hzBmem σR_rep hσR
  -- Step 1 (DR route-a, 2026-06-21): move the RHS seam homeos off the cochain onto the chain side
  --   (`kronecker_mapChain`), landing both legs as `⟨a'rep, seam-chain⟩` ⟹ the cross-realization is a
  --   seam-chain agreement, closeable via cap-Leibniz (`cover_partition_cap_boundary`, ∂z₀=0) + cover-agree
  --   (`SingularChainInclAgree.chainIncl_symm_agree`). The 1st homeo moves cleanly; the 2nd (seamHomeo)
  --   needs explicit-space alignment (next brick). RHS geom: σR=relCohomMvConnecting(g) → ⟨δφ,c⟩ via
  --   `SingularConnSquareCloseFinal.relKroneckerH_relMvDelta_pairing` + `chainIncl_pullbackDualityₗ`.
  simp only [← kronecker_mapChain]
  erw [← kronecker_mapChain]
  -- b4: descend `⟨a'rep, X⟩ = ⟨a'rep, Y⟩` to the seam homology-class equality `[X] = [Y]`.
  apply kronecker_eq_of_homology_eq a'rep
  case hx => exact boundaryExtract_mem_cycles _ (p + 1) ⟨zB, hzBmem⟩
  case hy =>
    exact mapChain_mem_cycles _ (mapChain_mem_cycles _
      (SingularLocalDualityK.pullbackDualityₗ_mem_cycles _ _ _ _
        (SingularOpenDualityCycle.fundCycleW_boundary _ _ _ _) σR_rep))
  case hclass =>
    -- The seam-class equality is the cap-naturality of the connecting map. Reduce to the homologous
    -- (boundary-membership) form: `X - Y ∈ boundaries`, i.e. ∃ W, ∂W = X - Y (= X + Y mod 2), where
    -- X = boundaryExtract zB (val⁻¹V connecting) and Y = transported cap σR z₀ (legSplitVᶜ cap of
    -- σR = relCohomMvConnecting g). The witness W comes from the cover-split + cap-Leibniz over z₀.
    -- ⚠ lead 1 (apply seamHomologyEquiv) hits the whnf heartbeat wall (Homology.map of the nested-seam
    -- homeo forces `sub(restr …)` type unfolding) — DR's nested-seam warning realized. Stay chain-level:
    -- reduce to the boundary-membership and build the witness W abstractly (no seam-homology-iso).
    rw [Submodule.Quotient.eq, Submodule.submoduleOf, Submodule.mem_comap]
    simp only [map_sub, Submodule.coe_subtype]
    rw [boundaries, LinearMap.mem_range]
    sorry

end SKEFTHawking.SingularConnSquareCloseNC
