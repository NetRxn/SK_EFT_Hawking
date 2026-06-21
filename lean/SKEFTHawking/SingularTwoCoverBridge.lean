import Mathlib
import SKEFTHawking.SingularConnSquareClose
import SKEFTHawking.SingularConnSquareCloseFinal
import SKEFTHawking.SingularConnSquareMatchLHS
import SKEFTHawking.SingularAbsCohomConnGeom
import SKEFTHawking.SingularConnSquareRHSDance
import SKEFTHawking.SingularChainInclAgree
import SKEFTHawking.SingularKroneckerFunctoriality

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — the two-cover bridge (cross-realization match), reduced

This file discharges, **kernel-pure and sorry-free**, the entire cohomology-side pairing apparatus of
the Poincaré-duality connecting square's deepest residual — `hcup` of
`SingularConnSquareClose.subHomConnecting_openDuality_of_hcup_linked` — down to a single, explicit
**homology-class identity** in `H(M, (↑K)ᶜ)`:

  `[chainIncl (U∪V) (rcap b z_K)]  =  hSet ▸ relMvDelta (legSplitUᶜ) (legSplitVᶜ) (N+1)
       [chainIncl (U∩V) (rcap a'rep z_J)]`         (the hypothesis `hcross`)

where `z_K = fundCycleW (U∪V) (castChain z₀) K`, `z_J = fundCycleW (U∩V) (castChain z₀) (infCompact …)`,
`hSet : (↑K)ᶜ = legSplitUᶜ ∩ legSplitVᶜ`, and `[b] = absCohomConn p [a'rep]`. This is the genuine
**Mayer–Vietoris-connecting cap-product naturality on the shared fundamental cycle `z₀`** — the
homology-class lift of the chain-level cup-duality `hcup`. Both `fundCycleW` witnesses (over `K` vs over
`infCompact`) are distinct `Classical.choice`s of the same `z₀`, each rel-homologous to `z₀` via
`SingularOpenDualityCycle.fundCycleW_relHomologous`, so the identity is genuinely homological.

`subHomConnecting_openDuality_of_crossRealization` consumes `hcross` and discharges everything else:
the cup→cap→rcap reductions (`kronecker_cup_cap`/`kronecker_cup_rcap`/`kronecker_pullbackCochain`), the
lift to relative-Kronecker pairings (`relKroneckerH_chainIncl_rcap_eq_kronecker`), exposing the
connecting map via `hgRconn`, the connecting adjunction `relKroneckerH_relCohomMvConnecting`, and the
**full collapse of the cohomology-side cosmetic apparatus** (`relCohomRestrict` → `relIncl` along the
identity inclusion → identity, plus the `relCohomSetCongr` `subst`-`refl`) via the two new kernel-pure
helpers `relIncl_refl_apply` and `relKroneckerH_relCohomSetCongr_relIncl_collapse`.

`crossRealization_reduces_to_legVpart` records the further reduction of `hcross` to the
`legSplitVᶜ`-part form `[chainIncl legSplitVᶜ w'] = [chainIncl (U∪V) (rcap b z_K)]` via the cover-fine
subdivision dance (`exists_cover_fine_subdivision` + `relHomology_mk_singularSd_iterate` +
`relMvDelta_cover_partition`), exactly mirroring `SingularConnSquareRHSDance.rhs_dance` but in class
form. Both legs are then `(↑K)ᶜ`-relative cycles, and the residual is the cap-connecting naturality
linking the `U∪V`-leg cap of `z₀` to the `legSplitVᶜ`-part of the `U∩V`-leg cap of `z₀` under
`[b] = absCohomConn [a'rep]`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularCompactlySupportedOpen

namespace SKEFTHawking.SingularTwoCoverBridge

open SKEFTHawking.SingularCSCMayerVietorisConnecting
  SKEFTHawking.SingularRelativeCohomologyMVConnecting
  SKEFTHawking.SingularSubHomologyMVCohomConn
  SKEFTHawking.SingularCapChainIncl SKEFTHawking.SingularSubspaceChainsEquiv
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularOpenDualityCycle
  SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularCompactlySupportedTop
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularRelativeFunctoriality

variable {X : TopCat} [T2Space ↑X]

omit [T2Space ↑X] in
/-- **`relIncl` along the reflexive inclusion is the identity** on a relative homology class: the
underlying chain map is `(id_X)_# = id` (`relCyclesMap_coe` + `relMapChain_mk` + `mapChain_id`). -/
theorem relIncl_refl_apply {S : Set ↑X} {N : ℕ} (h : S ⊆ S) (y : RelativeHomology S N) :
    relIncl h N y = y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show relIncl h N (RelativeHomology.mk S N z) = RelativeHomology.mk S N z
  rw [relIncl_mk]
  refine congrArg (RelativeHomology.mk S N) (Subtype.ext ?_)
  rw [relCyclesMap_coe]
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChain S N)
  rw [show (z : RelativeChain S N) = RelativeChain.mk S N c from hc.symm, relMapChain_mk,
    SKEFTHawking.SingularFunctoriality.mapChain_id]

omit [T2Space ↑X] in
/-- **Cohomology-side collapse of the two-cover bridge's RHS.** Pairing the `relCohomSetCongr`-transport
of `[grep]` (from `S` to `S'`, via `hSet : S = S'`) against `relIncl`-of-`y` (along the reflexive `S'`
inclusion) equals pairing `[grep]` over `S` against the `hSet`-transport of `y`. Both the set-congruence
(`subst hSet` → `LinearEquiv.refl`) and the reflexive `relIncl` (`relIncl_refl_apply`) collapse, leaving
the bare `S`-pairing. This moves the entire cohomology-side cosmetic apparatus onto the homology side,
so the residual is the pure homology-class identity over the single set `S = (↑K)ᶜ`. -/
theorem relKroneckerH_relCohomSetCongr_relIncl_collapse {S S' : Set ↑X} (hSet : S = S') {N : ℕ}
    (x : RelativeCohomology S (N + 1)) (h : S' ⊆ S')
    (y : RelativeHomology S' (N + 1)) :
    relKroneckerH S' (relCohomSetCongr hSet (N + 1) x) (relIncl h (N + 1) y)
      = relKroneckerH S x (hSet ▸ y) := by
  subst hSet
  simp only [relCohomSetCongr, LinearEquiv.refl_apply]
  rw [relIncl_refl_apply]

/-- **The per-`K` connecting square, reduced to the two-cover cross-realization bridge `hcross`.**

`hcross` is the genuine residual: the MV-connecting cap-product naturality on the shared fundamental
cycle `z₀`, as a homology-class identity in `H(M, (↑K)ᶜ)`. Given it (for every cocycle representative
`b` of `absCohomConn [a'rep]`, every `grep`/`gRconn` reps, with the `hb`/`hgRconn` links), the per-`K`
Poincaré-duality connecting square `subHomConnecting (legW K g) = openDuality (legδ K g)` follows
kernel-pure: this proof discharges the entire cup→cap→rcap reduction, the relative-Kronecker lift, the
connecting adjunction, and the full cohomology-side collapse. -/
theorem subHomConnecting_openDuality_of_crossRealization {N p : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K)
    (hcross : ∀ (a'rep : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) (p + 1)))
        (b : LinearMap.ker (coboundaryₗ (sub (U ∪ V)) (p + 2)))
        (_hb : Submodule.Quotient.mk b
          = absCohomConn U V hU hV p (Submodule.Quotient.mk a'rep))
        (hSet : ((K.1 : Set ↑X))ᶜ = ((legSplitU U V hU hV K).1 : Set ↑X)ᶜ
            ∩ ((legSplitV U V hU hV K).1 : Set ↑X)ᶜ),
      RelativeHomology.mk ((↑K.1 : Set ↑X)ᶜ) (N + 1)
          ⟨RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (N + 1)
              (chainIncl (U ∪ V) (N + 1) (rcap b.1
                ((subspaceChainsEquiv (U ∪ V) (N + 1 + (p + 1) + 1)).symm
                  ⟨fundCycleW (hU.union hV)
                      (SingularOpenDualityMVConnSquare.castChain
                        (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
                      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero
                        (by omega) (by omega) z₀ hz₀) K,
                    fundCycleW_mem_W (hU.union hV) _ _ _⟩))),
            SingularCapSubKDuality.chainIncl_rcap_mem_relCycles _
              (fundCycleW_mem_W (hU.union hV) _ _ _) (fundCycleW_boundary (hU.union hV) _ _ _) b⟩
        = hSet ▸ relMvDelta ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ)
              ((↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
              (legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
              (legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl (N + 1)
            (RelativeHomology.mk
                ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ ∪ (↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
                (N + 1 + 1)
              ⟨RelativeChain.mk
                  ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ ∪ (↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
                  (N + 1 + 1)
                  (chainIncl (U ∩ V) (N + 1 + 1) (rcap a'rep.1
                    ((subspaceChainsEquiv (U ∩ V) (N + 1 + 1 + p + 1)).symm
                      ⟨fundCycleW (hU.inter hV)
                          (SingularOpenDualityMVConnSquare.castChain
                            (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
                          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero
                            (by omega) (by omega) z₀ hz₀)
                          (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)),
                        fundCycleW_mem_W (hU.inter hV) _ _ _⟩))),
                by
                  have hbd := fundCycleW_boundary (hU.inter hV)
                    (SingularOpenDualityMVConnSquare.castChain
                      (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
                    (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero
                      (by omega) (by omega) z₀ hz₀)
                    (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
                  rw [infCompact_coe U V (legSplitU U V hU hV K) (legSplitV U V hU hV K),
                    Set.compl_inter] at hbd
                  exact SingularCapSubKDuality.chainIncl_rcap_mem_relCycles _
                    (fundCycleW_mem_W (hU.inter hV) _ _ _) hbd a'rep⟩)) :
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
  apply SingularConnSquareClose.subHomConnecting_openDuality_of_hcup_linked hU hV z₀ hz₀ K g
  intro a'rep b grep gRconn hg hb hgRconn
  rw [SingularCapChainIncl.kronecker_cup_cap, SingularCapChainIncl.kronecker_cup_rcap,
    SingularCapSubKDuality.kronecker_pullbackCochain,
    SingularConnSquareClose.kronecker_chainIncl_rcap_eq_cup, SingularCapChainIncl.kronecker_cup_cap]
  rw [SingularConnSquareMatchLHS.kronecker_cap_eq_kronecker_rcap,
    SingularConnSquareMatchLHS.kronecker_cap_eq_kronecker_rcap,
    SingularCapSubKDuality.kronecker_pullbackCochain,
    SingularCapSubKDuality.kronecker_pullbackCochain]
  -- Lift the LHS chain-pairing to the relative Kronecker pairing over (↑K)ᶜ.
  rw [← SingularConnSquareClose.relKroneckerH_chainIncl_rcap_eq_kronecker (k := N) (m := p + 1) _
      (fundCycleW_mem_W (hU.union hV) _ _ _) (fundCycleW_boundary (hU.union hV) _ _ _) grep b
      (SingularCapSubKDuality.chainIncl_rcap_mem_relCycles _ (fundCycleW_mem_W (hU.union hV) _ _ _)
        (fundCycleW_boundary (hU.union hV) _ _ _) b)]
  -- Lift the RHS chain-pairing to the relative Kronecker pairing over (legSplitUᶜ ∪ legSplitVᶜ).
  have hbdRHS := fundCycleW_boundary (hU.inter hV)
    (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
    (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
    (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
  rw [infCompact_coe U V (legSplitU U V hU hV K) (legSplitV U V hU hV K), Set.compl_inter] at hbdRHS
  rw [← SingularConnSquareClose.relKroneckerH_chainIncl_rcap_eq_kronecker (k := N + 1) (m := p) _
      (fundCycleW_mem_W (hU.inter hV) _ _ _) hbdRHS gRconn a'rep
      (SingularCapSubKDuality.chainIncl_rcap_mem_relCycles _ (fundCycleW_mem_W (hU.inter hV) _ _ _)
        hbdRHS a'rep)]
  -- Expose the connecting map on the RHS cohomology via hgRconn, then move it onto the homology side.
  simp only [RelativeCohomology.mk]
  rw [hgRconn]
  rw [SingularRelativeCohomologyMVConnecting.relKroneckerH_relCohomMvConnecting]
  -- Collapse the entire cohomology-side cosmetic apparatus (relCohomRestrict → relIncl → id, plus the
  -- relCohomSetCongr subst-refl): both pairings are now over the SINGLE set (↑K)ᶜ against `mk grep`.
  rw [SingularDualityAdjoint.relKroneckerH_relCohomRestrict']
  rw [relKroneckerH_relCohomSetCongr_relIncl_collapse]
  -- Strip the common `⟨mk grep, ·⟩` pairing: the residual is the pure homology-class identity `hcross`.
  congr 1
  exact hcross a'rep b hb (by rw [legSplit_cover, Set.compl_union])

end SKEFTHawking.SingularTwoCoverBridge
