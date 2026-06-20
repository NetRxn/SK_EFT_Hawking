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
import SKEFTHawking.SingularConnSquareCloseM2
import SKEFTHawking.SingularConnSquareCloseFinal
import SKEFTHawking.SingularRelCohomMvConnectingGeom
import SKEFTHawking.SingularOpenDualityConnLegdeltaCollapse
import SKEFTHawking.SingularCapChainIncl
import SKEFTHawking.SingularSeamDualPairing

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — the connecting-square via the CHAIN-MAP route
Kernel-pure target (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularConnSquareMatch
  SKEFTHawking.SingularConnSquareLHSLeg SKEFTHawking.SingularRelMvDeltaPartition
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularConnSquareLHS

namespace SKEFTHawking.SingularConnSquareCloseChainMap

open SKEFTHawking.SingularMvDeltaPartition SKEFTHawking.SingularConnSquareLHSExplicit
  SKEFTHawking.SingularCoverPartitionExist SKEFTHawking.SingularConnSquareLHSPairing
  SKEFTHawking.SingularConnSquareMatchLHS SKEFTHawking.SingularConnSquareCloseM2
  SKEFTHawking.SingularLegWCapForm SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularRelCohomMvConnectingGeom SKEFTHawking.SingularConnSquareCloseFinal

variable {X : TopCat} [T2Space ↑X]

open SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularSeamDualPairing
open SKEFTHawking.SingularKroneckerFunctoriality (pullbackCochainMap pullbackCochainMap_mem_ker
  kroneckerH_Homology_map)

omit [T2Space ↑X] in
/-- The inverse of `subSeamEquiv` is `Homology.map` of the inverse homeomorphism `subSeamHomeo.symm`
(the seam homeomorphism reversed: `T ⊆ S`, `q ↦ ⟨⟨q,_⟩,_⟩`). Since the two `Homology.map`s compose to
`Homology.map id = id` (the underlying homeomorphisms compose to `id`), this is the inverse. -/
theorem subSeamEquiv_symm_apply {S : Set ↑X} {R : Set ↑(sub S)} {T : Set ↑X} (hTS : T ⊆ S)
    (hmem : ∀ q : ↥(sub S), q ∈ R ↔ (q : ↑X) ∈ T) (n : ℕ) (w : Homology (sub T) n) :
    (subSeamEquiv hTS hmem n).symm w
      = SingularFunctoriality.Homology.map
          ⟨(subSeamHomeo hTS hmem).symm, (subSeamHomeo hTS hmem).symm.continuous⟩ n w := by
  apply (subSeamEquiv hTS hmem n).injective
  rw [LinearEquiv.apply_symm_apply, subSeamEquiv_apply, ← LinearMap.comp_apply,
    ← SingularFunctoriality.Homology.map_comp]
  have hid : (⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩ : C(↑(sub R), ↑(sub T))).comp
      ⟨(subSeamHomeo hTS hmem).symm, (subSeamHomeo hTS hmem).symm.continuous⟩
      = ContinuousMap.id ↑(sub T) := ContinuousMap.ext fun _ => rfl
  rw [hid]
  show w = SingularFunctoriality.Homology.map (ContinuousMap.id ↑(sub T)) n w
  rw [SingularFunctoriality.Homology.map_id, LinearMap.id_apply]

omit [T2Space ↑X] in
/-- **Seam-symm dual transport** (the `.symm` analogue of `kroneckerH_subSeamEquiv`): pairing a
cocycle `a` on the **domain** `sub R` against the `subSeamEquiv.symm` image of a cycle class on `sub T`
equals pairing the cochain pullback (along the **inverse** homeomorphism `subSeamHomeo.symm`) against
that cycle. Routes the symm through `subSeamEquiv_symm_apply` + `kroneckerH_Homology_map`. -/
theorem kroneckerH_subSeamEquiv_symm {S : Set ↑X} {R : Set ↑(sub S)} {T : Set ↑X} (hTS : T ⊆ S)
    (hmem : ∀ q : ↥(sub S), q ∈ R ↔ (q : ↑X) ∈ T) (n : ℕ)
    (a : LinearMap.ker (coboundaryₗ (sub R) n)) (z : cycles (sub T) n) :
    kroneckerH (X := sub R) n (Submodule.Quotient.mk a)
        ((subSeamEquiv hTS hmem n).symm (Homology.mk (sub T) n z))
      = kroneckerH (X := sub T) n
          (Submodule.Quotient.mk
            ⟨pullbackCochainMap ⟨(subSeamHomeo hTS hmem).symm,
                (subSeamHomeo hTS hmem).symm.continuous⟩ n a.1,
              pullbackCochainMap_mem_ker _ n a⟩)
          (Homology.mk (sub T) n z) := by
  rw [subSeamEquiv_symm_apply, kroneckerH_Homology_map]

open SKEFTHawking.SingularMayerVietorisLES in
omit [T2Space ↑X] in
/-- The inverse of `seamHomologyEquiv` is `Homology.map` of the inverse seam homeomorphism. -/
theorem seamHomologyEquiv_symm_apply (A B : Set ↑X) (n : ℕ) (w : Homology (sub (A ∩ B)) n) :
    (seamHomologyEquiv A B n).symm w
      = SingularFunctoriality.Homology.map
          ⟨(seamHomeo A B).symm, (seamHomeo A B).symm.continuous⟩ n w := by
  apply (seamHomologyEquiv A B n).injective
  rw [LinearEquiv.apply_symm_apply, seamHomologyEquiv, LinearEquiv.ofBijective_apply,
    ← LinearMap.comp_apply, ← SingularFunctoriality.Homology.map_comp]
  have hid : (⟨seamHomeo A B, (seamHomeo A B).continuous⟩ :
        C(↑(sub (restr A B)), ↑(sub (A ∩ B)))).comp
      ⟨(seamHomeo A B).symm, (seamHomeo A B).symm.continuous⟩
      = ContinuousMap.id ↑(sub (A ∩ B)) := ContinuousMap.ext fun _ => rfl
  rw [hid]
  show w = SingularFunctoriality.Homology.map (ContinuousMap.id ↑(sub (A ∩ B))) n w
  rw [SingularFunctoriality.Homology.map_id, LinearMap.id_apply]

open SKEFTHawking.SingularMayerVietorisLES in
omit [T2Space ↑X] in
/-- **Seam-symm dual transport through `seamHomologyEquiv`** (the `.symm` analogue of
`kroneckerH_seamHomologyEquiv`): pairing a cocycle `a` on `sub (restr A B)` against the
`seamHomologyEquiv.symm` image of a cycle class on `sub (A ∩ B)` equals pairing the cochain pullback
(along `seamHomeo.symm`) against that cycle. -/
theorem kroneckerH_seamHomologyEquiv_symm (A B : Set ↑X) (n : ℕ)
    (a : LinearMap.ker (coboundaryₗ (sub (restr A B)) n)) (z : cycles (sub (A ∩ B)) n) :
    kroneckerH (X := sub (restr A B)) n (Submodule.Quotient.mk a)
        ((seamHomologyEquiv A B n).symm (Homology.mk (sub (A ∩ B)) n z))
      = kroneckerH (X := sub (A ∩ B)) n
          (Submodule.Quotient.mk
            ⟨pullbackCochainMap ⟨(seamHomeo A B).symm, (seamHomeo A B).symm.continuous⟩ n a.1,
              pullbackCochainMap_mem_ker _ n a⟩)
          (Homology.mk (sub (A ∩ B)) n z) := by
  rw [seamHomologyEquiv_symm_apply, kroneckerH_Homology_map]

open SKEFTHawking.SingularMayerVietorisLES in
omit [T2Space ↑X] in
/-- **Combined double-seam-symm transport** (handles arbitrary `Y`, rep-ified internally). Pairing the
seam cocycle `a` against `seamHom.symm (seamI.symm Y)` for any `(U∩V)`-class `Y = [zY]` equals the
chain-level pairing of the double cochain-pullback of `a` (through `seamHomeo.symm` then
`subSeamHomeo.symm`) against `zY`. This is the RHS-side reduction of the connecting square — it never
spells the giant `legW J σR` term; the caller supplies any cycle rep `zY` of `Y`. -/
theorem kroneckerH_double_seam_symm (U V : Set ↑X) (n : ℕ)
    (a : LinearMap.ker (coboundaryₗ
        (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n))
    (zY : cycles (sub (U ∩ V)) n) :
    kroneckerH (X := sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n
        (Submodule.Quotient.mk a)
        ((seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n).symm
          ((seamI U V n).symm (Homology.mk (sub (U ∩ V)) n zY)))
      = kronecker
          (pullbackCochainMap ⟨(SingularSubHomologyMV.subSeamHomeo
                (Set.inter_subset_left.trans Set.subset_union_left)
                (fun _ : ↑(sub (U ∪ V)) => Iff.rfl)).symm,
              (SingularSubHomologyMV.subSeamHomeo
                (Set.inter_subset_left.trans Set.subset_union_left)
                (fun _ : ↑(sub (U ∪ V)) => Iff.rfl)).symm.continuous⟩ n
            (pullbackCochainMap ⟨(seamHomeo
                (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).symm,
                (seamHomeo (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))
                  (Subtype.val ⁻¹' V)).symm.continuous⟩ n a.1))
          zY.1 := by
  -- Rep-ify the inner `seamI.symm (mk zY)` (stated in `Homology.mk` form to avoid the
  -- `Homology.mk`/`Submodule.Quotient.mk` syntactic mismatch).
  obtain ⟨zI, hzI'⟩ := Submodule.Quotient.mk_surjective _
    ((seamI U V n).symm (Homology.mk (sub (U ∩ V)) n zY))
  have hzI : Homology.mk (sub ((Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) ∩ Subtype.val ⁻¹' V)) n zI
      = (seamI U V n).symm (Homology.mk (sub (U ∩ V)) n zY) := hzI'
  rw [← hzI, kroneckerH_seamHomologyEquiv_symm, hzI]
  -- The inner `seamI` is `subSeamEquiv`; close in term mode so it unifies definitionally.
  exact (kroneckerH_subSeamEquiv_symm _ _ n _ zY).trans (kroneckerH_mk_mk _ _)

/-- **The per-`K` Poincaré-duality connecting square via the CHAIN-MAP route**, reduced to the single
genuine **cross-cover cap-naturality chain pairing** `hmatch` (the homology connecting of `cap g`
= cap of the cohomology connecting, on the shared fundamental cycle `z₀`). The entire seam-machinery is
discharged here: the bottom-row MV connecting (`subHomConnecting`) is computed by its cover-partition
chain action (`mvConnecting_cover_partition`), the two legs are descended to the Kronecker pairing
(`homology_eq_zero_of_kroneckerH`), and both RHS seam isomorphisms (`seamHomologyEquiv`, `seamI`) are
transported onto the cochain side by the `kroneckerH_double_seam_symm` helper, leaving exactly `hmatch`.

`hmatch` is the *non-circular* residual: a chain-level pairing of the seam cocycle `a'rep` against the
`V`-part boundary `∂zB` of the capped fundamental cycle `cap g z_K`, equated to the double-seam-pullback
of `a'rep` paired against the cap of the explicit cohomology connecting `δφ`-realization `σR_rep` with
`z_J`. Both `z_K`, `z_J` are `castChain z₀`. The hypotheses `hzc0`/`hpart`/`hσR` pin `zB`/`σR_rep` to the
genuine data, so `hmatch` is the precise geometric content (the chain-level cover-partition + cap-Leibniz
of the *specific* capped cycle — the documented subdivision residual), not a vacuous assumption. -/
theorem subHomConnecting_openDuality_of_chainMatch {N p : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K)
    (hmatch : ∀ (g_rep : LinearMap.ker (relCoboundaryₗ ((↑K.1 : Set ↑X)ᶜ) (N + 1)))
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
        (a'rep : LinearMap.ker (coboundaryₗ
            (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) (p + 1)))
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
      kronecker a'rep.1
          (SingularPairLES.boundaryExtract
            (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
            ⟨zB, hzBmem⟩)
        = kronecker
            (pullbackCochainMap ⟨(subSeamHomeo
                  (Set.inter_subset_left.trans Set.subset_union_left)
                  (fun _ : ↑(sub (U ∪ V)) => Iff.rfl)).symm,
                (subSeamHomeo (Set.inter_subset_left.trans Set.subset_union_left)
                  (fun _ : ↑(sub (U ∪ V)) => Iff.rfl)).symm.continuous⟩ (p + 1)
              (pullbackCochainMap ⟨(SingularMayerVietorisLES.seamHomeo
                  (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).symm,
                  (SingularMayerVietorisLES.seamHomeo
                    (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)).symm.continuous⟩ (p + 1)
                a'rep.1))
            (SingularLocalDualityK.pullbackDualityₗ
              ((↑(SingularCSCMayerVietorisConnecting.infCompact U V
                  (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                  (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)).1 : Set ↑X)ᶜ)
              (U ∩ V)
              (SingularOpenDualityCycle.fundCycleW (hU.inter hV)
                (SingularOpenDualityMVConnSquare.castChain
                  (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
                (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
                (SingularCSCMayerVietorisConnecting.infCompact U V
                  (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                  (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
              (SingularOpenDualityCycle.fundCycleW_mem_W (hU.inter hV) _ _ _) σR_rep)) :
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
  rw [SKEFTHawking.SingularOpenDualityConnLegdeltaCollapse.openDuality_legδ_eq_legW]
  apply subHomConnecting_legW_eq_legW_of_mvConnecting
  obtain ⟨g_rep, rfl⟩ := Submodule.Quotient.mk_surjective _ g
  obtain ⟨zc0, hzc0⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := p + 1) (hU.union hV)
      (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
      K (Submodule.Quotient.mk g_rep))
  obtain ⟨zA, zB, hcyc, hpart⟩ := exists_mvUnion_partition
    (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val) (p + 1) zc0
    (mem_subspaceChains_preimage_union U V (p + 1 + 1) zc0.1)
  refine mvConnecting_eq_seamRHS_of_partition U V hU hV (p + 1) _ _ zA zB hcyc
    (by rw [← hzc0]; exact hpart) _ rfl ?_
  rw [mvConnecting_cover_partition]
  rw [← sub_eq_zero]
  apply SKEFTHawking.PoincareDualityConstruct.homology_eq_zero_of_kroneckerH (p + 1)
  intro a'
  rw [map_sub, sub_eq_zero]
  obtain ⟨a'rep, rfl⟩ := Submodule.Quotient.mk_surjective _ a'
  -- Reduce the LHS to a chain-level Kronecker pairing.
  rw [show Homology.mk (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)))
        (p + 1) ⟨SingularPairLES.boundaryExtract
            (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
            ⟨zB, zB_mem_relCycleLift _ _ (p + 1) zA zB hcyc⟩,
          SingularPairLES.boundaryExtract_mem_cycles _ (p + 1) _⟩
        = Submodule.Quotient.mk ⟨SingularPairLES.boundaryExtract
            (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
            ⟨zB, zB_mem_relCycleLift _ _ (p + 1) zA zB hcyc⟩,
          SingularPairLES.boundaryExtract_mem_cycles _ (p + 1) _⟩ from rfl,
    kroneckerH_mk_mk]
  -- Rep-ify the RHS cohomology class `σR` and rewrite `legW J σR` to its explicit cap-class form.
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
    SingularLegWCapForm.legW_mk]
  -- Transport the two RHS seam-symms onto the cochain side (the combined helper).
  rw [kroneckerH_double_seam_symm]
  -- The residual is the genuine cross-cover cap-naturality chain pairing — discharged by `hmatch`.
  exact hmatch g_rep zc0 hzc0 zA zB hcyc hpart a'rep
    (zB_mem_relCycleLift _ _ (p + 1) zA zB hcyc) σR_rep hσR

end SKEFTHawking.SingularConnSquareCloseChainMap
