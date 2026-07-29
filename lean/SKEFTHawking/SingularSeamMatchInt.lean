/-
# Phase 5q.H (E1 CSC-PD tower) — the per-(A,B,K,g) connecting-square seam-match (integral, brick 6e)

The per-`(A,B,K,g)` connecting-square naturality `subHomConnectingInt (legW K g) = openDuality (legδ K g)`
at the two windows — the two conjuncts of `SingularPDWindowInt.HcoreG`, stated for general open `A,B ⊆ X`
(no manifold/chart structure). Proven in this LIGHT-import module (crucially NOT `SingularPDWindowInt`)
so the doubly-nested `restr`/`mvConnectingInt` types elaborate without the whnf wall that fires under
`SingularPDWindowInt`'s heavy transitive closure. `SingularHcoreGDischargeInt` consumes these to
discharge `HcoreG` unconditionally.

**The upper conjunct is COMPLETE (2026-07-12)** — the former `(★)` A∩B-support wall is closed by the
SHARED F₂-split design (see `SingularSharedSplitInt`): ONE split `∂(Sd^jF z_J) = aFamb + bFamb`
(legs over `U'∩(A∩B)` / `V'∩(A∩B)`) feeds BOTH `fact_i_ambient_coreInt` (Brick M, the `hFsplit` slot)
AND the zc-side cap computation (Z1 subdivision correction + Z2 cap-Leibniz + the indUf/kk kills), so
every residual is `C(A∩B)`-supported by cap-support and the descent bridge closes the seam-match.
The final witness is `E = E_M + (indUf U' gW)⌢Sd^jF z_J + kk⌢Sd^jF z_J + zc⌢D_jF z_J`.

Kernel-purity target `{propext, Classical.choice, Quot.sound}`; no axiom/native_decide/maxHeartbeats.
(WIP: the BOT conjunct's `hmatch` — the degree-0 mirror — remains `sorry`; NOT imported into the
library root until it closes.)
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityConnLegdeltaCollapseInt
import SKEFTHawking.SingularConnSquareCloseM2Int
import SKEFTHawking.SingularCoverPartitionMkInt
import SKEFTHawking.SingularOpenDualityMVConnSquareInt
import SKEFTHawking.SingularOpenDualityBotLegdeltaCollapseInt
import SKEFTHawking.SingularLegWCapFormInt
import SKEFTHawking.SingularCapCoverPartitionInt
import SKEFTHawking.SingularCapMapChainInt
import SKEFTHawking.SingularCapIndUfBridgeInt
import SKEFTHawking.SingularRelativeCohomologyMVConnectingInt
import SKEFTHawking.SingularConnSquareFactICoreInt
import SKEFTHawking.SingularConnSquareFactIStage1Int
import SKEFTHawking.SingularMvDeltaPartitionInt
import SKEFTHawking.SingularSeamTransportInt
import SKEFTHawking.SingularHomologyDescentBridgeInt
import SKEFTHawking.SingularFundCycleReconTransportInt
import SKEFTHawking.SingularSharedSplitInt
import SKEFTHawking.SingularIndUfCapAgreeInt
import SKEFTHawking.SingularCapSupportInt
import SKEFTHawking.SingularConnSquareFactIBotInt
import SKEFTHawking.SingularLocalDualityKBotInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularSubHomologyMVInt (subHomConnectingInt seamI)
open SKEFTHawking.SingularMayerVietorisLESInt (mvConnectingInt seamHomologyEquivInt)
open SKEFTHawking.SingularSubHomologyMV (cover_preimage)
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularOpenDualityBotInt (openDuality₀Int)
open SKEFTHawking.SingularOpenDualityMVConnSquareInt (castChainInt chainBoundary_castChainInt_eq_zero)
open SKEFTHawking.SingularCSCMayerVietorisConnectingInt
  (legδInt infCompactInt legSplitUInt legSplitVInt infCompactInt_coe legSplit_coverInt)
open SKEFTHawking.SingularConnSquareCloseM2Int
  (subHomConnecting_legW_eq_legW_of_mvConnectingInt mvConnecting_eq_seamRHS_of_partitionInt)
open SKEFTHawking.SingularMvDeltaPartitionInt (mvConnecting_cover_partition zB_mem_relCycleLift)
open SKEFTHawking.SingularConnSquareCloseNCInt (fact_i_stage1Int)
open SKEFTHawking.SingularCSCMayerVietorisMiddleInt (relCohomSetCongrInt)
open SKEFTHawking.SingularRelativeCohomologyMVConnectingInt (relCohomMvConnectingInt)
open SKEFTHawking.SingularRelativeCohomologyRestrictInt (relCohomRestrictInt)
open SKEFTHawking.SingularLegWCapFormInt (legW_mkInt)
open SKEFTHawking.SingularLocalDualityKInt (pullbackDualityIntₗ chainIncl_pullbackDualityIntₗ)
open SKEFTHawking.SingularHomologyDescentBridgeInt (homology_eq_of_ambient_boundaryInt)
open SKEFTHawking.SingularSeamTransportInt (chainIncl_seam_boundaryExtractInt)
open SKEFTHawking.SingularOpenDualityCycleInt (fundCycleW)
open SKEFTHawking.SingularRelativeCohomologyMVConnectingInt (indUf exists_mvUnion_of_connecting_mk_eq)
open SKEFTHawking.SingularRelativeCohomologyRestrictInt (relCohomRestrictInt_mk relCocycleRestrictInt)
open SKEFTHawking.SingularQCohomologyInt (mvUnionCochainsInt)

namespace SKEFTHawking.SingularSeamMatchInt

variable {X : TopCat} [T2Space ↑X]

omit [T2Space ↑X] in
/-- `relCohomSetCongrInt` pushed through `mk` (the missing `_mk` rule). -/
theorem relCohomSetCongrInt_mk {S T : Set ↑X} (h : S = T) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryIntₗ S n)) :
    relCohomSetCongrInt h n (RelativeCohomologyInt.mk S n z)
      = RelativeCohomologyInt.mk T n (h ▸ z) := by
  subst h; rfl

omit [T2Space ↑X] in
/-- `(relCohomSetCongrInt h).symm` pushed through `mk`. -/
theorem relCohomSetCongrInt_symm_mk {S T : Set ↑X} (h : S = T) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryIntₗ T n)) :
    (relCohomSetCongrInt h n).symm (RelativeCohomologyInt.mk T n z)
      = RelativeCohomologyInt.mk S n (h ▸ z) := by
  subst h; rfl

omit [T2Space ↑X] in
/-- Transporting a relative cocycle along a set-equality preserves its underlying cochain. -/
theorem ker_transport_coe {S T : Set ↑X} (h : S = T) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryIntₗ T n)) :
    ((h ▸ z : LinearMap.ker (relCoboundaryIntₗ S n)).1.1 : SingularCochainInt X n)
      = (z.1.1 : SingularCochainInt X n) := by
  subst h; rfl

/-- **Upper-window connecting-square seam-match** (integral, `k=1+1`, `m=0+1`) — the first conjunct
of `HcoreG`, COMPLETE. Reduction: brick 4 (RHS collapse) + brick 6a + the fact-(i) stage-1 partition;
then the `(★)` E-construction closes via the SHARED F₂-split (`SingularSharedSplitInt`) feeding both
Brick M (`fact_i_ambient_coreInt`) and the zc-side (Z1 subdivision correction + Z2 cap-Leibniz + the
indUf/kk kills), finished by the homology descent bridge. -/
theorem seamMatch_upperInt (A B : Set ↑X) (hA : IsOpen A) (hB : IsOpen B)
    (z : SingularChainInt X (1 + 0 + 3)) (hz : chainBoundary X (1 + 0 + 2) z = 0)
    (K : CompactsIn (A ∪ B)) (g : cohomGWInt (A ∪ B) (1 + 1) K) :
    subHomConnectingInt A B hA hB (0 + 1)
        (legW (k := 1 + 1) (m := 0 + 1) (hA.union hB)
          (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) z)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz) K g)
      = openDuality (k := 1 + 2) (m := 0) (hA.inter hB)
          (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 2 + 0 + 1 by omega) z)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
          (legδInt A B hA hB 1 K g) := by
  rw [SKEFTHawking.SingularOpenDualityConnLegdeltaCollapseInt.openDuality_legδ_eq_legWInt hA hB _ _ K g]
  obtain ⟨gW, rfl⟩ := RelativeCohomologyInt.mk_surjective ((↑K.1 : Set ↑X)ᶜ) (1 + 1) g
  obtain ⟨μ, f₁, f₂, f₃, hf₁, hf₂, hf₃, hIsplit, zA, zB, hzA, hzB, hcyc, hcls⟩ :=
    fact_i_stage1Int (U := A) (V := B) (LU := (↑(legSplitUInt A B hA hB K).1 : Set ↑X))
      (LV := (↑(legSplitVInt A B hA hB K).1 : Set ↑X)) (k := 1 + 1) (m := 0 + 1) hA hB
      (legSplitUInt A B hA hB K).1.isCompact'.isClosed.isOpen_compl
      (legSplitVInt A B hA hB K).1.isCompact'.isClosed.isOpen_compl
      (legSplitUInt A B hA hB K).2 (legSplitVInt A B hA hB K).2
      (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) z)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz) K gW
  apply subHomConnecting_legW_eq_legW_of_mvConnectingInt A B hA hB _ _ K (RelativeCohomologyInt.mk _ _ gW) _
  refine mvConnecting_eq_seamRHS_of_partitionInt A B hA hB (0 + 1) _ _ zA zB hcyc hcls _
    (mvConnecting_cover_partition _ _ (0 + 1) (cover_preimage A B hA hB) zA zB hcyc) ?_
  rw [LinearEquiv.eq_symm_apply, LinearEquiv.eq_symm_apply,
    SKEFTHawking.SingularMayerVietorisLESInt.seamHomologyEquivInt_apply,
    SKEFTHawking.SingularFunctorialityInt.Homology.mapInt_mk]
  rw [SKEFTHawking.SingularSubHomologyMVInt.seamI]
  erw [SKEFTHawking.SingularSubHomologyMVInt.subSeamEquivInt_apply,
    SKEFTHawking.SingularFunctorialityInt.Homology.mapInt_mk]
  obtain ⟨zc, hzc⟩ := RelativeCohomologyInt.mk_surjective
    ((↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ) (1 + 2)
    (relCohomSetCongrInt (by rw [infCompactInt_coe, Set.compl_inter]) (1 + 2)
      (relCohomMvConnectingInt _ _ _ _ 1
        (relCohomRestrictInt (Set.inter_subset_inter subset_rfl subset_rfl) (1 + 1)
          (relCohomSetCongrInt (by rw [legSplit_coverInt A B hA hB K, Set.compl_union]) (1 + 1)
            (RelativeCohomologyInt.mk _ (1 + 1) gW)))))
  rw [← hzc, legW_mkInt]
  set zJ := fundCycleW (hA.inter hB)
      (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 2 + 0 + 1 by omega) z)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
      (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)) with hzJ_def
  obtain ⟨E, hEmem, hEbd⟩ : ∃ E : SingularChainInt X (0 + 1 + 1),
      E ∈ subspaceChainsInt (A ∩ B) (0 + 1 + 1) ∧
      chainBoundary X (0 + 1) E
        = chainBoundary X (0 + 1) (capInt (m := 0 + 1 + 1) gW.1.1 (f₂ + f₃))
          - capInt (m := 0 + 1) zc.1.1 zJ := by
    -- gW is an absolute cocycle vanishing on Kᶜ-simplices
    have hgc : coboundaryₗ X (1 + 1) gW.1.1 = 0 := by
      have hh := congrArg Subtype.val gW.2
      simp only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] at hh
      exact hh
    have hgvan : ∀ τ, gW.1.1 (SKEFTHawking.SingularRelativeHomologyMod2.simplexIncl ((↑K.1 : Set ↑X)ᶜ) (1 + 1) τ) = 0 :=
      fun τ => relCochainInt_vanish ((↑K.1 : Set ↑X)ᶜ) gW.1 τ
    -- STEP 1: ∂(capInt gW (f₂+f₃)) = − capInt gW (∂f₁)   [cocycle-chainmap + gW kills Sdᵘ(∂ fundCycleW K)]
    have hcyc0 : capInt (m := 0 + 1) gW.1.1 (chainBoundary X (1 + 1 + (0 + 1)) (f₁ + f₂ + f₃)) = 0 := by
      rw [← hIsplit, SKEFTHawking.SingularSubdivisionInt.singularSdInt_iterate_chainBoundary]
      exact capInt_subspaceChainInt_eq_zero ((↑K.1 : Set ↑X)ᶜ) gW.1.1 hgvan
        (SKEFTHawking.SingularExcisionIsoInt.singularSdInt_iterate_mem_subspaceChainsInt
          (SKEFTHawking.SingularOpenDualityCycleInt.fundCycleW_boundary (hA.union hB) _ _ K) μ)
    have h1 : chainBoundary X (0 + 1) (capInt (m := 0 + 1 + 1) gW.1.1 (f₂ + f₃))
        = - capInt (m := 0 + 1) gW.1.1 (chainBoundary X (1 + 1 + (0 + 1)) f₁) := by
      rw [capInt_cocycle_chainMap (m := 0 + 1) gW.1.1 hgc (f₂ + f₃),
        show ((-1 : ℤ) ^ (1 + 1)) = 1 by norm_num, one_smul]
      have hbdsplit : chainBoundary X (1 + 1 + (0 + 1)) (f₂ + f₃)
          = chainBoundary X (1 + 1 + (0 + 1)) (f₁ + f₂ + f₃)
            - chainBoundary X (1 + 1 + (0 + 1)) f₁ := by rw [← map_sub]; congr 1; abel
      rw [hbdsplit, ← capIntₗ_apply, map_sub, capIntₗ_apply, capIntₗ_apply, hcyc0, zero_sub]
    -- STEP 2a: decompose the connecting cocycle  zc.1.1 = δ(indUf U' gW) + δ(kk)  (kk ∈ mvUnion(U',V'))
    rw [relCohomSetCongrInt_mk, relCohomRestrictInt_mk] at hzc
    have hU' : IsOpen ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) :=
      (legSplitUInt A B hA hB K).1.isCompact'.isClosed.isOpen_compl
    have hV' : IsOpen ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ) :=
      (legSplitVInt A B hA hB K).1.isCompact'.isClosed.isOpen_compl
    have hδ0 := (LinearEquiv.symm_apply_eq _).mpr hzc
    rw [relCohomSetCongrInt_symm_mk] at hδ0
    obtain ⟨kk, hkk⟩ := exists_mvUnion_of_connecting_mk_eq _ _ hU' hV' 1 _ _ hδ0.symm
    simp only [SKEFTHawking.SingularRelativeCohomologyRestrictInt.relCocycleRestrictInt_coe,
      SKEFTHawking.SingularRelativeCohomologyRestrictInt.relCochainRestrictInt_coe] at hkk
    have hgWset : ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ)
        = (↑K.1 : Set ↑X)ᶜ := by rw [← Set.compl_union, ← legSplit_coverInt]
    have hJset : ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∪ (↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ)
        = (↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ := by
      rw [infCompactInt_coe, Set.compl_inter]
    rw [ker_transport_coe hJset, ker_transport_coe hgWset] at hkk
    -- ═══ (★) CLOSED via the SHARED F₂-split (design correction 2026-07-12): one split of
    -- ∂(Sd^jF zJ) feeds BOTH fact_i_ambient_coreInt (Brick M) and the zc-side cap computation. ═══
    have hzJmem : zJ ∈ subspaceChainsInt (A ∩ B) (1 + 2 + 0 + 1) :=
      SKEFTHawking.SingularOpenDualityCycleInt.fundCycleW_mem_W (hA.inter hB)
        (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 2 + 0 + 1 by omega) z)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
        (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))
    have hzJbd : chainBoundary X (1 + 2 + 0) zJ ∈ subspaceChainsInt
        ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∪ (↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ)
        (1 + 2 + 0) := by
      rw [hJset]
      exact SKEFTHawking.SingularOpenDualityCycleInt.fundCycleW_boundary (hA.inter hB)
        (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 2 + 0 + 1 by omega) z)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
        (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))
    obtain ⟨jF, aF, bF, hFsplit⟩ :=
      SKEFTHawking.SingularSharedSplitInt.exists_shared_boundary_split_int hU' hV' zJ hzJmem hzJbd
    -- zJ's rel-witness to z₀ (the F₂ data for Brick M)
    obtain ⟨η₂, a₂, heq₂, ha₂⟩ :=
      SKEFTHawking.SingularConnSquareCloseNCInt.fundCycleW_chain_relInt (hA.inter hB)
        (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 2 + 0 + 1 by omega) z)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
        (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))
    rw [← hJset] at ha₂
    -- Brick M with the SHARED (aF, bF): ∂(capInt gW (f₂+f₃)) + (-1)^1 • capInt gW bFamb = ∂E_M
    obtain ⟨EM, hEMmem, hEM⟩ :=
      SKEFTHawking.SingularConnSquareCloseNCInt.fact_i_ambient_coreInt (N := 1) (p := 0)
        hA hB hU' hV'
        (legSplitUInt A B hA hB K).2 (legSplitVInt A B hA hB K).2
        (hgWset ▸ gW)
        (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) z)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
        K (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))
        hgWset.symm hJset.symm μ jF f₁ f₂ f₃ hf₁ hf₂ hf₃ hIsplit
        zJ hzJmem η₂ a₂ heq₂ ha₂ hzJbd aF bF hFsplit
    rw [ker_transport_coe hgWset] at hEM
    rw [show ((-1 : ℤ) ^ 1) = -1 by norm_num, neg_smul, one_smul] at hEM
    -- ── the zc side ──
    have hzcc : coboundaryₗ X (1 + 2) zc.1.1 = 0 := by
      have hh := congrArg Subtype.val zc.2
      simp only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] at hh
      exact hh
    have hzcvan : ∀ τ, zc.1.1 (SKEFTHawking.SingularRelativeHomologyMod2.simplexIncl
        ((↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ)
        (1 + 2) τ) = 0 :=
      fun τ => relCochainInt_vanish _ zc.1 τ
    -- Z1: subdivision correction  capInt zc zJ = capInt zc (Sd^jF zJ) − ∂(capInt zc (D_jF zJ))
    have hzJbd2 : chainBoundary X (1 + 2) zJ ∈ subspaceChainsInt
        ((↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ)
        (1 + 2) := hJset ▸ hzJbd
    have hh := SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt_chainHomotopy X jF (1 + 2) zJ
    have hcapDbd : capInt (m := 0 + 1) zc.1.1
        (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (1 + 2) jF
          (chainBoundary X (1 + 2) zJ)) = 0 :=
      capInt_subspaceChainInt_eq_zero _ zc.1.1 hzcvan
        (SKEFTHawking.SingularExcisionIsoInt.iterHomotopyInt_mem_subspaceChainsInt hzJbd2 jF)
    have hcapDbnd : capInt (m := 0 + 1) zc.1.1 (chainBoundary X (1 + 2 + 1)
          (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (1 + 2 + 1) jF zJ))
        = - chainBoundary X (0 + 1) (capInt (m := 0 + 1 + 1) zc.1.1
            (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (1 + 2 + 1) jF zJ)) := by
      have h := capInt_cocycle_chainMap (k := 1 + 2) (m := 0 + 1) zc.1.1 hzcc
        (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (1 + 2 + 1) jF zJ)
      rw [show ((-1 : ℤ) ^ (1 + 2)) = -1 by norm_num, neg_smul, one_smul] at h
      rw [h, neg_neg]
    have hZ1 : capInt (m := 0 + 1) zc.1.1 zJ
        = capInt (m := 0 + 1) zc.1.1
            ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ)
          - chainBoundary X (0 + 1) (capInt (m := 0 + 1 + 1) zc.1.1
              (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (1 + 2 + 1) jF zJ)) := by
      have hzJeq : zJ = (⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ
          + (chainBoundary X (1 + 2 + 1)
              (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (1 + 2 + 1) jF zJ)
            + SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (1 + 2) jF
              (chainBoundary X (1 + 2) zJ)) := by
        rw [hh]; abel
      conv_lhs => rw [hzJeq]
      rw [map_add, map_add, hcapDbd, add_zero, hcapDbnd]
      abel
    -- Z2: cap-Leibniz splitter at k = 1+1
    have hLeib : ∀ ω : SingularCochainInt X (1 + 1),
        capInt (m := 0 + 1) (coboundary X (1 + 1) ω)
            ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ)
          = capInt (m := 0 + 1) ω (chainBoundary X (1 + 2)
              ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ))
            - chainBoundary X (0 + 1) (capInt (m := 0 + 1 + 1) ω
                ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ)) := by
      intro ω
      have h := capInt_leibniz (k := 1 + 1) (m := 0 + 1) ω
        ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ) (by omega)
      rw [show ((-1 : ℤ) ^ (1 + 1 + 1)) = -1 by norm_num,
        show ((-1 : ℤ) ^ (1 + 1)) = 1 by norm_num, neg_smul, one_smul, one_smul] at h
      -- re-type h with the ▸ collapsed (literal-equal degrees; defeq)
      have h' : chainBoundary X (0 + 1) (capInt (m := 0 + 1 + 1) ω
            ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ))
          = -capInt (m := 0 + 1) (coboundary X (1 + 1) ω)
              ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ)
            + capInt (m := 0 + 1) ω (chainBoundary X (1 + 2)
              ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ)) := h
      rw [h']; abel
    -- zc = δ(indUf U' gW) + δ(kk): split the Sd-cap
    have hzcsplit : capInt (m := 0 + 1) zc.1.1
        ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ)
        = capInt (m := 0 + 1) (coboundary X (1 + 1)
              (indUf ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (1 + 1) gW.1.1))
            ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ)
          + capInt (m := 0 + 1) (coboundary X (1 + 1) (kk : SingularCochainInt X (1 + 1)))
            ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ) := by
      rw [← capInt_add_cochain, hkk]
    -- memberships of the split legs
    have haU' : chainIncl ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (1 + 2) aF
        ∈ subspaceChainsInt ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (1 + 2) :=
      SKEFTHawking.SingularRelativeMVInt.subspaceChainsInt_mono Set.inter_subset_left _
        (LinearMap.mem_range_self _ aF)
    have hbV' : chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (1 + 2) bF
        ∈ subspaceChainsInt ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ) (1 + 2) :=
      SKEFTHawking.SingularRelativeMVInt.subspaceChainsInt_mono Set.inter_subset_left _
        (LinearMap.mem_range_self _ bF)
    -- indUf-cap: kills the U'-leg, equals the gW-cap on the V'-leg
    have hind_a : capInt (m := 0 + 1)
        (indUf ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (1 + 1) gW.1.1)
        (chainIncl ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (1 + 2) aF) = 0 :=
      SKEFTHawking.SingularCapIndUfBridgeInt.capInt_indUf_subspaceU_eq_zeroInt _ _ haU'
    have hind_b : capInt (m := 0 + 1)
        (indUf ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (1 + 1) gW.1.1)
        (chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (1 + 2) bF)
        = capInt (m := 0 + 1) gW.1.1
            (chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (1 + 2) bF) := by
      have h := SKEFTHawking.SingularIndUfCapAgreeInt.capInt_indUf_eq_on_subspaceVInt
        (U := (↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ)
        (V := (↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ) (k := 1 + 1) (m := 0 + 1)
        (hgWset ▸ gW) hbV'
      rw [ker_transport_coe hgWset] at h
      exact h
    -- kk-cap kills both legs (mvUnion kronecker-vanish, per-simplex)
    have hkkvan : ∀ (T : Set ↑X), subspaceChainsInt T (1 + 1) ≤
          SKEFTHawking.SingularRelativeMVInt.mvUnionChainsInt
            ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ)
            ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ) (1 + 1) →
        ∀ τ, (kk : SingularCochainInt X (1 + 1))
          (SKEFTHawking.SingularRelativeHomologyMod2.simplexIncl T (1 + 1) τ) = 0 := by
      intro T hT τ
      have h0 := kk.2 _ (hT (LinearMap.mem_range_self (chainIncl T (1 + 1)) (Finsupp.single τ 1)))
      rwa [chainIncl_single, kronecker_single, one_mul] at h0
    have hkk_a : capInt (m := 0 + 1) (kk : SingularCochainInt X (1 + 1))
        (chainIncl ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (1 + 2) aF) = 0 :=
      capInt_subspaceChainInt_eq_zero _ _
        (hkkvan _ (le_trans (SKEFTHawking.SingularRelativeMVInt.subspaceChainsInt_mono
          Set.inter_subset_left (1 + 1)) le_sup_left))
        (LinearMap.mem_range_self _ aF)
    have hkk_b : capInt (m := 0 + 1) (kk : SingularCochainInt X (1 + 1))
        (chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (1 + 2) bF) = 0 :=
      capInt_subspaceChainInt_eq_zero _ _
        (hkkvan _ (le_trans (SKEFTHawking.SingularRelativeMVInt.subspaceChainsInt_mono
          Set.inter_subset_left (1 + 1)) le_sup_right))
        (LinearMap.mem_range_self _ bF)
    -- the assembled zc-side identity
    have hZfin : capInt (m := 0 + 1) zc.1.1 zJ
        = capInt (m := 0 + 1) gW.1.1
            (chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (1 + 2) bF)
          - chainBoundary X (0 + 1) (capInt (m := 0 + 1 + 1)
              (indUf ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (1 + 1) gW.1.1)
              ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ))
          - chainBoundary X (0 + 1) (capInt (m := 0 + 1 + 1) (kk : SingularCochainInt X (1 + 1))
              ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ))
          - chainBoundary X (0 + 1) (capInt (m := 0 + 1 + 1) zc.1.1
              (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (1 + 2 + 1) jF zJ)) := by
      rw [hZ1, hzcsplit, hLeib, hLeib, hFsplit, map_add, map_add, hind_a, hind_b, hkk_a, hkk_b]
      abel
    -- align the bF-leg degree spelling with Brick M's (1+1+(0+1)) — literal-equal
    have hbFdeg : chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (1 + 2) bF
        = chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (1 + 1 + (0 + 1)) bF :=
      rfl
    -- final witness: E = E_M + capInt(indUf) Sd + capInt(kk) Sd + capInt(zc) D — all C(A∩B)
    refine ⟨EM + capInt (m := 0 + 1 + 1)
        (indUf ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (1 + 1) gW.1.1)
        ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ)
      + capInt (m := 0 + 1 + 1) (kk : SingularCochainInt X (1 + 1))
        ((⇑(SingularSubdivisionInt.singularSdInt X (1 + 2 + 1)))^[jF] zJ)
      + capInt (m := 0 + 1 + 1) zc.1.1
        (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (1 + 2 + 1) jF zJ),
      ?_, ?_⟩
    · refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ hEMmem ?_) ?_) ?_
      · exact SKEFTHawking.SingularCapSupportInt.capInt_mem_subspaceChainsInt _ _
          (SKEFTHawking.SingularExcisionIsoInt.singularSdInt_iterate_mem_subspaceChainsInt
            hzJmem jF)
      · exact SKEFTHawking.SingularCapSupportInt.capInt_mem_subspaceChainsInt _ _
          (SKEFTHawking.SingularExcisionIsoInt.singularSdInt_iterate_mem_subspaceChainsInt
            hzJmem jF)
      · exact SKEFTHawking.SingularCapSupportInt.capInt_mem_subspaceChainsInt _ _
          (SKEFTHawking.SingularExcisionIsoInt.iterHomotopyInt_mem_subspaceChainsInt hzJmem jF)
    · rw [map_add, map_add, map_add, hZfin, ← hbFdeg, ← hEM]
      abel
  refine homology_eq_of_ambient_boundaryInt _ _ E hEmem ?_
  rw [chainIncl_pullbackDualityIntₗ]
  simp only [SKEFTHawking.SingularFunctorialityInt.cyclesMapInt_coe]
  erw [chainIncl_seam_boundaryExtractInt]
  rw [chainIncl_chainBoundary]
  erw [hzB]
  exact hEbd

/-- **Bot-window connecting-square seam-match** (integral, `k=2+1`, `m=0`). Matches the second conjunct of
`HcoreG`. Same reduction as the upper via brick 4-bot (`openDuality₀_legδ_eq_legW₀Int`) + brick 6a; the
residual `hmatch` is the degree-0 mirror of the upper one (WIP — mirror the upper's shared-split close at
`N=2, m=0`, which needs the deg-0 variants of the stage-1/Brick-M chain). -/
theorem seamMatch_botInt (A B : Set ↑X) (hA : IsOpen A) (hB : IsOpen B)
    (z : SingularChainInt X (1 + 0 + 3)) (hz : chainBoundary X (1 + 0 + 2) z = 0)
    (K : CompactsIn (A ∪ B)) (g : cohomGWInt (A ∪ B) (2 + 1) K) :
    subHomConnectingInt A B hA hB 0
        (legW (k := 2 + 1) (m := 0) (hA.union hB)
          (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz) K g)
      = -openDuality₀Int (k := 2 + 1) (hA.inter hB)
          (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
          (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
          (legδInt A B hA hB 2 K g) := by
  rw [SKEFTHawking.SingularOpenDualityBotLegdeltaCollapseInt.openDuality₀_legδ_eq_legW₀Int hA hB _ _ K g]
  obtain ⟨gW, rfl⟩ := RelativeCohomologyInt.mk_surjective ((↑K.1 : Set ↑X)ᶜ) (2 + 1) g
  obtain ⟨μ, f₁, f₂, f₃, hf₁, hf₂, hf₃, hIsplit, zA, zB, hzA, hzB, hcyc, hcls⟩ :=
    fact_i_stage1Int (U := A) (V := B) (LU := (↑(legSplitUInt A B hA hB K).1 : Set ↑X))
      (LV := (↑(legSplitVInt A B hA hB K).1 : Set ↑X)) (k := 2 + 1) (m := 0) hA hB
      (legSplitUInt A B hA hB K).1.isCompact'.isClosed.isOpen_compl
      (legSplitVInt A B hA hB K).1.isCompact'.isClosed.isOpen_compl
      (legSplitUInt A B hA hB K).2 (legSplitVInt A B hA hB K).2
      (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz) K gW
  apply subHomConnecting_legW_eq_legW_of_mvConnectingInt A B hA hB _ _ K (RelativeCohomologyInt.mk _ _ gW) _
  refine mvConnecting_eq_seamRHS_of_partitionInt A B hA hB 0 _ _ zA zB hcyc hcls _
    (mvConnecting_cover_partition _ _ 0 (cover_preimage A B hA hB) zA zB hcyc) ?_
  rw [LinearEquiv.eq_symm_apply, LinearEquiv.eq_symm_apply,
    SKEFTHawking.SingularMayerVietorisLESInt.seamHomologyEquivInt_apply,
    SKEFTHawking.SingularFunctorialityInt.Homology.mapInt_mk]
  rw [SKEFTHawking.SingularSubHomologyMVInt.seamI]
  erw [SKEFTHawking.SingularSubHomologyMVInt.subSeamEquivInt_apply,
    SKEFTHawking.SingularFunctorialityInt.Homology.mapInt_mk]
  obtain ⟨zc, hzc⟩ := RelativeCohomologyInt.mk_surjective
    ((↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ) (2 + 2)
    (relCohomSetCongrInt (by rw [infCompactInt_coe, Set.compl_inter]) (2 + 2)
      (relCohomMvConnectingInt _ _ _ _ 2
        (relCohomRestrictInt (Set.inter_subset_inter subset_rfl subset_rfl) (2 + 1)
          (relCohomSetCongrInt (by rw [legSplit_coverInt A B hA hB K, Set.compl_union]) (2 + 1)
            (RelativeCohomologyInt.mk _ (2 + 1) gW)))))
  rw [← hzc, SKEFTHawking.SingularConnSquareCloseNCInt.legW₀Int_mk]
  set zJ := SKEFTHawking.SingularOpenDualityBotInt.fundCycleW₀Int (hA.inter hB)
      (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
      (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)) with hzJ_def
  -- ⚠ ANTI-COMMUTATION (kernel-adjudicated 2026-07-12): at the BOT window the PD–MV square
  -- anti-commutes — the compiled M₀ (+capbF) and zc-side (+capbF) leave a −2·capbF residual in the
  -- plain-equality orientation, and cancel EXACTLY in the `+` orientation below. The classical
  -- statement (PD intertwines the connecting maps up to (−1)^deg) picks −1 at this degree pair.
  -- The HcoreG bot conjunct must therefore be the (−1)-twisted equation; surgery pending.
  obtain ⟨E, hEmem, hEbd⟩ : ∃ E : SingularChainInt X (0 + 1),
      E ∈ subspaceChainsInt (A ∩ B) (0 + 1) ∧
      chainBoundary X 0 E
        = chainBoundary X 0 (capInt (m := 0 + 1) gW.1.1 (f₂ + f₃))
          + capInt (m := 0) zc.1.1 zJ := by
    -- gW is an absolute cocycle
    have hgc : coboundaryₗ X (2 + 1) gW.1.1 = 0 := by
      have hh := congrArg Subtype.val gW.2
      simp only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] at hh
      exact hh
    -- STEP 2a: zc = δ(indUf U' gW) + δ(kk)
    rw [relCohomSetCongrInt_mk, relCohomRestrictInt_mk] at hzc
    have hU' : IsOpen ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) :=
      (legSplitUInt A B hA hB K).1.isCompact'.isClosed.isOpen_compl
    have hV' : IsOpen ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ) :=
      (legSplitVInt A B hA hB K).1.isCompact'.isClosed.isOpen_compl
    have hδ0 := (LinearEquiv.symm_apply_eq _).mpr hzc
    rw [relCohomSetCongrInt_symm_mk] at hδ0
    obtain ⟨kk, hkk⟩ := exists_mvUnion_of_connecting_mk_eq _ _ hU' hV' 2 _ _ hδ0.symm
    simp only [SKEFTHawking.SingularRelativeCohomologyRestrictInt.relCocycleRestrictInt_coe,
      SKEFTHawking.SingularRelativeCohomologyRestrictInt.relCochainRestrictInt_coe] at hkk
    have hgWset : ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ)
        = (↑K.1 : Set ↑X)ᶜ := by rw [← Set.compl_union, ← legSplit_coverInt]
    have hJset : ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∪ (↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ)
        = (↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ := by
      rw [infCompactInt_coe, Set.compl_inter]
    rw [ker_transport_coe hJset, ker_transport_coe hgWset] at hkk
    -- the SHARED F₂-split of ∂(Sd^jF zJ) (fundCycleW₀Int unfolds definitionally to fundCycleW)
    have hzJmem : zJ ∈ subspaceChainsInt (A ∩ B) (2 + 1 + 0 + 1) :=
      SKEFTHawking.SingularOpenDualityBotInt.fundCycleW₀Int_mem_W (hA.inter hB)
        (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
        (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))
    have hzJbd : chainBoundary X (2 + 1 + 0) zJ ∈ subspaceChainsInt
        ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∪ (↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ)
        (2 + 1 + 0) := by
      rw [hJset]
      exact SKEFTHawking.SingularOpenDualityBotInt.fundCycleW₀Int_boundary (hA.inter hB)
        (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
        (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))
    obtain ⟨jF, aF, bF, hFsplit⟩ :=
      SKEFTHawking.SingularSharedSplitInt.exists_shared_boundary_split_int hU' hV' zJ hzJmem hzJbd
    -- zJ's rel-witness to z₀ (the F₂ data for Brick M₀; fundCycleW₀Int ≡ fundCycleW definitionally)
    obtain ⟨η₂, a₂, heq₂', ha₂⟩ :=
      SKEFTHawking.SingularConnSquareCloseNCInt.fundCycleW_chain_relInt (k := 2 + 1) (m := 0)
        (hA.inter hB)
        (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
        (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))
    have heq₂ : zJ - castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z
        = chainBoundary X (2 + 1 + 0 + 1) η₂ + a₂ := by
      rw [hzJ_def, SKEFTHawking.SingularOpenDualityBotInt.fundCycleW₀Int,
        SKEFTHawking.SingularOpenDualityMVConnSquareInt.castChainInt_eq]
      exact heq₂'
    rw [← hJset] at ha₂
    -- Brick M₀ with the SHARED (aF, bF):  ∂(capInt gW (f₂+f₃)) + capInt gW bFamb = ∂E_M
    obtain ⟨EM, hEMmem, hEM⟩ :=
      SKEFTHawking.SingularConnSquareCloseNCInt.fact_i_ambient_core₀Int
        hA hB hU' hV'
        (legSplitUInt A B hA hB K).2 (legSplitVInt A B hA hB K).2
        (hgWset ▸ gW)
        (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
        K (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))
        hgWset.symm hJset.symm μ jF f₁ f₂ f₃ hf₁ hf₂ hf₃ hIsplit
        zJ hzJmem η₂ a₂ heq₂ ha₂ hzJbd aF bF hFsplit
    rw [ker_transport_coe hgWset] at hEM
    -- ── the zc side (bot signs: k = 2+2 even ⟹ the ∂-terms enter POSITIVELY) ──
    have hzcc : coboundaryₗ X (2 + 2) zc.1.1 = 0 := by
      have hh := congrArg Subtype.val zc.2
      simp only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] at hh
      exact hh
    have hzcvan : ∀ τ, zc.1.1 (SKEFTHawking.SingularRelativeHomologyMod2.simplexIncl
        ((↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ)
        (2 + 2) τ) = 0 :=
      fun τ => relCochainInt_vanish _ zc.1 τ
    have hzJbd2 : chainBoundary X (2 + 1) zJ ∈ subspaceChainsInt
        ((↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ)
        (2 + 1) := hJset ▸ hzJbd
    have hh := SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt_chainHomotopy X jF (2 + 1) zJ
    have hcapDbd : capInt (m := 0) zc.1.1
        (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (2 + 1) jF
          (chainBoundary X (2 + 1) zJ)) = 0 :=
      capInt_subspaceChainInt_eq_zero _ zc.1.1 hzcvan
        (SKEFTHawking.SingularExcisionIsoInt.iterHomotopyInt_mem_subspaceChainsInt hzJbd2 jF)
    have hcapDbnd : capInt (m := 0) zc.1.1 (chainBoundary X (2 + 1 + 1)
          (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (2 + 1 + 1) jF zJ))
        = chainBoundary X 0 (capInt (m := 0 + 1) zc.1.1
            (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (2 + 1 + 1) jF zJ)) := by
      have h := capInt_cocycle_chainMap (k := 2 + 2) (m := 0) zc.1.1 hzcc
        (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (2 + 1 + 1) jF zJ)
      rw [show ((-1 : ℤ) ^ (2 + 2)) = 1 by norm_num, one_smul] at h
      rw [← h]
    have hZ1 : capInt (m := 0) zc.1.1 zJ
        = capInt (m := 0) zc.1.1
            ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ)
          + chainBoundary X 0 (capInt (m := 0 + 1) zc.1.1
              (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (2 + 1 + 1) jF zJ)) := by
      have hzJeq : zJ = (⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ
          + (chainBoundary X (2 + 1 + 1)
              (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (2 + 1 + 1) jF zJ)
            + SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (2 + 1) jF
              (chainBoundary X (2 + 1) zJ)) := by
        rw [hh]; abel
      conv_lhs => rw [hzJeq]
      rw [map_add, map_add, hcapDbd]
      simp only [add_zero]
      exact congrArg (HAdd.hAdd _) hcapDbnd
    -- Z2: cap-Leibniz splitter at k = 2+1 (even total sign: + on both terms)
    have hLeib : ∀ ω : SingularCochainInt X (2 + 1),
        capInt (m := 0) (coboundary X (2 + 1) ω)
            ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ)
          = capInt (m := 0) ω (chainBoundary X (2 + 1)
              ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ))
            + chainBoundary X 0 (capInt (m := 0 + 1) ω
                ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ)) := by
      intro ω
      have h := capInt_leibniz (k := 2 + 1) (m := 0) ω
        ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ) (by omega)
      rw [show ((-1 : ℤ) ^ (2 + 1 + 1)) = 1 by norm_num,
        show ((-1 : ℤ) ^ (2 + 1)) = -1 by norm_num, neg_smul, one_smul, one_smul] at h
      have h' : chainBoundary X 0 (capInt (m := 0 + 1) ω
            ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ))
          = capInt (m := 0) (coboundary X (2 + 1) ω)
              ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ)
            + -capInt (m := 0) ω (chainBoundary X (2 + 1)
              ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ)) := h
      linear_combination (norm := module) -h'
    -- zc = δ(indUf U' gW) + δ(kk): split the Sd-cap
    have hzcsplit : capInt (m := 0) zc.1.1
        ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ)
        = capInt (m := 0) (coboundary X (2 + 1)
              (indUf ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (2 + 1) gW.1.1))
            ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ)
          + capInt (m := 0) (coboundary X (2 + 1) (kk : SingularCochainInt X (2 + 1)))
            ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ) := by
      rw [← capInt_add_cochain, hkk]
    -- memberships + kills (mirrors of the upper at k = 2+1)
    have haU' : chainIncl ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (2 + 1) aF
        ∈ subspaceChainsInt ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (2 + 1) :=
      SKEFTHawking.SingularRelativeMVInt.subspaceChainsInt_mono Set.inter_subset_left _
        (LinearMap.mem_range_self _ aF)
    have hbV' : chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (2 + 1) bF
        ∈ subspaceChainsInt ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ) (2 + 1) :=
      SKEFTHawking.SingularRelativeMVInt.subspaceChainsInt_mono Set.inter_subset_left _
        (LinearMap.mem_range_self _ bF)
    have hind_a : capInt (m := 0)
        (indUf ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (2 + 1) gW.1.1)
        (chainIncl ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (2 + 1) aF) = 0 :=
      SKEFTHawking.SingularCapIndUfBridgeInt.capInt_indUf_subspaceU_eq_zeroInt _ _ haU'
    have hind_b : capInt (m := 0)
        (indUf ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (2 + 1) gW.1.1)
        (chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (2 + 1) bF)
        = capInt (m := 0) gW.1.1
            (chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (2 + 1) bF) := by
      have h := SKEFTHawking.SingularIndUfCapAgreeInt.capInt_indUf_eq_on_subspaceVInt
        (U := (↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ)
        (V := (↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ) (k := 2 + 1) (m := 0)
        (hgWset ▸ gW) hbV'
      rw [ker_transport_coe hgWset] at h
      exact h
    have hkkvan : ∀ (T : Set ↑X), subspaceChainsInt T (2 + 1) ≤
          SKEFTHawking.SingularRelativeMVInt.mvUnionChainsInt
            ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ)
            ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ) (2 + 1) →
        ∀ τ, (kk : SingularCochainInt X (2 + 1))
          (SKEFTHawking.SingularRelativeHomologyMod2.simplexIncl T (2 + 1) τ) = 0 := by
      intro T hT τ
      have h0 := kk.2 _ (hT (LinearMap.mem_range_self (chainIncl T (2 + 1)) (Finsupp.single τ 1)))
      rwa [chainIncl_single, kronecker_single, one_mul] at h0
    have hkk_a : capInt (m := 0) (kk : SingularCochainInt X (2 + 1))
        (chainIncl ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (2 + 1) aF) = 0 :=
      capInt_subspaceChainInt_eq_zero _ _
        (hkkvan _ (le_trans (SKEFTHawking.SingularRelativeMVInt.subspaceChainsInt_mono
          Set.inter_subset_left (2 + 1)) le_sup_left))
        (LinearMap.mem_range_self _ aF)
    have hkk_b : capInt (m := 0) (kk : SingularCochainInt X (2 + 1))
        (chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (2 + 1) bF) = 0 :=
      capInt_subspaceChainInt_eq_zero _ _
        (hkkvan _ (le_trans (SKEFTHawking.SingularRelativeMVInt.subspaceChainsInt_mono
          Set.inter_subset_left (2 + 1)) le_sup_right))
        (LinearMap.mem_range_self _ bF)
    -- the assembled zc-side identity (bot: the ∂-terms enter with +)
    have hZfin : capInt (m := 0) zc.1.1 zJ
        = capInt (m := 0) gW.1.1
            (chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (2 + 1) bF)
          + chainBoundary X 0 (capInt (m := 0 + 1)
              (indUf ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (2 + 1) gW.1.1)
              ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ))
          + chainBoundary X 0 (capInt (m := 0 + 1) (kk : SingularCochainInt X (2 + 1))
              ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ))
          + chainBoundary X 0 (capInt (m := 0 + 1) zc.1.1
              (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (2 + 1 + 1) jF zJ)) := by
      rw [hZ1, hzcsplit, hLeib, hLeib, hFsplit, map_add, map_add, hind_a, hind_b, hkk_a, hkk_b]
      abel
    -- combine with Brick M₀ (∂cap(f₂+f₃) + capbF = ∂E_M): in the `+` orientation the capbF's
    -- cancel exactly — E := E_M + ζ⌢Sd-terms + zc⌢D-term, all C(A∩B) by cap-support
    refine ⟨EM + capInt (m := 0 + 1)
        (indUf ((↑(legSplitUInt A B hA hB K).1 : Set ↑X)ᶜ) (2 + 1) gW.1.1)
        ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ)
      + capInt (m := 0 + 1) (kk : SingularCochainInt X (2 + 1))
        ((⇑(SingularSubdivisionInt.singularSdInt X (2 + 1 + 1)))^[jF] zJ)
      + capInt (m := 0 + 1) zc.1.1
        (SKEFTHawking.SingularSubdivisionInt.iterHomotopyInt X (2 + 1 + 1) jF zJ),
      ?_, ?_⟩
    · refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ hEMmem ?_) ?_) ?_
      · exact SKEFTHawking.SingularCapSupportInt.capInt_mem_subspaceChainsInt _ _
          (SKEFTHawking.SingularExcisionIsoInt.singularSdInt_iterate_mem_subspaceChainsInt
            hzJmem jF)
      · exact SKEFTHawking.SingularCapSupportInt.capInt_mem_subspaceChainsInt _ _
          (SKEFTHawking.SingularExcisionIsoInt.singularSdInt_iterate_mem_subspaceChainsInt
            hzJmem jF)
      · exact SKEFTHawking.SingularCapSupportInt.capInt_mem_subspaceChainsInt _ _
          (SKEFTHawking.SingularExcisionIsoInt.iterHomotopyInt_mem_subspaceChainsInt hzJmem jF)
    · rw [map_add, map_add, map_add, hZfin,
        show chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (2 + 1) bF
          = chainIncl ((↑(legSplitVInt A B hA hB K).1 : Set ↑X)ᶜ ∩ (A ∩ B)) (2 + 1 + 0) bF from rfl,
        ← hEM]
      abel
  -- pull the −1 through `Homology.mk` (Quotient.mk is additive), then descend
  rw [show -Homology.mk (sub (A ∩ B)) 0
        ⟨SKEFTHawking.SingularLocalDualityKBotInt.pullbackDualityIntₗ₀
            ((↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ)
            (A ∩ B) zJ
            (SKEFTHawking.SingularOpenDualityBotInt.fundCycleW₀Int_mem_W (hA.inter hB)
              (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
              (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
              (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))) zc,
          Submodule.mem_top⟩
      = Homology.mk (sub (A ∩ B)) 0
          (-⟨SKEFTHawking.SingularLocalDualityKBotInt.pullbackDualityIntₗ₀
              ((↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ)
              (A ∩ B) zJ
              (SKEFTHawking.SingularOpenDualityBotInt.fundCycleW₀Int_mem_W (hA.inter hB)
                (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
                (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
                (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))) zc,
            Submodule.mem_top⟩)
      from by rw [Homology.mk, Homology.mk, Submodule.Quotient.mk_neg]; rfl]
  refine SKEFTHawking.SingularConnSquareCloseNCInt.homology_eq_of_ambient_boundary₀Int
    _ _ E hEmem ?_
  rw [show ((-⟨SKEFTHawking.SingularLocalDualityKBotInt.pullbackDualityIntₗ₀
          ((↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ)
          (A ∩ B) zJ
          (SKEFTHawking.SingularOpenDualityBotInt.fundCycleW₀Int_mem_W (hA.inter hB)
            (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
            (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))) zc,
        Submodule.mem_top⟩ : cycles (sub (A ∩ B)) 0) : SingularChainInt (sub (A ∩ B)) 0)
      = -(SKEFTHawking.SingularLocalDualityKBotInt.pullbackDualityIntₗ₀
          ((↑(infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K)).1 : Set ↑X)ᶜ)
          (A ∩ B) zJ
          (SKEFTHawking.SingularOpenDualityBotInt.fundCycleW₀Int_mem_W (hA.inter hB)
            (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) z)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) z hz)
            (infCompactInt A B (legSplitUInt A B hA hB K) (legSplitVInt A B hA hB K))) zc)
      from rfl,
    map_neg, SKEFTHawking.SingularLocalDualityKBotInt.chainIncl_pullbackDualityIntₗ₀, sub_neg_eq_add]
  simp only [SKEFTHawking.SingularFunctorialityInt.cyclesMapInt_coe]
  erw [chainIncl_seam_boundaryExtractInt]
  rw [chainIncl_chainBoundary]
  erw [hzB]
  exact hEbd

end SKEFTHawking.SingularSeamMatchInt
