import Mathlib
import SKEFTHawking.SingularCSCMayerVietoris
import SKEFTHawking.SingularCSCMayerVietorisConnecting
import SKEFTHawking.SingularCSCMayerVietorisMiddle
import SKEFTHawking.SingularRelativeCohomologyMVConnecting

/-!
# Phase 5q.F (w₂-foundation) — compactly-supported cohomology MV connecting-exactness

Exactness of the compactly-supported-cohomology Mayer–Vietoris sequence at the intersection term one
degree up,
  `Hᵏ_c(U∪V) --δ_csc--> Hᵏ⁺¹_c(U∩V) --Δ--> Hᵏ⁺¹_c(U) ⊕ Hᵏ⁺¹_c(V)`,
i.e. `range (cscMvConnecting U V hU hV N) = ker (cscMvDiag U V (N + 2))`. Mirrors the middle exactness
`SingularCSCMayerVietorisMiddle.cscMv_exact_middle`: a pair-indexed colimit element-chase with the
enlargement trick, driven by the per-pair relative-cohomology MV connecting exactness
(`SingularRelativeCohomologyMVConnecting.relCohomMv_exact_connecting`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyRestrict
  SKEFTHawking.SingularRelativeCohomologyMV SKEFTHawking.SingularRelativeCohomologyMVConnecting
  SKEFTHawking.SingularCohomologyColimit SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularCSCOpenMonotone
  SKEFTHawking.SingularCSCMayerVietoris SKEFTHawking.SingularCSCMayerVietorisConnecting
  SKEFTHawking.SingularCompactlySupportedTop

namespace SKEFTHawking.SingularCSCMayerVietorisConnExact

variable {M : TopCat}

theorem cscMv_exact_connecting [T2Space ↑M] (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) {N : ℕ} :
    Function.Exact (SKEFTHawking.SingularCSCMayerVietorisConnecting.cscMvConnecting U V hU hV N)
      (SKEFTHawking.SingularCSCMayerVietoris.cscMvDiag U V (N + 2)) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun p hp => ?_) (fun p hp => ?_)
  · -- ker Δ ⊆ range δ_csc (the substantive chase)
    rw [LinearMap.mem_ker] at hp
    revert hp
    refine Module.DirectLimit.induction_on p (fun J h => ?_)
    intro hp
    rw [cscMvDiag_of] at hp
    have hU0 := congrArg Prod.fst hp
    have hV0 := congrArg Prod.snd hp
    simp only [Prod.fst_zero, Prod.snd_zero] at hU0 hV0
    -- U-vanishing: a compact K_U ⊇ J (in U) where the restriction of h vanishes
    rw [show (0 : CompactlySupportedCohomologyOpen U (N + 2))
        = Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U (N + 2)) (cohomFW U (N + 2))
            (compactsInIncl Set.inter_subset_left J) 0 from (map_zero _).symm] at hU0
    obtain ⟨KU, hKU, hKU0⟩ := Module.DirectLimit.exists_eq_of_of_eq hU0
    rw [show (0 : CompactlySupportedCohomologyOpen V (N + 2))
        = Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V (N + 2)) (cohomFW V (N + 2))
            (compactsInIncl Set.inter_subset_right J) 0 from (map_zero _).symm] at hV0
    obtain ⟨KV, hKV, hKV0⟩ := Module.DirectLimit.exists_eq_of_of_eq hV0
    rw [map_zero] at hKU0 hKV0
    -- the split subspaces A = (↑KU)ᶜ, B = (↑KV)ᶜ (open) and the merged compact K = KU ⊔ KV ⊆ U∪V
    have hAopen : IsOpen ((↑KU.1 : Set ↑M)ᶜ) := KU.1.isCompact'.isClosed.isOpen_compl
    have hBopen : IsOpen ((↑KV.1 : Set ↑M)ᶜ) := KV.1.isCompact'.isClosed.isOpen_compl
    have hKsub : (↑(KU.1 ⊔ KV.1) : Set ↑M) ⊆ U ∪ V := by
      rw [TopologicalSpace.Compacts.coe_sup]; exact Set.union_subset_union KU.2 KV.2
    set K : CompactsIn (U ∪ V) := ⟨KU.1 ⊔ KV.1, hKsub⟩ with hK
    -- (↑K)ᶜ = A ∩ B and the cover congruence A ∪ B = (↑(KU⊓KV))ᶜ
    have hKcompl : ((↑K.1 : Set ↑M)ᶜ) = (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ := by
      rw [hK, TopologicalSpace.Compacts.coe_sup, Set.compl_union]
    have hJleU : (↑J.1 : Set ↑M) ⊆ (↑KU.1 : Set ↑M) := Subtype.coe_le_coe.mpr hKU
    have hJleV : (↑J.1 : Set ↑M) ⊆ (↑KV.1 : Set ↑M) := Subtype.coe_le_coe.mpr hKV
    -- ζ = restrict h to A∪B = (↑(KU⊓KV))ᶜ ⊆ (↑J)ᶜ; this lies in ker (relCohomMvDiag A B)
    have hABJ : ((↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ) ⊆ (↑J.1 : Set ↑M)ᶜ := by
      rw [← Set.compl_inter]
      exact Set.compl_subset_compl.mpr (Set.subset_inter hJleU hJleV)
    set ζ : RelativeCohomology ((↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ) (N + 2) :=
      relCohomRestrict hABJ (N + 2) h with hζ
    have hζker : relCohomMvDiag ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ) (N + 2) ζ = 0 := by
      rw [relCohomMvDiag_apply, hζ, Prod.mk_eq_zero]
      refine ⟨?_, ?_⟩
      · rw [relCohomRestrict_trans Set.subset_union_left hABJ (N + 2) h]
        exact hKU0
      · rw [relCohomRestrict_trans Set.subset_union_right hABJ (N + 2) h]
        exact hKV0
    -- per-pair connecting exactness: ζ ∈ ker Δ = range δ → preimage ω : Hᵏ(M|A∩B)
    have hexact := relCohomMv_exact_connecting ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ) hAopen hBopen (N := N)
    rw [LinearMap.exact_iff] at hexact
    obtain ⟨ω, hω⟩ := hexact ▸ (LinearMap.mem_ker.mpr hζker)
    -- transport ω to a K-stage class g and take q := of_{U∪V} K g as the preimage candidate
    set g : cohomGW (U ∪ V) (N + 1) K := relCohomSetCongr hKcompl.symm (N + 1) ω with hg
    refine ⟨Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
        (cohomFW (U ∪ V) (N + 1)) K g, ?_⟩
    rw [cscMvConnecting_of]
    -- enlarge the chosen split of K to (LU, LV) ⊇ (KU, KV); express legδ as a rawLeg there
    set LU := CompactsIn.sup KU (legSplitU U V hU hV K) with hLU
    set LV := CompactsIn.sup KV (legSplitV U V hU hV K) with hLV
    have hKULU : (legSplitU U V hU hV K).1 ≤ LU.1 := le_sup_right
    have hKVLV : (legSplitV U V hU hV K).1 ≤ LV.1 := le_sup_right
    have hcoeLU : (↑LU.1 : Set ↑M) = ↑KU.1 ∪ ↑(legSplitU U V hU hV K).1 := by
      rw [hLU, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]
    have hcoeLV : (↑LV.1 : Set ↑M) = ↑KV.1 ∪ ↑(legSplitV U V hU hV K).1 := by
      rw [hLV, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]
    have hLUKU : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑(legSplitU U V hU hV K).1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLU]; exact Set.subset_union_right)
    have hLVKV : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑(legSplitV U V hU hV K).1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLV]; exact Set.subset_union_right)
    have hJL : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑(infCompact U V LU LV).1 : Set ↑M)ᶜ := by
      rw [infCompact_coe, Set.compl_inter]
    have hcongr : ((↑K.1 : Set ↑M)ᶜ)
        = (↑(legSplitU U V hU hV K).1 : Set ↑M)ᶜ ∩ (↑(legSplitV U V hU hV K).1 : Set ↑M)ᶜ := by
      rw [legSplit_cover, Set.compl_union]
    rw [legδ_eq_enlarge U V hU hV N K LU LV hKULU hKVLV hLUKU hLVKV hJL hcongr g, rawLeg_apply]
    -- the enlarged-subspace inclusions (↑LU)ᶜ ⊆ (↑KU)ᶜ, (↑LV)ᶜ ⊆ (↑KV)ᶜ
    have hLU_KU : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑KU.1 : Set ↑M)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLU]; exact Set.subset_union_left)
    have hLV_KV : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑KV.1 : Set ↑M)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLV]; exact Set.subset_union_left)
    -- the restricted source class equals the restriction of ω to (↑LU)ᶜ ∩ (↑LV)ᶜ
    have hsrc : relCohomRestrict (Set.inter_subset_inter hLUKU hLVKV) (N + 1)
          (relCohomSetCongr hcongr (N + 1) g)
        = relCohomRestrict (Set.inter_subset_inter hLU_KU hLV_KV) (N + 1) ω := by
      rw [hg, SingularCSCMayerVietorisMiddle.relCohomRestrict_relCohomSetCongr hcongr _ (N + 1)
            (relCohomSetCongr hKcompl.symm (N + 1) ω),
          SingularCSCMayerVietorisMiddle.relCohomRestrict_relCohomSetCongr hKcompl.symm _ (N + 1) ω]
    rw [hsrc, relCohomMvConnecting_naturality' ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ)
        ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ) hAopen hBopen
        LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl
        hLU_KU hLV_KV N ω, hω]
    -- the colimit collapse: J ≤ infCompact LU LV and the transported restriction is the transition map
    have hJLU : (↑J.1 : Set ↑M) ⊆ ↑LU.1 := by rw [hcoeLU]; exact hJleU.trans Set.subset_union_left
    have hJLV : (↑J.1 : Set ↑M) ⊆ ↑LV.1 := by rw [hcoeLV]; exact hJleV.trans Set.subset_union_left
    have hJinf : J ≤ infCompact U V LU LV := Subtype.coe_le_coe.mp (le_inf hJLU hJLV)
    have hcollapse : relCohomSetCongr hJL (N + 2)
          (relCohomRestrict (Set.union_subset_union hLU_KU hLV_KV) (N + 2) ζ)
        = cohomFW (U ∩ V) (N + 2) J (infCompact U V LU LV) hJinf h := by
      rw [hζ, relCohomRestrict_trans (Set.union_subset_union hLU_KU hLV_KV) hABJ (N + 2) h,
        SingularCSCMayerVietorisConnecting.relCohomSetCongr_relCohomRestrict hJL _ (N + 2) h,
        cohomFW, SingularCohomologyColimit.cohomF]
      rfl
    rw [hcollapse]
    exact Module.DirectLimit.of_f
  · -- range δ_csc ⊆ ker Δ (the chain-complex condition Δ ∘ δ_csc = 0)
    obtain ⟨q, rfl⟩ := hp
    rw [LinearMap.mem_ker]
    refine Module.DirectLimit.induction_on q (fun K g => ?_)
    rw [cscMvConnecting_of]
    set KU := legSplitU U V hU hV K with hKU
    set KV := legSplitV U V hU hV K with hKV
    set J := infCompact U V KU KV with hJ
    have hAopen : IsOpen ((↑KU.1 : Set ↑M)ᶜ) := KU.1.isCompact'.isClosed.isOpen_compl
    have hBopen : IsOpen ((↑KV.1 : Set ↑M)ᶜ) := KV.1.isCompact'.isClosed.isOpen_compl
    have hcongr : ((↑K.1 : Set ↑M)ᶜ) = (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ := by
      rw [hKU, hKV, legSplit_cover, Set.compl_union]
    have hJtarget : ((↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ) = (↑J.1 : Set ↑M)ᶜ := by
      rw [hJ, infCompact_coe, Set.compl_inter]
    -- the source class y and the connecting image ω
    set y : RelativeCohomology ((↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ) (N + 1) :=
      relCohomSetCongr hcongr (N + 1) g with hy
    set ω : RelativeCohomology ((↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ) (N + 2) :=
      relCohomMvConnecting ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ) hAopen hBopen N y with hω
    set γ₀' : cohomGW (U ∩ V) (N + 2) J := relCohomSetCongr hJtarget (N + 2) ω with hγ₀'
    have hbase : legδ U V hU hV N K g
        = Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∩ V)) (cohomGW (U ∩ V) (N + 2))
            (cohomFW (U ∩ V) (N + 2)) J γ₀' := rfl
    -- the chain-complex condition Δ ∘ δ = 0 at the per-pair level: both restrictions of ω vanish
    have hΔδ : relCohomMvDiag ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ) (N + 2) ω = 0 := by
      rw [hω]
      exact relCohomMvDiag_relCohomMvConnecting ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ) hAopen hBopen y
    rw [relCohomMvDiag_apply, Prod.mk_eq_zero] at hΔδ
    obtain ⟨hΔU, hΔV⟩ := hΔδ
    rw [hbase, cscMvDiag_of]
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_zero, Prod.snd_zero]
    · -- U-component: enlarge J ↦ KU; the restriction is the vanishing first leg hΔU
      have h₁ : compactsInIncl Set.inter_subset_left J ≤ KU :=
        Subtype.coe_le_coe.mp inf_le_left
      have hF : cohomFW U (N + 2) (compactsInIncl Set.inter_subset_left J) KU h₁ γ₀'
          = relCohomRestrict Set.subset_union_left (N + 2) ω := by
        rw [hγ₀', cohomFW, SingularCohomologyColimit.cohomF]
        exact SingularCSCMayerVietorisMiddle.relCohomRestrict_relCohomSetCongr hJtarget _ (N + 2) ω
      calc Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U (N + 2)) (cohomFW U (N + 2))
              (compactsInIncl Set.inter_subset_left J) γ₀'
          = Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U (N + 2)) (cohomFW U (N + 2)) KU
              (cohomFW U (N + 2) (compactsInIncl Set.inter_subset_left J) KU h₁ γ₀') :=
            (Module.DirectLimit.of_f).symm
        _ = Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U (N + 2)) (cohomFW U (N + 2)) KU
              (relCohomRestrict Set.subset_union_left (N + 2) ω) := by rw [hF]
        _ = 0 := by rw [hΔU]; exact map_zero _
    · -- V-component: enlarge J ↦ KV; the restriction is the vanishing second leg hΔV
      have h₁ : compactsInIncl Set.inter_subset_right J ≤ KV :=
        Subtype.coe_le_coe.mp inf_le_right
      have hF : cohomFW V (N + 2) (compactsInIncl Set.inter_subset_right J) KV h₁ γ₀'
          = relCohomRestrict Set.subset_union_right (N + 2) ω := by
        rw [hγ₀', cohomFW, SingularCohomologyColimit.cohomF]
        exact SingularCSCMayerVietorisMiddle.relCohomRestrict_relCohomSetCongr hJtarget _ (N + 2) ω
      calc Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V (N + 2)) (cohomFW V (N + 2))
              (compactsInIncl Set.inter_subset_right J) γ₀'
          = Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V (N + 2)) (cohomFW V (N + 2)) KV
              (cohomFW V (N + 2) (compactsInIncl Set.inter_subset_right J) KV h₁ γ₀') :=
            (Module.DirectLimit.of_f).symm
        _ = Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V (N + 2)) (cohomFW V (N + 2)) KV
              (relCohomRestrict Set.subset_union_right (N + 2) ω) := by rw [hF]
        _ = 0 := by rw [hΔV]; exact map_zero _

end SKEFTHawking.SingularCSCMayerVietorisConnExact
