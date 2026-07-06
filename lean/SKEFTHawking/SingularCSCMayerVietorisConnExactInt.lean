/-
# Phase 5q.H (E1 CSC-PD tower) — integral compactly-supported cohomology MV connecting-exactness

Integral (`ZMod 2 → ℤ`) mirror of `SingularCSCMayerVietorisConnExact`. Exactness of the integral
compactly-supported-cohomology Mayer–Vietoris sequence at the intersection term one degree up,
  `Hᵏ_c(U∪V;ℤ) --δ_csc--> Hᵏ⁺¹_c(U∩V;ℤ) --Δ--> Hᵏ⁺¹_c(U;ℤ) ⊕ Hᵏ⁺¹_c(V;ℤ)`,
i.e. `range (cscMvConnectingInt U V hU hV N) = ker (cscMvDiagInt U V (N + 2))`. A pair-indexed colimit
element-chase with the enlargement trick, driven by the per-pair relative connecting exactness
(`relCohomMv_exact_connectingInt`) and the torsion-safe connecting naturality
(`relCohomMvConnecting_naturalityInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCSCMayerVietorisConnectingInt

open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeCohomologyRestrictInt
open SKEFTHawking.SingularRelativeCohomologyMVInt
open SKEFTHawking.SingularRelativeCohomologyMVConnectingInt
open SKEFTHawking.SingularCohomologyColimitInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCSCOpenMonotoneInt
open SKEFTHawking.SingularCSCMayerVietorisInt
open SKEFTHawking.SingularCSCMayerVietorisMiddleInt
open SKEFTHawking.SingularCSCMayerVietorisConnectingInt

namespace SKEFTHawking.SingularCSCMayerVietorisConnExactInt

variable {M : TopCat}

theorem cscMv_exact_connectingInt [T2Space ↑M] (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) {N : ℕ} :
    Function.Exact (cscMvConnectingInt U V hU hV N) (cscMvDiagInt U V (N + 2)) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun p hp => ?_) (fun p hp => ?_)
  · -- ker Δ ⊆ range δ_csc
    rw [LinearMap.mem_ker] at hp
    revert hp
    refine Module.DirectLimit.induction_on p (fun J h => ?_)
    intro hp
    rw [cscMvDiagInt_of] at hp
    have hU0 := congrArg Prod.fst hp
    have hV0 := congrArg Prod.snd hp
    simp only [Prod.fst_zero, Prod.snd_zero] at hU0 hV0
    rw [show (0 : CompactlySupportedCohomologyOpenInt U (N + 2))
        = Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U (N + 2)) (cohomFWInt U (N + 2))
            (compactsInIncl Set.inter_subset_left J) 0 from (map_zero _).symm] at hU0
    obtain ⟨KU, hKU, hKU0⟩ := Module.DirectLimit.exists_eq_of_of_eq hU0
    rw [show (0 : CompactlySupportedCohomologyOpenInt V (N + 2))
        = Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V (N + 2)) (cohomFWInt V (N + 2))
            (compactsInIncl Set.inter_subset_right J) 0 from (map_zero _).symm] at hV0
    obtain ⟨KV, hKV, hKV0⟩ := Module.DirectLimit.exists_eq_of_of_eq hV0
    rw [map_zero] at hKU0 hKV0
    have hAopen : IsOpen ((↑KU.1 : Set ↑M)ᶜ) := KU.1.isCompact'.isClosed.isOpen_compl
    have hBopen : IsOpen ((↑KV.1 : Set ↑M)ᶜ) := KV.1.isCompact'.isClosed.isOpen_compl
    have hKsub : (↑(KU.1 ⊔ KV.1) : Set ↑M) ⊆ U ∪ V := by
      rw [TopologicalSpace.Compacts.coe_sup]; exact Set.union_subset_union KU.2 KV.2
    set K : CompactsIn (U ∪ V) := ⟨KU.1 ⊔ KV.1, hKsub⟩ with hK
    have hKcompl : ((↑K.1 : Set ↑M)ᶜ) = (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ := by
      rw [hK, TopologicalSpace.Compacts.coe_sup, Set.compl_union]
    have hJleU : (↑J.1 : Set ↑M) ⊆ (↑KU.1 : Set ↑M) := Subtype.coe_le_coe.mpr hKU
    have hJleV : (↑J.1 : Set ↑M) ⊆ (↑KV.1 : Set ↑M) := Subtype.coe_le_coe.mpr hKV
    have hABJ : ((↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ) ⊆ (↑J.1 : Set ↑M)ᶜ := by
      rw [← Set.compl_inter]
      exact Set.compl_subset_compl.mpr (Set.subset_inter hJleU hJleV)
    set ζ : RelativeCohomologyInt ((↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ) (N + 2) :=
      relCohomRestrictInt hABJ (N + 2) h with hζ
    have hζker : relCohomMvDiagInt ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ) (N + 2) ζ = 0 := by
      rw [relCohomMvDiagInt_apply, hζ, Prod.mk_eq_zero]
      refine ⟨?_, ?_⟩
      · rw [relCohomRestrictInt_trans Set.subset_union_left hABJ (N + 2) h]
        exact hKU0
      · rw [relCohomRestrictInt_trans Set.subset_union_right hABJ (N + 2) h]
        exact hKV0
    have hexact := relCohomMv_exact_connectingInt ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ) hAopen hBopen (n := N)
    rw [LinearMap.exact_iff] at hexact
    obtain ⟨ω, hω⟩ := hexact ▸ (LinearMap.mem_ker.mpr hζker)
    set g : cohomGWInt (U ∪ V) (N + 1) K := relCohomSetCongrInt hKcompl.symm (N + 1) ω with hg
    refine ⟨Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
        (cohomFWInt (U ∪ V) (N + 1)) K g, ?_⟩
    rw [cscMvConnectingInt_of]
    set LU := CompactsIn.sup KU (legSplitUInt U V hU hV K) with hLU
    set LV := CompactsIn.sup KV (legSplitVInt U V hU hV K) with hLV
    have hKULU : (legSplitUInt U V hU hV K).1 ≤ LU.1 := le_sup_right
    have hKVLV : (legSplitVInt U V hU hV K).1 ≤ LV.1 := le_sup_right
    have hcoeLU : (↑LU.1 : Set ↑M) = ↑KU.1 ∪ ↑(legSplitUInt U V hU hV K).1 := by
      rw [hLU, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]
    have hcoeLV : (↑LV.1 : Set ↑M) = ↑KV.1 ∪ ↑(legSplitVInt U V hU hV K).1 := by
      rw [hLV, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]
    have hLUKU : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑(legSplitUInt U V hU hV K).1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLU]; exact Set.subset_union_right)
    have hLVKV : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑(legSplitVInt U V hU hV K).1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLV]; exact Set.subset_union_right)
    have hJL : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑(infCompactInt U V LU LV).1 : Set ↑M)ᶜ := by
      rw [infCompactInt_coe, Set.compl_inter]
    have hcongr : ((↑K.1 : Set ↑M)ᶜ)
        = (↑(legSplitUInt U V hU hV K).1 : Set ↑M)ᶜ ∩ (↑(legSplitVInt U V hU hV K).1 : Set ↑M)ᶜ := by
      rw [legSplit_coverInt, Set.compl_union]
    rw [legδInt_eq_enlarge U V hU hV N K LU LV hKULU hKVLV hLUKU hLVKV hJL hcongr g, rawLegInt_apply]
    have hLU_KU : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑KU.1 : Set ↑M)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLU]; exact Set.subset_union_left)
    have hLV_KV : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑KV.1 : Set ↑M)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLV]; exact Set.subset_union_left)
    have hsrc : relCohomRestrictInt (Set.inter_subset_inter hLUKU hLVKV) (N + 1)
          (relCohomSetCongrInt hcongr (N + 1) g)
        = relCohomRestrictInt (Set.inter_subset_inter hLU_KU hLV_KV) (N + 1) ω := by
      rw [hg, relCohomRestrict_relCohomSetCongrInt hcongr _ (N + 1)
            (relCohomSetCongrInt hKcompl.symm (N + 1) ω),
          relCohomRestrict_relCohomSetCongrInt hKcompl.symm _ (N + 1) ω]
    rw [hsrc, relCohomMvConnecting_naturalityInt ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ)
        ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ) hAopen hBopen
        LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl
        hLU_KU hLV_KV N ω, hω]
    have hJLU : (↑J.1 : Set ↑M) ⊆ ↑LU.1 := by rw [hcoeLU]; exact hJleU.trans Set.subset_union_left
    have hJLV : (↑J.1 : Set ↑M) ⊆ ↑LV.1 := by rw [hcoeLV]; exact hJleV.trans Set.subset_union_left
    have hJinf : J ≤ infCompactInt U V LU LV := Subtype.coe_le_coe.mp (le_inf hJLU hJLV)
    have hcollapse : relCohomSetCongrInt hJL (N + 2)
          (relCohomRestrictInt (Set.union_subset_union hLU_KU hLV_KV) (N + 2) ζ)
        = cohomFWInt (U ∩ V) (N + 2) J (infCompactInt U V LU LV) hJinf h := by
      rw [hζ, relCohomRestrictInt_trans (Set.union_subset_union hLU_KU hLV_KV) hABJ (N + 2) h,
        relCohomSetCongr_relCohomRestrictInt hJL _ (N + 2) h, cohomFWInt, cohomFInt]
      rfl
    rw [hcollapse]
    exact Module.DirectLimit.of_f
  · -- range δ_csc ⊆ ker Δ (the chain-complex condition Δ ∘ δ_csc = 0)
    obtain ⟨q, rfl⟩ := hp
    rw [LinearMap.mem_ker]
    refine Module.DirectLimit.induction_on q (fun K g => ?_)
    rw [cscMvConnectingInt_of]
    set KU := legSplitUInt U V hU hV K with hKU
    set KV := legSplitVInt U V hU hV K with hKV
    set J := infCompactInt U V KU KV with hJ
    have hAopen : IsOpen ((↑KU.1 : Set ↑M)ᶜ) := KU.1.isCompact'.isClosed.isOpen_compl
    have hBopen : IsOpen ((↑KV.1 : Set ↑M)ᶜ) := KV.1.isCompact'.isClosed.isOpen_compl
    have hcongr : ((↑K.1 : Set ↑M)ᶜ) = (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ := by
      rw [hKU, hKV, legSplit_coverInt, Set.compl_union]
    have hJtarget : ((↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ) = (↑J.1 : Set ↑M)ᶜ := by
      rw [hJ, infCompactInt_coe, Set.compl_inter]
    set y : RelativeCohomologyInt ((↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ) (N + 1) :=
      relCohomSetCongrInt hcongr (N + 1) g with hy
    set ω : RelativeCohomologyInt ((↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ) (N + 2) :=
      relCohomMvConnectingInt ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ) hAopen hBopen N y with hω
    set γ₀' : cohomGWInt (U ∩ V) (N + 2) J := relCohomSetCongrInt hJtarget (N + 2) ω with hγ₀'
    have hbase : legδInt U V hU hV N K g
        = Module.DirectLimit.of ℤ (CompactsIn (U ∩ V)) (cohomGWInt (U ∩ V) (N + 2))
            (cohomFWInt (U ∩ V) (N + 2)) J γ₀' := rfl
    have hΔδ : relCohomMvDiagInt ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ) (N + 2) ω = 0 := by
      rw [hω]
      exact relCohomMvDiagInt_relCohomMvConnectingInt ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ) hAopen hBopen N y
    rw [relCohomMvDiagInt_apply, Prod.mk_eq_zero] at hΔδ
    obtain ⟨hΔU, hΔV⟩ := hΔδ
    rw [hbase, cscMvDiagInt_of]
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_zero, Prod.snd_zero]
    · have h₁ : compactsInIncl Set.inter_subset_left J ≤ KU :=
        Subtype.coe_le_coe.mp inf_le_left
      have hF : cohomFWInt U (N + 2) (compactsInIncl Set.inter_subset_left J) KU h₁ γ₀'
          = relCohomRestrictInt Set.subset_union_left (N + 2) ω := by
        rw [hγ₀', cohomFWInt, cohomFInt]
        exact relCohomRestrict_relCohomSetCongrInt hJtarget _ (N + 2) ω
      calc Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U (N + 2)) (cohomFWInt U (N + 2))
              (compactsInIncl Set.inter_subset_left J) γ₀'
          = Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U (N + 2)) (cohomFWInt U (N + 2)) KU
              (cohomFWInt U (N + 2) (compactsInIncl Set.inter_subset_left J) KU h₁ γ₀') :=
            (Module.DirectLimit.of_f).symm
        _ = Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U (N + 2)) (cohomFWInt U (N + 2)) KU
              (relCohomRestrictInt Set.subset_union_left (N + 2) ω) := by rw [hF]
        _ = 0 := by rw [hΔU]; exact map_zero _
    · have h₁ : compactsInIncl Set.inter_subset_right J ≤ KV :=
        Subtype.coe_le_coe.mp inf_le_right
      have hF : cohomFWInt V (N + 2) (compactsInIncl Set.inter_subset_right J) KV h₁ γ₀'
          = relCohomRestrictInt Set.subset_union_right (N + 2) ω := by
        rw [hγ₀', cohomFWInt, cohomFInt]
        exact relCohomRestrict_relCohomSetCongrInt hJtarget _ (N + 2) ω
      calc Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V (N + 2)) (cohomFWInt V (N + 2))
              (compactsInIncl Set.inter_subset_right J) γ₀'
          = Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V (N + 2)) (cohomFWInt V (N + 2)) KV
              (cohomFWInt V (N + 2) (compactsInIncl Set.inter_subset_right J) KV h₁ γ₀') :=
            (Module.DirectLimit.of_f).symm
        _ = Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V (N + 2)) (cohomFWInt V (N + 2)) KV
              (relCohomRestrictInt Set.subset_union_right (N + 2) ω) := by rw [hF]
        _ = 0 := by rw [hΔV]; exact map_zero _

end SKEFTHawking.SingularCSCMayerVietorisConnExactInt
