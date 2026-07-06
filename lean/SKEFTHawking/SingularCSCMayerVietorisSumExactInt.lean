/-
# Phase 5q.H (E1 CSC-PD tower) — integral compactly-supported cohomology MV sum-exactness

Integral (`ZMod 2 → ℤ`) mirror of `SingularCSCMayerVietorisSumExact`. Exactness of the integral
compactly-supported-cohomology Mayer–Vietoris LES at the **union** term `Hᵏ_c(U∪V;ℤ)`:
  `Hᵏ_c(U;ℤ) ⊕ Hᵏ_c(V;ℤ) --Σ--> Hᵏ_c(U∪V;ℤ) --δ_csc--> Hᵏ⁺¹_c(U∩V;ℤ)`,
`range Σ = ker δ_csc`. A pair-indexed colimit element-chase with the enlargement trick, consuming the
per-pair relative connecting sum-exactness (`relCohomMv_exact_sumInt`) and δ∘Σ=0
(`relCohomMvConnectingInt_relCohomMvSumInt`). Over ℤ the MV sum is an honest DIFFERENCE, so the mod-2
`ZModModule.neg_eq_self` bridge (needed there to reconcile the `coprod`-sum with the cscMv difference)
disappears — both sides are already the same subtraction.

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

namespace SKEFTHawking.SingularCSCMayerVietorisSumExactInt

variable {M : TopCat}

theorem cscMv_exact_sumInt [T2Space ↑M] (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) {N : ℕ} :
    Function.Exact (cscMvSumInt U V (N + 1)) (cscMvConnectingInt U V hU hV N) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun p hp => ?_) (fun p hp => ?_)
  · revert hp
    refine Module.DirectLimit.induction_on p (fun K g => ?_)
    intro hp
    rw [LinearMap.mem_ker, cscMvConnectingInt_of, legδInt, LinearMap.comp_apply, rawLegInt_apply] at hp
    set KU := legSplitUInt U V hU hV K with hKU
    set KV := legSplitVInt U V hU hV K with hKV
    have hcongrK : ((↑K.1 : Set ↑M)ᶜ)
        = (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ := by
      rw [hKU, hKV, legSplit_coverInt, Set.compl_union]
    have hJU : ((↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ)
        = (↑(infCompactInt U V KU KV).1 : Set ↑M)ᶜ := by rw [infCompactInt_coe, Set.compl_inter]
    obtain ⟨J', hJJ', hdie⟩ := Module.DirectLimit.of.zero_exact hp
    set JU : CompactsIn U := ⟨J'.1, J'.2.trans Set.inter_subset_left⟩ with hJU'
    set JV : CompactsIn V := ⟨J'.1, J'.2.trans Set.inter_subset_right⟩ with hJV'
    set LU : CompactsIn U := CompactsIn.sup KU JU with hLU
    set LV : CompactsIn V := CompactsIn.sup KV JV with hLV
    have hcoeLU : (↑LU.1 : Set ↑M) = ↑KU.1 ∪ ↑J'.1 := by
      rw [hLU, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]
    have hcoeLV : (↑LV.1 : Set ↑M) = ↑KV.1 ∪ ↑J'.1 := by
      rw [hLV, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]
    have hLUKU : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑KU.1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLU]; exact Set.subset_union_left)
    have hLVKV : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑KV.1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLV]; exact Set.subset_union_left)
    have hJ'LU : (↑J'.1 : Set ↑M) ⊆ ↑LU.1 := by rw [hcoeLU]; exact Set.subset_union_right
    have hJ'LV : (↑J'.1 : Set ↑M) ⊆ ↑LV.1 := by rw [hcoeLV]; exact Set.subset_union_right
    have hUnionJ' : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) ⊆ (↑J'.1)ᶜ := by
      rw [← Set.compl_inter]
      exact Set.compl_subset_compl.mpr (Set.subset_inter hJ'LU hJ'LV)
    set ω := relCohomMvConnectingInt ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ)
      KU.1.isCompact'.isClosed.isOpen_compl KV.1.isCompact'.isClosed.isOpen_compl N
      (relCohomSetCongrInt hcongrK (N + 1) g) with hω
    have hdie2 : relCohomRestrictInt
        (show (↑J'.1 : Set ↑M)ᶜ ⊆ (↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ from
          hJU ▸ Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hJJ')) (N + 2) ω = 0 := by
      rw [← relCohomRestrict_relCohomSetCongrInt hJU
        (Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hJJ')) (N + 2) ω]
      exact hdie
    have hdelta0 : relCohomMvConnectingInt ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
        LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl N
        (relCohomRestrictInt (Set.inter_subset_inter hLUKU hLVKV) (N + 1)
          (relCohomSetCongrInt hcongrK (N + 1) g)) = 0 := by
      rw [relCohomMvConnecting_naturalityInt ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ)
        ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
        KU.1.isCompact'.isClosed.isOpen_compl KV.1.isCompact'.isClosed.isOpen_compl
        LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl
        hLUKU hLVKV N (relCohomSetCongrInt hcongrK (N + 1) g), ← hω,
        ← relCohomRestrictInt_trans hUnionJ'
          (show (↑J'.1 : Set ↑M)ᶜ ⊆ (↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ from
            hJU ▸ Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hJJ')) (N + 2) ω,
        hdie2, map_zero]
    have hexact := relCohomMv_exact_sumInt ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
      LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl (n := N)
    rw [LinearMap.exact_iff] at hexact
    obtain ⟨⟨x, y⟩, hxy⟩ := hexact ▸ (LinearMap.mem_ker.mpr hdelta0)
    rw [relCohomMvSumInt_apply] at hxy
    refine ⟨(Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U (N + 1))
          (cohomFWInt U (N + 1)) LU x,
        Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V (N + 1))
          (cohomFWInt V (N + 1)) LV y), ?_⟩
    rw [cscMvSumInt_of]
    set MU : CompactsIn (U ∪ V) := compactsInIncl Set.subset_union_left LU with hMU
    set MV : CompactsIn (U ∪ V) := compactsInIncl Set.subset_union_right LV with hMV
    set M' : CompactsIn (U ∪ V) := CompactsIn.sup MU MV with hM'
    have hcoeM' : (↑M'.1 : Set ↑M) = ↑LU.1 ∪ ↑LV.1 := by
      rw [hM', CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]; rfl
    have hMUM' : MU ≤ M' := Subtype.coe_le_coe.mp le_sup_left
    have hMVM' : MV ≤ M' := Subtype.coe_le_coe.mp le_sup_right
    have hKcoe : (↑K.1 : Set ↑M) = ↑KU.1 ∪ ↑KV.1 := by
      rw [← compl_inj_iff, Set.compl_union, ← hcongrK]
    have hKM' : K ≤ M' := by
      refine Subtype.coe_le_coe.mp ?_
      show (↑K.1 : Set ↑M) ⊆ ↑M'.1
      rw [hcoeM', hKcoe]
      exact Set.union_subset_union
        (by rw [hcoeLU]; exact Set.subset_union_left)
        (by rw [hcoeLV]; exact Set.subset_union_left)
    have hM'eq : (↑M'.1 : Set ↑M)ᶜ = (↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ := by
      rw [hcoeM', Set.compl_union]
    rw [show Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
            (cohomFWInt (U ∪ V) (N + 1)) MU x
          = Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
              (cohomFWInt (U ∪ V) (N + 1)) M' (cohomFWInt (U ∪ V) (N + 1) MU M' hMUM' x)
        from (Module.DirectLimit.of_f).symm,
      show Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
            (cohomFWInt (U ∪ V) (N + 1)) MV y
          = Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
              (cohomFWInt (U ∪ V) (N + 1)) M' (cohomFWInt (U ∪ V) (N + 1) MV M' hMVM' y)
        from (Module.DirectLimit.of_f).symm,
      show Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
            (cohomFWInt (U ∪ V) (N + 1)) K g
          = Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
              (cohomFWInt (U ∪ V) (N + 1)) M' (cohomFWInt (U ∪ V) (N + 1) K M' hKM' g)
        from (Module.DirectLimit.of_f).symm,
      ← map_sub]
    congr 1
    apply (relCohomSetCongrInt hM'eq (N + 1)).injective
    erw [map_sub]
    have hcU : (cohomFWInt (U ∪ V) (N + 1) MU M' hMUM') x
        = relCohomRestrictInt (show (↑M'.1 : Set ↑M)ᶜ ⊆ (↑LU.1 : Set ↑M)ᶜ from
            Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hMUM')) (N + 1) x := rfl
    have hcV : (cohomFWInt (U ∪ V) (N + 1) MV M' hMVM') y
        = relCohomRestrictInt (show (↑M'.1 : Set ↑M)ᶜ ⊆ (↑LV.1 : Set ↑M)ᶜ from
            Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hMVM')) (N + 1) y := rfl
    have hcK : (cohomFWInt (U ∪ V) (N + 1) K M' hKM') g
        = relCohomRestrictInt (show (↑M'.1 : Set ↑M)ᶜ ⊆ (↑K.1 : Set ↑M)ᶜ from
            Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hKM')) (N + 1) g := rfl
    rw [hcU, hcV, hcK,
      relCohomSetCongr_relCohomRestrictInt hM'eq _ (N + 1) x,
      relCohomSetCongr_relCohomRestrictInt hM'eq _ (N + 1) y,
      relCohomSetCongr_relCohomRestrictInt hM'eq _ (N + 1) g,
      ← relCohomRestrict_relCohomSetCongrInt hcongrK
        (show (↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ
            ⊆ (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ from
          Set.inter_subset_inter hLUKU hLVKV) (N + 1) g]
    rw [← hxy]
  · obtain ⟨⟨α, β⟩, rfl⟩ := hp
    refine Module.DirectLimit.induction_on α (fun Kα a => ?_)
    refine Module.DirectLimit.induction_on β (fun Kβ b => ?_)
    rw [LinearMap.mem_ker, cscMvSumInt_of]
    set L : CompactsIn (U ∪ V) :=
      CompactsIn.sup (compactsInIncl Set.subset_union_left Kα)
        (compactsInIncl Set.subset_union_right Kβ) with hL
    have hαL : compactsInIncl Set.subset_union_left Kα ≤ L := Subtype.coe_le_coe.mp le_sup_left
    have hβL : compactsInIncl Set.subset_union_right Kβ ≤ L :=
      Subtype.coe_le_coe.mp le_sup_right
    rw [show Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
            (cohomFWInt (U ∪ V) (N + 1)) (compactsInIncl Set.subset_union_left Kα) a
          = Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
              (cohomFWInt (U ∪ V) (N + 1)) L
              (cohomFWInt (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_left Kα) L hαL a)
        from (Module.DirectLimit.of_f).symm,
      show Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
            (cohomFWInt (U ∪ V) (N + 1)) (compactsInIncl Set.subset_union_right Kβ) b
          = Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
              (cohomFWInt (U ∪ V) (N + 1)) L
              (cohomFWInt (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_right Kβ) L hβL b)
        from (Module.DirectLimit.of_f).symm,
      ← map_sub, cscMvConnectingInt_of]
    set KU := legSplitUInt U V hU hV L with hKU
    set KV := legSplitVInt U V hU hV L with hKV
    set g := (cohomFWInt (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_left Kα) L hαL) a -
      (cohomFWInt (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_right Kβ) L hβL) b with hg
    set LU : CompactsIn U := CompactsIn.sup KU Kα with hLU
    set LV : CompactsIn V := CompactsIn.sup KV Kβ with hLV
    have hcoeLU : (↑LU.1 : Set ↑M) = ↑KU.1 ∪ ↑Kα.1 := by
      rw [hLU, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]
    have hcoeLV : (↑LV.1 : Set ↑M) = ↑KV.1 ∪ ↑Kβ.1 := by
      rw [hLV, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]
    have hKULU : KU.1 ≤ LU.1 := le_sup_left
    have hKVLV : KV.1 ≤ LV.1 := le_sup_left
    have hLUKU : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑KU.1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLU]; exact Set.subset_union_left)
    have hLVKV : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑KV.1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLV]; exact Set.subset_union_left)
    have hJL : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ)
        = (↑(infCompactInt U V LU LV).1 : Set ↑M)ᶜ := by
      rw [infCompactInt_coe, Set.compl_inter]
    have hcongr : ((↑L.1 : Set ↑M)ᶜ)
        = (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ := by
      rw [hKU, hKV, legSplit_coverInt, Set.compl_union]
    rw [legδInt_eq_enlarge U V hU hV N L LU LV hKULU hKVLV hLUKU hLVKV hJL hcongr g, rawLegInt_apply]
    suffices hkey : relCohomMvConnectingInt ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
        LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl N
        (relCohomRestrictInt (Set.inter_subset_inter hLUKU hLVKV) (N + 1)
          (relCohomSetCongrInt hcongr (N + 1) g)) = 0 by
      rw [hkey, map_zero]; exact map_zero _
    have hKαLU : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑Kα.1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLU]; exact Set.subset_union_right)
    have hKβLV : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑Kβ.1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLV]; exact Set.subset_union_right)
    set xa : RelativeCohomologyInt ((↑LU.1 : Set ↑M)ᶜ) (N + 1) :=
      relCohomRestrictInt hKαLU (N + 1) a with hxa
    set yb : RelativeCohomologyInt ((↑LV.1 : Set ↑M)ᶜ) (N + 1) :=
      relCohomRestrictInt hKβLV (N + 1) b with hyb
    have hsum : relCohomRestrictInt (Set.inter_subset_inter hLUKU hLVKV) (N + 1)
          (relCohomSetCongrInt hcongr (N + 1) g)
        = relCohomMvSumInt ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ) (N + 1) (xa, yb) := by
      rw [relCohomMvSumInt_apply, hxa, hyb,
        relCohomRestrictInt_trans Set.inter_subset_left hKαLU (N + 1) a,
        relCohomRestrictInt_trans Set.inter_subset_right hKβLV (N + 1) b, hg]
      erw [map_sub, map_sub]
      have hca : (cohomFWInt (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_left Kα) L hαL) a
          = relCohomRestrictInt (show (↑L.1 : Set ↑M)ᶜ ⊆ (↑Kα.1)ᶜ from
              Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hαL)) (N + 1) a := rfl
      have hcb : (cohomFWInt (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_right Kβ) L hβL) b
          = relCohomRestrictInt (show (↑L.1 : Set ↑M)ᶜ ⊆ (↑Kβ.1)ᶜ from
              Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hβL)) (N + 1) b := rfl
      rw [hca, hcb,
        relCohomSetCongr_relCohomRestrictInt hcongr _ (N + 1) a,
        relCohomSetCongr_relCohomRestrictInt hcongr _ (N + 1) b,
        relCohomRestrictInt_trans (Set.inter_subset_inter hLUKU hLVKV) _ (N + 1) a,
        relCohomRestrictInt_trans (Set.inter_subset_inter hLUKU hLVKV) _ (N + 1) b]
    rw [hsum, relCohomMvConnectingInt_relCohomMvSumInt]

end SKEFTHawking.SingularCSCMayerVietorisSumExactInt
