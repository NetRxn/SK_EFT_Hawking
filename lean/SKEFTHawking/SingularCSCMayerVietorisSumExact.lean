import Mathlib
import SKEFTHawking.SingularCSCMayerVietoris
import SKEFTHawking.SingularCSCMayerVietorisMiddle
import SKEFTHawking.SingularCSCMayerVietorisConnecting
import SKEFTHawking.SingularRelativeCohomologyMVConnecting

/-!
# Phase 5q.F (w₂-foundation) — compactly-supported cohomology MV sum-exactness

The exactness of the compactly-supported-cohomology Mayer–Vietoris LES at the **union** term
`Hᵏ_c(U∪V)`:
  `Hᵏ_c(U) ⊕ Hᵏ_c(V) --Σ--> Hᵏ_c(U∪V) --δ_csc--> Hᵏ⁺¹_c(U∩V)`,
`range Σ = ker δ_csc`. Mirrors `SingularCSCMayerVietorisMiddle.cscMv_exact_middle` (the
pair-indexed colimit element-chase with the enlargement trick) but consuming the per-pair
connecting-term engine
`SingularRelativeCohomologyMVConnecting.relCohomMv_exact_sum` instead of the middle one.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyRestrict
  SKEFTHawking.SingularRelativeCohomologyMV SKEFTHawking.SingularRelativeCohomologyMVConnecting
  SKEFTHawking.SingularCohomologyColimit SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularCSCOpenMonotone
  SKEFTHawking.SingularCSCMayerVietoris SKEFTHawking.SingularCSCMayerVietorisMiddle
  SKEFTHawking.SingularCSCMayerVietorisConnecting SKEFTHawking.SingularCompactlySupportedTop

namespace SKEFTHawking.SingularCSCMayerVietorisSumExact

variable {M : TopCat}

theorem cscMv_exact_sum [T2Space ↑M] (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) {N : ℕ} :
    Function.Exact (SKEFTHawking.SingularCSCMayerVietoris.cscMvSum U V (N + 1))
      (SKEFTHawking.SingularCSCMayerVietorisConnecting.cscMvConnecting U V hU hV N) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun p hp => ?_) (fun p hp => ?_)
  · revert hp
    refine Module.DirectLimit.induction_on p (fun K g => ?_)
    intro hp
    rw [LinearMap.mem_ker, cscMvConnecting_of, legδ, LinearMap.comp_apply, rawLeg_apply] at hp
    -- name the chosen split of K and the associated complement-congruence
    set KU := legSplitU U V hU hV K with hKU
    set KV := legSplitV U V hU hV K with hKV
    have hcongrK : ((↑K.1 : Set ↑M)ᶜ)
        = (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ := by
      rw [hKU, hKV, legSplit_cover, Set.compl_union]
    have hJU : ((↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ)
        = (↑(infCompact U V KU KV).1 : Set ↑M)ᶜ := by rw [infCompact_coe, Set.compl_inter]
    -- the connecting class dies at a finer compact J' ⊇ KU⊓KV (DirectLimit zero_exact)
    obtain ⟨J', hJJ', hdie⟩ := Module.DirectLimit.of.zero_exact hp
    -- view J' as a compact in U and in V, and enlarge the chosen split to absorb it
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
    -- (↑LU)ᶜ ∪ (↑LV)ᶜ ⊆ (↑J')ᶜ  (since J' ⊆ LU ∩ LV)
    have hUnionJ' : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) ⊆ (↑J'.1)ᶜ := by
      rw [← Set.compl_inter]
      exact Set.compl_subset_compl.mpr (Set.subset_inter hJ'LU hJ'LV)
    -- abbreviation for the connecting class at the chosen split, before the target set-congruence
    set ω := relCohomMvConnecting ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ)
      KU.1.isCompact'.isClosed.isOpen_compl KV.1.isCompact'.isClosed.isOpen_compl N
      (relCohomSetCongr hcongrK (N + 1) g) with hω
    -- `hdie` says the J'-restriction of (setCongr ω) vanishes; absorb the set-congruence
    have hdie2 : relCohomRestrict
        (show (↑J'.1 : Set ↑M)ᶜ ⊆ (↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ from
          hJU ▸ Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hJJ')) (N + 2) ω = 0 := by
      rw [← relCohomRestrict_relCohomSetCongr hJU
        (Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hJJ')) (N + 2) ω]
      exact hdie
    -- restrict the vanishing further onto (↑LU)ᶜ ∪ (↑LV)ᶜ, then transport via the naturality
    have hdelta0 : relCohomMvConnecting ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
        LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl N
        (relCohomRestrict (Set.inter_subset_inter hLUKU hLVKV) (N + 1)
          (relCohomSetCongr hcongrK (N + 1) g)) = 0 := by
      rw [relCohomMvConnecting_naturality' ((↑KU.1 : Set ↑M)ᶜ) ((↑KV.1 : Set ↑M)ᶜ)
        ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
        KU.1.isCompact'.isClosed.isOpen_compl KV.1.isCompact'.isClosed.isOpen_compl
        LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl
        hLUKU hLVKV N (relCohomSetCongr hcongrK (N + 1) g), ← hω,
        ← relCohomRestrict_trans hUnionJ'
          (show (↑J'.1 : Set ↑M)ᶜ ⊆ (↑KU.1 : Set ↑M)ᶜ ∪ (↑KV.1 : Set ↑M)ᶜ from
            hJU ▸ Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hJJ')) (N + 2) ω,
        hdie2, map_zero]
    -- per-pair MV exactness: the restricted class is a per-pair MV sum
    have hexact := relCohomMv_exact_sum ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
      LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl (N := N)
    rw [LinearMap.exact_iff] at hexact
    obtain ⟨⟨x, y⟩, hxy⟩ := hexact ▸ (LinearMap.mem_ker.mpr hdelta0)
    rw [relCohomMvSum_apply] at hxy
    -- exhibit the cscMvSum preimage (of_U LU x, of_V LV y)
    refine ⟨(Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U (N + 1))
          (cohomFW U (N + 1)) LU x,
        Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V (N + 1))
          (cohomFW V (N + 1)) LV y), ?_⟩
    rw [cscMvSum_of]
    -- common (U∪V)-compact M' = LU ⊔ LV carrying both legs and K
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
    -- push both legs and `of K g` to the common stage M' = LU ⊔ LV
    rw [show Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
            (cohomFW (U ∪ V) (N + 1)) MU x
          = Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
              (cohomFW (U ∪ V) (N + 1)) M' (cohomFW (U ∪ V) (N + 1) MU M' hMUM' x)
        from (Module.DirectLimit.of_f).symm,
      show Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
            (cohomFW (U ∪ V) (N + 1)) MV y
          = Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
              (cohomFW (U ∪ V) (N + 1)) M' (cohomFW (U ∪ V) (N + 1) MV M' hMVM' y)
        from (Module.DirectLimit.of_f).symm,
      show Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
            (cohomFW (U ∪ V) (N + 1)) K g
          = Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
              (cohomFW (U ∪ V) (N + 1)) M' (cohomFW (U ∪ V) (N + 1) K M' hKM' g)
        from (Module.DirectLimit.of_f).symm,
      ← map_sub]
    congr 1
    -- transport the M'-stage equation onto (↑LU)ᶜ ∩ (↑LV)ᶜ, where it is exactly `hxy`
    apply (relCohomSetCongr hM'eq (N + 1)).injective
    erw [map_sub]
    -- the three cohomFW are relCohomRestrict over complements; absorb the M'-congruence
    have hcU : (cohomFW (U ∪ V) (N + 1) MU M' hMUM') x
        = relCohomRestrict (show (↑M'.1 : Set ↑M)ᶜ ⊆ (↑LU.1 : Set ↑M)ᶜ from
            Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hMUM')) (N + 1) x := rfl
    have hcV : (cohomFW (U ∪ V) (N + 1) MV M' hMVM') y
        = relCohomRestrict (show (↑M'.1 : Set ↑M)ᶜ ⊆ (↑LV.1 : Set ↑M)ᶜ from
            Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hMVM')) (N + 1) y := rfl
    have hcK : (cohomFW (U ∪ V) (N + 1) K M' hKM') g
        = relCohomRestrict (show (↑M'.1 : Set ↑M)ᶜ ⊆ (↑K.1 : Set ↑M)ᶜ from
            Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hKM')) (N + 1) g := rfl
    rw [hcU, hcV, hcK,
      relCohomSetCongr_relCohomRestrict hM'eq _ (N + 1) x,
      relCohomSetCongr_relCohomRestrict hM'eq _ (N + 1) y,
      relCohomSetCongr_relCohomRestrict hM'eq _ (N + 1) g,
      ← relCohomRestrict_relCohomSetCongr hcongrK
        (show (↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ
            ⊆ (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ from
          Set.inter_subset_inter hLUKU hLVKV) (N + 1) g]
    rw [sub_eq_add_neg, ZModModule.neg_eq_self, ← hxy]
  · obtain ⟨⟨α, β⟩, rfl⟩ := hp
    refine Module.DirectLimit.induction_on α (fun Kα a => ?_)
    refine Module.DirectLimit.induction_on β (fun Kβ b => ?_)
    rw [LinearMap.mem_ker, cscMvSum_of]
    -- enlarge both stage-compacts to a common L ⊆ U∪V, collapse the difference into one `of L`
    set L : CompactsIn (U ∪ V) :=
      CompactsIn.sup (compactsInIncl Set.subset_union_left Kα)
        (compactsInIncl Set.subset_union_right Kβ) with hL
    have hαL : compactsInIncl Set.subset_union_left Kα ≤ L := Subtype.coe_le_coe.mp le_sup_left
    have hβL : compactsInIncl Set.subset_union_right Kβ ≤ L :=
      Subtype.coe_le_coe.mp le_sup_right
    rw [show Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
            (cohomFW (U ∪ V) (N + 1)) (compactsInIncl Set.subset_union_left Kα) a
          = Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
              (cohomFW (U ∪ V) (N + 1)) L
              (cohomFW (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_left Kα) L hαL a)
        from (Module.DirectLimit.of_f).symm,
      show Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
            (cohomFW (U ∪ V) (N + 1)) (compactsInIncl Set.subset_union_right Kβ) b
          = Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
              (cohomFW (U ∪ V) (N + 1)) L
              (cohomFW (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_right Kβ) L hβL b)
        from (Module.DirectLimit.of_f).symm,
      ← map_sub, cscMvConnecting_of]
    -- abbreviations for the chosen split and the two stage classes pushed to L
    set KU := legSplitU U V hU hV L with hKU
    set KV := legSplitV U V hU hV L with hKV
    set g := (cohomFW (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_left Kα) L hαL) a -
      (cohomFW (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_right Kβ) L hβL) b with hg
    -- enlarge the chosen split to also contain Kα (in U) and Kβ (in V)
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
        = (↑(infCompact U V LU LV).1 : Set ↑M)ᶜ := by
      rw [infCompact_coe, Set.compl_inter]
    have hcongr : ((↑L.1 : Set ↑M)ᶜ)
        = (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ := by
      rw [hKU, hKV, legSplit_cover, Set.compl_union]
    rw [legδ_eq_enlarge U V hU hV N L LU LV hKULU hKVLV hLUKU hLVKV hJL hcongr g, rawLeg_apply]
    -- the inner connecting class vanishes: its argument is in the range of the per-pair MV sum
    suffices hkey : relCohomMvConnecting ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
        LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl N
        (relCohomRestrict (Set.inter_subset_inter hLUKU hLVKV) (N + 1)
          (relCohomSetCongr hcongr (N + 1) g)) = 0 by
      rw [hkey, map_zero]; exact map_zero _
    -- Kα ⊆ LU, Kβ ⊆ LV (so a, b restrict to the complement subspaces A=(↑LU)ᶜ, B=(↑LV)ᶜ)
    have hKαLU : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑Kα.1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLU]; exact Set.subset_union_right)
    have hKβLV : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑Kβ.1)ᶜ :=
      Set.compl_subset_compl.mpr (by rw [hcoeLV]; exact Set.subset_union_right)
    -- the per-pair MV-sum preimage: restrict a, b to A, B respectively
    set xa : RelativeCohomology ((↑LU.1 : Set ↑M)ᶜ) (N + 1) :=
      relCohomRestrict hKαLU (N + 1) a with hxa
    set yb : RelativeCohomology ((↑LV.1 : Set ↑M)ᶜ) (N + 1) :=
      relCohomRestrict hKβLV (N + 1) b with hyb
    have hsum : relCohomRestrict (Set.inter_subset_inter hLUKU hLVKV) (N + 1)
          (relCohomSetCongr hcongr (N + 1) g)
        = relCohomMvSum ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ) (N + 1) (xa, yb) := by
      rw [relCohomMvSum_apply, hxa, hyb,
        relCohomRestrict_trans Set.inter_subset_left hKαLU (N + 1) a,
        relCohomRestrict_trans Set.inter_subset_right hKβLV (N + 1) b, hg]
      erw [map_sub, map_sub]
      -- each LHS summand collapses to a single restriction of a (resp. b)
      have hca : (cohomFW (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_left Kα) L hαL) a
          = relCohomRestrict (show (↑L.1 : Set ↑M)ᶜ ⊆ (↑Kα.1)ᶜ from
              Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hαL)) (N + 1) a := rfl
      have hcb : (cohomFW (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_right Kβ) L hβL) b
          = relCohomRestrict (show (↑L.1 : Set ↑M)ᶜ ⊆ (↑Kβ.1)ᶜ from
              Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hβL)) (N + 1) b := rfl
      rw [hca, hcb,
        relCohomSetCongr_relCohomRestrict hcongr _ (N + 1) a,
        relCohomSetCongr_relCohomRestrict hcongr _ (N + 1) b,
        relCohomRestrict_trans (Set.inter_subset_inter hLUKU hLVKV) _ (N + 1) a,
        relCohomRestrict_trans (Set.inter_subset_inter hLUKU hLVKV) _ (N + 1) b,
        sub_eq_add_neg, ZModModule.neg_eq_self]
    rw [hsum, relCohomMvConnecting_relCohomMvSum]

end SKEFTHawking.SingularCSCMayerVietorisSumExact
