/-
# Phase 5q.H (E1 CSC-PD tower) — Route B, fact-(i) stage 1 assembly (integral)

`fact_i_stage1Int` — the canonical-partition package in one existential. ℤ port of the mod-2
`SingularConnSquareCloseNC.fact_i_stage1`: assembles the three committed sub-bricks
(`exists_iterate_three_set_split_ambInt` → `cap_induced_partition_of_splitInt` →
`legW_iterate_cap_class_eqInt`) into: a cover-fine three-set split of `fundCycleW`, the cap-induced
canonical `{U,V}`-partition of the capped class, and the `legW = Homology.mk ⟨partition⟩` class equality.

This is the fact-(i) substrate the ℤ-native `hcoreG` (seam-match `hmv`) discharge consumes (together with
`fact_i_ambient_coreInt` and the descent bridge) — the mod-2 Route-B Kronecker top (`fact_i_discharge`/
`fact_ii`, built on the field-only β-pairing) does NOT port to ℤ, so the finish routes through the
committed descent bridge instead.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConnSquareFactIDischargeInt
import SKEFTHawking.SingularConnSquareCapInducedInt
import SKEFTHawking.SingularConnSquareLegWClassInt
import SKEFTHawking.SingularOpenDualityInt
import SKEFTHawking.SingularOpenDualityCycleInt
import SKEFTHawking.SingularSubdivisionInt
import SKEFTHawking.SingularRelativeMVInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityInt (legW)
open SKEFTHawking.SingularOpenDualityCycleInt (fundCycleW fundCycleW_mem_W fundCycleW_boundary)
open SKEFTHawking.SingularSubdivisionInt (singularSdInt)
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)

namespace SKEFTHawking.SingularConnSquareCloseNCInt

variable {X : TopCat} [T2Space ↑X]

/-- **Fact-(i) STAGE 1** (integral) — the canonical-partition package in ONE existential. ℤ port of the
mod-2 `SingularConnSquareCloseNC.fact_i_stage1`: assembles the three-set split
(`exists_iterate_three_set_split_ambInt`), the cap-induced canonical partition
(`cap_induced_partition_of_splitInt`), and the class-equality feed
(`legW_iterate_cap_class_eqInt`). -/
theorem fact_i_stage1Int {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ) (hLUU : LU ⊆ U) (hLVV : LV ⊆ V)
    {k m : ℕ}
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K₁ : CompactsIn (U ∪ V))
    (gW : LinearMap.ker (relCoboundaryIntₗ (((↑K₁.1 : Set ↑X))ᶜ) k)) :
    ∃ (μ : ℕ) (f₁ f₂ f₃ : SingularChainInt X (k + m + 1)),
      f₁ ∈ subspaceChainsInt (U ∩ LVᶜ) (k + m + 1)
      ∧ f₂ ∈ subspaceChainsInt (V ∩ LUᶜ) (k + m + 1)
      ∧ f₃ ∈ subspaceChainsInt (U ∩ V) (k + m + 1)
      ∧ (⇑(singularSdInt X (k + m + 1)))^[μ]
          (fundCycleW (hU.union hV) z₀ hz₀ K₁) = f₁ + f₂ + f₃
      ∧ ∃ (zA : SingularChainInt (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (m + 1))
          (zB : SingularChainInt (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (m + 1)),
          chainIncl (U ∪ V) (m + 1) (chainIncl _ (m + 1) zA) = capInt (m := m + 1) gW.1.1 f₁
          ∧ chainIncl (U ∪ V) (m + 1) (chainIncl _ (m + 1) zB)
              = capInt (m := m + 1) gW.1.1 (f₂ + f₃)
          ∧ ∃ (hcyc : chainIncl _ (m + 1) zA + chainIncl _ (m + 1) zB
                ∈ cycles (sub (U ∪ V)) (m + 1)),
              legW (hU.union hV) z₀ hz₀ K₁ (RelativeCohomologyInt.mk ((↑K₁.1 : Set ↑X)ᶜ) k gW)
                = Homology.mk (sub (U ∪ V)) (m + 1) ⟨_, hcyc⟩ := by
  have hgWc : coboundary X k gW.1.1 = 0 := by
    have hh := congrArg Subtype.val gW.2
    simpa only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] using hh
  obtain ⟨μ, f₁, f₂, f₃, hf₁, hf₂, hf₃, hIsplit⟩ :=
    exists_iterate_three_set_split_ambInt hU hV hLUc hLVc hLUU hLVV
      (fundCycleW (hU.union hV) z₀ hz₀ K₁)
      (fundCycleW_mem_W (hU.union hV) z₀ hz₀ K₁)
  have hsplit' : (⇑(singularSdInt X (k + m + 1)))^[μ]
      (fundCycleW (hU.union hV) z₀ hz₀ K₁) = f₁ + (f₂ + f₃) :=
    hIsplit.trans (add_assoc f₁ f₂ f₃)
  obtain ⟨zA, zB, hzA, hzB, hcyc⟩ :=
    cap_induced_partition_of_splitInt (U := U) (V := V) (k := k) (m := m) gW.1.1 hgWc gW.1.2
      (fundCycleW (hU.union hV) z₀ hz₀ K₁) μ
      (fundCycleW_boundary (hU.union hV) z₀ hz₀ K₁)
      f₁ (f₂ + f₃)
      (subspaceChainsInt_mono Set.inter_subset_left _ hf₁)
      (Submodule.add_mem _
        (subspaceChainsInt_mono Set.inter_subset_left _ hf₂)
        (subspaceChainsInt_mono Set.inter_subset_right _ hf₃))
      hsplit'
  refine ⟨μ, f₁, f₂, f₃, hf₁, hf₂, hf₃, hIsplit, zA, zB, hzA, hzB, hcyc, ?_⟩
  exact legW_iterate_cap_class_eqInt (hU.union hV) z₀ hz₀ K₁ gW μ _ hcyc
    (by rw [map_add, hzA, hzB, hsplit']; simp only [map_add])

end SKEFTHawking.SingularConnSquareCloseNCInt
