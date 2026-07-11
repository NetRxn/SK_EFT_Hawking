/-
# Phase 5q.H (E1 CSC-PD tower) — Route B, cap-induced canonical partition (integral, stage-1 sub-brick 2/3)

`cap_induced_partition_of_splitInt` — ℤ-realizer RE-derivation of the mod-2
`cap_induced_partition_of_split`: the mod-2 `subspaceChainsEquiv.symm ⟨_,_⟩` becomes an `obtain` from
`range (chainIncl _)` + the `val⁻¹`-descent `chainIncl_mem_subspaceChainsInt_iff`; the cycle step's
`(-1)^k` (from `capInt_cocycle_chainMap`) vanishes into `• 0`. Kernel-pure.
-/
import Mathlib
import SKEFTHawking.SingularConnSquareFactIDischargeInt
import SKEFTHawking.SingularCapSupportInt
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularSubdivisionInt
import SKEFTHawking.SingularRelativeMVInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularSubdivisionInt (singularSdInt singularSdInt_iterate_chainBoundary)
open SKEFTHawking.SingularCapSupportInt (capInt_mem_subspaceChainsInt)
open SKEFTHawking.SingularEuclideanCapIsoInt (capInt_subspaceChainInt_eq_zero relCochainInt_vanish
  relCochainsInt)
open SKEFTHawking.SingularExcisionIsoInt (chainIncl_mem_subspaceChainsInt_iff
  singularSdInt_iterate_mem_subspaceChainsInt)
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)

namespace SKEFTHawking.SingularConnSquareCloseNCInt

variable {X : TopCat} [T2Space ↑X]

omit [T2Space ↑X] in
/-- **Cap-induced canonical partition over a GIVEN split** (integral). ℤ re-derivation of the mod-2
`SingularConnSquareCloseNC.cap_induced_partition_of_split` on the ℤ realizer: the mod-2
`subspaceChainsEquiv.symm ⟨_, _⟩` is replaced by obtaining a witness from `range (chainIncl _)`, and
the `val⁻¹`-descent by `chainIncl_mem_subspaceChainsInt_iff`. The cycle step's `(-1)^k` (from
`capInt_cocycle_chainMap`) vanishes into `• 0`. -/
theorem cap_induced_partition_of_splitInt {U V S : Set ↑X} {k m : ℕ}
    (g : SingularCochainInt X k) (hgc : coboundary X k g = 0) (hgrel : g ∈ relCochainsInt S k)
    (f : SingularChainInt X (k + m + 1)) (μ : ℕ)
    (hbd : chainBoundary X (k + m) f ∈ subspaceChainsInt S (k + m))
    (fA fB : SingularChainInt X (k + m + 1))
    (hfA : fA ∈ subspaceChainsInt U (k + m + 1)) (hfB : fB ∈ subspaceChainsInt V (k + m + 1))
    (hsplit : (⇑(singularSdInt X (k + m + 1)))^[μ] f = fA + fB) :
    ∃ (zA : SingularChainInt (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (m + 1))
      (zB : SingularChainInt (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (m + 1)),
      chainIncl (U ∪ V) (m + 1) (chainIncl _ (m + 1) zA) = capInt (m := m + 1) g fA
      ∧ chainIncl (U ∪ V) (m + 1) (chainIncl _ (m + 1) zB) = capInt (m := m + 1) g fB
      ∧ chainIncl _ (m + 1) zA + chainIncl _ (m + 1) zB ∈ cycles (sub (U ∪ V)) (m + 1) := by
  have hgvan : ∀ τ, g (simplexIncl S k τ) = 0 := fun τ => relCochainInt_vanish S ⟨g, hgrel⟩ τ
  have hcA : capInt (m := m + 1) g fA ∈ subspaceChainsInt U (m + 1) :=
    capInt_mem_subspaceChainsInt U g hfA
  have hcB : capInt (m := m + 1) g fB ∈ subspaceChainsInt V (m + 1) :=
    capInt_mem_subspaceChainsInt V g hfB
  have hcA' : capInt (m := m + 1) g fA ∈ subspaceChainsInt (U ∪ V) (m + 1) :=
    subspaceChainsInt_mono Set.subset_union_left (m + 1) hcA
  have hcB' : capInt (m := m + 1) g fB ∈ subspaceChainsInt (U ∪ V) (m + 1) :=
    subspaceChainsInt_mono Set.subset_union_right (m + 1) hcB
  rw [subspaceChainsInt, LinearMap.mem_range] at hcA' hcB'
  obtain ⟨yA, hyA⟩ := hcA'
  obtain ⟨yB, hyB⟩ := hcB'
  have hyAmem : yA ∈ subspaceChainsInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (m + 1) :=
    (chainIncl_mem_subspaceChainsInt_iff U (U ∪ V) yA).mp (hyA.symm ▸ hcA)
  have hyBmem : yB ∈ subspaceChainsInt (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) (m + 1) :=
    (chainIncl_mem_subspaceChainsInt_iff V (U ∪ V) yB).mp (hyB.symm ▸ hcB)
  rw [subspaceChainsInt, LinearMap.mem_range] at hyAmem hyBmem
  obtain ⟨zA, hzA⟩ := hyAmem
  obtain ⟨zB, hzB⟩ := hyBmem
  refine ⟨zA, zB, ?_, ?_, ?_⟩
  · rw [hzA, hyA]
  · rw [hzB, hyB]
  · have hcycamb : chainBoundary X m (capInt (m := m + 1) g
        ((⇑(singularSdInt X (k + m + 1)))^[μ] f)) = 0 := by
      rw [capInt_cocycle_chainMap (m := m) g hgc _, singularSdInt_iterate_chainBoundary,
        capInt_subspaceChainInt_eq_zero (m := m) S g hgvan
          (singularSdInt_iterate_mem_subspaceChainsInt hbd μ), smul_zero]
    have hsum : chainIncl (U ∪ V) (m + 1)
        (chainIncl _ (m + 1) zA + chainIncl _ (m + 1) zB)
        = capInt (m := m + 1) g ((⇑(singularSdInt X (k + m + 1)))^[μ] f) := by
      rw [map_add, hzA, hzB, hyA, hyB, hsplit, map_add]
    refine LinearMap.mem_ker.mpr ?_
    apply chainIncl_injective (U ∪ V) m
    rw [chainIncl_chainBoundary, hsum, hcycamb, map_zero]

end SKEFTHawking.SingularConnSquareCloseNCInt
