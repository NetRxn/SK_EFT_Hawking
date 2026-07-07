/-
# Phase 5q.H (E1 CSC-PD tower) — integral degree-0 excision

Integral (`ZMod 2 → ℤ`) mirror of `SingularExcisionBot`. The `H₀`-instances of the excision machinery,
floored at `H_{n+1}` in their generic integral forms (`excisionMapInt_injective` is `n+1`-only):

* `relative_small_boundary₀Int` — the injective-half small-chains homotopy for a `0`-chain (SIMPLER than
  generic: `Sd = id` on `0`-chains via `singularSdInt_iterate_zero_degree`, so `w' := Sdᵐw` alone works);
* `excisionMap_injective₀Int` — excision is injective on `H₀`.

**The two ℤ-vs-mod-2 sign-fixes:** the mod-2 chase collapses `∂w − chainIncl c'` and `∂v − c'` to their
`+` forms via `ZModModule.add_self`; over ℤ these are honest, resolved by feeding the negated bounding chain
(`−w`, `−v`) so `chainIncl c' + ∂(−w) = −(∂w − chainIncl c')` is a genuine `subspaceChainsInt` element.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularSubdivisionBotInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularExcisionInt
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularSubdivisionInt
open SKEFTHawking.SingularSubdivisionBotInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularExcisionBotInt

variable {X : TopCat}

/-- **The integral relative small-chains homotopy at degree 0** (injective half): a `0`-chain `z` that is
a relative boundary `z ≡ ∂w (mod C(A))` is one by a *small* chain `w' := Sdᵐw` — since `∂w` is a `0`-chain,
`∂(Sdᵐw) = Sdᵐ(∂w) = ∂w`, so the membership is the hypothesis verbatim. -/
theorem relative_small_boundary₀Int {A : Set X} {𝒰 : Set (Set X)}
    (hcov : (⋃ U ∈ 𝒰, interior U) = Set.univ) {z : SingularChainInt X 0}
    {w : SingularChainInt X (0 + 1)} (hw : z + chainBoundary X 0 w ∈ subspaceChainsInt A 0) :
    ∃ w' ∈ smallChainsInt 𝒰 (0 + 1), z + chainBoundary X 0 w' ∈ subspaceChainsInt A 0 := by
  obtain ⟨m, hm⟩ := exists_iterate_smallChainsInt hcov w
  refine ⟨(⇑(singularSdInt X (0 + 1)))^[m] w, hm, ?_⟩
  rw [singularSdInt_iterate_chainBoundary, singularSdInt_iterate_zero_degree]
  exact hw

/-- **Excision is injective on `H₀`** (integral degree-0 companion of `excisionMapInt_injective`): the
generic chase with the vacuous cycle-side hypotheses dropped, `relative_small_boundary₀Int` at the
small-chains step, and the two honest ℤ signs restored. -/
theorem excisionMap_injective₀Int (A B : Set X)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) :
    Function.Injective (excisionMapInt A B 0) := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨c', hc'⟩ := Submodule.Quotient.mk_surjective _ (z' : RelativeChainInt (restr A B) 0)
  replace hc' : RelativeChainInt.mk (restr A B) 0 c' = (z' : RelativeChainInt (restr A B) 0) := hc'
  rw [show (Submodule.Quotient.mk z' : RelHomologyInt (restr A B) 0)
        = RelHomologyInt.mk (restr A B) 0 z' from rfl, excisionMapInt_mk,
      RelHomologyInt.mk_eq_zero_iff] at hh
  have hval : relChainInclInt A B 0 (z' : RelativeChainInt (restr A B) 0)
      = RelativeChainInt.mk A 0 (chainIncl B 0 c') := by rw [← hc', relChainInclInt_mk]
  have hh2 : RelativeChainInt.mk A 0 (chainIncl B 0 c') ∈ relBoundariesInt A 0 := by
    rw [← hval]; exact hh
  obtain ⟨wbar, hwbar⟩ := hh2
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wbar
  replace hwbar : RelativeChainInt.mk A 0 (chainBoundary X 0 w)
      = RelativeChainInt.mk A 0 (chainIncl B 0 c') := hwbar
  have hw_bound : chainIncl B 0 c' + chainBoundary X 0 (-w) ∈ subspaceChainsInt A 0 := by
    have hsub := (Submodule.Quotient.eq _).1 hwbar
    rw [map_neg, show chainIncl B 0 c' + -chainBoundary X 0 w
        = -(chainBoundary X 0 w - chainIncl B 0 c') by abel]
    exact Submodule.neg_mem _ hsub
  obtain ⟨w', hw'_small, hw'_bound⟩ := relative_small_boundary₀Int hcov hw_bound
  rw [smallChainsInt_two_eq] at hw'_small
  obtain ⟨wA, hwA, wB, hwB, hwAB⟩ := Submodule.mem_sup.mp hw'_small
  have hmemA : chainIncl B 0 c' + chainBoundary X 0 wB ∈ subspaceChainsInt A 0 := by
    have h2 : chainIncl B 0 c'
        + (chainBoundary X 0 wA + chainBoundary X 0 wB) ∈ subspaceChainsInt A 0 := by
      rw [← map_add, hwAB]; exact hw'_bound
    have h1 : chainBoundary X 0 wA ∈ subspaceChainsInt A 0 :=
      chainBoundary_mem_subspaceChainsInt A 0 wA hwA
    rw [show chainIncl B 0 c' + chainBoundary X 0 wB
        = (chainIncl B 0 c' + (chainBoundary X 0 wA + chainBoundary X 0 wB))
          - chainBoundary X 0 wA by abel]
    exact Submodule.sub_mem _ h2 h1
  have hmemB : chainIncl B 0 c' + chainBoundary X 0 wB ∈ subspaceChainsInt B 0 :=
    Submodule.add_mem _ ⟨c', rfl⟩ (chainBoundary_mem_subspaceChainsInt B 0 wB hwB)
  have hkey : chainIncl B 0 c' + chainBoundary X 0 wB ∈ subspaceChainsInt (A ∩ B) 0 := by
    rw [← subspaceChainsInt_inf]; exact Submodule.mem_inf.2 ⟨hmemA, hmemB⟩
  obtain ⟨v, rfl⟩ := hwB
  rw [← chainIncl_chainBoundary, ← map_add, chainIncl_mem_inter_iffInt] at hkey
  refine (RelHomologyInt.mk_eq_zero_iff (restr A B) 0 z').2 ?_
  refine ⟨RelativeChainInt.mk (restr A B) (0 + 1) (-v), ?_⟩
  rw [relBoundaryInt_mk, ← hc']
  show Submodule.Quotient.mk (chainBoundary (sub B) 0 (-v)) = Submodule.Quotient.mk c'
  rw [map_neg, Submodule.Quotient.eq, show -chainBoundary (sub B) 0 v - c'
      = -(c' + chainBoundary (sub B) 0 v) by abel]
  exact Submodule.neg_mem _ hkey

end SKEFTHawking.SingularExcisionBotInt
