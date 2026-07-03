import Mathlib
import SKEFTHawking.SingularExcisionIso
import SKEFTHawking.SingularSubdivisionBot

/-!
# Phase 5q.G (G1 PD-induction, D⁰-substrate) — degree-0 excision

The `H₀`-instances of the excision machinery, floored at `H_{n+1}` in their generic forms:

* `relative_small_boundary₀` — the injective-half small-chains homotopy for a `0`-chain; SIMPLER
  than the generic thanks to `Sd = id` on `0`-chains (`w' := Sdᵐw` alone works — the boundary
  `∂w` is a `0`-chain, fixed by `Sdᵐ`, so the membership is the input `hw` verbatim);
* `excisionMap_injective₀` — excision is injective on `H₀`; the generic chase mirrors 1:1 with
  the cycle-side hypotheses dropped (`relCycles _ 0` conditions are vacuous — nothing below
  degree `0`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcision SKEFTHawking.SingularSubdivision
  SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularSubdivisionBot

namespace SKEFTHawking.SingularExcisionBot

variable {X : TopCat}

/-- **The relative small-chains homotopy at degree 0** (injective half): a `0`-chain `z` that is
a relative boundary `z ≡ ∂w (mod C(A))` is one by a *small* chain `w' := Sdᵐw` — since `∂w` is a
`0`-chain, `∂(Sdᵐw) = Sdᵐ(∂w) = ∂w` and the membership is the hypothesis verbatim. -/
theorem relative_small_boundary₀ {A : Set X} {𝒰 : Set (Set X)}
    (hcov : (⋃ U ∈ 𝒰, interior U) = Set.univ) {z : SingularChain X 0}
    {w : SingularChain X (0 + 1)} (hw : z + chainBoundary X 0 w ∈ subspaceChains A 0) :
    ∃ w' ∈ smallChains 𝒰 (0 + 1), z + chainBoundary X 0 w' ∈ subspaceChains A 0 := by
  obtain ⟨m, hm⟩ := exists_iterate_smallChains hcov w
  refine ⟨(⇑(singularSd X (0 + 1)))^[m] w, hm, ?_⟩
  rw [singularSd_iterate_chainBoundary, singularSd_iterate_zero_degree]
  exact hw

/-- **Excision is injective on `H₀`** (the degree-0 companion of `excisionMap_injective`): the
generic chase with the vacuous cycle-side hypotheses dropped and `relative_small_boundary₀` at
the small-chains step. -/
theorem excisionMap_injective₀ (A B : Set X)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) :
    Function.Injective (excisionMap A B 0) := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨c', hc'⟩ := Submodule.Quotient.mk_surjective _ (z' : RelativeChain (restr A B) 0)
  replace hc' : RelativeChain.mk (restr A B) 0 c' = (z' : RelativeChain (restr A B) 0) :=
    hc'
  rw [show (Submodule.Quotient.mk z' : RelativeHomology (restr A B) 0)
        = RelativeHomology.mk (restr A B) 0 z' from rfl, excisionMap_mk,
      RelativeHomology.mk_eq_zero_iff] at hh
  have hval : relChainIncl A B 0 (z' : RelativeChain (restr A B) 0)
      = RelativeChain.mk A 0 (chainIncl B 0 c') := by rw [← hc', relChainIncl_mk]
  have hh2 : RelativeChain.mk A 0 (chainIncl B 0 c') ∈ relBoundaries A 0 := by
    rw [← hval]; exact hh
  obtain ⟨wbar, hwbar⟩ := hh2
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wbar
  replace hwbar : RelativeChain.mk A 0 (chainBoundary X 0 w)
      = RelativeChain.mk A 0 (chainIncl B 0 c') := hwbar
  have hw_bound : chainIncl B 0 c' + chainBoundary X 0 w ∈ subspaceChains A 0 := by
    have hsub := (Submodule.Quotient.eq _).1 hwbar
    rw [show chainBoundary X 0 w - chainIncl B 0 c'
        = chainIncl B 0 c' + chainBoundary X 0 w by
          rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]; abel] at hsub
    exact hsub
  obtain ⟨w', hw'_small, hw'_bound⟩ := relative_small_boundary₀ hcov hw_bound
  rw [smallChains_two_eq] at hw'_small
  obtain ⟨wA, hwA, wB, hwB, hwAB⟩ := Submodule.mem_sup.mp hw'_small
  have hmemA : chainIncl B 0 c' + chainBoundary X 0 wB ∈ subspaceChains A 0 := by
    have h2 : chainIncl B 0 c'
        + (chainBoundary X 0 wA + chainBoundary X 0 wB) ∈ subspaceChains A 0 := by
      rw [← map_add, hwAB]; exact hw'_bound
    have h1 : chainBoundary X 0 wA ∈ subspaceChains A 0 :=
      chainBoundary_mem_subspaceChains A 0 wA hwA
    rw [show chainIncl B 0 c' + chainBoundary X 0 wB
        = (chainIncl B 0 c'
            + (chainBoundary X 0 wA + chainBoundary X 0 wB))
          - chainBoundary X 0 wA by abel]
    exact Submodule.sub_mem _ h2 h1
  have hmemB : chainIncl B 0 c' + chainBoundary X 0 wB ∈ subspaceChains B 0 :=
    Submodule.add_mem _ ⟨c', rfl⟩ (chainBoundary_mem_subspaceChains B 0 wB hwB)
  have hkey : chainIncl B 0 c' + chainBoundary X 0 wB ∈ subspaceChains (A ∩ B) 0 := by
    rw [← subspaceChains_inf]; exact Submodule.mem_inf.2 ⟨hmemA, hmemB⟩
  obtain ⟨v, rfl⟩ := hwB
  rw [← chainIncl_chainBoundary, ← map_add, chainIncl_mem_inter_iff] at hkey
  refine (RelativeHomology.mk_eq_zero_iff (restr A B) 0 z').2 ?_
  refine ⟨RelativeChain.mk (restr A B) (0 + 1) v, ?_⟩
  rw [relBoundary_mk, ← hc']
  show Submodule.Quotient.mk (chainBoundary (sub B) 0 v) = Submodule.Quotient.mk c'
  rw [Submodule.Quotient.eq,
    show chainBoundary (sub B) 0 v - c' = c' + chainBoundary (sub B) 0 v by
      rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]; abel]
  exact hkey

end SKEFTHawking.SingularExcisionBot
