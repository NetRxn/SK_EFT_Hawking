/-
# Phase 5q.H (N5 witness tower) — the clopen homology splitting in EVERY degree (integral):
# `Hₙ(X;ℤ) ≅ Hₙ(U;ℤ) × Hₙ(Uᶜ;ℤ)` for clopen `U`

The product-homology arc's S⁰-type primitive, and the arc's next keystone after the
contractible-factor collapse (`SingularProdContractibleInt`): the `SphereProdHData` H₂ slice
routes through `H_{≤2}(S²×S¹)`-grade Mayer–Vietoris inputs whose polar-cover intersections have
TWO components (`S² × (two arcs) ≃ S² ⊔ S²`) — every such leg needs disjoint-union additivity of
integral homology in positive degrees, which this module supplies.

The degree-0 case is in-tree (`SingularLineMinusPointInt.splitH0IntEquiv`, §D). Both chain-level
inputs are ALREADY degree-generic there (`subspaceChainsInt_sup_compl_eq_top` /
`subspaceChainsInt_inf_compl_eq_bot` at every `k`); what was missing is the homology-level
positive-degree assembly, which needs one genuinely new ingredient over the degree-0 case: a
CYCLE's clopen components are cycles (`chainBoundary_split_components` — at degree 0 every chain
is a cycle, so §D never needed it). The injectivity core (`chainIncl_add_mem_boundaries_splitInt`)
generalizes verbatim (the argument was always degree-agnostic; only the boundary-witness degree
shifts): a boundary's clopen components are boundaries in their own subspaces.

* `splitHInt U n : Hₙ(U;ℤ) × Hₙ(Uᶜ;ℤ) →ₗ Hₙ(X;ℤ)` — the additivity map `(a,b) ↦ i_*a + i_*b`
  (every degree).
* `chainBoundary_split_components` — cycle components are cycles (disjoint supports at degree `n`).
* `chainIncl_add_mem_boundaries_splitAllInt` — boundary components are boundaries (every degree;
  the §D core's degree-generic form).
* `splitHInt_bijective` / **`splitHIntEquiv (hU : IsClopen U) (n) :
  Hₙ(U;ℤ) × Hₙ(Uᶜ;ℤ) ≃ₗ[ℤ] Hₙ(X;ℤ)`** — the splitting in every degree (degree 0 delegating to
  the in-tree §D equiv).

The mod-2 mirror relationship: the chain-level splitting inputs live mod-2 in
`SingularDisjointUnion` (same shape); mirroring this module is the same homology-layer
re-instantiation (`Homology.map`/`homIncl` mod-2 for the Int forms).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularLineMinusPointInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularLineMinusPointInt (subspaceChainsInt_sup_compl_eq_top
  subspaceChainsInt_inf_compl_eq_bot splitH0IntEquiv splitH0Int)

namespace SKEFTHawking.SingularClopenSplitInt

variable {X : TopCat} {U : Set ↑X}

/-- **The degree-`n` clopen additivity map** `Hₙ(U;ℤ) × Hₙ(Uᶜ;ℤ) → Hₙ(X;ℤ)`,
`(a, b) ↦ i_*(a) + i_*(b)` — the every-degree form of `splitH0Int`. -/
noncomputable def splitHInt (U : Set ↑X) (n : ℕ) :
    Homology (sub U) n × Homology (sub Uᶜ) n →ₗ[ℤ] Homology X n :=
  (homIncl U n).coprod (homIncl Uᶜ n)

/-- At degree 0 the additivity map IS the in-tree `splitH0Int`. -/
theorem splitHInt_zero (U : Set ↑X) : splitHInt U 0 = splitH0Int U := rfl

/-- **A cycle's clopen components are cycles**: if `chainIncl zU + chainIncl zUc` is a cycle, the
disjointness of the clopen supports at degree `n` (`inf = ⊥`) forces each component's boundary to
vanish separately. The genuinely new ingredient over degree 0 (where every chain is a cycle). -/
theorem chainBoundary_split_components {n : ℕ}
    (zU : SingularChainInt (sub U) (n + 1)) (zUc : SingularChainInt (sub Uᶜ) (n + 1))
    (hz : chainBoundary X n (chainIncl U (n + 1) zU + chainIncl Uᶜ (n + 1) zUc) = 0) :
    chainBoundary (sub U) n zU = 0 ∧ chainBoundary (sub Uᶜ) n zUc = 0 := by
  rw [map_add, ← chainIncl_chainBoundary, ← chainIncl_chainBoundary] at hz
  have hkey : chainIncl U n (chainBoundary (sub U) n zU)
      = chainIncl Uᶜ n (-(chainBoundary (sub Uᶜ) n zUc)) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left hz
  have hmem : chainIncl U n (chainBoundary (sub U) n zU)
      ∈ subspaceChainsInt (S := U) n ⊓ subspaceChainsInt (S := Uᶜ) n :=
    ⟨⟨_, rfl⟩, hkey ▸ ⟨_, rfl⟩⟩
  rw [subspaceChainsInt_inf_compl_eq_bot, Submodule.mem_bot] at hmem
  refine ⟨chainIncl_injective U n (hmem.trans (map_zero _).symm), ?_⟩
  have h2 : -(chainBoundary (sub Uᶜ) n zUc) = 0 :=
    chainIncl_injective Uᶜ n ((hkey ▸ hmem).trans (map_zero _).symm)
  exact neg_eq_zero.mp h2

/-- **A boundary's clopen components are boundaries — every degree** (integral): the boundary
witness also splits across the clopen partition, and each split piece bounds the matching
component (disjoint supports). The degree-generic form of the §D core
`chainIncl_add_mem_boundaries_splitInt`. -/
theorem chainIncl_add_mem_boundaries_splitAllInt (hU : IsClopen U) {n : ℕ}
    (zU : SingularChainInt (sub U) n) (zUc : SingularChainInt (sub Uᶜ) n)
    (h : chainIncl U n zU + chainIncl Uᶜ n zUc ∈ boundaries X n) :
    zU ∈ boundaries (sub U) n ∧ zUc ∈ boundaries (sub Uᶜ) n := by
  obtain ⟨w, hw⟩ := h
  have hwsplit : w ∈ subspaceChainsInt (S := U) (n + 1) ⊔ subspaceChainsInt (S := Uᶜ) (n + 1) := by
    rw [subspaceChainsInt_sup_compl_eq_top hU]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hwsplit
  obtain ⟨_, ⟨wU, rfl⟩, _, ⟨wUc, rfl⟩, hwsum⟩ := hwsplit
  rw [← hwsum, map_add, ← chainIncl_chainBoundary, ← chainIncl_chainBoundary] at hw
  set bU := chainBoundary (sub U) n wU
  set bUc := chainBoundary (sub Uᶜ) n wUc
  have hkey : chainIncl U n (bU - zU) = chainIncl Uᶜ n (zUc - bUc) := by
    rw [map_sub, map_sub]
    linear_combination (norm := abel) hw
  have hmemU : chainIncl U n (bU - zU)
      ∈ subspaceChainsInt (S := U) n ⊓ subspaceChainsInt (S := Uᶜ) n :=
    ⟨⟨_, rfl⟩, hkey ▸ ⟨_, rfl⟩⟩
  rw [subspaceChainsInt_inf_compl_eq_bot, Submodule.mem_bot] at hmemU
  have hzU : zU = bU :=
    (sub_eq_zero.mp (chainIncl_injective U n (hmemU.trans (map_zero _).symm))).symm
  have hzUc : zUc = bUc :=
    sub_eq_zero.mp ((hkey ▸ hmemU).trans (map_zero _).symm |> chainIncl_injective Uᶜ n)
  exact ⟨⟨wU, hzU.symm⟩, ⟨wUc, hzUc.symm⟩⟩

/-- `splitHInt` is **surjective** in positive degrees: split the representing cycle across the
clopen partition (`sup = ⊤`); the components are cycles by `chainBoundary_split_components`. -/
theorem splitHInt_surjective_succ (hU : IsClopen U) (n : ℕ) :
    Function.Surjective (splitHInt U (n + 1)) := by
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (z : SingularChainInt X (n + 1))
      ∈ subspaceChainsInt (S := U) (n + 1) ⊔ subspaceChainsInt (S := Uᶜ) (n + 1) := by
    rw [subspaceChainsInt_sup_compl_eq_top hU]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hz
  obtain ⟨_, ⟨zU, rfl⟩, _, ⟨zUc, rfl⟩, hsum⟩ := hz
  have hzcyc : chainBoundary X n (chainIncl U (n + 1) zU + chainIncl Uᶜ (n + 1) zUc) = 0 := by
    rw [hsum]; exact z.2
  obtain ⟨hcU, hcUc⟩ := chainBoundary_split_components zU zUc hzcyc
  have hmemU : chainIncl U (n + 1) zU ∈ cycles X (n + 1) := by
    show chainIncl U (n + 1) zU ∈ LinearMap.ker (chainBoundary X n)
    rw [LinearMap.mem_ker, ← chainIncl_chainBoundary, hcU, map_zero]
  have hmemUc : chainIncl Uᶜ (n + 1) zUc ∈ cycles X (n + 1) := by
    show chainIncl Uᶜ (n + 1) zUc ∈ LinearMap.ker (chainBoundary X n)
    rw [LinearMap.mem_ker, ← chainIncl_chainBoundary, hcUc, map_zero]
  refine ⟨(Homology.mk (sub U) (n + 1) ⟨zU, LinearMap.mem_ker.mpr hcU⟩,
    Homology.mk (sub Uᶜ) (n + 1) ⟨zUc, LinearMap.mem_ker.mpr hcUc⟩), ?_⟩
  show homIncl U (n + 1) (Homology.mk (sub U) (n + 1) _)
      + homIncl Uᶜ (n + 1) (Homology.mk (sub Uᶜ) (n + 1) _) = Homology.mk X (n + 1) z
  rw [homIncl_mk, homIncl_mk,
    show z = (⟨chainIncl U (n + 1) zU, hmemU⟩ : cycles X (n + 1)) + ⟨chainIncl Uᶜ (n + 1) zUc, hmemUc⟩
      from Subtype.ext hsum.symm]
  rfl

/-- `splitHInt` is **injective** in positive degrees (via the degree-generic boundary-splitting
core). -/
theorem splitHInt_injective_succ (hU : IsClopen U) (n : ℕ) :
    Function.Injective (splitHInt U (n + 1)) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro ⟨a, b⟩ hab
  rw [LinearMap.mem_ker] at hab
  obtain ⟨zU, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨zUc, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have hcycU : chainIncl U (n + 1) (zU : SingularChainInt (sub U) (n + 1))
      ∈ cycles X (n + 1) := by
    show _ ∈ LinearMap.ker (chainBoundary X n)
    rw [LinearMap.mem_ker, ← chainIncl_chainBoundary,
      show chainBoundary (sub U) n (zU : SingularChainInt (sub U) (n + 1)) = 0 from zU.2, map_zero]
  have hcycUc : chainIncl Uᶜ (n + 1) (zUc : SingularChainInt (sub Uᶜ) (n + 1))
      ∈ cycles X (n + 1) := by
    show _ ∈ LinearMap.ker (chainBoundary X n)
    rw [LinearMap.mem_ker, ← chainIncl_chainBoundary,
      show chainBoundary (sub Uᶜ) n (zUc : SingularChainInt (sub Uᶜ) (n + 1)) = 0 from zUc.2,
      map_zero]
  have hab' : chainIncl U (n + 1) (zU : SingularChainInt (sub U) (n + 1))
      + chainIncl Uᶜ (n + 1) (zUc : SingularChainInt (sub Uᶜ) (n + 1))
      ∈ boundaries X (n + 1) := by
    have hrw : splitHInt U (n + 1) (Submodule.Quotient.mk zU, Submodule.Quotient.mk zUc)
        = Homology.mk X (n + 1) ⟨chainIncl U (n + 1) (zU : SingularChainInt (sub U) (n + 1))
            + chainIncl Uᶜ (n + 1) (zUc : SingularChainInt (sub Uᶜ) (n + 1)),
          (cycles X (n + 1)).add_mem hcycU hcycUc⟩ := rfl
    rw [hrw] at hab
    exact (Submodule.Quotient.mk_eq_zero
      ((boundaries X (n + 1)).submoduleOf (cycles X (n + 1)))).mp hab
  obtain ⟨hzU, hzUc⟩ := chainIncl_add_mem_boundaries_splitAllInt hU _ _ hab'
  rw [Submodule.mem_bot, Prod.ext_iff]
  exact ⟨(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr hzU),
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr hzUc)⟩

/-- **The clopen homology splitting — every degree** (integral):
`Hₙ(X;ℤ) ≅ Hₙ(U;ℤ) × Hₙ(Uᶜ;ℤ)` for clopen `U`. Degree 0 delegates to the in-tree
`splitH0IntEquiv`; positive degrees are this module's assembly. The S⁰-type disjoint-union
primitive of the product-homology arc. -/
noncomputable def splitHIntEquiv (hU : IsClopen U) (n : ℕ) :
    (Homology (sub U) n × Homology (sub Uᶜ) n) ≃ₗ[ℤ] Homology X n :=
  match n with
  | 0 => splitH0IntEquiv hU
  | m + 1 => LinearEquiv.ofBijective (splitHInt U (m + 1))
      ⟨splitHInt_injective_succ hU m, splitHInt_surjective_succ hU m⟩

end SKEFTHawking.SingularClopenSplitInt
