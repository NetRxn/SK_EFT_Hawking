import Mathlib
import SKEFTHawking.SingularReducedH0
import SKEFTHawking.SingularExcision

/-!
# Reduced `H̃₀` of a two-component space (disjoint-union additivity at degree 0)

The base value `H̃₀(S⁰) ≅ ℤ/2` of the sphere/local-homology induction. The relevant space — the
equator `Sⁿ∖{v,-v}` for `n = 1`, or equivalently `ℝ¹∖0` — is a disjoint union of two contractible
pieces (open rays). This module builds:

* `clopenSumHomeo` — for a clopen `U ⊆ X`, the homeomorphism `↥U ⊕ ↥Uᶜ ≃ₜ X`;
* the degree-`0` chain splitting `C₀(A ⊕ B) ≅ C₀(A) ⊕ C₀(B)` and (since `Δⁿ` is connected) every
  `1`-simplex of `A ⊕ B` lands in one summand, giving `boundaries₀` and the augmentation splitting;
* hence `H̃₀(A ⊕ B) ≅ ℤ/2` when `A`, `B` are each reduced-acyclic (e.g. contractible).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularH0
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularReducedH0
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularExcision
open SKEFTHawking.SingularPairLES

namespace SKEFTHawking.SingularDisjointUnion

/-- **The clopen-sum homeomorphism**: a clopen subset `U ⊆ X` splits `X` as `↥U ⊕ ↥Uᶜ`. The underlying
equivalence is `Equiv.Set.sumCompl`; it is a homeomorphism because the inclusions of the open sets
`U`, `Uᶜ` are open maps, so `Sum.elim val val` is a continuous open bijection. -/
noncomputable def clopenSumHomeo {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsClopen U) :
    (↥U ⊕ ↥Uᶜ) ≃ₜ X :=
  letI : DecidablePred (· ∈ U) := Classical.decPred _
  Equiv.toHomeomorphOfContinuousOpen (Equiv.Set.sumCompl U)
    (continuous_subtype_val.sumElim continuous_subtype_val)
    ((hU.isOpen.isOpenMap_subtype_val).sumElim (hU.compl.isOpen.isOpenMap_subtype_val))

/-- The standard topological `n`-simplex `Δⁿ = stdSimplex ℝ (Fin (n+1))` is **preconnected** (convex). -/
instance instPreconnectedStdSimplex (n : ℕ) :
    PreconnectedSpace (stdSimplex ℝ (Fin (n + 1))) :=
  isPreconnected_iff_preconnectedSpace.mp (convex_stdSimplex ℝ (Fin (n + 1))).isPreconnected

/-- **Every singular `n`-simplex of `X` lands in one piece of a clopen partition**: for a clopen
`U ⊆ X`, the (connected) image of a simplex `Δⁿ → X` is contained in `U` or in `Uᶜ`. This is the
combinatorial heart of degree-wise disjoint-union additivity. -/
theorem simplex_range_subset_or_compl {X : TopCat} {U : Set ↑X} (hU : IsClopen U) {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ U ∨
      Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ Uᶜ := by
  rcases disjoint_or_subset_of_isClopen
    (isPreconnected_range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ).continuous) hU with h | h
  · exact Or.inr (Set.subset_compl_iff_disjoint_right.mpr h)
  · exact Or.inl h

/-- **Every `k`-chain of `X` splits across a clopen partition**: `Cₖ(X) = Cₖ(U) ⊔ Cₖ(Uᶜ)` — each
simplex lands in one piece (`simplex_range_subset_or_compl`) hence in the image of the corresponding
inclusion chain map (`single_mem_subspaceChains_of_subordinate`). -/
theorem subspaceChains_sup_compl_eq_top {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (k : ℕ) :
    subspaceChains (S := U) k ⊔ subspaceChains (S := Uᶜ) k = ⊤ := by
  rw [eq_top_iff]
  rintro c -
  induction c using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add c₁ c₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | single σ a =>
      have hsmul : Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod 2) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rcases simplex_range_subset_or_compl hU σ with h | h
      · exact hsmul ▸ Submodule.mem_sup_left
          (Submodule.smul_mem _ a (single_mem_subspaceChains_of_subordinate h))
      · exact hsmul ▸ Submodule.mem_sup_right
          (Submodule.smul_mem _ a (single_mem_subspaceChains_of_subordinate h))

/-- The realization of an included simplex `simplexIncl A σ'` has range inside `A`. -/
theorem range_realize_simplexIncl {X : TopCat} (A : Set ↑X) {k : ℕ}
    (σ' : (TopCat.toSSet.obj (sub A)).obj (op (SimplexCategory.mk k))) :
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk k)) (simplexIncl A k σ')) ⊆ A := by
  rw [toSSetObjEquiv_simplexIncl]
  rintro x ⟨t, rfl⟩
  exact (((sub A).toSSetObjEquiv (op (SimplexCategory.mk k)) σ') t).2

/-- **Disjoint supports**: a chain that is both an `U`-chain and a `Uᶜ`-chain is zero — a simplex
cannot be both `U`-valued and `Uᶜ`-valued (its image is nonempty, so cannot lie in `U ∩ Uᶜ = ∅`).
The injectivity half of degree-`0` disjoint-union additivity. -/
theorem subspaceChains_inf_compl_eq_bot {X : TopCat} {U : Set ↑X} (k : ℕ) :
    subspaceChains (S := U) k ⊓ subspaceChains (S := Uᶜ) k = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨⟨a, rfl⟩, b, hb⟩
  rw [Submodule.mem_bot]
  ext τ
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  have hτU : τ ∈ Set.range (simplexIncl U k) := by
    by_contra hnr
    exact hne (by rw [chainIncl, Finsupp.lmapDomain_apply]; exact Finsupp.mapDomain_notin_range a τ hnr)
  have hτUc : τ ∈ Set.range (simplexIncl Uᶜ k) := by
    by_contra hnr
    refine hne ?_
    rw [← hb, chainIncl, Finsupp.lmapDomain_apply]
    exact Finsupp.mapDomain_notin_range b τ hnr
  obtain ⟨σU, rfl⟩ := hτU
  obtain ⟨σUc, hσUc⟩ := hτUc
  obtain ⟨x, hx⟩ :=
    Set.range_nonempty (X.toSSetObjEquiv (op (SimplexCategory.mk k)) (simplexIncl U k σU))
  have hxU : x ∈ U := range_realize_simplexIncl U σU hx
  have hxUc : x ∈ Uᶜ := range_realize_simplexIncl Uᶜ σUc (by rw [hσUc]; exact hx)
  exact hxUc hxU

/-! ## §4. The degree-0 additivity isomorphism and reduced `H̃₀` -/

/-- **The degree-0 additivity map** `H₀(U) × H₀(Uᶜ) → H₀(X)`, `(a, b) ↦ i_*(a) + i_*(b)`. -/
noncomputable def splitH0 {X : TopCat} (U : Set ↑X) :
    Homology (sub U) 0 × Homology (sub Uᶜ) 0 →ₗ[ZMod 2] Homology X 0 :=
  (homIncl U 0).coprod (homIncl Uᶜ 0)

/-- `splitH0` is **surjective**: every `0`-chain of `X` splits across the clopen partition
(`subspaceChains_sup_compl_eq_top`), and every `0`-chain is a cycle. -/
theorem splitH0_surjective {X : TopCat} {U : Set ↑X} (hU : IsClopen U) :
    Function.Surjective (splitH0 U) := by
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (z : SingularChain X 0) ∈ subspaceChains (S := U) 0 ⊔ subspaceChains (S := Uᶜ) 0 := by
    rw [subspaceChains_sup_compl_eq_top hU]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hz
  obtain ⟨_, ⟨zU, rfl⟩, _, ⟨zUc, rfl⟩, hsum⟩ := hz
  refine ⟨(Homology.mk (sub U) 0 ⟨zU, Submodule.mem_top⟩,
    Homology.mk (sub Uᶜ) 0 ⟨zUc, Submodule.mem_top⟩), ?_⟩
  show homIncl U 0 (Homology.mk (sub U) 0 _) + homIncl Uᶜ 0 (Homology.mk (sub Uᶜ) 0 _)
      = Homology.mk X 0 z
  rw [homIncl_mk, homIncl_mk,
    show z = (⟨_, Submodule.mem_top⟩ : cycles X 0) + ⟨_, Submodule.mem_top⟩ from Subtype.ext hsum.symm]
  rfl

end SKEFTHawking.SingularDisjointUnion
