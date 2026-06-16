import Mathlib
import SKEFTHawking.SingularReducedH0

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

end SKEFTHawking.SingularDisjointUnion
