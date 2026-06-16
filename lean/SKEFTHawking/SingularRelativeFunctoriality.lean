import Mathlib
import SKEFTHawking.SingularExcision
import SKEFTHawking.SingularPairLES
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularDisjointUnion

/-!
# Functoriality of relative homology

A **map of pairs** `φ : (X, A) → (Y, B)` (a continuous `φ : X → Y` with `φ(A) ⊆ B`) induces
`Hₙ(X, A) → Hₙ(Y, B)`: the pushforward `φ_#` sends `A`-chains to `B`-chains (an `A`-valued simplex
post-composed with `φ` is `B`-valued), so it descends to relative chains and then to relative
homology. A homeomorphism of pairs induces an isomorphism. This is the engine of the chart↔excision
bridge `Hₙ(M, M∖x) ≅ Hₙ(ℝⁿ, ℝⁿ∖0)` for the fundamental class.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularExcision
open SKEFTHawking.SingularDisjointUnion

namespace SKEFTHawking.SingularRelativeFunctoriality

/-- The realization of a pushforward simplex is `φ` post-composed with the realization. -/
theorem range_realize_mapSimplex {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    Set.range (Y.toSSetObjEquiv (op (SimplexCategory.mk n)) (mapSimplex φ σ))
      = φ '' Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) := by
  rw [mapSimplex, Equiv.apply_symm_apply, ← Set.range_comp]
  rfl

/-- **`φ_#` sends `A`-chains to `B`-chains** when `φ` maps `A` into `B`: an `A`-valued simplex
post-composed with `φ` is `B`-valued (`single_mem_subspaceChains_of_subordinate`). -/
theorem mapChain_mem_subspaceChains {X Y : TopCat} (φ : C(↑X, ↑Y)) {A : Set ↑X} {B : Set ↑Y}
    (hAB : Set.MapsTo φ A B) (n : ℕ) (c : SingularChain X n)
    (hc : c ∈ subspaceChains (S := A) n) :
    mapChain φ n c ∈ subspaceChains (S := B) n := by
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d₁ d₂ h₁ h₂ => rw [map_add, map_add]; exact Submodule.add_mem _ h₁ h₂
  | single σ' a =>
      rw [chainIncl_single, mapChain_single,
        show Finsupp.single (mapSimplex φ (simplexIncl A n σ')) a
          = a • Finsupp.single (mapSimplex φ (simplexIncl A n σ')) (1 : ZMod 2) by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      refine (subspaceChains (S := B) n).smul_mem a ?_
      apply single_mem_subspaceChains_of_subordinate (A := B)
      rw [range_realize_mapSimplex]
      exact (Set.image_mono (range_realize_simplexIncl A σ')).trans hAB.image_subset

variable {X Y : TopCat} (φ : C(↑X, ↑Y)) {A : Set ↑X} {B : Set ↑Y} (hAB : Set.MapsTo φ A B)

/-- **The induced map on relative chains** `C(X, A) → C(Y, B)` (the pushforward `φ_#` descended). -/
noncomputable def relMapChain (n : ℕ) : RelativeChain A n →ₗ[ZMod 2] RelativeChain B n :=
  Submodule.mapQ _ _ (mapChain φ n) (fun c hc => mapChain_mem_subspaceChains φ hAB n c hc)

@[simp] theorem relMapChain_mk (n : ℕ) (c : SingularChain X n) :
    relMapChain φ hAB n (RelativeChain.mk A n c) = RelativeChain.mk B n (mapChain φ n c) :=
  Submodule.mapQ_apply _ _ _ _

/-- **`φ_#` is a relative chain map**: it commutes with the relative boundary. -/
theorem relMapChain_relBoundary (n : ℕ) (x : RelativeChain A (n + 1)) :
    relBoundary B n (relMapChain φ hAB (n + 1) x) = relMapChain φ hAB n (relBoundary A n x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relBoundary B n (relMapChain φ hAB (n + 1) (RelativeChain.mk A (n + 1) c))
      = relMapChain φ hAB n (relBoundary A n (RelativeChain.mk A (n + 1) c))
  rw [relMapChain_mk, relBoundary_mk, relBoundary_mk, relMapChain_mk]
  exact congrArg (RelativeChain.mk B n) (chainBoundary_mapChain φ c)

end SKEFTHawking.SingularRelativeFunctoriality
