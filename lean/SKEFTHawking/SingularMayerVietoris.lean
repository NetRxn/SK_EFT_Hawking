import Mathlib
import SKEFTHawking.SingularDisjointUnion

/-!
# Mayer–Vietoris: the chain-level intersection and sum

Toward Mayer–Vietoris (the engine of the fundamental-class gluing, Hatcher 3.26). The two submodules
`subspaceChains A`, `subspaceChains B` of `Cₙ(X)` satisfy:

* `subspaceChains A ⊓ subspaceChains B = subspaceChains (A ∩ B)` — a chain supported on `A`-valued AND
  `B`-valued simplices is supported on `(A∩B)`-valued ones (a simplex with image in both `A` and `B`
  has image in `A ∩ B`);
* monotonicity `A ⊆ B ⟹ subspaceChains A ≤ subspaceChains B`.

These are the algebra underlying the Mayer–Vietoris short exact sequence
`0 → C(A∩B) → C(A) ⊕ C(B) → C(A) + C(B) → 0`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcision SKEFTHawking.SingularDisjointUnion

namespace SKEFTHawking.SingularMayerVietoris

/-- **Subspace chains are monotone**: `A ⊆ B ⟹ subspaceChains A ≤ subspaceChains B`. -/
theorem subspaceChains_mono {X : TopCat} {A B : Set ↑X} (h : A ⊆ B) (n : ℕ) :
    subspaceChains (S := A) n ≤ subspaceChains (S := B) n := by
  rintro c ⟨a, rfl⟩
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a₁ a₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | single σ' x =>
      rw [chainIncl_single,
        show Finsupp.single (simplexIncl A n σ') x
          = x • Finsupp.single (simplexIncl A n σ') (1 : ZMod 2) by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ x
        (single_mem_subspaceChains_of_subordinate ((range_realize_simplexIncl A σ').trans h))

/-- **The Mayer–Vietoris intersection identity**: `subspaceChains A ⊓ subspaceChains B =
subspaceChains (A ∩ B)`. -/
theorem subspaceChains_inf {X : TopCat} (A B : Set ↑X) (n : ℕ) :
    subspaceChains (S := A) n ⊓ subspaceChains (S := B) n = subspaceChains (S := A ∩ B) n := by
  refine le_antisymm (fun c ⟨hcA, hcB⟩ => ?_)
    (le_inf (subspaceChains_mono Set.inter_subset_left n)
      (subspaceChains_mono Set.inter_subset_right n))
  -- every simplex in `support c` is `(A∩B)`-valued, so `c ∈ subspaceChains (A∩B)`
  rw [← Finsupp.sum_single c]
  refine Submodule.sum_mem _ fun τ hτ => ?_
  have hne : c τ ≠ 0 := Finsupp.mem_support_iff.mp hτ
  have hτA : τ ∈ Set.range (simplexIncl A n) := by
    obtain ⟨a, rfl⟩ := hcA
    by_contra hnr
    exact hne (by rw [chainIncl, Finsupp.lmapDomain_apply]; exact Finsupp.mapDomain_notin_range a τ hnr)
  have hτB : τ ∈ Set.range (simplexIncl B n) := by
    obtain ⟨b, rfl⟩ := hcB
    by_contra hnr
    exact hne (by rw [chainIncl, Finsupp.lmapDomain_apply]; exact Finsupp.mapDomain_notin_range b τ hnr)
  obtain ⟨σA, rfl⟩ := hτA
  obtain ⟨σB, hσB⟩ := hτB
  rw [show Finsupp.single (simplexIncl A n σA) (c (simplexIncl A n σA))
      = c (simplexIncl A n σA) • Finsupp.single (simplexIncl A n σA) (1 : ZMod 2) by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
  refine Submodule.smul_mem _ _ (single_mem_subspaceChains_of_subordinate ?_)
  rw [Set.subset_inter_iff]
  exact ⟨range_realize_simplexIncl A σA, hσB ▸ range_realize_simplexIncl B σB⟩

end SKEFTHawking.SingularMayerVietoris
