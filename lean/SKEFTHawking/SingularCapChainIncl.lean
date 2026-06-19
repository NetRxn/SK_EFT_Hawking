import Mathlib
import SKEFTHawking.SingularRelativeCap
import SKEFTHawking.SingularCapSupport

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-c1) — cap-chainIncl naturality + the cochain pullback

The cap product commutes with the subspace inclusion `sub S ↪ X` (the front/back Alexander–Whitney faces
are natural in `simplexIncl`, `frontFace_simplexIncl`/`backFace_simplexIncl`):
  `a ⌢ (chainIncl c) = chainIncl ((pullbackCochain a) ⌢ c)`,
where `pullbackCochain S k a` is the precomposition of the cochain `a` with `simplexIncl` (the cochain
pullback `sub S ↪ X`). This is the foundational lemma of the **connecting-square** cap×Kronecker bridge:
for an `S`-supported fundamental cycle `z = chainIncl z_sub` it makes the absolute cap `a ⌢ z` a genuine
`sub S`-cap `chainIncl ((pullbackCochain a) ⌢ z_sub)`, so the cohomology–homology Kronecker pairing
`⟨a', relativeDualityK … (mk a)⟩_{sub S}` becomes a cup pairing `⟨a' ∪ (pullbackCochain a), z_sub⟩` via
`kronecker_cup_cap` instantiated at `X := sub S` — with no cochain representative of
`relCohomMvConnecting` needed.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCap

namespace SKEFTHawking.SingularCapChainIncl

variable {X : TopCat} (S : Set X)

/-- **The cochain pullback** along the subspace inclusion `sub S ↪ X`: precompose with `simplexIncl`. -/
noncomputable def pullbackCochain (k : ℕ) (a : SingularCochain X k) : SingularCochain (sub S) k :=
  fun τ => a (simplexIncl S k τ)

@[simp] theorem pullbackCochain_apply (k : ℕ) (a : SingularCochain X k)
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))) :
    pullbackCochain S k a τ = a (simplexIncl S k τ) := rfl

/-- **Cap-chainIncl naturality**: `a ⌢ (chainIncl c) = chainIncl ((pullbackCochain a) ⌢ c)`. On a basis
`sub S`-simplex `τ`, both sides are `a(simplexIncl (frontₖ τ)) • [simplexIncl (backₘ τ)]`
(`frontFace`/`backFace` commute with `simplexIncl`). -/
theorem cap_chainIncl {k m : ℕ} (a : SingularCochain X k) (c : SingularChain (sub S) (k + m)) :
    cap a (chainIncl S (k + m) c) = chainIncl S m (cap (pullbackCochain S k a) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]
  | single τ s =>
      rw [chainIncl_single, cap_single_smul, cap_single_smul, capBasis, capBasis,
        pullbackCochain_apply, frontFace_simplexIncl, backFace_simplexIncl, map_smul, map_smul,
        chainIncl_single]

end SKEFTHawking.SingularCapChainIncl
