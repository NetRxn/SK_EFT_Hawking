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

/-- **Cap–cup adjunction** `⟨a ∪ b, c⟩ = ⟨b, a ⌢ c⟩` (chain level): the Kronecker pairing of a cup
product against a chain equals the pairing of the right factor against the cap product. Both sides use
the same Alexander–Whitney front/back split (`a` evaluated on the front `k`-face, `b`/the chain on the
back `l`-face), so on a basis simplex both equal `a(frontₖσ) · b(backₗσ)`. This is the algebraic bridge
from the cup pairing `(a,b) ↦ ⟨a∪b, z⟩` to the cap-with-`z` duality map — used both for the
`PoincareDual4Mid.nondeg` field (cap with `[M]`) and the connecting-square sub-`K` Kronecker bridge
(cap with a fundamental cycle, `SingularCapSubKDuality`). -/
theorem kronecker_cup_cap {Y : TopCat} {k l : ℕ} (a : SingularCochain Y k) (b : SingularCochain Y l)
    (c : SingularChain Y (k + l)) :
    kronecker (cup a b) c = kronecker b (cap a c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [map_zero]
  | add c d hc hd =>
      rw [kronecker_add_right, map_add, kronecker_add_right, hc, hd]
  | single σ s =>
      rw [cap_single_smul, capBasis, kronecker_single, kronecker_smul_right, kronecker_smul_right,
        kronecker_single, cup_apply]
      simp only [smul_eq_mul]; ring

/-- The **right cap** of an `(k+l)`-simplex `σ` against an `l`-cochain `b` on a *single basis* simplex:
`σ ⌢ʳ b = b(backₗ σ) • [frontₖ σ]` (evaluate `b` on the back `l`-face, keep the front `k`-face). The
mirror of `capBasis` with the front/back roles of cochain and chain swapped. -/
noncomputable def rcapBasis {Y : TopCat} {k l : ℕ} (b : SingularCochain Y l)
    (σ : (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk (k + l)))) : SingularChain Y k :=
  b (backFace σ) • Finsupp.single (frontFace σ) 1

/-- The **right cap product** `⌢ʳ : Cₖ₊ₗ × Cˡ → Cₖ`, the `ℤ/2`-linear extension of
`σ ↦ b(backₗ σ) • [frontₖ σ]`. Unlike the (left) `cap` it keeps the *front* face and evaluates the
cochain on the *back*; it is the adjoint used to extract the **left** cup factor in a Kronecker pairing
(`kronecker_cup_rcap`), where the non-commutative chain-level `cup` blocks `kronecker_cup_cap`. -/
noncomputable def rcap {Y : TopCat} {k l : ℕ} (b : SingularCochain Y l) :
    SingularChain Y (k + l) →ₗ[ZMod 2] SingularChain Y k :=
  Finsupp.linearCombination (ZMod 2) (rcapBasis b)

/-- The right cap on a scaled basis simplex. -/
theorem rcap_single_smul {Y : TopCat} {k l : ℕ} (b : SingularCochain Y l)
    (σ : (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk (k + l)))) (s : ZMod 2) :
    rcap (k := k) b (Finsupp.single σ s) = s • rcapBasis b σ := by
  rw [rcap, Finsupp.linearCombination_single]

/-- **Left-factor cap–cup adjunction** `⟨a ∪ b, z⟩ = ⟨a, z ⌢ʳ b⟩` (chain level): the Kronecker pairing of
a cup product against a chain equals the pairing of the **left** factor `a` against the right cap `z ⌢ʳ b`.
Both sides are `a(frontₖσ) · b(backₗσ)` on a basis simplex. Mirror of `kronecker_cup_cap` (which extracts
the right factor `b` via the left cap); needed because the chain-level `cup` is non-commutative, so the
left factor `a` (e.g. a connecting-map class whose only interface is a Kronecker adjunction) cannot be
reached through `kronecker_cup_cap`. -/
theorem kronecker_cup_rcap {Y : TopCat} {k l : ℕ} (a : SingularCochain Y k) (b : SingularCochain Y l)
    (z : SingularChain Y (k + l)) :
    kronecker (cup a b) z = kronecker a (rcap b z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp [map_zero]
  | add c d hc hd =>
      rw [kronecker_add_right, map_add, kronecker_add_right, hc, hd]
  | single σ s =>
      rw [rcap_single_smul, rcapBasis, kronecker_single, kronecker_smul_right, kronecker_smul_right,
        kronecker_single, cup_apply]
      simp only [smul_eq_mul]; ring

end SKEFTHawking.SingularCapChainIncl
