import Mathlib
import SKEFTHawking.SingularExcision

/-!
# Phase 5q.F (w₂-foundation) — singular chain image compactness

The foundation of the `Hᵢ(M | K)` direct-limit (Hatcher 3.27, step 3): a singular chain has only
finitely many support simplices, each the continuous image of the compact standard simplex, so its
**image** `chainImage c ⊆ X` is compact. For a relative cycle `z` of the pair `(M, M∖K)`, the
boundary `∂z` lies in `M∖K`, so `chainImage (∂z)` is a compact set disjoint from the compact `K` —
separable by open neighbourhoods, the key to representing a class of `Hᵢ(M|K)` over a compact
neighbourhood of `K`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.SingularChainSupport

variable {X : TopCat}

/-- The **image of a singular chain** `c` — the union of the images of its (finitely many) support
simplices `τ` (each the realization `Δⁿ → X`, `X.toSSetObjEquiv … τ`). -/
def chainImage {n : ℕ} (c : SingularChain X n) : Set ↑X :=
  ⋃ τ ∈ c.support, Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ)

/-- **A singular chain has compact image**: finitely many support simplices, each a continuous image
of the compact standard simplex `Δⁿ`. The compactness used (with manifold separation) to push a class
of `Hᵢ(M | K)` onto a compact neighbourhood of `K` — the `Hᵢ(M|K)` direct-limit foundation. -/
theorem isCompact_chainImage {n : ℕ} (c : SingularChain X n) : IsCompact (chainImage c) := by
  refine c.support.finite_toSet.isCompact_biUnion (fun τ _ => ?_)
  exact isCompact_range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ).continuous

/-- A point lies in `chainImage c` iff it is in the image of some support simplex. -/
theorem mem_chainImage_iff {n : ℕ} (c : SingularChain X n) (x : ↑X) :
    x ∈ chainImage c ↔ ∃ τ ∈ c.support, x ∈ Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) := by
  simp only [chainImage, Set.mem_iUnion, exists_prop]

end SKEFTHawking.SingularChainSupport
