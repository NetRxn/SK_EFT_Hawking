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
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcision

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

/-- **`chainImage` is contained in any subspace the chain lives in**: if `c ∈ subspaceChains S` then
every support simplex (hence the whole image) lands in `S`. -/
theorem chainImage_subset_of_mem_subspaceChains {S : Set ↑X} {n : ℕ} {c : SingularChain X n}
    (hc : c ∈ subspaceChains S n) : chainImage c ⊆ S := by
  intro x hx
  obtain ⟨τ, hτ, hxτ⟩ := (mem_chainImage_iff c x).mp hx
  exact range_of_mem_subspaceChains hc hτ hxτ

/-- **Separation of a relative cycle's boundary from a compact `K`** (the `Hᵢ(M|K)` colimit core):
for a chain `c` whose boundary `∂c` lies in `M∖K` (`subspaceChains Kᶜ`), and a compact `K` in a
locally-compact Hausdorff space, there is a **compact neighbourhood** `C` of `K` with `∂c` still in
`M∖C` (`subspaceChains Cᶜ`). So the relative cycle factors over the compact `C ⊇ K` — the surjectivity
half of `Hᵢ(M|K) = colim_C Hᵢ(M|C)`. -/
theorem exists_compact_boundary_avoiding [T2Space ↑X] [LocallyCompactSpace ↑X]
    {n : ℕ} {K : Set ↑X} (hK : IsCompact K) {c : SingularChain X (n + 1)}
    (hc : chainBoundary X n c ∈ subspaceChains Kᶜ n) :
    ∃ C : Set ↑X, IsCompact C ∧ K ⊆ interior C ∧ chainBoundary X n c ∈ subspaceChains Cᶜ n := by
  have himg : chainImage (chainBoundary X n c) ⊆ Kᶜ := chainImage_subset_of_mem_subspaceChains hc
  have hdisj : K ⊆ (chainImage (chainBoundary X n c))ᶜ := fun x hxK hx => himg hx hxK
  obtain ⟨C, hCcompact, hKC, hCsub⟩ :=
    exists_compact_between hK (isCompact_chainImage (chainBoundary X n c)).isClosed.isOpen_compl hdisj
  refine ⟨C, hCcompact, hKC, mem_subspaceChains_of_support (fun τ hτ x hx => ?_)⟩
  exact fun hxC => hCsub hxC ((mem_chainImage_iff _ x).mpr ⟨τ, hτ, hx⟩)

end SKEFTHawking.SingularChainSupport
