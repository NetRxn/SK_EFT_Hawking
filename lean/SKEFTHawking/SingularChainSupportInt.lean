/-
# Phase 5q.H (E1 integral topology) — the image (support) of an integral singular chain

Integral (`ZMod 2 → ℤ`) mirror of the `chainImage` helpers of `SingularChainSupport`. `chainImageInt c`
(the union of the realizations of `c`'s finitely many support simplices) depends ONLY on `c.support`, so
these are verbatim coefficient mirrors. Needed for the open-cover-induction homology-exhaustion step
(`§3` of `SingularOpenDualityMonotoneUnionInt`): a representing integral cycle has compact image, absorbed
into a stage of the monotone tower.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularExcisionIsoInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularExcisionIsoInt

namespace SKEFTHawking.SingularChainSupportInt

variable {X : TopCat}

/-- The **image of an integral singular chain** `c` — the union of the images of its (finitely many)
support simplices. -/
def chainImageInt {n : ℕ} (c : SingularChainInt X n) : Set ↑X :=
  ⋃ τ ∈ c.support, Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ)

/-- **An integral singular chain has compact image**: finitely many support simplices, each a continuous
image of the compact standard simplex `Δⁿ`. -/
theorem isCompact_chainImageInt {n : ℕ} (c : SingularChainInt X n) : IsCompact (chainImageInt c) := by
  refine c.support.finite_toSet.isCompact_biUnion (fun τ _ => ?_)
  exact isCompact_range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ).continuous

/-- A point lies in `chainImageInt c` iff it is in the image of some support simplex. -/
theorem mem_chainImageInt_iff {n : ℕ} (c : SingularChainInt X n) (x : ↑X) :
    x ∈ chainImageInt c ↔
      ∃ τ ∈ c.support, x ∈ Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) := by
  simp only [chainImageInt, Set.mem_iUnion, exists_prop]

/-- **`chainImageInt` is contained in any subspace the chain lives in**: if `c ∈ subspaceChainsInt S`
then every support simplex (hence the whole image) lands in `S`. -/
theorem chainImage_subset_of_mem_subspaceChainsInt {S : Set ↑X} {n : ℕ} {c : SingularChainInt X n}
    (hc : c ∈ subspaceChainsInt S n) : chainImageInt c ⊆ S := by
  intro x hx
  obtain ⟨τ, hτ, hxτ⟩ := (mem_chainImageInt_iff c x).mp hx
  exact range_of_mem_subspaceChainsInt hc hτ hxτ

end SKEFTHawking.SingularChainSupportInt
