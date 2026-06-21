import Mathlib
import SKEFTHawking.SingularSubspaceChainsEquiv

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — chainIncl agreement on a shared support

`chainIncl_symm_agree`: an `X`-chain `x` supported in BOTH `A` and `B` has the same `sub`-realization
inclusion either way — `chainIncl A ((equivₐ).symm x) = chainIncl B ((equiv_b).symm x)` (both equal `x`).
A trivial consequence of `chainIncl_subspaceChainsEquiv_symm` (the inclusion inverts the pull-back), but
the reusable shape for any two-cover chain identity where a single ambient chain is realized through two
different cover sets — e.g. the connecting-square `hRHS` where the shared `rcap ωrep z₀` V-part lives in
`U∩V ∩ legSplitVᶜ` and is realized via both `chainIncl (U∩V)` and `chainIncl legSplitVᶜ`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularSubspaceChainsEquiv

namespace SKEFTHawking.SingularChainInclAgree

variable {X : TopCat}

/-- **chainIncl agreement on a shared support**: a chain `x` supported in both `A` and `B` realizes the
same ambient chain through either cover set. -/
theorem chainIncl_symm_agree {A B : Set ↑X} {n : ℕ} (x : SingularChain X n)
    (hxA : x ∈ subspaceChains A n) (hxB : x ∈ subspaceChains B n) :
    chainIncl A n ((subspaceChainsEquiv A n).symm ⟨x, hxA⟩)
      = chainIncl B n ((subspaceChainsEquiv B n).symm ⟨x, hxB⟩) := by
  rw [chainIncl_subspaceChainsEquiv_symm, chainIncl_subspaceChainsEquiv_symm]

end SKEFTHawking.SingularChainInclAgree
