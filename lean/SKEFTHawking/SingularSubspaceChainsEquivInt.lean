/-
# Phase 5q.H (E1 integral topology) — integral subspace-chains pullback: bounded ⟹ sub-K boundary

Integral (`ZMod 2 → ℤ`) mirror of the load-bearing lemma of `SingularSubspaceChainsEquiv`. The pullback
equiv `C(sub S; ℤ) ≃ₗ subspaceChainsInt S n` itself already exists on main as
`SingularRelHomologyInt.inclRangeEquiv` (with `chainIncl_inclRangeEquiv_symm`); this module adds the one
remaining consumer-facing fact the local-duality map `D_K` needs for its well-definedness:

**Pullback of an `S`-supported boundary with an `S`-supported bounding chain is a `sub S` boundary.** If
an `S`-supported `(n+1)`-chain `c` bounds an **`S`-supported** `(n+2)`-chain `d` (`∂d = c`), then the
pulled-back chain `(inclRangeEquiv S (n+1)).symm ⟨c⟩` is a boundary of the subspace `sub S` — its bounding
chain is the pullback of `d`. (`chainIncl` is an injective chain map, so the boundary identity transfers.)
This is what turns the cap-of-a-relative-coboundary — which is `S`-supported *and* bounds the `S`-supported
cap-of-the-cochain — into a genuine boundary of `H_{n-k}(sub S; ℤ)`, giving well-definedness of the
`H(sub S)`-valued duality map modulo coboundaries.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelHomologyInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)

namespace SKEFTHawking.SingularRelHomologyInt

variable {X : TopCat} (S : Set X)

/-- **Pullback of an `S`-supported boundary with an `S`-supported bounding chain is a `sub S` boundary.**
Integral mirror of `SingularSubspaceChainsEquiv.subspaceChainsEquiv_symm_mem_boundaries`, over the
on-main integral pullback equiv `inclRangeEquiv`. -/
theorem inclRangeEquiv_symm_mem_boundariesInt (n : ℕ) (c : SingularChainInt X (n + 1))
    (hc : c ∈ subspaceChainsInt S (n + 1)) (d : SingularChainInt X (n + 2))
    (hd : d ∈ subspaceChainsInt S (n + 2)) (hbd : chainBoundary X (n + 1) d = c) :
    (inclRangeEquiv S (n + 1)).symm ⟨c, hc⟩ ∈ boundaries (sub S) (n + 1) := by
  refine ⟨(inclRangeEquiv S (n + 2)).symm ⟨d, hd⟩, ?_⟩
  apply chainIncl_injective S (n + 1)
  rw [chainIncl_chainBoundary, chainIncl_inclRangeEquiv_symm, chainIncl_inclRangeEquiv_symm]
  exact hbd

end SKEFTHawking.SingularRelHomologyInt
