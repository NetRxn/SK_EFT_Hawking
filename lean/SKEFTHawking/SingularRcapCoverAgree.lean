import Mathlib
import SKEFTHawking.SingularRcapRelHomology
import SKEFTHawking.SingularChainInclAgree

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — rcap cover-realization agreement (BRICK 2 starter)

The two-cover bridge residual `hcross` reconciles a `(U∪V)`-leg right cap with a `(U∩V)`-leg right cap
under the MV-connecting `relMvDelta`. A first piece of the cover reconciliation: when a realized right
cap `chainIncl A (a' ⌢ʳ z_sub)` happens to be supported in a SECOND cover set `B` as well, its
ambient chain (hence its relative homology class over any `S`) is the same whether realized through `A`
or through `B`. This is the `rcap`-class lift of `SingularChainInclAgree.chainIncl_symm_agree`, the shape
the `val⁻¹V`-vs-`legSplitVᶜ` reconciliation needs: a single ambient right-cap chain realized through two
different cover sets gives one relative homology class.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularCapChainIncl SKEFTHawking.SingularSubspaceChainsEquiv
  SKEFTHawking.SingularCapSubKDuality SKEFTHawking.SingularChainInclAgree

namespace SKEFTHawking.SingularRcapCoverAgree

variable {X : TopCat}

/-- **Ambient agreement of a right cap realized through two cover sets.** If the realized right cap
`chainIncl A (a' ⌢ʳ z_sub)` (with `z` an `A`-supported `(k+1+m+1)`-chain) is also supported in `B`, then
realizing it directly through `B` (via the `B`-pullback of the same ambient chain) gives the SAME ambient
chain. The `rcap`-level instance of `chainIncl_symm_agree`. -/
theorem chainIncl_rcap_cover_agree {k m : ℕ} {A B : Set ↑X}
    (z : SingularChain X (k + 1 + m + 1)) (hzA : z ∈ subspaceChains A (k + 1 + m + 1))
    (a' : LinearMap.ker (coboundaryₗ (sub A) (m + 1)))
    (hxB : chainIncl A (k + 1) (rcap a'.1 ((subspaceChainsEquiv A (k + 1 + m + 1)).symm ⟨z, hzA⟩))
      ∈ subspaceChains B (k + 1)) :
    chainIncl A (k + 1) (rcap a'.1 ((subspaceChainsEquiv A (k + 1 + m + 1)).symm ⟨z, hzA⟩))
      = chainIncl B (k + 1)
        ((subspaceChainsEquiv B (k + 1)).symm
          ⟨chainIncl A (k + 1) (rcap a'.1 ((subspaceChainsEquiv A (k + 1 + m + 1)).symm ⟨z, hzA⟩)),
            hxB⟩) := by
  rw [chainIncl_subspaceChainsEquiv_symm]

/-- **Relative homology class agreement of a right cap realized through two cover sets.** With the same
hypotheses, the relative homology class over `S` of the `A`-realized right cap equals the class of its
`B`-realization. (Both have the *same* ambient relative cycle, by `chainIncl_rcap_cover_agree`, so the
classes coincide.) The class-level reconciliation tool for the bridge's `val⁻¹V`-vs-`legSplitVᶜ` step. -/
theorem relHomology_mk_chainIncl_rcap_cover_agree {k m : ℕ} {A B S : Set ↑X}
    (z : SingularChain X (k + 1 + m + 1)) (hzA : z ∈ subspaceChains A (k + 1 + m + 1))
    (a' : LinearMap.ker (coboundaryₗ (sub A) (m + 1)))
    (hxB : chainIncl A (k + 1) (rcap a'.1 ((subspaceChainsEquiv A (k + 1 + m + 1)).symm ⟨z, hzA⟩))
      ∈ subspaceChains B (k + 1))
    (hcycA : RelativeChain.mk S (k + 1)
        (chainIncl A (k + 1) (rcap a'.1 ((subspaceChainsEquiv A (k + 1 + m + 1)).symm ⟨z, hzA⟩)))
      ∈ relCycles S (k + 1))
    (hcycB : RelativeChain.mk S (k + 1)
        (chainIncl B (k + 1)
          ((subspaceChainsEquiv B (k + 1)).symm
            ⟨chainIncl A (k + 1) (rcap a'.1 ((subspaceChainsEquiv A (k + 1 + m + 1)).symm ⟨z, hzA⟩)),
              hxB⟩))
      ∈ relCycles S (k + 1)) :
    RelativeHomology.mk S (k + 1)
        ⟨RelativeChain.mk S (k + 1)
          (chainIncl A (k + 1) (rcap a'.1 ((subspaceChainsEquiv A (k + 1 + m + 1)).symm ⟨z, hzA⟩))),
          hcycA⟩
      = RelativeHomology.mk S (k + 1)
        ⟨RelativeChain.mk S (k + 1)
          (chainIncl B (k + 1)
            ((subspaceChainsEquiv B (k + 1)).symm
              ⟨chainIncl A (k + 1) (rcap a'.1 ((subspaceChainsEquiv A (k + 1 + m + 1)).symm ⟨z, hzA⟩)),
                hxB⟩)),
          hcycB⟩ := by
  congr 1
  exact Subtype.ext (congrArg (RelativeChain.mk S (k + 1)) (chainIncl_rcap_cover_agree z hzA a' hxB))

end SKEFTHawking.SingularRcapCoverAgree
