import Mathlib
import SKEFTHawking.SingularOpenDuality

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-M4 support) — the explicit cap-chain form of `legW`

The per-compact open-Poincaré-duality leg `legW K g = relativeDualityK ((↑K)ᶜ) W z_K g` reads, on a
cocycle representative `g_rep` of the relative cohomology class `g` (recall `cohomGW W k K =
RelativeCohomology ((↑K)ᶜ) k`), as the homology class of the `W`-supported cap `g_rep ⌢ z_K`:
  `legW K (mk g_rep) = [ (subspaceChainsEquiv W).symm (g_rep ⌢ z_K) ]`.

This is the M2-direct entry point for the connecting-square LHS: it presents `legW K g` as a literal
cap class, the form on which the absolute MV connecting `subHomConnecting = seamI ∘ mvDelta` can be
computed by its cover-partition chain action (`SingularMvDeltaPartition.mvDelta_cover_partition`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularLocalDualityK
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularOpenDuality
  SKEFTHawking.SingularOpenDualityCycle

namespace SKEFTHawking.SingularLegWCapForm

variable {X : TopCat} [T2Space ↑X]

/-- **The cap-chain form of the per-compact duality leg.** On a cocycle representative `g_rep` of a
relative cohomology class, `legW K (mk g_rep)` is the homology class of the `W`-supported cap
`g_rep ⌢ z_K` (with `z_K = fundCycleW`, the per-`K` fundamental cycle of the global ancestor `z₀`). -/
theorem legW_mk {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : CompactsIn W) (g_rep : LinearMap.ker (relCoboundaryₗ ((↑K.1 : Set ↑X)ᶜ) k)) :
    legW hW z₀ hz₀ K (RelativeCohomology.mk ((↑K.1 : Set ↑X)ᶜ) k g_rep)
      = Homology.mk (sub W) (m + 1)
          ⟨pullbackDualityₗ ((↑K.1 : Set ↑X)ᶜ) W (fundCycleW hW z₀ hz₀ K)
              (fundCycleW_mem_W hW z₀ hz₀ K) g_rep,
            pullbackDualityₗ_mem_cycles ((↑K.1 : Set ↑X)ᶜ) W (fundCycleW hW z₀ hz₀ K)
              (fundCycleW_mem_W hW z₀ hz₀ K) (fundCycleW_boundary hW z₀ hz₀ K) g_rep⟩ :=
  rfl

end SKEFTHawking.SingularLegWCapForm
