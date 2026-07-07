/-
# Phase 5q.H (E1 CSC-PD tower) — the explicit cap-chain form of `legW` (integral)

Integral mirror of `SingularLegWCapForm`. The per-compact open-Poincaré-duality leg `legW K g =
relativeDualityKInt ((↑K)ᶜ) W z_K g` reads, on a cocycle representative `g_rep` of the relative
cohomology class `g` (`cohomGWInt W k K = RelativeCohomologyInt ((↑K)ᶜ) k`), as the homology class of the
`W`-supported cap `pullbackDualityIntₗ (g_rep) z_K`:
  `legW K (mk g_rep) = [ pullbackDualityIntₗ ((↑K)ᶜ) W z_K g_rep ]`.

The M2-direct entry point for the integral connecting-square LHS: it presents `legW K g` as a literal
cap class, the form on which the absolute MV connecting `subHomConnectingInt = seamI ∘ mvDeltaInt` is
computed by its cover-partition chain action (`SingularMvDeltaPartitionInt.mvDelta_cover_partition`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularLocalDualityKInt (pullbackDualityIntₗ pullbackDualityIntₗ_mem_cycles)
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularOpenDualityCycleInt (fundCycleW fundCycleW_mem_W fundCycleW_boundary)

namespace SKEFTHawking.SingularLegWCapFormInt

variable {X : TopCat} [T2Space ↑X]

/-- **The cap-chain form of the per-compact duality leg** (integral). On a cocycle representative `g_rep`
of a relative cohomology class, `legW K (mk g_rep)` is the homology class of the `W`-supported cap
`pullbackDualityIntₗ ((↑K)ᶜ) W z_K g_rep` (with `z_K = fundCycleW`). Definitional (via
`relativeDualityKInt_mk`). -/
theorem legW_mkInt {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : CompactsIn W) (g_rep : LinearMap.ker (relCoboundaryIntₗ ((↑K.1 : Set ↑X)ᶜ) k)) :
    legW hW z₀ hz₀ K (RelativeCohomologyInt.mk ((↑K.1 : Set ↑X)ᶜ) k g_rep)
      = Homology.mk (sub W) (m + 1)
          ⟨pullbackDualityIntₗ ((↑K.1 : Set ↑X)ᶜ) W (fundCycleW hW z₀ hz₀ K)
              (fundCycleW_mem_W hW z₀ hz₀ K) g_rep,
            pullbackDualityIntₗ_mem_cycles ((↑K.1 : Set ↑X)ᶜ) W (fundCycleW hW z₀ hz₀ K)
              (fundCycleW_mem_W hW z₀ hz₀ K) (fundCycleW_boundary hW z₀ hz₀ K) g_rep⟩ :=
  rfl

end SKEFTHawking.SingularLegWCapFormInt
