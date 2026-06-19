import Mathlib
import SKEFTHawking.SingularOpenDuality
import SKEFTHawking.SingularLocalDualityKMono
import SKEFTHawking.SingularCSCOpenMonotone

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-ii) — `D_W` naturality with the MV extension maps

`D_W : Hᵏ_c(W) → H_{n-k}(sub W)` is **natural** in the open `W`: for `W ⊆ W'` the compactly-supported
extension `cscOpenMonotone` commutes with the subspace-inclusion `homOfSubset` through the duality,
  `D_{W'} ∘ cscOpenMonotone (W ⊆ W') = homOfSubset (W ⊆ W') ∘ D_W`.
Per `K`-stage: `cscOpenMonotone` keeps the same compact `K`, so the left side caps the `W'`-fundamental
cycle `z'_K` while the right caps the `W`-fundamental cycle `z_K` (after `relativeDualityK_homOfSubset`
enlarges the support `W → W'`); both are relatively homologous to the common ancestor `z₀` in `(M, Kᶜ)`,
so the cycle-difference compatibility closes the square.

These are the `Δ`/`Σ` ladder squares of the Poincaré-duality `5`-lemma (`cscMvDiag`/`cscMvSum` are built
from `cscOpenMonotone`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularLocalDualityK
  SKEFTHawking.SingularLocalDualityKMono SKEFTHawking.SingularLocalDualityKCycle
  SKEFTHawking.SingularFundCycleOpen SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularCohomologyColimit SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularSubsetHomology SKEFTHawking.SingularCSCOpenMonotone
  SKEFTHawking.SingularOpenDualityCycle SKEFTHawking.SingularOpenDuality

namespace SKEFTHawking.SingularOpenDualityNat

variable {X : TopCat} [T2Space ↑X]

/-- A `ℤ/2`-module rearrangement (`2•c = 0`): `a + b = (c + b) + (c + a)`. -/
private theorem add_swap_zmod2 {Mod : Type*} [AddCommGroup Mod] [Module (ZMod 2) Mod] (a b c : Mod) :
    a + b = (c + b) + (c + a) := by
  rw [add_add_add_comm, ZModModule.add_self, zero_add, add_comm]

/-- **`D_W` naturality** with the compactly-supported extension `cscOpenMonotone` (the `Δ`/`Σ` ladder
squares): `D_{W'} ∘ cscOpenMonotone = homOfSubset ∘ D_W`. -/
theorem openDuality_cscOpenMonotone {k m : ℕ} {W W' : Set ↑X} (hW : IsOpen W) (hW' : IsOpen W')
    (h : W ⊆ W') (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (α : CompactlySupportedCohomologyOpen W k) :
    openDuality hW' z₀ hz₀ (cscOpenMonotone h k α)
      = homOfSubset h (m + 1) (openDuality hW z₀ hz₀ α) := by
  induction α using Module.DirectLimit.induction_on with
  | _ K a =>
    rw [cscOpenMonotone_of, openDuality_of, openDuality_of, legW, legW]
    refine Eq.trans ?_ (relativeDualityK_homOfSubset h (fundCycleW hW z₀ hz₀ K)
      (fundCycleW_mem_W hW z₀ hz₀ K)
      (SKEFTHawking.SingularMayerVietoris.subspaceChains_mono h (k + m + 1)
        (fundCycleW_mem_W hW z₀ hz₀ K)) (fundCycleW_boundary hW z₀ hz₀ K) a).symm
    -- cycle-difference: z'_K = fundCycleW hW' (compactsInIncl h K) vs z_K = fundCycleW hW K, at (↑K.1)ᶜ.
    refine relativeDualityK_cycle_compat_relB (fundCycleW hW' z₀ hz₀ (compactsInIncl h K))
      (fundCycleW hW z₀ hz₀ K) (fundCycleW_mem_W hW' z₀ hz₀ (compactsInIncl h K))
      (SKEFTHawking.SingularMayerVietoris.subspaceChains_mono h (k + m + 1)
        (fundCycleW_mem_W hW z₀ hz₀ K))
      (fundCycleW_boundary hW' z₀ hz₀ (compactsInIncl h K)) (fundCycleW_boundary hW z₀ hz₀ K)
      (interiors_cover_of_compact_subset_open K.1.isCompact' hW' (K.2.trans h)) ?_ a
    show RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW' z₀ hz₀ (compactsInIncl h K))
        + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW z₀ hz₀ K)
      ∈ relBoundaries ((↑K.1 : Set ↑X)ᶜ) (k + m + 1)
    have hA := fundCycleW_relHomologous hW z₀ hz₀ K
    have hB := fundCycleW_relHomologous hW' z₀ hz₀ (compactsInIncl h K)
    have heq : RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1)
          (fundCycleW hW' z₀ hz₀ (compactsInIncl h K))
        + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW z₀ hz₀ K)
      = (RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) z₀
          + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW z₀ hz₀ K))
        + (RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) z₀
          + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1)
            (fundCycleW hW' z₀ hz₀ (compactsInIncl h K))) :=
      add_swap_zmod2 _ _ _
    rw [heq]
    exact Submodule.add_mem _ hA hB

end SKEFTHawking.SingularOpenDualityNat
