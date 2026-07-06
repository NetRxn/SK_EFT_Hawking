/-
# Phase 5q.H (E1 integral topology) — `D_W` naturality with the MV extension maps (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularOpenDualityNat.openDuality_cscOpenMonotone`. The open
Poincaré-duality map `D_W : Hᵏ_c(W;ℤ) → H_{n-k}(sub W;ℤ)` is **natural** in the open `W`: for `W ⊆ W'` the
compactly-supported extension `cscOpenMonotoneInt` commutes with the subspace-inclusion `homOfSubsetInt`
through the duality,
  `D_{W'} ∘ cscOpenMonotoneInt (W ⊆ W') = homOfSubsetInt (W ⊆ W') ∘ D_W`.
Per `K`-stage: `cscOpenMonotoneInt` keeps the same compact `K` (`compactsInIncl`), so the left caps the
`W'`-fundamental cycle `z'_K` while the right caps the `W`-fundamental cycle `z_K` (after
`relativeDualityKInt_homOfSubset` enlarges the support `W → W'` at the fixed cycle `z_K`); both `z_K, z'_K`
are relatively homologous to the common ancestor `z₀` in `(M, Kᶜ)`, so the cycle-difference compatibility
`relativeDualityKInt_cycle_compat_relB` closes the square. The mod-2 `add_swap_zmod2` (`2•c = 0`) becomes
the honest `Submodule.sub_mem` identity `mk z'_K − mk z_K = (mk z₀ − mk z_K) − (mk z₀ − mk z'_K)` (as in
`SingularOpenDualityInt.legW_compat`). Note `(compactsInIncl h K).1 = K.1` definitionally, so both duality
legs share the same subspace `(↑K.1)ᶜ`.

These are the `Δ`/`Σ` ladder squares of the integral Poincaré-duality `5`-lemma (`cscMvDiagInt`/`cscMvSumInt`
are built from `cscOpenMonotoneInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityInt
import SKEFTHawking.SingularLocalDualityKMonoInt
import SKEFTHawking.SingularCSCOpenMonotoneInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularLocalDualityKInt
open SKEFTHawking.SingularLocalDualityKMonoInt
open SKEFTHawking.SingularOpenDualityCycleInt
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularCSCOpenMonotoneInt
open SKEFTHawking.SingularSubsetHomologyInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)
open SKEFTHawking.SingularFundCycleOpen (interiors_cover_of_compact_subset_open)

namespace SKEFTHawking.SingularOpenDualityNatInt

variable {X : TopCat} [T2Space ↑X]

/-- **`D_W` naturality** with the integral compactly-supported extension `cscOpenMonotoneInt` (the `Δ`/`Σ`
ladder squares of the integral PD `5`-lemma): `D_{W'} ∘ cscOpenMonotoneInt = homOfSubsetInt ∘ D_W`. -/
theorem openDuality_cscOpenMonotoneInt {k m : ℕ} {W W' : Set ↑X} (hW : IsOpen W) (hW' : IsOpen W')
    (h : W ⊆ W') (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (α : CompactlySupportedCohomologyOpenInt W k) :
    openDuality hW' z₀ hz₀ (cscOpenMonotoneInt h k α)
      = homOfSubsetInt h (m + 1) (openDuality hW z₀ hz₀ α) := by
  induction α using Module.DirectLimit.induction_on with
  | _ K a =>
    rw [cscOpenMonotoneInt_of, openDuality_of, openDuality_of, legW, legW]
    -- Step 1: enlarge the support `W → W'` at the fixed `W`-cycle `z_K = fundCycleW hW K`.
    refine Eq.trans ?_ (relativeDualityKInt_homOfSubset h (fundCycleW hW z₀ hz₀ K)
      (fundCycleW_mem_W hW z₀ hz₀ K)
      (subspaceChainsInt_mono h (k + m + 1) (fundCycleW_mem_W hW z₀ hz₀ K))
      (fundCycleW_boundary hW z₀ hz₀ K) a).symm
    -- Step 2: swap the cycle `z'_K = fundCycleW hW' (compactsInIncl h K)` → `z_K` at subspace `(↑K)ᶜ`.
    refine relativeDualityKInt_cycle_compat_relB (fundCycleW hW' z₀ hz₀ (compactsInIncl h K))
      (fundCycleW hW z₀ hz₀ K) (fundCycleW_mem_W hW' z₀ hz₀ (compactsInIncl h K))
      (subspaceChainsInt_mono h (k + m + 1) (fundCycleW_mem_W hW z₀ hz₀ K))
      (fundCycleW_boundary hW' z₀ hz₀ (compactsInIncl h K)) (fundCycleW_boundary hW z₀ hz₀ K)
      (interiors_cover_of_compact_subset_open K.1.isCompact' hW' (K.2.trans h)) ?_ a
    -- the rel-homology `mk z'_K − mk z_K ∈ relBoundaries (↑K)ᶜ` from the two ancestor rel-homologies.
    -- normalize the subspace `(↑(compactsInIncl h K).1)ᶜ → (↑K.1)ᶜ` (definitionally equal).
    show RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW' z₀ hz₀ (compactsInIncl h K))
        - RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) (fundCycleW hW z₀ hz₀ K)
      ∈ relBoundariesInt ((↑K.1 : Set ↑X)ᶜ) (k + m + 1)
    set S : Set ↑X := (↑K.1 : Set ↑X)ᶜ with hS
    have hA := fundCycleW_relHomologous hW z₀ hz₀ K
    have hB := fundCycleW_relHomologous hW' z₀ hz₀ (compactsInIncl h K)
    have heq : RelativeChainInt.mk S (k + m + 1) (fundCycleW hW' z₀ hz₀ (compactsInIncl h K))
          - RelativeChainInt.mk S (k + m + 1) (fundCycleW hW z₀ hz₀ K)
        = (RelativeChainInt.mk S (k + m + 1) z₀
              - RelativeChainInt.mk S (k + m + 1) (fundCycleW hW z₀ hz₀ K))
          - (RelativeChainInt.mk S (k + m + 1) z₀
              - RelativeChainInt.mk S (k + m + 1) (fundCycleW hW' z₀ hz₀ (compactsInIncl h K))) := by
      abel
    rw [heq]
    exact Submodule.sub_mem _ hA hB

end SKEFTHawking.SingularOpenDualityNatInt
