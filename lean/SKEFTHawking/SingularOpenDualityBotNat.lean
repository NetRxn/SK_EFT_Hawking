import Mathlib
import SKEFTHawking.SingularOpenDualityBot
import SKEFTHawking.SingularLocalDualityKMono
import SKEFTHawking.SingularOpenDualityNat
import SKEFTHawking.SingularOpenDualityMVSquare

/-!
# Phase 5q.G (G1 PD-induction, the ₀-family, part 3) — bottom naturality + the bottom Δ/Σ squares

The `H₀`-level naturality of the bottom duality map under the compactly-supported extension
(`openDuality₀_cscOpenMonotone`, via the bottom `homOfSubset`-compat
`relativeDualityK₀_homOfSubset`), and the two bottom ladder squares `subHomDiag_openDuality₀` /
`subHomSum_openDuality₀` — the pos4/pos5 naturality squares of the `(3,0)`-center five-lemma
ladder (L2 notebook, 32nd–37th pushes).

Fund-family discipline (37th push): every `fundCycleW*`-lemma application carries explicit
`(k := k) (m := 0)` pins — unpinned `{k m}` forces the `?k+?m+1 =?= k+0+1` higher-order
unification explosion.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularLocalDualityKBot
  SKEFTHawking.SingularOpenDualityCycle SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularOpenDuality
  SKEFTHawking.SingularOpenDualityBot SKEFTHawking.SingularOpenDualityMVConnSquare
  SKEFTHawking.SingularFundCycleOpen SKEFTHawking.SingularMayerVietoris
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularOpenDualityMVSquare
  SKEFTHawking.SingularCSCMayerVietoris SKEFTHawking.SingularSubsetHomology
  SKEFTHawking.SingularCSCOpenMonotone SKEFTHawking.SingularFunctoriality
  SKEFTHawking.SingularMayerVietorisLES

namespace SKEFTHawking.SingularOpenDualityBotNat

variable {X : TopCat}

private theorem relB_pair_castChain' {a b : ℕ} (e : a = b) {S : Set ↑X}
    (x y : SingularChain X a)
    (h : RelativeChain.mk S a x + RelativeChain.mk S a y ∈ relBoundaries S a) :
    RelativeChain.mk S b (castChain e x) + RelativeChain.mk S b (castChain e y)
      ∈ relBoundaries S b := by
  subst e; rw [castChain_eq, castChain_eq]; exact h

/-- **Bottom `homOfSubset`-naturality of `relativeDualityK₀`** (the `m = 0` analogue of
`relativeDualityK_homOfSubset`): enlarging the carrier `W ⊆ W'` with the cycle fixed commutes
with the bottom duality map through `homOfSubset` at `H₀`. -/
theorem relativeDualityK₀_homOfSubset {k : ℕ} {S W W' : Set ↑X} (h : W ⊆ W')
    (z : SingularChain X (k + 1)) (hzW : z ∈ subspaceChains W (k + 1))
    (hzW' : z ∈ subspaceChains W' (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChains S k)
    (x : RelativeCohomology S (k + 1)) :
    homOfSubset h 0 (relativeDualityK₀ S W k z hzW hzS x)
      = relativeDualityK₀ S W' k z hzW' hzS x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk a : RelativeCohomology S (k + 1))
      = RelativeCohomology.mk S (k + 1) a from rfl,
    relativeDualityK₀_mk, relativeDualityK₀_mk, homOfSubset,
    SKEFTHawking.SingularFunctoriality.Homology.map_mk]
  congr 1
  apply Subtype.ext
  rw [cyclesMap_coe]
  apply chainIncl_injective W' 0
  rw [chainIncl_pullbackDualityₗ₀,
    show chainIncl W' 0 (SingularFunctoriality.mapChain (subInclCM h) 0
        (pullbackDualityₗ₀ S W z hzW a))
      = chainIncl W 0 (pullbackDualityₗ₀ S W z hzW a) from by
      rw [← mapChain_ambIncl W', ← SingularFunctoriality.mapChain_comp,
        show (ambIncl W').comp (subInclCM h) = ambIncl W from ContinuousMap.ext fun _ => rfl,
        mapChain_ambIncl],
    chainIncl_pullbackDualityₗ₀]

/-- **`D_W⁰` naturality** with the compactly-supported extension (the bottom `Δ`/`Σ` ladder-square
engine): `D⁰_{W'} ∘ cscOpenMonotone = homOfSubset ∘ D⁰_W`. -/
theorem openDuality₀_cscOpenMonotone [T2Space ↑X] {k : ℕ} {W W' : Set ↑X}
    (hW : IsOpen W) (hW' : IsOpen W') (h : W ⊆ W')
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (α : CompactlySupportedCohomologyOpen W (k + 1)) :
    openDuality₀ hW' z₀ hz₀ (cscOpenMonotone h (k + 1) α)
      = homOfSubset h 0 (openDuality₀ hW z₀ hz₀ α) := by
  induction α using Module.DirectLimit.induction_on with
  | _ K a =>
    rw [cscOpenMonotone_of, openDuality₀_of, openDuality₀_of, legW₀, legW₀]
    refine Eq.trans ?_ (relativeDualityK₀_homOfSubset h (fundCycleW₀ hW z₀ hz₀ K)
      (fundCycleW₀_mem_W hW z₀ hz₀ K)
      (SKEFTHawking.SingularMayerVietoris.subspaceChains_mono h (k + 1)
        (fundCycleW₀_mem_W hW z₀ hz₀ K)) (fundCycleW₀_boundary hW z₀ hz₀ K) a).symm
    refine relativeDualityK₀_cycle_compat_relB (fundCycleW₀ hW' z₀ hz₀ (compactsInIncl h K))
      (fundCycleW₀ hW z₀ hz₀ K) (fundCycleW₀_mem_W hW' z₀ hz₀ (compactsInIncl h K))
      (SKEFTHawking.SingularMayerVietoris.subspaceChains_mono h (k + 1)
        (fundCycleW₀_mem_W hW z₀ hz₀ K))
      (fundCycleW₀_boundary hW' z₀ hz₀ (compactsInIncl h K))
      (fundCycleW₀_boundary hW z₀ hz₀ K)
      (interiors_cover_of_compact_subset_open K.1.isCompact' hW' (K.2.trans h)) ?_ a
    -- the relB glue at the native (k+0+1)-spelling, transported once through castChain
    have hglue : RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
          (fundCycleW (k := k) (m := 0) hW' z₀ hz₀ (compactsInIncl h K))
        + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
          (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)
        ∈ relBoundaries ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) := by
      have hA := fundCycleW_relHomologous (k := k) (m := 0) hW z₀ hz₀ K
      have hB : RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
          (z₀ + fundCycleW (k := k) (m := 0) hW' z₀ hz₀ (compactsInIncl h K))
          ∈ relBoundaries ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) := by
        have hK'c : (↑(compactsInIncl h K).1 : Set ↑X)ᶜ = (↑K.1 : Set ↑X)ᶜ := rfl
        show Submodule.Quotient.mk
            (z₀ + fundCycleW (k := k) (m := 0) hW' z₀ hz₀ (compactsInIncl h K))
          ∈ relBoundaries ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
        rw [Submodule.Quotient.mk_add]
        exact fundCycleW_relHomologous (k := k) (m := 0) hW' z₀ hz₀ (compactsInIncl h K)
      have heq : RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
            (fundCycleW (k := k) (m := 0) hW' z₀ hz₀ (compactsInIncl h K))
          + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
            (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)
          = (RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) z₀
              + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
                (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K))
            + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
              (z₀ + fundCycleW (k := k) (m := 0) hW' z₀ hz₀ (compactsInIncl h K)) := by
        simp only [RelativeChain.mk, Submodule.Quotient.mk_add]
        abel_nf
        simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
      rw [heq]
      exact Submodule.add_mem _ hA hB
    exact relB_pair_castChain' (a := k + 0 + 1) (b := k + 1) rfl _ _ hglue

/-- **The bottom `Δ` square**: `subHomDiag ∘ D⁰_{U∩V} = (D⁰_U ⊕ D⁰_V) ∘ cscMvDiag` at `H₀` —
the pos4/pos5 diag square of the `(3,0)`-ladder. -/
theorem subHomDiag_openDuality₀ [T2Space ↑X] {k : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (α : CompactlySupportedCohomologyOpen (U ∩ V) (k + 1)) :
    subHomDiag U V 0 (openDuality₀ (hU.inter hV) z₀ hz₀ α)
      = (openDuality₀ hU z₀ hz₀ (cscOpenMonotone Set.inter_subset_left (k + 1) α),
          openDuality₀ hV z₀ hz₀ (cscOpenMonotone Set.inter_subset_right (k + 1) α)) := by
  rw [subHomDiag, LinearMap.prod_apply]
  simp only [Function.prod_def]
  rw [
    openDuality₀_cscOpenMonotone (hU.inter hV) hU Set.inter_subset_left z₀ hz₀,
    openDuality₀_cscOpenMonotone (hU.inter hV) hV Set.inter_subset_right z₀ hz₀]

/-- **The bottom `Σ` square**: `D⁰_{U∪V} ∘ cscMvSum = subHomSum ∘ (D⁰_U ⊕ D⁰_V)` at `H₀`. -/
theorem subHomSum_openDuality₀ [T2Space ↑X] {k : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (αU : CompactlySupportedCohomologyOpen U (k + 1))
    (αV : CompactlySupportedCohomologyOpen V (k + 1)) :
    openDuality₀ (hU.union hV) z₀ hz₀ (cscMvSum U V (k + 1) (αU, αV))
      = subHomSum U V 0 (openDuality₀ hU z₀ hz₀ αU, openDuality₀ hV z₀ hz₀ αV) := by
  rw [cscMvSum, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, map_sub,
    openDuality₀_cscOpenMonotone hU (hU.union hV) Set.subset_union_left z₀ hz₀,
    openDuality₀_cscOpenMonotone hV (hU.union hV) Set.subset_union_right z₀ hz₀, subHomSum,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply]

end SKEFTHawking.SingularOpenDualityBotNat
