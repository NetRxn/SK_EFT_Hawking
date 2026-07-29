/-
# Phase 5q.H (E1 CSC-PD tower) — integral bottom naturality + the bottom Δ/Σ squares

Integral (`ZMod 2 → ℤ`) mirror of `SingularOpenDualityBotNat`. The `H₀`-level naturality of the bottom
duality map `D_W⁰` under the compactly-supported extension (`openDuality₀Int_cscOpenMonotone`, via the
bottom `homOfSubsetInt`-compat `relativeDualityK₀Int_homOfSubset`), and the two bottom ladder squares
`subHomDiagInt_openDuality₀Int` (hc₄ of the integral PD bottom five-lemma) / `subHomSumInt_openDuality₀Int`.

**The ℤ-vs-mod-2 divergence:** the mod-2 `hglue` uses `z₀ + fundCycleW`/`ZModModule.add_self`; over ℤ this is
the honest DIFFERENCE `z₀ − fundCycleW` (`fundCycleW_relHomologous` is already stated as a difference over ℤ),
and the `relB` swap goes through the difference-form `relativeDualityK₀Int_cycle_compat_relB` +
`relB_pair_castChainInt`. `(compactsInIncl h K).1ᶜ = K.1ᶜ` by `rfl`, so no `relBoundaries_monoInt` is needed
here (unlike the K ≤ K' colimit-compat glue in `legW₀Int_compat`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityBotInt
import SKEFTHawking.SingularLocalDualityKMonoInt
import SKEFTHawking.SingularOpenDualityNatInt
import SKEFTHawking.SingularOpenDualityMVSquareInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularSubsetHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularConvexRadialBaseInt
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl)
open SKEFTHawking.SingularLocalDualityKBotInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCSCOpenMonotoneInt
open SKEFTHawking.SingularCSCMayerVietorisInt
open SKEFTHawking.SingularOpenDualityCycleInt
open SKEFTHawking.SingularOpenDualityBotInt
open SKEFTHawking.SingularOpenDualityMVConnSquareInt
open SKEFTHawking.SingularOpenDualityMVSquareInt
open SKEFTHawking.SingularFundCycleOpen (interiors_cover_of_compact_subset_open)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)

namespace SKEFTHawking.SingularOpenDualityBotNatInt

variable {X : TopCat}

/-- Local ℤ-difference `relB` transport (duplicate of `SingularOpenDualityBotInt`'s private helper,
mirroring the mod-2 `SingularOpenDualityBotNat.relB_pair_castChain'` convention). -/
private theorem relB_pair_castChainInt' {a b : ℕ} (e : a = b) {S : Set ↑X}
    (x y : SingularChainInt X a)
    (h : RelativeChainInt.mk S a x - RelativeChainInt.mk S a y ∈ relBoundariesInt S a) :
    RelativeChainInt.mk S b (castChainInt e x) - RelativeChainInt.mk S b (castChainInt e y)
      ∈ relBoundariesInt S b := by
  subst e; rw [castChainInt_eq, castChainInt_eq]; exact h

/-- **Bottom `homOfSubsetInt`-naturality of `relativeDualityK₀Int`** (the `m = 0` analogue of the general
`relativeDualityKInt_homOfSubset`): enlarging the carrier `W ⊆ W'` with the cycle fixed commutes with the
bottom duality map through `homOfSubsetInt` at `H₀`. -/
theorem relativeDualityK₀Int_homOfSubset {k : ℕ} {S W W' : Set ↑X} (h : W ⊆ W')
    (z : SingularChainInt X (k + 1)) (hzW : z ∈ subspaceChainsInt W (k + 1))
    (hzW' : z ∈ subspaceChainsInt W' (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChainsInt S k)
    (x : RelativeCohomologyInt S (k + 1)) :
    homOfSubsetInt h 0 (relativeDualityK₀Int S W k z hzW hzS x)
      = relativeDualityK₀Int S W' k z hzW' hzS x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk a : RelativeCohomologyInt S (k + 1))
      = RelativeCohomologyInt.mk S (k + 1) a from rfl,
    relativeDualityK₀Int_mk, relativeDualityK₀Int_mk, homOfSubsetInt, Homology.mapInt_mk]
  congr 1
  apply Subtype.ext
  rw [cyclesMapInt_coe]
  apply chainIncl_injective W' 0
  rw [chainIncl_pullbackDualityIntₗ₀,
    show chainIncl W' 0 (mapChainInt (subInclCM h) 0 (pullbackDualityIntₗ₀ S W z hzW a))
        = chainIncl W 0 (pullbackDualityIntₗ₀ S W z hzW a) from by
      rw [← mapChainInt_ambIncl W', ← mapChainInt_comp,
        show (ambIncl W').comp (subInclCM h) = ambIncl W from ContinuousMap.ext fun _ => rfl,
        mapChainInt_ambIncl],
    chainIncl_pullbackDualityIntₗ₀]

/-- **`D_W⁰` naturality** with the compactly-supported extension (the bottom `Δ`/`Σ` ladder-square
engine, ℤ): `D⁰_{W'} ∘ cscOpenMonotoneInt = homOfSubsetInt ∘ D⁰_W`. -/
theorem openDuality₀Int_cscOpenMonotone [T2Space ↑X] {k : ℕ} {W W' : Set ↑X}
    (hW : IsOpen W) (hW' : IsOpen W') (h : W ⊆ W')
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (α : CompactlySupportedCohomologyOpenInt W (k + 1)) :
    openDuality₀Int hW' z₀ hz₀ (cscOpenMonotoneInt h (k + 1) α)
      = homOfSubsetInt h 0 (openDuality₀Int hW z₀ hz₀ α) := by
  induction α using Module.DirectLimit.induction_on with
  | _ K a =>
    rw [cscOpenMonotoneInt_of, openDuality₀Int_of, openDuality₀Int_of, legW₀Int, legW₀Int]
    refine Eq.trans ?_ (relativeDualityK₀Int_homOfSubset h (fundCycleW₀Int hW z₀ hz₀ K)
      (fundCycleW₀Int_mem_W hW z₀ hz₀ K)
      (subspaceChainsInt_mono h (k + 1) (fundCycleW₀Int_mem_W hW z₀ hz₀ K))
      (fundCycleW₀Int_boundary hW z₀ hz₀ K) a).symm
    refine relativeDualityK₀Int_cycle_compat_relB (fundCycleW₀Int hW' z₀ hz₀ (compactsInIncl h K))
      (fundCycleW₀Int hW z₀ hz₀ K) (fundCycleW₀Int_mem_W hW' z₀ hz₀ (compactsInIncl h K))
      (subspaceChainsInt_mono h (k + 1) (fundCycleW₀Int_mem_W hW z₀ hz₀ K))
      (fundCycleW₀Int_boundary hW' z₀ hz₀ (compactsInIncl h K))
      (fundCycleW₀Int_boundary hW z₀ hz₀ K)
      (interiors_cover_of_compact_subset_open K.1.isCompact' hW' (K.2.trans h)) ?_ a
    -- the relB glue (ℤ-difference), at the native (k+0+1)-spelling, transported once through castChainInt
    have hglue : RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
          (fundCycleW (k := k) (m := 0) hW' z₀ hz₀ (compactsInIncl h K))
        - RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
          (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)
        ∈ relBoundariesInt ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) := by
      have hA : RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) z₀
            - RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
              (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)
          ∈ relBoundariesInt ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) :=
        fundCycleW_relHomologous (k := k) (m := 0) hW z₀ hz₀ K
      have hB' : RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) z₀
            - RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
              (fundCycleW (k := k) (m := 0) hW' z₀ hz₀ (compactsInIncl h K))
          ∈ relBoundariesInt ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) :=
        fundCycleW_relHomologous (k := k) (m := 0) hW' z₀ hz₀ (compactsInIncl h K)
      have heq : RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
            (fundCycleW (k := k) (m := 0) hW' z₀ hz₀ (compactsInIncl h K))
          - RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
            (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)
          = (RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) z₀
              - RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
                (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K))
            - (RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) z₀
              - RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
                (fundCycleW (k := k) (m := 0) hW' z₀ hz₀ (compactsInIncl h K))) := by
        abel
      rw [heq]
      exact Submodule.sub_mem _ hA hB'
    exact relB_pair_castChainInt' (a := k + 0 + 1) (b := k + 1) rfl _ _ hglue

/-- **The bottom `Δ` square** (ℤ): `subHomDiagInt ∘ D⁰_{U∩V} = (D⁰_U ⊕ D⁰_V) ∘ cscMvDiagInt` at `H₀` —
hc₄ of the integral PD bottom-window five-lemma. -/
theorem subHomDiagInt_openDuality₀ [T2Space ↑X] {k : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (α : CompactlySupportedCohomologyOpenInt (U ∩ V) (k + 1)) :
    subHomDiagInt U V 0 (openDuality₀Int (hU.inter hV) z₀ hz₀ α)
      = (openDuality₀Int hU z₀ hz₀ (cscOpenMonotoneInt Set.inter_subset_left (k + 1) α),
          openDuality₀Int hV z₀ hz₀ (cscOpenMonotoneInt Set.inter_subset_right (k + 1) α)) := by
  rw [subHomDiagInt, LinearMap.prod_apply]
  simp only [Function.prod_def]
  rw [
    openDuality₀Int_cscOpenMonotone (hU.inter hV) hU Set.inter_subset_left z₀ hz₀,
    openDuality₀Int_cscOpenMonotone (hU.inter hV) hV Set.inter_subset_right z₀ hz₀]

/-- **The bottom `Σ` square** (ℤ): `D⁰_{U∪V} ∘ cscMvSumInt = subHomSumInt ∘ (D⁰_U ⊕ D⁰_V)` at `H₀`. -/
theorem subHomSumInt_openDuality₀ [T2Space ↑X] {k : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (αU : CompactlySupportedCohomologyOpenInt U (k + 1))
    (αV : CompactlySupportedCohomologyOpenInt V (k + 1)) :
    openDuality₀Int (hU.union hV) z₀ hz₀ (cscMvSumInt U V (k + 1) (αU, αV))
      = subHomSumInt U V 0 (openDuality₀Int hU z₀ hz₀ αU, openDuality₀Int hV z₀ hz₀ αV) := by
  rw [cscMvSumInt, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, map_sub,
    openDuality₀Int_cscOpenMonotone hU (hU.union hV) Set.subset_union_left z₀ hz₀,
    openDuality₀Int_cscOpenMonotone hV (hU.union hV) Set.subset_union_right z₀ hz₀, subHomSumInt,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply]

end SKEFTHawking.SingularOpenDualityBotNatInt
