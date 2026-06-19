import Mathlib
import SKEFTHawking.SingularLocalDualityK
import SKEFTHawking.SingularSubsetHomology
import SKEFTHawking.SingularMayerVietorisLES

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-i) — support-enlargement naturality of `D_K`

The `H(sub K_cyc)`-valued duality `relativeDualityK S K_cyc z` is **natural in the cycle-support open**:
for `W ⊆ W'` (both supporting the cycle `z`), enlarging the target via the subspace inclusion
`homOfSubset (W ⊆ W')` commutes with capping,
  `homOfSubset (W ⊆ W') ∘ relativeDualityK S W z = relativeDualityK S W' z`.
Both classes are `[a ⌢ z]` with the *same* underlying absolute chain `a ⌢ z` (the cap is `W`-supported
⊆ `W'`-supported); the subspace inclusion `sub W ↪ sub W'` followed by `chainIncl` into `M` equals the
direct `chainIncl` (`mapChain_ambIncl` + `mapChain_comp`), so the pulled-back `sub W'`-cycles agree.

This is the duality side of the Poincaré-duality `5`-lemma ladder's vertical-naturality squares (`D_W`
commutes with the compactly-supported MV extension maps `cscOpenMonotone`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularLocalDualityK
  SKEFTHawking.SingularSubsetHomology SKEFTHawking.SingularMayerVietorisLES
  SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularLocalDualityKMono

variable {X : TopCat}

theorem relativeDualityK_homOfSubset {k m : ℕ} {S W W' : Set ↑X} (h : W ⊆ W')
    (z : SingularChain X (k + m + 1)) (hzW : z ∈ subspaceChains W (k + m + 1))
    (hzW' : z ∈ subspaceChains W' (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (x : RelativeCohomology S k) :
    homOfSubset h (m + 1) (relativeDualityK S W k m z hzW hzS x)
      = relativeDualityK S W' k m z hzW' hzS x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk a : RelativeCohomology S k) = RelativeCohomology.mk S k a from rfl,
    relativeDualityK_mk, relativeDualityK_mk, homOfSubset, Homology.map_mk]
  congr 1
  apply Subtype.ext
  rw [cyclesMap_coe]
  apply chainIncl_injective W' (m + 1)
  rw [chainIncl_pullbackDualityₗ,
    show chainIncl W' (m + 1) (mapChain (subInclCM h) (m + 1) (pullbackDualityₗ S W z hzW a))
        = chainIncl W (m + 1) (pullbackDualityₗ S W z hzW a) from by
      rw [← mapChain_ambIncl W', ← mapChain_comp,
        show (ambIncl W').comp (subInclCM h) = ambIncl W from ContinuousMap.ext fun _ => rfl,
        mapChain_ambIncl],
    chainIncl_pullbackDualityₗ]

end SKEFTHawking.SingularLocalDualityKMono
