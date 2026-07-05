/-
# Phase 5q.H (E1 integral topology) — support-enlargement naturality of `D_K` (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularLocalDualityKMono`. The `H(sub K_cyc)`-valued duality
`relativeDualityKInt S W z` is **natural in the cycle-support open**: for `W ⊆ W'` (both supporting the
cycle `z`), enlarging the target via the subspace inclusion `homOfSubsetInt (W ⊆ W')` commutes with
capping,
  `homOfSubsetInt (W ⊆ W') ∘ relativeDualityKInt S W z = relativeDualityKInt S W' z`.
Both classes are `[a ⌢ z]` with the *same* underlying absolute chain `a ⌢ z` (the cap is `W`-supported
⊆ `W'`-supported); `sub W ↪ sub W'` followed by `chainIncl` into `M` equals the direct `chainIncl`
(`mapChainInt_ambIncl` + `mapChainInt_comp`), so the pulled-back `sub W'`-cycles agree. This is the
duality side of the PD 5-lemma ladder's vertical-naturality squares.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularLocalDualityKInt
import SKEFTHawking.SingularSubsetHomologyInt
import SKEFTHawking.SingularConvexRadialBaseInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularMayerVietorisLES (ambIncl)
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularLocalDualityKInt
open SKEFTHawking.SingularSubsetHomologyInt
open SKEFTHawking.SingularConvexRadialBaseInt (mapChainInt_ambIncl)

namespace SKEFTHawking.SingularLocalDualityKMonoInt

variable {X : TopCat}

/-- **Support-enlargement naturality of the integral `H(sub K)`-valued duality**: for `W ⊆ W'` and a
cycle `z` supported in both, `homOfSubsetInt (W⊆W') ∘ D_K^W = D_K^{W'}`. Integral mirror of
`SingularLocalDualityKMono.relativeDualityK_homOfSubset`. -/
theorem relativeDualityKInt_homOfSubset {k m : ℕ} {S W W' : Set ↑X} (h : W ⊆ W')
    (z : SingularChainInt X (k + m + 1)) (hzW : z ∈ subspaceChainsInt W (k + m + 1))
    (hzW' : z ∈ subspaceChainsInt W' (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (x : RelativeCohomologyInt S k) :
    homOfSubsetInt h (m + 1) (relativeDualityKInt S W k m z hzW hzS x)
      = relativeDualityKInt S W' k m z hzW' hzS x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk a : RelativeCohomologyInt S k)
      = RelativeCohomologyInt.mk S k a from rfl,
    relativeDualityKInt_mk, relativeDualityKInt_mk, homOfSubsetInt, Homology.mapInt_mk]
  congr 1
  apply Subtype.ext
  rw [cyclesMapInt_coe]
  apply chainIncl_injective W' (m + 1)
  rw [chainIncl_pullbackDualityIntₗ,
    show chainIncl W' (m + 1) (mapChainInt (subInclCM h) (m + 1) (pullbackDualityIntₗ S W z hzW a))
        = chainIncl W (m + 1) (pullbackDualityIntₗ S W z hzW a) from by
      rw [← mapChainInt_ambIncl W', ← mapChainInt_comp,
        show (ambIncl W').comp (subInclCM h) = ambIncl W from ContinuousMap.ext fun _ => rfl,
        mapChainInt_ambIncl],
    chainIncl_pullbackDualityIntₗ]

end SKEFTHawking.SingularLocalDualityKMonoInt
