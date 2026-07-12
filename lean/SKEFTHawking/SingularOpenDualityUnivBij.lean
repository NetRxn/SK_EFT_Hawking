/-
# Phase 5q.H (E1, mod-2 assembly port) — the `(2,1)`-window openDuality on `univ` is bijective (mod 2)

Mod-2 twin of `SingularOpenDualityUnivBijInt` — the univ-bijectivity extraction from the window ladder.
STRICTLY SIMPLER than the integral version: the mod-2 `pdWindowP_univ` is self-contained (its connecting
core closed in-file — no `hcoreG` input), so the extraction takes only the mod-2 fundamental-cycle datum
(`zM`/`hzM`/`hcyc`/`hloc` — no orientation over ℤ/2 beyond the local-generator property, which every
closed 4-manifold satisfies mod 2). First brick of the mod-2 univ-assembly port whose target is
`PoincareDual4Mid.nondeg` (launch-pad inventory: E1 shard, 2026-07-12 arm-2 turn 5).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularPDWindow

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularOpenDuality
open SKEFTHawking.SingularOpenDualityMVConnSquare (castChain chainBoundary_castChain_eq_zero)
open SKEFTHawking.SingularPDWindow

namespace SKEFTHawking.SingularOpenDualityUnivBij

/-- **The `(2,1)`-window openDuality on `univ` is bijective (mod 2)** — the first conjunct of
`pdWindowP_univ`, extracted at the closed-manifold instance. The mod-2 mirror of
`openDuality_univ_bij_of_hcoreGInt`, with NO core hypothesis (the mod-2 connecting core is a theorem).
This is the `hD` input of the mod-2 cap-equiv assembly toward `PoincareDual4Mid.nondeg`. -/
theorem openDuality_univ_bij {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (zM : SingularChain (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcyc : castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (2 + 2) (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = (SKEFTHawking.SingularChartBridge.manifoldLocalIso x).symm 1) :
    Function.Bijective
      (openDuality (k := 1 + 1) (m := 0 + 1)
        (isOpen_univ : IsOpen (Set.univ : Set ↑(TopCat.of M)))
        (castChain (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) zM)
        (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM)) :=
  (pdWindowP_univ zM hzM hcyc hloc isOpen_univ).1

/-- **The `(3,0)`-window openDuality on `univ` is bijective (mod 2)** — the second conjunct, extracted
for the bot-window consumers (the mod-2 `D⁰`/degree-0 assembly). -/
theorem openDuality_univ_bij_bot {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (zM : SingularChain (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcyc : castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (2 + 2) (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = (SKEFTHawking.SingularChartBridge.manifoldLocalIso x).symm 1) :
    Function.Bijective
      (openDuality (k := 2 + 1) (m := 0)
        (isOpen_univ : IsOpen (Set.univ : Set ↑(TopCat.of M)))
        (castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
        (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM)) :=
  (pdWindowP_univ zM hzM hcyc hloc isOpen_univ).2.1

end SKEFTHawking.SingularOpenDualityUnivBij
