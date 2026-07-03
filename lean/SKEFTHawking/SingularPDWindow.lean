import Mathlib
import SKEFTHawking.SingularBaseCaseUpper
import SKEFTHawking.SingularBaseCaseD0

/-!
# Phase 5q.G (G1 PD-induction, B6) — the deg-4 induction predicate `P(W)` and its base case

`pdWindowP zM hzM W hW` is the three-conjunct Bott–Tu induction carrier for the deg-4 Poincaré
duality: `Bij D@(2,1) ∧ Bij D@(3,0) ∧ Bij D⁰`, all presented from ONE master cycle
`zM : chain (1+0+3)` (the upper-engine-native spelling) via `castChain` junctions:

* conjunct 1 at the upper-engine-instantiated `(k, m) = (1+1, 0+1)` — the `(2,1)`-window, exactly
  the `openDuality_union_bijective_upper (N := 1) (p := 0)` conclusion/hypothesis shape;
* conjuncts 2–3 at the bot/D⁰-engine-native `(k := 2+1)` spelling over the SHARED
  `castChain (1+0+3 = 2+1+0+1) zM` presentation — `openDuality_union_bijective_bot (N := 2)` and
  `openDuality₀_union_bijective (N := 2)` consume/produce them verbatim (the sole junction left
  to Layer-A is the upper engine's `(1+2)`-spelled `(3,0)`-inputs).

**Base case (B6)**: `pdWindowP_of_chartConvex` — for a chart-convex `W`, conjuncts 1–2 are
bijections between trivial modules (B3 + B5 via `openDuality_bijective_of_chartConvex`) and
conjunct 3 is B4c (`openDuality₀_bijective_of_chartConvex`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularOpenDuality
open SKEFTHawking.SingularOpenDualityBot SKEFTHawking.SingularOpenDualityMVConnSquare
open SKEFTHawking.SingularBaseCaseUpper

namespace SKEFTHawking.SingularPDWindow

/-- **The deg-4 PD-induction predicate** `P(W) = Bij D@(2,1) ∧ Bij D@(3,0) ∧ Bij D⁰`, all
presented from the master cycle `zM` (engine-native spellings; see the module docstring). -/
def pdWindowP {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    (W : Set ↑M) (hW : IsOpen W) : Prop :=
  Function.Bijective (openDuality (k := 1 + 1) (m := 0 + 1) hW
      (castChain (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) zM)
      (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM))
  ∧ Function.Bijective (openDuality (k := 2 + 1) (m := 0) hW
      (castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
      (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM))
  ∧ Function.Bijective (openDuality₀ (k := 2 + 1) hW
      (castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
      (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM))

open SKEFTHawking.SingularChartBridge in
/-- **B6: the base case** — `P(W)` holds for every chart-convex open `W` (the chart `e` carries
`W` exactly onto a convex open `C ∋ p₀`), given the master cycle's local-generator property. -/
theorem pdWindowP_of_chartConvex {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    {U : Set ↑(TopCat.of M)} {V : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (2 + 2)))} (hCconv : Convex ℝ C) (hCopen : IsOpen C)
    {p₀ : EuclideanSpace ℝ (Fin (2 + 2))} (hp₀ : p₀ ∈ C) (hCV : C ⊆ V)
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2))) ∈ C))
    (zM : SingularChain (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcyc : castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (2 + 2) (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = (manifoldLocalIso x).symm 1) :
    pdWindowP zM hzM W hWo := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  exact ⟨openDuality_bijective_of_chartConvex hU hV e hCconv hCopen hp₀ hCV hWo hWU hWe
      (by omega) (by omega) _ _,
    openDuality_bijective_of_chartConvex hU hV e hCconv hCopen hp₀ hCV hWo hWU hWe
      (by omega) (by omega) _ _,
    SKEFTHawking.SingularBaseCaseD0.openDuality₀_bijective_of_chartConvex hU hV e hCconv
      hCopen hp₀ hCV hWo hWU hWe _ _ hcyc hloc⟩

end SKEFTHawking.SingularPDWindow
