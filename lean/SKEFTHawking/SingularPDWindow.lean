import Mathlib
import SKEFTHawking.SingularBaseCaseUpper
import SKEFTHawking.SingularBaseCaseD0
import SKEFTHawking.SingularConnSquareCloseNCBotApex

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

/-- **Layer-A: the Mayer–Vietoris step** — `P(U) ∧ P(V) ∧ P(U∩V) → P(U∪V)`, through the three
five-lemma engines (upper at `(N,p) = (1,0)`, bot at `N = 2`, `D⁰`-step at `N = 2`). The
`csc⁵`-vanishing hypotheses feed the `D⁰`-step's truncated right end (discharged once, manifold-
level, by the track-A vanishing bricks at the induction assembly). -/
theorem pdWindowP_union {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    {U V : Set ↑M} (hU : IsOpen U) (hV : IsOpen V)
    (hvanI : ∀ α : CompactlySupportedCohomologyOpen (U ∩ V) (2 + 1 + 2), α = 0)
    (hvanU : ∀ α : CompactlySupportedCohomologyOpen U (2 + 1 + 2), α = 0)
    (hvanV : ∀ α : CompactlySupportedCohomologyOpen V (2 + 1 + 2), α = 0)
    (hPU : pdWindowP zM hzM U hU) (hPV : pdWindowP zM hzM V hV)
    (hPI : pdWindowP zM hzM (U ∩ V) (hU.inter hV)) :
    pdWindowP zM hzM (U ∪ V) (hU.union hV) := by
  obtain ⟨hU1, hU2, hU3⟩ := hPU
  obtain ⟨hV1, hV2, hV3⟩ := hPV
  obtain ⟨hI1, hI2, hI3⟩ := hPI
  refine ⟨?_, ?_, ?_⟩
  · exact SKEFTHawking.SingularConnSquareCloseNCBotApex.openDuality_union_bijective_upper
      (N := 1) (p := 0) hU hV zM hzM hI1.surjective hU1 hV1 hI2 hU2.injective hV2.injective
  · exact SKEFTHawking.SingularConnSquareCloseNCBotApex.openDuality_union_bijective_bot
      (N := 2) hU hV
      (castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
      (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM)
      hI2.surjective hU2 hV2 hI3 hU3.injective hV3.injective
  · exact SKEFTHawking.SingularConnSquareCloseNCBotApex.openDuality₀_union_bijective
      (N := 2) hU hV
      (castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
      (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM)
      hvanI hvanU hvanV hI3.surjective hU3 hV3


/-- **Layer-A: monotone-union stability** — `P` passes to increasing unions (`A3`; the three
monotone-union engines, conjunct-wise). -/
theorem pdWindowP_monotone_union {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    {W : ℕ → Set ↑M} (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (hP : ∀ n, pdWindowP zM hzM (W n) (hopen n)) :
    pdWindowP zM hzM (⋃ n, W n) (isOpen_iUnion hopen) :=
  ⟨SKEFTHawking.SingularOpenDualityMonotoneUnion.openDuality_monotone_union_bijective
      hmono hopen _ _ (fun n => (hP n).1),
    SKEFTHawking.SingularOpenDualityMonotoneUnion.openDuality_monotone_union_bijective
      hmono hopen _ _ (fun n => (hP n).2.1),
    SKEFTHawking.SingularConnSquareCloseNCBotApex.openDuality₀_monotone_union_bijective
      hmono hopen _ _ (fun n => (hP n).2.2)⟩


end SKEFTHawking.SingularPDWindow
