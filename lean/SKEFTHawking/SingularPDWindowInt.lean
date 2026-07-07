/-
# Phase 5q.H (E1 CSC-PD tower) — the deg-4 PD cover-induction predicate `pdWindowPInt` (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularPDWindow.pdWindowP` — the three-conjunct predicate
`P(W) = Bij D@(2,1) ∧ Bij D@(3,0) ∧ Bij D⁰(W)` presented from the master cycle `zM` via `castChainInt`
recasts. The Hatcher-3.35 cover-induction that lifts the chart-convex base case (B6/D0) through
union/monotone/biUnion to `openDuality univ` bijective → `IntCapIso` → `σ÷16`.

This module ships the predicate + the trivial transport/empty base; the substantive `_union` step (the 3
MV five-lemmas + `hcore`) and the `_of_chartConvex` base (B6+D0) thread their deep inputs as hypotheses.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityInt
import SKEFTHawking.SingularOpenDualityBotInt
import SKEFTHawking.SingularOpenDualityMVConnSquareInt
import SKEFTHawking.SingularOpenDualityUpperFiveLemmaInt
import SKEFTHawking.SingularOpenDualityBotFiveLemmaInt
import SKEFTHawking.SingularOpenDualityD0FiveLemmaInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularOpenDualityBotInt (openDuality₀Int)
open SKEFTHawking.SingularOpenDualityMVConnSquareInt (castChainInt chainBoundary_castChainInt_eq_zero)
open SKEFTHawking.SingularSubHomologyMVInt (subHomConnectingInt)
open SKEFTHawking.SingularCSCMayerVietorisConnectingInt (legδInt)
open SKEFTHawking.SingularOpenDualityUpperFiveLemmaInt (openDuality_union_bijective_upperInt)
open SKEFTHawking.SingularOpenDualityBotFiveLemmaInt (openDuality_union_bijective_botInt)
open SKEFTHawking.SingularOpenDualityD0FiveLemmaInt (openDuality₀_union_bijectiveInt)

namespace SKEFTHawking.SingularPDWindowInt

/-- **The deg-4 PD-induction predicate (integral)** `P(W) = Bij D@(2,1) ∧ Bij D@(3,0) ∧ Bij D⁰`, presented
from the master cycle `zM` (engine-native `castChainInt` spellings). -/
def pdWindowPInt {M : TopCat} [T2Space ↑M]
    (zM : SingularChainInt M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    (W : Set ↑M) (hW : IsOpen W) : Prop :=
  Function.Bijective (openDuality (k := 1 + 1) (m := 0 + 1) hW
      (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) zM)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM))
  ∧ Function.Bijective (openDuality (k := 2 + 1) (m := 0) hW
      (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM))
  ∧ Function.Bijective (openDuality₀Int (k := 2 + 1) hW
      (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM))

/-- `P`-transport across a set identity (integral). -/
theorem pdWindowPInt_congr {M : TopCat} [T2Space ↑M]
    (zM : SingularChainInt M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    {W W' : Set ↑M} (h : W = W') (hW : IsOpen W) (hW' : IsOpen W')
    (hP : pdWindowPInt zM hzM W hW) : pdWindowPInt zM hzM W' hW' := by
  subst h
  exact hP

/-- **Layer-A: the Mayer–Vietoris step (integral)** — `P(U) ∧ P(V) ∧ P(U∩V) → P(U∪V)`, through the three
integral five-lemma engines (upper at `(N,p)=(1,0)`, bot at `N=2`, `D⁰`-step at `N=2`). The two per-`K`
connecting cores (`hcoreU` upper, `hcore₀` bot — the deep torsion-safe `hcoreInt` at the two window
degrees) and the `csc⁵`-vanishings are threaded as hypotheses; NO project axiom. -/
theorem pdWindowPInt_union {M : TopCat} [T2Space ↑M]
    (zM : SingularChainInt M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    {U V : Set ↑M} (hU : IsOpen U) (hV : IsOpen V)
    (hcoreU : ∀ (K : CompactsIn (U ∪ V)) (g : cohomGWInt (U ∪ V) (1 + 1) K),
      subHomConnectingInt U V hU hV (0 + 1)
          (legW (k := 1 + 1) (m := 0 + 1) (hU.union hV)
            (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) zM)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM) K g)
        = openDuality (k := 1 + 2) (m := 0) (hU.inter hV)
            (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 2 + 0 + 1 by omega) zM)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM)
            (legδInt U V hU hV 1 K g))
    (hcore₀ : ∀ (K : CompactsIn (U ∪ V)) (g : cohomGWInt (U ∪ V) (2 + 1) K),
      subHomConnectingInt U V hU hV 0
          (legW (k := 2 + 1) (m := 0) (hU.union hV)
            (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM) K g)
        = openDuality₀Int (hU.inter hV)
            (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM)
            (legδInt U V hU hV 2 K g))
    (hvanI : ∀ α : CompactlySupportedCohomologyOpenInt (U ∩ V) (2 + 1 + 2), α = 0)
    (hvanU : ∀ α : CompactlySupportedCohomologyOpenInt U (2 + 1 + 2), α = 0)
    (hvanV : ∀ α : CompactlySupportedCohomologyOpenInt V (2 + 1 + 2), α = 0)
    (hPU : pdWindowPInt zM hzM U hU) (hPV : pdWindowPInt zM hzM V hV)
    (hPI : pdWindowPInt zM hzM (U ∩ V) (hU.inter hV)) :
    pdWindowPInt zM hzM (U ∪ V) (hU.union hV) := by
  obtain ⟨hU1, hU2, hU3⟩ := hPU
  obtain ⟨hV1, hV2, hV3⟩ := hPV
  obtain ⟨hI1, hI2, hI3⟩ := hPI
  refine ⟨?_, ?_, ?_⟩
  · exact openDuality_union_bijective_upperInt (N := 1) (p := 0) hU hV zM hzM hcoreU
      hI1.surjective hU1 hV1 hI2 hU2.injective hV2.injective
  · exact openDuality_union_bijective_botInt (N := 2) hU hV
      (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM) hcore₀
      hI2.surjective hU2 hV2 hI3 hU3.injective hV3.injective
  · exact openDuality₀_union_bijectiveInt (N := 2) hU hV
      (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM)
      hvanI hvanU hvanV hI3.surjective hU3 hV3

end SKEFTHawking.SingularPDWindowInt
