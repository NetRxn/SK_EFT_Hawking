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
import SKEFTHawking.SingularOpenDualityBotMonotoneUnionInt
import SKEFTHawking.SingularCSCEmptyInt
import SKEFTHawking.SingularBaseCaseUpper
import SKEFTHawking.SingularBaseCaseUpperInt
import SKEFTHawking.SingularCSCVanishAboveCohomInt
import SKEFTHawking.SingularPDWindow

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
open SKEFTHawking.SingularOpenDualityMonotoneUnionInt (openDuality_monotone_union_bijectiveInt)
open SKEFTHawking.SingularOpenDualityBotMonotoneUnionInt (openDuality₀_monotone_union_bijectiveInt)
open SKEFTHawking.SingularCSCEmptyInt (cscOpen_empty_eq_zeroInt homology_sub_empty_eq_zeroInt)
open SKEFTHawking.SingularBaseCaseUpper (bijective_of_forall_eq_zero)
open SKEFTHawking.SingularCSCVanishAboveCohomInt (cscOpen_eq_zero_of_isOpenInt)
open SKEFTHawking.SingularBaseCaseUpperInt (openDuality_bijective_of_chartConvexInt)
open SKEFTHawking.SingularPDWindow (chartPull chartPull_isOpen chartPull_subset mem_chartPull
  chartPull_iUnion chartPull_image)

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

/-- **The `P` base case (integral)** — chart-convex opens: the two upper conjuncts are B6
(`openDuality_bijective_of_chartConvexInt`, threading `hproj`), the `D⁰` conjunct is the threaded D0 base
case `hD0` (the reduced-H₀ pairing bijectivity, discharged separately via its ChartBridge/ConvexStageIso/
ReducedH0 Int dep-tree). -/
theorem pdWindowPInt_of_chartConvex {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (hproj : ∀ (S : Set ↑(TopCat.of M)) (j : ℕ), Module.Projective ℤ (relBoundariesInt S j))
    {U : Set ↑(TopCat.of M)} {V : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (2 + 2)))} (hCconv : Convex ℝ C) (hCopen : IsOpen C)
    {p₀ : EuclideanSpace ℝ (Fin (2 + 2))} (hp₀ : p₀ ∈ C) (hCV : C ⊆ V)
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2))) ∈ C))
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hD0 : Function.Bijective (openDuality₀Int (k := 2 + 1) hWo
      (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM))) :
    pdWindowPInt zM hzM W hWo := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  exact ⟨openDuality_bijective_of_chartConvexInt hproj hU hV e hCconv hCopen hp₀ hCV hWo hWU hWe
      (by omega) (by omega) _ _,
    openDuality_bijective_of_chartConvexInt hproj hU hV e hCconv hCopen hp₀ hCV hWo hWU hWe
      (by omega) (by omega) _ _,
    hD0⟩

/-- **The charted-manifold MV-step (integral)** — `pdWindowPInt_union` with the `csc⁵`-vanishing
hypotheses discharged by the integral top-degree vanishing (`cscOpen_eq_zero_of_isOpenInt`, `m = 2`,
`k = 5 > 4`). Threads `hproj` (Kaplansky) + `hfree` (top-degree Ext-freeness) into the vanishing and the two
per-`K` connecting cores (`hcoreU`/`hcore₀`) into the five-lemmas; NO project axiom. -/
theorem pdWindowPInt_union_charted {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (hproj : ∀ (S : Set ↑(TopCat.of M)) (j : ℕ), Module.Projective ℤ (relBoundariesInt S j))
    (hfree : ∀ (S : Set ↑(TopCat.of M)), IsCompact S →
      Module.Free ℤ (RelHomologyInt (Sᶜ) (2 + 2)))
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    {U V : Set ↑(TopCat.of M)} (hU : IsOpen U) (hV : IsOpen V)
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
    (hPU : pdWindowPInt zM hzM U hU) (hPV : pdWindowPInt zM hzM V hV)
    (hPI : pdWindowPInt zM hzM (U ∩ V) (hU.inter hV)) :
    pdWindowPInt zM hzM (U ∪ V) (hU.union hV) := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  exact pdWindowPInt_union zM hzM hU hV hcoreU hcore₀
    (fun α => cscOpen_eq_zero_of_isOpenInt (m := 2) hproj hfree (hU.inter hV) (by omega) α)
    (fun α => cscOpen_eq_zero_of_isOpenInt (m := 2) hproj hfree hU (by omega) α)
    (fun α => cscOpen_eq_zero_of_isOpenInt (m := 2) hproj hfree hV (by omega) α)
    hPU hPV hPI

/-- **Layer-A: monotone-union stability (integral)** — `P` passes to increasing unions (`A3`; the three
monotone-union engines, conjunct-wise). -/
theorem pdWindowPInt_monotone_union {M : TopCat} [T2Space ↑M]
    (zM : SingularChainInt M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    {W : ℕ → Set ↑M} (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (hP : ∀ n, pdWindowPInt zM hzM (W n) (hopen n)) :
    pdWindowPInt zM hzM (⋃ n, W n) (isOpen_iUnion hopen) :=
  ⟨openDuality_monotone_union_bijectiveInt hmono hopen _ _ (fun n => (hP n).1),
    openDuality_monotone_union_bijectiveInt hmono hopen _ _ (fun n => (hP n).2.1),
    openDuality₀_monotone_union_bijectiveInt hmono hopen _ _ (fun n => (hP n).2.2)⟩

/-- **`P(∅)`** (integral) — all three conjuncts are bijections between trivial modules (the empty-
intersection branch of the finite-union induction). -/
theorem pdWindowPInt_empty {M : TopCat} [T2Space ↑M]
    (zM : SingularChainInt M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0) :
    pdWindowPInt zM hzM (∅ : Set ↑M) isOpen_empty :=
  ⟨bijective_of_forall_eq_zero _
      (fun α => cscOpen_empty_eq_zeroInt α) (fun b => homology_sub_empty_eq_zeroInt _ b),
    bijective_of_forall_eq_zero _
      (fun α => cscOpen_empty_eq_zeroInt α) (fun b => homology_sub_empty_eq_zeroInt _ b),
    bijective_of_forall_eq_zero _
      (fun α => cscOpen_empty_eq_zeroInt α) (fun b => homology_sub_empty_eq_zeroInt _ b)⟩

/-- **(A4b) Within-chart finite unions (integral)**: `P(⋃ i ∈ s, Wf i)` for a finite family of opens in a
COMMON chart, each carried to a convex (possibly empty) open image. Strong `Finset.induction_on` double
induction — the MV intersection `Wf j ∩ ⋃ᵢ Wf i = ⋃ᵢ (Wf j ∩ Wf i)` is again such a family. Threads the
global connecting core `hcoreG` (into `_union_charted`), the chart-convex base case `hbaseConv`, and
`hproj`/`hfree`; NO project axiom. -/
theorem pdWindowPInt_finset_biUnion {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (hproj : ∀ (S : Set ↑(TopCat.of M)) (j : ℕ), Module.Projective ℤ (relBoundariesInt S j))
    (hfree : ∀ (S : Set ↑(TopCat.of M)), IsCompact S →
      Module.Free ℤ (RelHomologyInt (Sᶜ) (2 + 2)))
    {U : Set ↑(TopCat.of M)} {V : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcoreG : ∀ (A B : Set ↑(TopCat.of M)) (hA : IsOpen A) (hB : IsOpen B),
      (∀ (K : CompactsIn (A ∪ B)) (g : cohomGWInt (A ∪ B) (1 + 1) K),
        subHomConnectingInt A B hA hB (0 + 1)
            (legW (k := 1 + 1) (m := 0 + 1) (hA.union hB)
              (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) zM)
              (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM) K g)
          = openDuality (k := 1 + 2) (m := 0) (hA.inter hB)
              (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 2 + 0 + 1 by omega) zM)
              (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM)
              (legδInt A B hA hB 1 K g)) ∧
      (∀ (K : CompactsIn (A ∪ B)) (g : cohomGWInt (A ∪ B) (2 + 1) K),
        subHomConnectingInt A B hA hB 0
            (legW (k := 2 + 1) (m := 0) (hA.union hB)
              (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
              (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM) K g)
          = openDuality₀Int (hA.inter hB)
              (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
              (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM)
              (legδInt A B hA hB 2 K g)))
    (hbaseConv : ∀ {W : Set ↑(TopCat.of M)} (hWo : IsOpen W), W ⊆ U →
      ∀ {Cw : Set (EuclideanSpace ℝ (Fin (2 + 2)))}, Convex ℝ Cw → IsOpen Cw →
      ∀ {pw : EuclideanSpace ℝ (Fin (2 + 2))}, pw ∈ Cw → Cw ⊆ V →
      (∀ u : ↥U, (u : M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2))) ∈ Cw)) →
      pdWindowPInt zM hzM W hWo)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    ∀ (Wf : ι → Set ↑(TopCat.of M)) (Cf : ι → Set (EuclideanSpace ℝ (Fin (2 + 2)))),
      (∀ i ∈ s, IsOpen (Wf i)) → (∀ i ∈ s, Convex ℝ (Cf i)) → (∀ i ∈ s, IsOpen (Cf i)) →
      (∀ i ∈ s, Cf i ⊆ V) → (∀ i ∈ s, Wf i ⊆ U) →
      (∀ i ∈ s, ∀ u : ↥U, (u : M) ∈ Wf i ↔
        ((e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2))) ∈ Cf i)) →
      ∀ hop : IsOpen (⋃ i ∈ s, Wf i), pdWindowPInt zM hzM (⋃ i ∈ s, Wf i) hop := by
  induction s using Finset.induction_on with
  | empty =>
    intro Wf Cf _ _ _ _ _ _ hop
    exact pdWindowPInt_congr zM hzM (by simp) isOpen_empty hop (pdWindowPInt_empty zM hzM)
  | insert j s hj ih =>
    intro Wf Cf hopen hconv hCopen hCV hWU hWe hop
    have hjmem : j ∈ insert j s := Finset.mem_insert_self j s
    have hmem : ∀ i ∈ s, i ∈ insert j s := fun i hi => Finset.mem_insert_of_mem hi
    have hopj : IsOpen (Wf j) := hopen j hjmem
    have hopS : IsOpen (⋃ i ∈ s, Wf i) := isOpen_biUnion (fun i hi => hopen i (hmem i hi))
    have hPj : pdWindowPInt zM hzM (Wf j) hopj := by
      rcases (Cf j).eq_empty_or_nonempty with hCe | hCne
      · refine pdWindowPInt_congr zM hzM ?_ isOpen_empty hopj (pdWindowPInt_empty zM hzM)
        symm; ext x; simp only [Set.mem_empty_iff_false, iff_false]; intro hx
        have h := (hWe j hjmem ⟨x, hWU j hjmem hx⟩).mp hx
        rw [hCe] at h; exact h
      · obtain ⟨p₀, hp₀⟩ := hCne
        exact hbaseConv hopj (hWU j hjmem) (hconv j hjmem) (hCopen j hjmem) hp₀
          (hCV j hjmem) (hWe j hjmem)
    have hPS : pdWindowPInt zM hzM (⋃ i ∈ s, Wf i) hopS :=
      ih Wf Cf (fun i hi => hopen i (hmem i hi)) (fun i hi => hconv i (hmem i hi))
        (fun i hi => hCopen i (hmem i hi)) (fun i hi => hCV i (hmem i hi))
        (fun i hi => hWU i (hmem i hi)) (fun i hi => hWe i (hmem i hi)) hopS
    have hPI : pdWindowPInt zM hzM (Wf j ∩ ⋃ i ∈ s, Wf i) (hopj.inter hopS) := by
      have hidt : Wf j ∩ (⋃ i ∈ s, Wf i) = ⋃ i ∈ s, (Wf j ∩ Wf i) := Set.inter_iUnion₂ _ _
      have hopI : IsOpen (⋃ i ∈ s, (Wf j ∩ Wf i)) :=
        isOpen_biUnion (fun i hi => hopj.inter (hopen i (hmem i hi)))
      refine pdWindowPInt_congr zM hzM hidt.symm hopI (hopj.inter hopS) ?_
      exact ih (fun i => Wf j ∩ Wf i) (fun i => Cf j ∩ Cf i)
        (fun i hi => hopj.inter (hopen i (hmem i hi)))
        (fun i hi => (hconv j hjmem).inter (hconv i (hmem i hi)))
        (fun i hi => (hCopen j hjmem).inter (hCopen i (hmem i hi)))
        (fun i hi => Set.inter_subset_right.trans (hCV i (hmem i hi)))
        (fun i hi => Set.inter_subset_left.trans (hWU j hjmem))
        (fun i hi u => by
          simp only [Set.mem_inter_iff]
          exact and_congr (hWe j hjmem u) (hWe i (hmem i hi) u)) hopI
    refine pdWindowPInt_congr zM hzM (Finset.set_biUnion_insert j s Wf).symm
      (hopj.union hopS) hop ?_
    exact pdWindowPInt_union_charted hproj hfree zM hzM hopj hopS
      (hcoreG (Wf j) (⋃ i ∈ s, Wf i) hopj hopS).1 (hcoreG (Wf j) (⋃ i ∈ s, Wf i) hopj hopS).2
      hPj hPS hPI

/-- **(A4c) Chart-open exhaustion (integral)**: `P(W)` for any open `W ⊆ U` (`W` inside a chart source),
by exhausting its Euclidean chart image `O` with countably many open balls (convex), taking the monotone
finite-truncation exhaustion (each an A4b within-chart family), and gluing with `_monotone_union`. The
chart machinery is coefficient-agnostic (reused from the mod-2 `SingularPDWindow`); threads
`hproj`/`hfree`/`hcoreG`/`hbaseConv`. -/
theorem pdWindowPInt_of_chartOpen {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (hproj : ∀ (S : Set ↑(TopCat.of M)) (j : ℕ), Module.Projective ℤ (relBoundariesInt S j))
    (hfree : ∀ (S : Set ↑(TopCat.of M)), IsCompact S →
      Module.Free ℤ (RelHomologyInt (Sᶜ) (2 + 2)))
    {U : Set ↑(TopCat.of M)} {V : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcoreG : ∀ (A B : Set ↑(TopCat.of M)) (hA : IsOpen A) (hB : IsOpen B),
      (∀ (K : CompactsIn (A ∪ B)) (g : cohomGWInt (A ∪ B) (1 + 1) K),
        subHomConnectingInt A B hA hB (0 + 1)
            (legW (k := 1 + 1) (m := 0 + 1) (hA.union hB)
              (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) zM)
              (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM) K g)
          = openDuality (k := 1 + 2) (m := 0) (hA.inter hB)
              (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 2 + 0 + 1 by omega) zM)
              (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM)
              (legδInt A B hA hB 1 K g)) ∧
      (∀ (K : CompactsIn (A ∪ B)) (g : cohomGWInt (A ∪ B) (2 + 1) K),
        subHomConnectingInt A B hA hB 0
            (legW (k := 2 + 1) (m := 0) (hA.union hB)
              (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
              (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM) K g)
          = openDuality₀Int (hA.inter hB)
              (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
              (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM)
              (legδInt A B hA hB 2 K g)))
    (hbaseConv : ∀ {W : Set ↑(TopCat.of M)} (hWo : IsOpen W), W ⊆ U →
      ∀ {Cw : Set (EuclideanSpace ℝ (Fin (2 + 2)))}, Convex ℝ Cw → IsOpen Cw →
      ∀ {pw : EuclideanSpace ℝ (Fin (2 + 2))}, pw ∈ Cw → Cw ⊆ V →
      (∀ u : ↥U, (u : M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2))) ∈ Cw)) →
      pdWindowPInt zM hzM W hWo)
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (hWU : W ⊆ U) :
    pdWindowPInt zM hzM W hWo := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  set em : ↥U → EuclideanSpace ℝ (Fin (2 + 2)) :=
    fun u => (e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2))) with hemdef
  set O : Set (EuclideanSpace ℝ (Fin (2 + 2))) := em '' (Subtype.val ⁻¹' W) with hOdef
  have hOV : O ⊆ V := by rintro q ⟨u, _, rfl⟩; exact (e u).2
  have hOopen : IsOpen O := by
    have hpre : IsOpen (Subtype.val ⁻¹' W : Set ↥U) := continuous_subtype_val.isOpen_preimage _ hWo
    have himg : IsOpen ((fun u : ↥U => e u) '' (Subtype.val ⁻¹' W) : Set ↥V) := e.isOpenMap _ hpre
    have := hV.isOpenMap_subtype_val _ himg
    rwa [show Subtype.val '' ((fun u : ↥U => e u) '' (Subtype.val ⁻¹' W)) = O by
      rw [hOdef, ← Set.image_comp]; rfl] at this
  have hball : ∀ q : ↥O, ∃ ε > 0, Metric.ball (q : EuclideanSpace ℝ (Fin (2 + 2))) ε ⊆ O :=
    fun q => Metric.isOpen_iff.mp hOopen q q.2
  choose ε hε hballO using hball
  have hcover : (⋃ q : ↥O, Metric.ball (q : EuclideanSpace ℝ (Fin (2 + 2))) (ε q)) = O := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun q => hballO q)
    · exact fun q hq => Set.mem_iUnion.mpr ⟨⟨q, hq⟩, Metric.mem_ball_self (hε ⟨q, hq⟩)⟩
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun q : ↥O => Metric.ball (q : EuclideanSpace ℝ (Fin (2 + 2))) (ε q))
    (fun q => Metric.isOpen_ball)
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · have hOempty : O = ∅ := by rw [← hcover, ← hTeq, hTe]; simp
    have hWempty : W = ∅ := by
      have := hOempty
      rw [hOdef, Set.image_eq_empty] at this
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      exact absurd (show (⟨x, hWU hx⟩ : ↥U) ∈ (Subtype.val ⁻¹' W : Set ↥U) from hx)
        (by rw [this]; exact Set.notMem_empty _)
    exact pdWindowPInt_congr zM hzM hWempty.symm isOpen_empty hWo (pdWindowPInt_empty zM hzM)
  · obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    have hstage : ∀ n : ℕ, ∀ hop : IsOpen (⋃ k ∈ Finset.range (n + 1),
        chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (2 + 2))) (ε (f k)))),
        pdWindowPInt zM hzM _ hop := by
      intro n hop
      exact pdWindowPInt_finset_biUnion hproj hfree hU hV e zM hzM hcoreG hbaseConv
        (Finset.range (n + 1))
        (fun k => chartPull e (Metric.ball ((f k : ↥O) : _) (ε (f k))))
        (fun k => Metric.ball ((f k : ↥O) : _) (ε (f k)))
        (fun k _ => chartPull_isOpen hU e Metric.isOpen_ball)
        (fun k _ => convex_ball _ _)
        (fun k _ => Metric.isOpen_ball)
        (fun k _ => (hballO (f k)).trans hOV)
        (fun k _ => chartPull_subset e _)
        (fun k _ u => mem_chartPull e _ u) hop
    have hopseq : ∀ n : ℕ, IsOpen (⋃ k ∈ Finset.range (n + 1),
        chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (2 + 2))) (ε (f k)))) :=
      fun n => isOpen_biUnion (fun k _ => chartPull_isOpen hU e Metric.isOpen_ball)
    have hmono : ∀ n, (⋃ k ∈ Finset.range (n + 1),
          chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (2 + 2))) (ε (f k))))
        ⊆ ⋃ k ∈ Finset.range (n + 1 + 1),
          chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (2 + 2))) (ε (f k))) :=
      fun n => Set.biUnion_subset_biUnion_left
        (fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))
    have hPmono := pdWindowPInt_monotone_union zM hzM hmono hopseq (fun n => hstage n (hopseq n))
    refine pdWindowPInt_congr zM hzM ?_ _ hWo hPmono
    have hcollapse : (⋃ n, ⋃ k ∈ Finset.range (n + 1),
          chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (2 + 2))) (ε (f k))))
        = ⋃ k : ℕ, chartPull e
            (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (2 + 2))) (ε (f k))) := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_range]
      exact ⟨fun ⟨n, k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, k, Nat.lt_succ_self k, h⟩⟩
    rw [hcollapse, ← chartPull_iUnion e]
    have hOre : (⋃ k : ℕ, Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (2 + 2))) (ε (f k)))
        = O := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset (fun k => hballO (f k))
      · intro q hq
        have h1 : q ∈ ⋃ i ∈ T, Metric.ball
            ((i : ↥O) : EuclideanSpace ℝ (Fin (2 + 2))) (ε i) := by rw [hTeq, hcover]; exact hq
        obtain ⟨i, hiT, hqi⟩ := Set.mem_iUnion₂.mp h1
        obtain ⟨k, rfl⟩ : ∃ k, f k = i := by
          have hir : i ∈ Set.range f := by rw [← hf]; exact hiT
          exact hir
        exact Set.mem_iUnion.mpr ⟨k, hqi⟩
    rw [hOre, hOdef]
    exact chartPull_image e hWU

/-- The chart-agnostic connecting-core hypothesis: the two per-`K` connecting cores for **any** open pair
`A, B` (the deep torsion-safe `hcoreInt` at the two window degrees, at every union). -/
def HcoreG (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0) : Prop :=
  ∀ (A B : Set ↑(TopCat.of M)) (hA : IsOpen A) (hB : IsOpen B),
    (∀ (K : CompactsIn (A ∪ B)) (g : cohomGWInt (A ∪ B) (1 + 1) K),
      subHomConnectingInt A B hA hB (0 + 1)
          (legW (k := 1 + 1) (m := 0 + 1) (hA.union hB)
            (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) zM)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM) K g)
        = openDuality (k := 1 + 2) (m := 0) (hA.inter hB)
            (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 2 + 0 + 1 by omega) zM)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM)
            (legδInt A B hA hB 1 K g)) ∧
    (∀ (K : CompactsIn (A ∪ B)) (g : cohomGWInt (A ∪ B) (2 + 1) K),
      subHomConnectingInt A B hA hB 0
          (legW (k := 2 + 1) (m := 0) (hA.union hB)
            (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM) K g)
        = openDuality₀Int (hA.inter hB)
            (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
            (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM)
            (legδInt A B hA hB 2 K g))

/-- The chart-agnostic base case: `P(W)` for a chart-convex `W` under **any** chart `e' : U' ≃ₜ V'`. -/
def HbaseConvG (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0) : Prop :=
  ∀ {U' : Set ↑(TopCat.of M)} {V' : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))}
    (_hU' : IsOpen U') (_hV' : IsOpen V') (e' : ↥U' ≃ₜ ↥V')
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W), W ⊆ U' →
    ∀ {Cw : Set (EuclideanSpace ℝ (Fin (2 + 2)))}, Convex ℝ Cw → IsOpen Cw →
    ∀ {pw : EuclideanSpace ℝ (Fin (2 + 2))}, pw ∈ Cw → Cw ⊆ V' →
    (∀ u : ↥U', (u : M) ∈ W ↔ ((e' u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2))) ∈ Cw)) →
    pdWindowPInt zM hzM W hWo

/-- **(A4c) Layer-B core (integral)**: `P(⋃ x ∈ t, chartSource x)` for a finite family of chart sources —
plain `Finset` induction; each member is a full chart source (A4c at `W := U`) via
`pdWindowPInt_of_chartOpen` under that chart, each MV intersection an open subset of ONE chart. Threads the
chart-agnostic `hcoreG`/`hbaseConvG` + `hproj`/`hfree`. -/
theorem pdWindowPInt_finset_chartSources {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (hproj : ∀ (S : Set ↑(TopCat.of M)) (j : ℕ), Module.Projective ℤ (relBoundariesInt S j))
    (hfree : ∀ (S : Set ↑(TopCat.of M)), IsCompact S →
      Module.Free ℤ (RelHomologyInt (Sᶜ) (2 + 2)))
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcoreG : HcoreG M zM hzM) (hbaseConvG : HbaseConvG M zM hzM)
    [DecidableEq M] (t : Finset M) :
    ∀ hop : IsOpen (⋃ x ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).source
      : Set ↑(TopCat.of M)),
    pdWindowPInt zM hzM
      (⋃ x ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).source) hop := by
  induction t using Finset.induction_on with
  | empty =>
    intro hop
    exact pdWindowPInt_congr zM hzM
      (show (∅ : Set ↑(TopCat.of M)) = _ by simp) isOpen_empty hop (pdWindowPInt_empty zM hzM)
  | insert x t hx ih =>
    intro hop
    set c := chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x with hcdef
    have hopx : IsOpen (c.source : Set ↑(TopCat.of M)) := c.open_source
    have hopS : IsOpen (⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source
        : Set ↑(TopCat.of M)) :=
      isOpen_biUnion (fun y _ => (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).open_source)
    have hPx : pdWindowPInt zM hzM (c.source : Set ↑(TopCat.of M)) hopx :=
      pdWindowPInt_of_chartOpen hproj hfree c.open_source c.open_target
        c.toHomeomorphSourceTarget zM hzM hcoreG
        (hbaseConvG c.open_source c.open_target c.toHomeomorphSourceTarget) hopx (le_refl _)
    have hPS : pdWindowPInt zM hzM
        (⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source
          : Set ↑(TopCat.of M)) hopS := ih hopS
    have hPI : pdWindowPInt zM hzM
        ((c.source : Set ↑(TopCat.of M))
          ∩ ⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source)
        (hopx.inter hopS) :=
      pdWindowPInt_of_chartOpen hproj hfree c.open_source c.open_target
        c.toHomeomorphSourceTarget zM hzM hcoreG
        (hbaseConvG c.open_source c.open_target c.toHomeomorphSourceTarget)
        (hopx.inter hopS) Set.inter_subset_left
    exact pdWindowPInt_congr zM hzM
      (Finset.set_biUnion_insert x t
        (fun y => (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source)).symm
      (hopx.union hopS) hop
      (pdWindowPInt_union_charted hproj hfree zM hzM hopx hopS
        (hcoreG (c.source : Set ↑(TopCat.of M)) _ hopx hopS).1
        (hcoreG (c.source : Set ↑(TopCat.of M)) _ hopx hopS).2 hPx hPS hPI)

/-- **`P(univ)` (integral)** — on a CLOSED (compact, charted) 4-manifold, the induction predicate holds on
the whole space. Threads the chart-agnostic `hcoreG`/`hbaseConvG` + `hproj`/`hfree`. -/
theorem pdWindowPInt_univ {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (hproj : ∀ (S : Set ↑(TopCat.of M)) (j : ℕ), Module.Projective ℤ (relBoundariesInt S j))
    (hfree : ∀ (S : Set ↑(TopCat.of M)), IsCompact S →
      Module.Free ℤ (RelHomologyInt (Sᶜ) (2 + 2)))
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcoreG : HcoreG M zM hzM) (hbaseConvG : HbaseConvG M zM hzM)
    (hop : IsOpen (Set.univ : Set ↑(TopCat.of M))) :
    pdWindowPInt zM hzM Set.univ hop := by
  classical
  haveI : CompactSpace ↑(TopCat.of M) := inferInstanceAs (CompactSpace M)
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover (isCompact_univ (X := ↑(TopCat.of M)))
    (fun x : M => ((chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).source : Set ↑(TopCat.of M)))
    (fun x => (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).open_source)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x⟩)
  have huniv : (⋃ x ∈ t, ((chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).source
      : Set ↑(TopCat.of M))) = Set.univ :=
    Set.Subset.antisymm (Set.subset_univ _) ht
  have hopt : IsOpen (⋃ x ∈ t, ((chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).source
      : Set ↑(TopCat.of M))) :=
    isOpen_biUnion (fun y _ => (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).open_source)
  exact pdWindowPInt_congr zM hzM huniv hopt hop
    (pdWindowPInt_finset_chartSources hproj hfree zM hzM hcoreG hbaseConvG t hopt)

end SKEFTHawking.SingularPDWindowInt
