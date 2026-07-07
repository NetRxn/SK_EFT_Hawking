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

end SKEFTHawking.SingularPDWindowInt
