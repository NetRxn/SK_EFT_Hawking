import Mathlib
import SKEFTHawking.SingularBaseCaseUpper
import SKEFTHawking.SingularBaseCaseD0
import SKEFTHawking.SingularConnSquareCloseNCBotApex
import SKEFTHawking.SingularCSCVanishAboveGeom
import SKEFTHawking.SingularGoodCompactEuclidean

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


/-- `Hᵏ⁺¹_c(∅) = 0`: every stage of the empty open's directed system is the relative cohomology
of the pair `(M, M∖∅) = (M, M)`, which vanishes (`relativeHomology_compl_empty_eq_zero` + relative
universal coefficients). -/
theorem cscOpen_empty_eq_zero {M : TopCat} {N : ℕ}
    (α : CompactlySupportedCohomologyOpen (∅ : Set ↑M) (N + 1)) : α = 0 := by
  refine SKEFTHawking.SingularCSCVanishAbove.cscOpen_eq_zero_of_stage_vanish
    (fun K x => ?_) α
  have hKempty : (↑K.1 : Set ↑M) = ∅ := Set.subset_empty_iff.mp K.2
  refine SKEFTHawking.SingularRelCohomVanishAbove.relCohomology_eq_zero_of_relHomology_eq_zero
    ((↑K.1 : Set ↑M)ᶜ) (fun β => ?_) x
  revert β
  rw [hKempty]
  exact fun β =>
    SKEFTHawking.SingularGoodCompactEuclidean.relativeHomology_compl_empty_eq_zero _ β

/-- `Hₙ(sub ∅) = 0`: the empty subspace has subsingleton chain modules. -/
theorem homology_sub_empty_eq_zero {M : TopCat} (n : ℕ)
    (b : Homology (sub (∅ : Set ↑M)) n) : b = 0 := by
  haveI := SKEFTHawking.SingularRelativeEmpty.singularChain_empty_subsingleton (X := M) n
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [show z = 0 from Subsingleton.elim z 0]
  exact Submodule.Quotient.mk_zero _

/-- **`P(∅)`** — all three conjuncts are bijections between trivial modules (the empty-
intersection branch of the finite-union induction). -/
theorem pdWindowP_empty {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0) :
    pdWindowP zM hzM (∅ : Set ↑M) isOpen_empty :=
  ⟨SKEFTHawking.SingularBaseCaseUpper.bijective_of_forall_eq_zero _
      (fun α => cscOpen_empty_eq_zero α) (fun b => homology_sub_empty_eq_zero _ b),
    SKEFTHawking.SingularBaseCaseUpper.bijective_of_forall_eq_zero _
      (fun α => cscOpen_empty_eq_zero α) (fun b => homology_sub_empty_eq_zero _ b),
    SKEFTHawking.SingularBaseCaseUpper.bijective_of_forall_eq_zero _
      (fun α => cscOpen_empty_eq_zero α) (fun b => homology_sub_empty_eq_zero _ b)⟩

/-- **The charted-manifold MV-step** — `pdWindowP_union` with the `csc⁵`-vanishing hypotheses
discharged by the track-A top-degree vanishing (`cscOpen_eq_zero_of_isOpen`, any open, `k > m+2`
at `m = 2`). -/
theorem pdWindowP_union_charted {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (zM : SingularChain (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    {U V : Set ↑(TopCat.of M)} (hU : IsOpen U) (hV : IsOpen V)
    (hPU : pdWindowP zM hzM U hU) (hPV : pdWindowP zM hzM V hV)
    (hPI : pdWindowP zM hzM (U ∩ V) (hU.inter hV)) :
    pdWindowP zM hzM (U ∪ V) (hU.union hV) := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  exact pdWindowP_union zM hzM hU hV
    (fun α => SKEFTHawking.SingularCSCVanishAboveGeom.cscOpen_eq_zero_of_isOpen (m := 2)
      (hU.inter hV) (by omega) α)
    (fun α => SKEFTHawking.SingularCSCVanishAboveGeom.cscOpen_eq_zero_of_isOpen (m := 2) hU (by omega) α)
    (fun α => SKEFTHawking.SingularCSCVanishAboveGeom.cscOpen_eq_zero_of_isOpen (m := 2) hV (by omega) α)
    hPU hPV hPI



/-- `P`-transport across a set identity (the `IsOpen` proofs are irrelevant). -/
theorem pdWindowP_congr {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    {W W' : Set ↑M} (h : W = W') (hW : IsOpen W) (hW' : IsOpen W')
    (hP : pdWindowP zM hzM W hW) : pdWindowP zM hzM W' hW' := by
  subst h
  exact hP

open SKEFTHawking.SingularChartBridge in
/-- **(A4b) Within-chart finite unions**: `P(⋃ i ∈ s, Wf i)` for a finite family of opens in a
COMMON chart, each carried to a convex (possibly empty) open image. Strong double induction:
`Finset.induction_on` with the family ∀-generalized — the MV intersection
`Wf j ∩ ⋃ᵢ Wf i = ⋃ᵢ (Wf j ∩ Wf i)` is again an `s`-indexed such family (convex ∩ convex);
empty images collapse to `P(∅)`, nonempty ones are B6. -/
theorem pdWindowP_finset_biUnion {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    {U : Set ↑(TopCat.of M)} {V : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    (zM : SingularChain (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcyc : castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (2 + 2) (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = (manifoldLocalIso x).symm 1)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    ∀ (Wf : ι → Set ↑(TopCat.of M)) (Cf : ι → Set (EuclideanSpace ℝ (Fin (2 + 2)))),
      (∀ i ∈ s, IsOpen (Wf i)) →
      (∀ i ∈ s, Convex ℝ (Cf i)) →
      (∀ i ∈ s, IsOpen (Cf i)) →
      (∀ i ∈ s, Cf i ⊆ V) →
      (∀ i ∈ s, Wf i ⊆ U) →
      (∀ i ∈ s, ∀ u : ↥U, (u : M) ∈ Wf i ↔
        ((e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2))) ∈ Cf i)) →
      ∀ hop : IsOpen (⋃ i ∈ s, Wf i),
      pdWindowP zM hzM (⋃ i ∈ s, Wf i) hop := by
  induction s using Finset.induction_on with
  | empty =>
    intro Wf Cf _ _ _ _ _ _ hop
    exact pdWindowP_congr zM hzM
      (show (∅ : Set ↑(TopCat.of M)) = ⋃ i ∈ (∅ : Finset ι), Wf i by simp)
      isOpen_empty hop (pdWindowP_empty zM hzM)
  | insert j s hj ih =>
    intro Wf Cf hopen hconv hCopen hCV hWU hWe hop
    have hjmem : j ∈ insert j s := Finset.mem_insert_self j s
    have hmem : ∀ i ∈ s, i ∈ insert j s := fun i hi => Finset.mem_insert_of_mem hi
    have hopj : IsOpen (Wf j) := hopen j hjmem
    have hopS : IsOpen (⋃ i ∈ s, Wf i) :=
      isOpen_biUnion (fun i hi => hopen i (hmem i hi))
    have hPj : pdWindowP zM hzM (Wf j) hopj := by
      rcases (Cf j).eq_empty_or_nonempty with hCe | hCne
      · refine pdWindowP_congr zM hzM ?_ isOpen_empty hopj (pdWindowP_empty zM hzM)
        symm
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have h := (hWe j hjmem ⟨x, hWU j hjmem hx⟩).mp hx
        rw [hCe] at h
        exact h
      · obtain ⟨p₀, hp₀⟩ := hCne
        exact pdWindowP_of_chartConvex hU hV e (hconv j hjmem) (hCopen j hjmem) hp₀
          (hCV j hjmem) hopj (hWU j hjmem) (hWe j hjmem) zM hzM hcyc hloc
    have hPS : pdWindowP zM hzM (⋃ i ∈ s, Wf i) hopS :=
      ih Wf Cf (fun i hi => hopen i (hmem i hi)) (fun i hi => hconv i (hmem i hi))
        (fun i hi => hCopen i (hmem i hi)) (fun i hi => hCV i (hmem i hi))
        (fun i hi => hWU i (hmem i hi)) (fun i hi => hWe i (hmem i hi)) hopS
    have hPI : pdWindowP zM hzM (Wf j ∩ ⋃ i ∈ s, Wf i) (hopj.inter hopS) := by
      have hidt : Wf j ∩ (⋃ i ∈ s, Wf i) = ⋃ i ∈ s, (Wf j ∩ Wf i) :=
        Set.inter_iUnion₂ _ _
      have hopI : IsOpen (⋃ i ∈ s, (Wf j ∩ Wf i)) :=
        isOpen_biUnion (fun i hi => hopj.inter (hopen i (hmem i hi)))
      refine pdWindowP_congr zM hzM hidt.symm hopI (hopj.inter hopS) ?_
      exact ih (fun i => Wf j ∩ Wf i) (fun i => Cf j ∩ Cf i)
        (fun i hi => hopj.inter (hopen i (hmem i hi)))
        (fun i hi => (hconv j hjmem).inter (hconv i (hmem i hi)))
        (fun i hi => (hCopen j hjmem).inter (hCopen i (hmem i hi)))
        (fun i hi => Set.inter_subset_right.trans (hCV i (hmem i hi)))
        (fun i hi => Set.inter_subset_left.trans (hWU j hjmem))
        (fun i hi u => by
          simp only [Set.mem_inter_iff]
          exact and_congr (hWe j hjmem u) (hWe i (hmem i hi) u)) hopI
    exact pdWindowP_congr zM hzM (Finset.set_biUnion_insert j s Wf).symm (hopj.union hopS) hop
      (pdWindowP_union_charted zM hzM hopj hopS hPj hPS hPI)


end SKEFTHawking.SingularPDWindow
