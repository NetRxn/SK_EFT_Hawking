import Mathlib
import SKEFTHawking.SingularBaseCaseUpper
import SKEFTHawking.SingularBaseCaseD0
import SKEFTHawking.SingularConnSquareCloseNCBotApex
import SKEFTHawking.SingularCSCVanishAboveGeom
import SKEFTHawking.SingularGoodCompactEuclidean
import SKEFTHawking.SingularFundamentalDualityEndpoint

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


/-! ## (A4c) The chart-open exhaustion -/

/-- The pullback of a Euclidean set through a chart: the subset of the chart domain carried
into `T`. -/
def chartPull {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))} (e : ↥U ≃ₜ ↥V)
    (T : Set (EuclideanSpace ℝ (Fin (2 + 2)))) : Set ↑(TopCat.of M) :=
  Subtype.val '' ((fun u : ↥U => (e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2)))) ⁻¹' T)

theorem mem_chartPull {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))} (e : ↥U ≃ₜ ↥V)
    (T : Set (EuclideanSpace ℝ (Fin (2 + 2)))) (u : ↥U) :
    (u : M) ∈ chartPull e T ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2))) ∈ T) := by
  constructor
  · rintro ⟨u', hu', hval⟩
    rwa [show u' = u from Subtype.ext hval] at hu'
  · exact fun h => ⟨u, h, rfl⟩

theorem chartPull_subset {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))} (e : ↥U ≃ₜ ↥V)
    (T : Set (EuclideanSpace ℝ (Fin (2 + 2)))) : chartPull e T ⊆ U := by
  rintro x ⟨u, _, rfl⟩
  exact u.2

theorem chartPull_isOpen {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))} (hU : IsOpen U) (e : ↥U ≃ₜ ↥V)
    {T : Set (EuclideanSpace ℝ (Fin (2 + 2)))} (hT : IsOpen T) :
    IsOpen (chartPull e T) :=
  hU.isOpenMap_subtype_val _
    (((continuous_subtype_val.comp e.continuous).isOpen_preimage) T hT)

theorem chartPull_iUnion {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))} (e : ↥U ≃ₜ ↥V)
    {ι : Sort*} (T : ι → Set (EuclideanSpace ℝ (Fin (2 + 2)))) :
    chartPull e (⋃ i, T i) = ⋃ i, chartPull e (T i) := by
  simp only [chartPull, Set.preimage_iUnion, Set.image_iUnion]

/-- The pullback of the chart image of `W ⊆ U` is `W` itself. -/
theorem chartPull_image {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (2 + 2))} (e : ↥U ≃ₜ ↥V)
    {W : Set ↑(TopCat.of M)} (hWU : W ⊆ U) :
    chartPull e ((fun u : ↥U => (e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2))))
      '' (Subtype.val ⁻¹' W)) = W := by
  have hinj : Function.Injective
      (fun u : ↥U => (e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2)))) :=
    fun u₁ u₂ h => e.injective (Subtype.ext h)
  rw [chartPull, Set.preimage_image_eq _ hinj, Subtype.image_preimage_coe,
    Set.inter_eq_self_of_subset_right hWU]

open SKEFTHawking.SingularChartBridge in
/-- **(A4c) `P` holds on every chart-open**: an open `W ⊆ U` is the pullback of its (open)
Euclidean chart image, which a countable family of balls exhausts (second countability);
the ball-truncations are A4b families and the exhaustion is monotone. The full Layer-A
conclusion for a single chart. -/
theorem pdWindowP_of_chartOpen {M : Type} [TopologicalSpace M] [T2Space M]
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
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (hWU : W ⊆ U) :
    pdWindowP zM hzM W hWo := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  -- the Euclidean chart image of W, an open subset of V
  set em : ↥U → EuclideanSpace ℝ (Fin (2 + 2)) :=
    fun u => (e u : ↑(SingularEuclideanAcyclic.Eucl (2 + 2))) with hemdef
  set O : Set (EuclideanSpace ℝ (Fin (2 + 2))) := em '' (Subtype.val ⁻¹' W) with hOdef
  have hOV : O ⊆ V := by
    rintro q ⟨u, _, rfl⟩
    exact (e u).2
  have hOopen : IsOpen O := by
    have hpre : IsOpen (Subtype.val ⁻¹' W : Set ↥U) := continuous_subtype_val.isOpen_preimage _ hWo
    have himg : IsOpen ((fun u : ↥U => e u) '' (Subtype.val ⁻¹' W) : Set ↥V) :=
      e.isOpenMap _ hpre
    have := hV.isOpenMap_subtype_val _ himg
    rwa [show Subtype.val '' ((fun u : ↥U => e u) '' (Subtype.val ⁻¹' W)) = O by
      rw [hOdef, ← Set.image_comp]; rfl] at this
  -- ball cover of O with balls inside O
  have hball : ∀ q : ↥O, ∃ ε > 0, Metric.ball (q : EuclideanSpace ℝ (Fin (2 + 2))) ε ⊆ O :=
    fun q => Metric.isOpen_iff.mp hOopen q q.2
  choose ε hε hballO using hball
  have hcover : (⋃ q : ↥O, Metric.ball (q : EuclideanSpace ℝ (Fin (2 + 2))) (ε q)) = O := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun q => hballO q)
    · exact fun q hq => Set.mem_iUnion.mpr ⟨⟨q, hq⟩, Metric.mem_ball_self (hε ⟨q, hq⟩)⟩
  -- countable subfamily
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun q : ↥O => Metric.ball (q : EuclideanSpace ℝ (Fin (2 + 2))) (ε q))
    (fun q => Metric.isOpen_ball)
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · -- O = ∅ hence W = ∅
    have hOempty : O = ∅ := by
      rw [← hcover, ← hTeq, hTe]
      simp
    have hWempty : W = ∅ := by
      have := hOempty
      rw [hOdef, Set.image_eq_empty] at this
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      exact absurd (show (⟨x, hWU hx⟩ : ↥U) ∈ (Subtype.val ⁻¹' W : Set ↥U) from hx)
        (by rw [this]; exact Set.notMem_empty _)
    exact pdWindowP_congr zM hzM hWempty.symm isOpen_empty hWo (pdWindowP_empty zM hzM)
  · -- enumerate the countable subfamily
    obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    -- the monotone finite-truncation exhaustion, each an A4b family
    have hstage : ∀ n : ℕ, ∀ hop : IsOpen (⋃ k ∈ Finset.range (n + 1),
        chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (2 + 2))) (ε (f k)))),
        pdWindowP zM hzM _ hop := by
      intro n hop
      exact pdWindowP_finset_biUnion hU hV e zM hzM hcyc hloc (Finset.range (n + 1))
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
    have hPmono := pdWindowP_monotone_union zM hzM hmono hopseq (fun n => hstage n (hopseq n))
    -- the union of the truncations is W
    refine pdWindowP_congr zM hzM ?_ _ hWo hPmono
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
            ((i : ↥O) : EuclideanSpace ℝ (Fin (2 + 2))) (ε i) := by
          rw [hTeq, hcover]
          exact hq
        obtain ⟨i, hiT, hqi⟩ := Set.mem_iUnion₂.mp h1
        obtain ⟨k, rfl⟩ : ∃ k, f k = i := by
          have hir : i ∈ Set.range f := by rw [← hf]; exact hiT
          exact hir
        exact Set.mem_iUnion.mpr ⟨k, hqi⟩
    rw [hOre, hOdef]
    exact chartPull_image e hWU


/-! ## Layer-B: the finite-chart-cover induction on the closed manifold -/

open SKEFTHawking.SingularChartBridge in
/-- **Layer-B core**: `P(⋃ x ∈ t, chartSource x)` for any finite family of chart sources —
plain `Finset` induction; each member is a full chart source (A4c at `W := U`), and each
MV intersection is an open subset of ONE chart (A4c again). -/
theorem pdWindowP_finset_chartSources {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (zM : SingularChain (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcyc : castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (2 + 2) (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = (manifoldLocalIso x).symm 1)
    [DecidableEq M] (t : Finset M) :
    ∀ hop : IsOpen (⋃ x ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).source
      : Set ↑(TopCat.of M)),
    pdWindowP zM hzM
      (⋃ x ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).source) hop := by
  induction t using Finset.induction_on with
  | empty =>
    intro hop
    exact pdWindowP_congr zM hzM
      (show (∅ : Set ↑(TopCat.of M)) = _ by simp) isOpen_empty hop (pdWindowP_empty zM hzM)
  | insert x t hx ih =>
    intro hop
    set c := chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x with hcdef
    have hopx : IsOpen (c.source : Set ↑(TopCat.of M)) := c.open_source
    have hopS : IsOpen (⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source
        : Set ↑(TopCat.of M)) :=
      isOpen_biUnion (fun y _ => (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).open_source)
    have hPx : pdWindowP zM hzM (c.source : Set ↑(TopCat.of M)) hopx :=
      pdWindowP_of_chartOpen c.open_source c.open_target c.toHomeomorphSourceTarget
        zM hzM hcyc hloc hopx (le_refl _)
    have hPS : pdWindowP zM hzM
        (⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source
          : Set ↑(TopCat.of M)) hopS := ih hopS
    have hPI : pdWindowP zM hzM
        ((c.source : Set ↑(TopCat.of M))
          ∩ ⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source)
        (hopx.inter hopS) :=
      pdWindowP_of_chartOpen c.open_source c.open_target c.toHomeomorphSourceTarget
        zM hzM hcyc hloc (hopx.inter hopS) Set.inter_subset_left
    exact pdWindowP_congr zM hzM
      (Finset.set_biUnion_insert x t
        (fun y => (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source)).symm
      (hopx.union hopS) hop
      (pdWindowP_union_charted zM hzM hopx hopS hPx hPS hPI)

open SKEFTHawking.SingularChartBridge in
/-- **`P(univ)` — the full Layer-A/Layer-B conclusion**: on a CLOSED (compact, charted)
4-manifold, the induction predicate holds on the whole space. -/
theorem pdWindowP_univ {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (zM : SingularChain (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcyc : castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (2 + 2) (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChain (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = (manifoldLocalIso x).symm 1)
    (hop : IsOpen (Set.univ : Set ↑(TopCat.of M))) :
    pdWindowP zM hzM Set.univ hop := by
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
  exact pdWindowP_congr zM hzM huniv hopt hop
    (pdWindowP_finset_chartSources zM hzM hcyc hloc t hopt)


/-! ## W-d1 (d1a): the ⊤-collapse of the P-side colimit (compact `M`) -/

/-- For compact `M`, `CompactsIn univ` has a top: the whole space as a compact. -/
noncomputable instance {M : TopCat} [CompactSpace ↑M] :
    OrderTop (SKEFTHawking.SingularCompactsInOpen.CompactsIn (Set.univ : Set ↑M)) where
  top := ⟨⊤, Set.subset_univ _⟩
  le_top _K := Subtype.coe_le_coe.mp le_top

/-- **The P-side colimit collapses onto its `⊤`-stage** (compact `M`): `of ⊤` is bijective. -/
theorem of_top_univ_bijective {M : TopCat} [CompactSpace ↑M] (k : ℕ) :
    Function.Bijective (Module.DirectLimit.of (ZMod 2)
      (SKEFTHawking.SingularCompactsInOpen.CompactsIn (Set.univ : Set ↑M))
      (cohomGW (Set.univ : Set ↑M) k) (cohomFW (Set.univ : Set ↑M) k) ⊤) :=
  SKEFTHawking.SingularDirectLimitTop.of_top_bijective _ _

/-- **The `⊤`-stage leg of an injective `D_univ` is injective** — the P-side half of the W-d1
endpoint bridge. -/
theorem legW_top_injective {M : TopCat} [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z₀ : SingularChain M (k + m + 1)) (hz₀ : chainBoundary M (k + m) z₀ = 0)
    (hD : Function.Injective ⇑(openDuality (k := k) (m := m) hop z₀ hz₀)) :
    Function.Injective ⇑(SKEFTHawking.SingularOpenDuality.legW hop z₀ hz₀ ⊤) := by
  intro a b hab
  have h1 : openDuality (k := k) (m := m) hop z₀ hz₀
        (Module.DirectLimit.of (ZMod 2)
          (SKEFTHawking.SingularCompactsInOpen.CompactsIn (Set.univ : Set ↑M))
          (cohomGW (Set.univ : Set ↑M) k) (cohomFW (Set.univ : Set ↑M) k) ⊤ a)
      = openDuality (k := k) (m := m) hop z₀ hz₀
        (Module.DirectLimit.of (ZMod 2)
          (SKEFTHawking.SingularCompactsInOpen.CompactsIn (Set.univ : Set ↑M))
          (cohomGW (Set.univ : Set ↑M) k) (cohomFW (Set.univ : Set ↑M) k) ⊤ b) := by
    rw [openDuality_of, openDuality_of]
    exact hab
  exact (of_top_univ_bijective k).injective (hD h1)


/-! ## W-d1 (d1b/d1c): the ⊤-stage leg square and the fundamental-duality injectivity -/

/-- Every chain is a `univ`-subspace chain. -/
theorem mem_subspaceChains_univ {M : TopCat} {n : ℕ} (c : SingularChain M n) :
    c ∈ subspaceChains (Set.univ : Set ↑M) n :=
  SKEFTHawking.SingularExcision.mem_subspaceChains_of_support (fun _ _ => Set.subset_univ _)

/-- `Homology.map` of the `univ`-subspace inclusion is bijective (it is a homeomorphism). -/
theorem homology_map_ambIncl_univ_bijective {M : TopCat} (n : ℕ) :
    Function.Bijective (SKEFTHawking.SingularFunctoriality.Homology.map
      (SKEFTHawking.SingularMayerVietorisLES.ambIncl (Set.univ : Set ↑M)) n) :=
  SKEFTHawking.SingularHomotopyInvariance.Homology.map_bijective_of_comp_id_all
    (SKEFTHawking.SingularMayerVietorisLES.ambIncl (Set.univ : Set ↑M))
    (⟨fun x => ⟨x, Set.mem_univ x⟩, Continuous.subtype_mk continuous_id _⟩ :
      C(↑M, ↑(sub (Set.univ : Set ↑M))))
    (ContinuousMap.ext fun _z => Subtype.ext rfl)
    (ContinuousMap.ext fun _z => rfl) n

open SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularOpenDualityCycle
  SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularRelativeDuality
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularMayerVietorisLES in
/-- Fresh-budget helper: the `D_univ` `⊤`-leg with its per-stage cycle swapped for the ambient
`z` (`fundCycleW_relHomologous` through `relativeDualityK_cycle_compat_relB`). -/
private theorem legW_top_eq_relativeDualityK {M : TopCat} [T2Space ↑M] [CompactSpace ↑M]
    {k m : ℕ} (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChain M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (x : cohomGW (Set.univ : Set ↑M) k (⊤ : SKEFTHawking.SingularCompactsInOpen.CompactsIn
      (Set.univ : Set ↑M))) :
    legW hop z hz (⊤ : SKEFTHawking.SingularCompactsInOpen.CompactsIn
        (Set.univ : Set ↑M)) x
      = relativeDualityK ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ)
          (Set.univ : Set ↑M) k m z (mem_subspaceChains_univ z)
          (by rw [hz]; exact Submodule.zero_mem _) x := by
  refine relativeDualityK_cycle_compat_relB _ _ _ _ _ _ ?_ ?_ x
  · rw [Set.biUnion_pair, interior_univ]
    exact Set.eq_univ_of_univ_subset (Set.subset_union_left)
  · have h := fundCycleW_relHomologous hop z hz
      (⊤ : SKEFTHawking.SingularCompactsInOpen.CompactsIn (Set.univ : Set ↑M))
    rwa [add_comm (RelativeChain.mk _ (k + m + 1) z)
      (RelativeChain.mk _ (k + m + 1) (fundCycleW hop z hz ⊤))] at h

open SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularOpenDualityCycle
  SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularRelativeDuality
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularMayerVietorisLES in
/-- **(d1b) The `⊤`-stage leg square**: the fundamental-duality `⊤`-leg (`relativeDuality` at the
ambient cycle `z`) is the `univ`-inclusion pushforward of the `D_univ` `⊤`-leg (`legW` at the
per-stage `fundCycleW`) — the cycle mismatch is `fundCycleW_relHomologous`, absorbed by
`relativeDualityK_cycle_compat_relB`. -/
theorem relativeDuality_top_eq_map_legW {M : TopCat} [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChain M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (x : cohomGW (Set.univ : Set ↑M) k (⊤ : SKEFTHawking.SingularCompactsInOpen.CompactsIn
      (Set.univ : Set ↑M))) :
    SKEFTHawking.SingularRelativeDuality.relativeDuality
        ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) k m z
        (by rw [hz]; exact Submodule.zero_mem _) x
      = Homology.map (ambIncl (Set.univ : Set ↑M)) (m + 1)
          (legW hop z hz (⊤ : SKEFTHawking.SingularCompactsInOpen.CompactsIn
            (Set.univ : Set ↑M)) x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hchain : mapChain (ambIncl (Set.univ : Set ↑M)) (m + 1)
        (pullbackDualityₗ ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ)
          (Set.univ : Set ↑M) z (mem_subspaceChains_univ z) a)
      = cap a.1.1 z :=
    (congrFun (congrArg DFunLike.coe (mapChain_ambIncl (Set.univ : Set ↑M) (m + 1)))
      _).trans (chainIncl_pullbackDualityₗ
        ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) (Set.univ : Set ↑M)
        z (mem_subspaceChains_univ z) a)
  exact (congrArg (fun t => Homology.mk M (m + 1) t) (Subtype.ext hchain.symm)).trans
    (congrArg (fun t => Homology.map (ambIncl (Set.univ : Set ↑M)) (m + 1) t)
      (legW_top_eq_relativeDualityK hop z hz (Submodule.Quotient.mk a)).symm)

open SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularFunctoriality
  SKEFTHawking.SingularMayerVietorisLES in
/-- **(d1c) W-d1: the fundamental duality is injective when `D_univ` is** — both colimits
collapse onto their `⊤`-stages, whose legs agree by the (d1b) square. -/
theorem fundamentalDuality_injective_of_openDuality_univ_injective {M : TopCat}
    [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChain M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (hD : Function.Injective ⇑(openDuality (k := k) (m := m) hop z hz)) :
    Function.Injective
      ⇑(SKEFTHawking.SingularFundamentalDuality.fundamentalDuality k m z hz) := by
  have hleg := legW_top_injective hop z hz hD
  intro α β hαβ
  obtain ⟨x, rfl⟩ := (SKEFTHawking.SingularDirectLimitTop.of_top_bijective
    (SKEFTHawking.SingularCohomologyColimit.cohomG (M := M) k) (SKEFTHawking.SingularCohomologyColimit.cohomF k)).surjective α
  obtain ⟨y, rfl⟩ := (SKEFTHawking.SingularDirectLimitTop.of_top_bijective
    (SKEFTHawking.SingularCohomologyColimit.cohomG (M := M) k) (SKEFTHawking.SingularCohomologyColimit.cohomF k)).surjective β
  have hfac : ∀ w, SKEFTHawking.SingularFundamentalDuality.fundamentalDuality k m z hz
        (Module.DirectLimit.of (ZMod 2) (TopologicalSpace.Compacts ↑M)
          (SKEFTHawking.SingularCohomologyColimit.cohomG k) (SKEFTHawking.SingularCohomologyColimit.cohomF k) ⊤ w)
      = SKEFTHawking.SingularRelativeDuality.relativeDuality
          ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) k m z
          (by rw [hz]; exact Submodule.zero_mem _) w := fun w =>
    Module.DirectLimit.lift_of _ _ w
  rw [hfac, hfac, relativeDuality_top_eq_map_legW hop z hz,
    relativeDuality_top_eq_map_legW hop z hz] at hαβ
  exact congrArg _ (hleg ((homology_map_ambIncl_univ_bijective (m + 1)).injective hαβ))


end SKEFTHawking.SingularPDWindow
