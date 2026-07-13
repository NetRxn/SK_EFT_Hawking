import Mathlib
import SKEFTHawking.SingularPDWindow

/-!
# W-A (P₂ window) — the deg-2 finite-chart-cover assembly for closed surfaces (the `m = 0` mirror)

`pdWindowP2 zM hzM W hW` is the TWO-conjunct Bott–Tu induction carrier for the deg-2 (surface)
Poincaré duality: `Bij D@(1,0) ∧ Bij D⁰`, both presented from ONE master cycle
`zM : SingularChain _ (0 + 1 + 0 + 1)` (the `N = 0` engine-native spelling, shared verbatim by both
conjuncts — unlike the 4-manifold's `pdWindowP`, no `castChain` junction is needed anywhere in this
file, because at `m = 0` there is no "upper" (`m ≥ 1`) engine to thread: no room for an intermediate
degree between the top cohomology and the `D⁰` truncation).

This is the dim-2 mirror of `SingularPDWindow.pdWindowP` (the closed-4-manifold deg-4 tower):

* conjunct 1 (`D@(1,0)`) is exactly `openDuality_union_bijective_bot (N := 0)`'s
  conclusion/hypothesis shape (the `SingularPDWindow.pdWindowP`'s conjunct-2 engine, re-indexed);
* conjunct 2 (`D⁰`) is exactly `openDuality₀_union_bijective (N := 0)`'s conclusion/hypothesis
  shape (the conjunct-3 `D⁰` engine, re-indexed) — both engines are already `N`-generic
  (`SingularConnSquareCloseNCBotApex`), so no NEW mathematics is required here.

**Base case (B6, dim-2)**: `pdWindowP2_of_chartConvex` — for a chart-convex `W`, conjunct 1 is
"both sides trivial" via the `k = 1` companion to the `2 ≤ k` upper base case
(`SingularCSCConvexChart.cscOpen_one_eq_zero_of_chartConvex`, dimension-generic) together with
`SingularConvexSubAcyclic.homology_chartConvexSub_eq_zero` (dimension-generic); conjunct 2 is B4c
(`SingularBaseCaseD0.openDuality₀_bijective_of_chartConvex`, dimension-generic at `m := 0`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularOpenDuality
open SKEFTHawking.SingularOpenDualityBot

namespace SKEFTHawking.SingularPDWindow2

/-- **The deg-2 PD-induction predicate** `P₂(W) = Bij D@(1,0) ∧ Bij D⁰`, both presented from the
master cycle `zM` (the `N = 0` engine-native spelling; the dim-2 mirror of
`SingularPDWindow.pdWindowP`). -/
def pdWindowP2 {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (0 + 1 + 0 + 1))
    (hzM : chainBoundary M (0 + 1 + 0) zM = 0)
    (W : Set ↑M) (hW : IsOpen W) : Prop :=
  Function.Bijective (openDuality (k := 0 + 1) (m := 0) hW zM hzM)
  ∧ Function.Bijective (openDuality₀ (k := 0 + 1) hW zM hzM)

open SKEFTHawking.SingularChartBridge in
/-- **B6 (dim-2): the base case** — `P₂(W)` holds for every chart-convex open `W` (the chart `e`
carries `W` exactly onto a convex open `C ∋ p₀`), given the master cycle's local-generator
property. -/
theorem pdWindowP2_of_chartConvex {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) M]
    {U : Set ↑(TopCat.of M)} {V : Set ↑(SingularEuclideanAcyclic.Eucl (0 + 2))}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (0 + 2)))} (hCconv : Convex ℝ C) (hCopen : IsOpen C)
    {p₀ : EuclideanSpace ℝ (Fin (0 + 2))} (hp₀ : p₀ ∈ C) (hCV : C ⊆ V)
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (0 + 2))) ∈ C))
    (zM : SingularChain (TopCat.of M) (0 + 1 + 0 + 1))
    (hzM : chainBoundary (TopCat.of M) (0 + 1 + 0) zM = 0)
    (hcyc : zM ∈ cycles (TopCat.of M) (0 + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (0 + 2) (Homology.mk (TopCat.of M) (0 + 2) ⟨zM, hcyc⟩)
      = (manifoldLocalIso x).symm 1) :
    pdWindowP2 zM hzM W hWo := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  refine ⟨SKEFTHawking.SingularBaseCaseUpper.bijective_of_forall_eq_zero _
      (fun α => SKEFTHawking.SingularCSCConvexChart.cscOpen_one_eq_zero_of_chartConvex
        hU hV e hCconv hCopen ⟨p₀, hp₀⟩ hCV hWU hWe α)
      (fun x => SKEFTHawking.SingularConvexSubAcyclic.homology_chartConvexSub_eq_zero
        e hCconv hp₀ hCV hWU hWe 0 x),
    SKEFTHawking.SingularBaseCaseD0.openDuality₀_bijective_of_chartConvex hU hV e hCconv
      hCopen hp₀ hCV hWo hWU hWe _ _ hcyc hloc⟩

/-- **Layer-A: the Mayer–Vietoris step** — `P₂(U) ∧ P₂(V) ∧ P₂(U∩V) → P₂(U∪V)`, through the two
five-lemma engines (bot at `N = 0`, `D⁰`-step at `N = 0`). The `csc⁵`-vanishing hypotheses feed the
`D⁰`-step's truncated right end. -/
theorem pdWindowP2_union {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (0 + 1 + 0 + 1))
    (hzM : chainBoundary M (0 + 1 + 0) zM = 0)
    {U V : Set ↑M} (hU : IsOpen U) (hV : IsOpen V)
    (hvanI : ∀ α : CompactlySupportedCohomologyOpen (U ∩ V) (0 + 1 + 2), α = 0)
    (hvanU : ∀ α : CompactlySupportedCohomologyOpen U (0 + 1 + 2), α = 0)
    (hvanV : ∀ α : CompactlySupportedCohomologyOpen V (0 + 1 + 2), α = 0)
    (hPU : pdWindowP2 zM hzM U hU) (hPV : pdWindowP2 zM hzM V hV)
    (hPI : pdWindowP2 zM hzM (U ∩ V) (hU.inter hV)) :
    pdWindowP2 zM hzM (U ∪ V) (hU.union hV) := by
  obtain ⟨hU1, hU2⟩ := hPU
  obtain ⟨hV1, hV2⟩ := hPV
  obtain ⟨hI1, hI2⟩ := hPI
  refine ⟨?_, ?_⟩
  · exact SKEFTHawking.SingularConnSquareCloseNCBotApex.openDuality_union_bijective_bot
      (N := 0) hU hV zM hzM hI1.surjective hU1 hV1 hI2 hU2.injective hV2.injective
  · exact SKEFTHawking.SingularConnSquareCloseNCBotApex.openDuality₀_union_bijective
      (N := 0) hU hV zM hzM hvanI hvanU hvanV hI2.surjective hU2 hV2

/-- **Layer-A: monotone-union stability** — `P₂` passes to increasing unions (the two
monotone-union engines, conjunct-wise). -/
theorem pdWindowP2_monotone_union {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (0 + 1 + 0 + 1))
    (hzM : chainBoundary M (0 + 1 + 0) zM = 0)
    {W : ℕ → Set ↑M} (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (hP : ∀ n, pdWindowP2 zM hzM (W n) (hopen n)) :
    pdWindowP2 zM hzM (⋃ n, W n) (isOpen_iUnion hopen) :=
  ⟨SKEFTHawking.SingularOpenDualityMonotoneUnion.openDuality_monotone_union_bijective
      hmono hopen _ _ (fun n => (hP n).1),
    SKEFTHawking.SingularConnSquareCloseNCBotApex.openDuality₀_monotone_union_bijective
      hmono hopen _ _ (fun n => (hP n).2)⟩

/-- **`P₂(∅)`** — both conjuncts are bijections between trivial modules (the empty-intersection
branch of the finite-union induction). Reuses `SingularPDWindow`'s dimension-generic empty-vanish
helpers. -/
theorem pdWindowP2_empty {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (0 + 1 + 0 + 1))
    (hzM : chainBoundary M (0 + 1 + 0) zM = 0) :
    pdWindowP2 zM hzM (∅ : Set ↑M) isOpen_empty :=
  ⟨SKEFTHawking.SingularBaseCaseUpper.bijective_of_forall_eq_zero _
      (fun α => SKEFTHawking.SingularPDWindow.cscOpen_empty_eq_zero α)
      (fun b => SKEFTHawking.SingularPDWindow.homology_sub_empty_eq_zero _ b),
    SKEFTHawking.SingularBaseCaseUpper.bijective_of_forall_eq_zero _
      (fun α => SKEFTHawking.SingularPDWindow.cscOpen_empty_eq_zero α)
      (fun b => SKEFTHawking.SingularPDWindow.homology_sub_empty_eq_zero _ b)⟩

/-- **The charted-manifold MV-step** — `pdWindowP2_union` with the `csc⁵`-vanishing hypotheses
discharged by the track-A top-degree vanishing (`cscOpen_eq_zero_of_isOpen`, any open, `k > m+2`
at `m = 0`). -/
theorem pdWindowP2_union_charted {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) M]
    (zM : SingularChain (TopCat.of M) (0 + 1 + 0 + 1))
    (hzM : chainBoundary (TopCat.of M) (0 + 1 + 0) zM = 0)
    {U V : Set ↑(TopCat.of M)} (hU : IsOpen U) (hV : IsOpen V)
    (hPU : pdWindowP2 zM hzM U hU) (hPV : pdWindowP2 zM hzM V hV)
    (hPI : pdWindowP2 zM hzM (U ∩ V) (hU.inter hV)) :
    pdWindowP2 zM hzM (U ∪ V) (hU.union hV) := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  exact pdWindowP2_union zM hzM hU hV
    (fun α => SKEFTHawking.SingularCSCVanishAboveGeom.cscOpen_eq_zero_of_isOpen (m := 0)
      (hU.inter hV) (by omega) α)
    (fun α => SKEFTHawking.SingularCSCVanishAboveGeom.cscOpen_eq_zero_of_isOpen (m := 0) hU (by omega) α)
    (fun α => SKEFTHawking.SingularCSCVanishAboveGeom.cscOpen_eq_zero_of_isOpen (m := 0) hV (by omega) α)
    hPU hPV hPI

/-- `P₂`-transport across a set identity (the `IsOpen` proofs are irrelevant). -/
theorem pdWindowP2_congr {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (0 + 1 + 0 + 1))
    (hzM : chainBoundary M (0 + 1 + 0) zM = 0)
    {W W' : Set ↑M} (h : W = W') (hW : IsOpen W) (hW' : IsOpen W')
    (hP : pdWindowP2 zM hzM W hW) : pdWindowP2 zM hzM W' hW' := by
  subst h
  exact hP

open SKEFTHawking.SingularChartBridge in
/-- **(A4b) Within-chart finite unions**: `P₂(⋃ i ∈ s, Wf i)` for a finite family of opens in a
COMMON chart, each carried to a convex (possibly empty) open image. Strong double induction:
`Finset.induction_on` with the family ∀-generalized. -/
theorem pdWindowP2_finset_biUnion {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) M]
    {U : Set ↑(TopCat.of M)} {V : Set ↑(SingularEuclideanAcyclic.Eucl (0 + 2))}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    (zM : SingularChain (TopCat.of M) (0 + 1 + 0 + 1))
    (hzM : chainBoundary (TopCat.of M) (0 + 1 + 0) zM = 0)
    (hcyc : zM ∈ cycles (TopCat.of M) (0 + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (0 + 2) (Homology.mk (TopCat.of M) (0 + 2) ⟨zM, hcyc⟩)
      = (manifoldLocalIso x).symm 1)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    ∀ (Wf : ι → Set ↑(TopCat.of M)) (Cf : ι → Set (EuclideanSpace ℝ (Fin (0 + 2)))),
      (∀ i ∈ s, IsOpen (Wf i)) →
      (∀ i ∈ s, Convex ℝ (Cf i)) →
      (∀ i ∈ s, IsOpen (Cf i)) →
      (∀ i ∈ s, Cf i ⊆ V) →
      (∀ i ∈ s, Wf i ⊆ U) →
      (∀ i ∈ s, ∀ u : ↥U, (u : M) ∈ Wf i ↔
        ((e u : ↑(SingularEuclideanAcyclic.Eucl (0 + 2))) ∈ Cf i)) →
      ∀ hop : IsOpen (⋃ i ∈ s, Wf i),
      pdWindowP2 zM hzM (⋃ i ∈ s, Wf i) hop := by
  induction s using Finset.induction_on with
  | empty =>
    intro Wf Cf _ _ _ _ _ _ hop
    exact pdWindowP2_congr zM hzM
      (show (∅ : Set ↑(TopCat.of M)) = ⋃ i ∈ (∅ : Finset ι), Wf i by simp)
      isOpen_empty hop (pdWindowP2_empty zM hzM)
  | insert j s hj ih =>
    intro Wf Cf hopen hconv hCopen hCV hWU hWe hop
    have hjmem : j ∈ insert j s := Finset.mem_insert_self j s
    have hmem : ∀ i ∈ s, i ∈ insert j s := fun i hi => Finset.mem_insert_of_mem hi
    have hopj : IsOpen (Wf j) := hopen j hjmem
    have hopS : IsOpen (⋃ i ∈ s, Wf i) :=
      isOpen_biUnion (fun i hi => hopen i (hmem i hi))
    have hPj : pdWindowP2 zM hzM (Wf j) hopj := by
      rcases (Cf j).eq_empty_or_nonempty with hCe | hCne
      · refine pdWindowP2_congr zM hzM ?_ isOpen_empty hopj (pdWindowP2_empty zM hzM)
        symm
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have h := (hWe j hjmem ⟨x, hWU j hjmem hx⟩).mp hx
        rw [hCe] at h
        exact h
      · obtain ⟨p₀, hp₀⟩ := hCne
        exact pdWindowP2_of_chartConvex hU hV e (hconv j hjmem) (hCopen j hjmem) hp₀
          (hCV j hjmem) hopj (hWU j hjmem) (hWe j hjmem) zM hzM hcyc hloc
    have hPS : pdWindowP2 zM hzM (⋃ i ∈ s, Wf i) hopS :=
      ih Wf Cf (fun i hi => hopen i (hmem i hi)) (fun i hi => hconv i (hmem i hi))
        (fun i hi => hCopen i (hmem i hi)) (fun i hi => hCV i (hmem i hi))
        (fun i hi => hWU i (hmem i hi)) (fun i hi => hWe i (hmem i hi)) hopS
    have hPI : pdWindowP2 zM hzM (Wf j ∩ ⋃ i ∈ s, Wf i) (hopj.inter hopS) := by
      have hidt : Wf j ∩ (⋃ i ∈ s, Wf i) = ⋃ i ∈ s, (Wf j ∩ Wf i) :=
        Set.inter_iUnion₂ _ _
      have hopI : IsOpen (⋃ i ∈ s, (Wf j ∩ Wf i)) :=
        isOpen_biUnion (fun i hi => hopj.inter (hopen i (hmem i hi)))
      refine pdWindowP2_congr zM hzM hidt.symm hopI (hopj.inter hopS) ?_
      exact ih (fun i => Wf j ∩ Wf i) (fun i => Cf j ∩ Cf i)
        (fun i hi => hopj.inter (hopen i (hmem i hi)))
        (fun i hi => (hconv j hjmem).inter (hconv i (hmem i hi)))
        (fun i hi => (hCopen j hjmem).inter (hCopen i (hmem i hi)))
        (fun i hi => Set.inter_subset_right.trans (hCV i (hmem i hi)))
        (fun i hi => Set.inter_subset_left.trans (hWU j hjmem))
        (fun i hi u => by
          simp only [Set.mem_inter_iff]
          exact and_congr (hWe j hjmem u) (hWe i (hmem i hi) u)) hopI
    exact pdWindowP2_congr zM hzM (Finset.set_biUnion_insert j s Wf).symm (hopj.union hopS) hop
      (pdWindowP2_union_charted zM hzM hopj hopS hPj hPS hPI)


/-! ## (A4c) The chart-open exhaustion -/

/-- The pullback of a Euclidean set through a chart: the subset of the chart domain carried
into `T`. -/
def chartPull {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (0 + 2))} (e : ↥U ≃ₜ ↥V)
    (T : Set (EuclideanSpace ℝ (Fin (0 + 2)))) : Set ↑(TopCat.of M) :=
  Subtype.val '' ((fun u : ↥U => (e u : ↑(SingularEuclideanAcyclic.Eucl (0 + 2)))) ⁻¹' T)

theorem mem_chartPull {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (0 + 2))} (e : ↥U ≃ₜ ↥V)
    (T : Set (EuclideanSpace ℝ (Fin (0 + 2)))) (u : ↥U) :
    (u : M) ∈ chartPull e T ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (0 + 2))) ∈ T) := by
  constructor
  · rintro ⟨u', hu', hval⟩
    rwa [show u' = u from Subtype.ext hval] at hu'
  · exact fun h => ⟨u, h, rfl⟩

theorem chartPull_subset {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (0 + 2))} (e : ↥U ≃ₜ ↥V)
    (T : Set (EuclideanSpace ℝ (Fin (0 + 2)))) : chartPull e T ⊆ U := by
  rintro x ⟨u, _, rfl⟩
  exact u.2

theorem chartPull_isOpen {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (0 + 2))} (hU : IsOpen U) (e : ↥U ≃ₜ ↥V)
    {T : Set (EuclideanSpace ℝ (Fin (0 + 2)))} (hT : IsOpen T) :
    IsOpen (chartPull e T) :=
  hU.isOpenMap_subtype_val _
    (((continuous_subtype_val.comp e.continuous).isOpen_preimage) T hT)

theorem chartPull_iUnion {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (0 + 2))} (e : ↥U ≃ₜ ↥V)
    {ι : Sort*} (T : ι → Set (EuclideanSpace ℝ (Fin (0 + 2)))) :
    chartPull e (⋃ i, T i) = ⋃ i, chartPull e (T i) := by
  simp only [chartPull, Set.preimage_iUnion, Set.image_iUnion]

/-- The pullback of the chart image of `W ⊆ U` is `W` itself. -/
theorem chartPull_image {M : Type} [TopologicalSpace M] {U : Set ↑(TopCat.of M)}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (0 + 2))} (e : ↥U ≃ₜ ↥V)
    {W : Set ↑(TopCat.of M)} (hWU : W ⊆ U) :
    chartPull e ((fun u : ↥U => (e u : ↑(SingularEuclideanAcyclic.Eucl (0 + 2))))
      '' (Subtype.val ⁻¹' W)) = W := by
  have hinj : Function.Injective
      (fun u : ↥U => (e u : ↑(SingularEuclideanAcyclic.Eucl (0 + 2)))) :=
    fun u₁ u₂ h => e.injective (Subtype.ext h)
  rw [chartPull, Set.preimage_image_eq _ hinj, Subtype.image_preimage_coe,
    Set.inter_eq_self_of_subset_right hWU]

open SKEFTHawking.SingularChartBridge in
/-- **(A4c) `P₂` holds on every chart-open**: an open `W ⊆ U` is the pullback of its (open)
Euclidean chart image, which a countable family of balls exhausts (second countability);
the ball-truncations are A4b families and the exhaustion is monotone. The full Layer-A
conclusion for a single chart. -/
theorem pdWindowP2_of_chartOpen {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) M]
    {U : Set ↑(TopCat.of M)} {V : Set ↑(SingularEuclideanAcyclic.Eucl (0 + 2))}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    (zM : SingularChain (TopCat.of M) (0 + 1 + 0 + 1))
    (hzM : chainBoundary (TopCat.of M) (0 + 1 + 0) zM = 0)
    (hcyc : zM ∈ cycles (TopCat.of M) (0 + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (0 + 2) (Homology.mk (TopCat.of M) (0 + 2) ⟨zM, hcyc⟩)
      = (manifoldLocalIso x).symm 1)
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (hWU : W ⊆ U) :
    pdWindowP2 zM hzM W hWo := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  -- the Euclidean chart image of W, an open subset of V
  set em : ↥U → EuclideanSpace ℝ (Fin (0 + 2)) :=
    fun u => (e u : ↑(SingularEuclideanAcyclic.Eucl (0 + 2))) with hemdef
  set O : Set (EuclideanSpace ℝ (Fin (0 + 2))) := em '' (Subtype.val ⁻¹' W) with hOdef
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
  have hball : ∀ q : ↥O, ∃ ε > 0, Metric.ball (q : EuclideanSpace ℝ (Fin (0 + 2))) ε ⊆ O :=
    fun q => Metric.isOpen_iff.mp hOopen q q.2
  choose ε hε hballO using hball
  have hcover : (⋃ q : ↥O, Metric.ball (q : EuclideanSpace ℝ (Fin (0 + 2))) (ε q)) = O := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun q => hballO q)
    · exact fun q hq => Set.mem_iUnion.mpr ⟨⟨q, hq⟩, Metric.mem_ball_self (hε ⟨q, hq⟩)⟩
  -- countable subfamily
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun q : ↥O => Metric.ball (q : EuclideanSpace ℝ (Fin (0 + 2))) (ε q))
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
    exact pdWindowP2_congr zM hzM hWempty.symm isOpen_empty hWo (pdWindowP2_empty zM hzM)
  · -- enumerate the countable subfamily
    obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    -- the monotone finite-truncation exhaustion, each an A4b family
    have hstage : ∀ n : ℕ, ∀ hop : IsOpen (⋃ k ∈ Finset.range (n + 1),
        chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (0 + 2))) (ε (f k)))),
        pdWindowP2 zM hzM _ hop := by
      intro n hop
      exact pdWindowP2_finset_biUnion hU hV e zM hzM hcyc hloc (Finset.range (n + 1))
        (fun k => chartPull e (Metric.ball ((f k : ↥O) : _) (ε (f k))))
        (fun k => Metric.ball ((f k : ↥O) : _) (ε (f k)))
        (fun k _ => chartPull_isOpen hU e Metric.isOpen_ball)
        (fun k _ => convex_ball _ _)
        (fun k _ => Metric.isOpen_ball)
        (fun k _ => (hballO (f k)).trans hOV)
        (fun k _ => chartPull_subset e _)
        (fun k _ u => mem_chartPull e _ u) hop
    have hopseq : ∀ n : ℕ, IsOpen (⋃ k ∈ Finset.range (n + 1),
        chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (0 + 2))) (ε (f k)))) :=
      fun n => isOpen_biUnion (fun k _ => chartPull_isOpen hU e Metric.isOpen_ball)
    have hmono : ∀ n, (⋃ k ∈ Finset.range (n + 1),
          chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (0 + 2))) (ε (f k))))
        ⊆ ⋃ k ∈ Finset.range (n + 1 + 1),
          chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (0 + 2))) (ε (f k))) :=
      fun n => Set.biUnion_subset_biUnion_left
        (fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))
    have hPmono := pdWindowP2_monotone_union zM hzM hmono hopseq (fun n => hstage n (hopseq n))
    -- the union of the truncations is W
    refine pdWindowP2_congr zM hzM ?_ _ hWo hPmono
    have hcollapse : (⋃ n, ⋃ k ∈ Finset.range (n + 1),
          chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (0 + 2))) (ε (f k))))
        = ⋃ k : ℕ, chartPull e
            (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (0 + 2))) (ε (f k))) := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_range]
      exact ⟨fun ⟨n, k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, k, Nat.lt_succ_self k, h⟩⟩
    rw [hcollapse, ← chartPull_iUnion e]
    have hOre : (⋃ k : ℕ, Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (0 + 2))) (ε (f k)))
        = O := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset (fun k => hballO (f k))
      · intro q hq
        have h1 : q ∈ ⋃ i ∈ T, Metric.ball
            ((i : ↥O) : EuclideanSpace ℝ (Fin (0 + 2))) (ε i) := by
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
/-- **Layer-B core**: `P₂(⋃ x ∈ t, chartSource x)` for any finite family of chart sources —
plain `Finset` induction; each member is a full chart source (A4c at `W := U`), and each
MV intersection is an open subset of ONE chart (A4c again). -/
theorem pdWindowP2_finset_chartSources {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) M]
    (zM : SingularChain (TopCat.of M) (0 + 1 + 0 + 1))
    (hzM : chainBoundary (TopCat.of M) (0 + 1 + 0) zM = 0)
    (hcyc : zM ∈ cycles (TopCat.of M) (0 + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (0 + 2) (Homology.mk (TopCat.of M) (0 + 2) ⟨zM, hcyc⟩)
      = (manifoldLocalIso x).symm 1)
    [DecidableEq M] (t : Finset M) :
    ∀ hop : IsOpen (⋃ x ∈ t, (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) x).source
      : Set ↑(TopCat.of M)),
    pdWindowP2 zM hzM
      (⋃ x ∈ t, (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) x).source) hop := by
  induction t using Finset.induction_on with
  | empty =>
    intro hop
    exact pdWindowP2_congr zM hzM
      (show (∅ : Set ↑(TopCat.of M)) = _ by simp) isOpen_empty hop (pdWindowP2_empty zM hzM)
  | insert x t hx ih =>
    intro hop
    set c := chartAt (EuclideanSpace ℝ (Fin (0 + 2))) x with hcdef
    have hopx : IsOpen (c.source : Set ↑(TopCat.of M)) := c.open_source
    have hopS : IsOpen (⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) y).source
        : Set ↑(TopCat.of M)) :=
      isOpen_biUnion (fun y _ => (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) y).open_source)
    have hPx : pdWindowP2 zM hzM (c.source : Set ↑(TopCat.of M)) hopx :=
      pdWindowP2_of_chartOpen c.open_source c.open_target c.toHomeomorphSourceTarget
        zM hzM hcyc hloc hopx (le_refl _)
    have hPS : pdWindowP2 zM hzM
        (⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) y).source
          : Set ↑(TopCat.of M)) hopS := ih hopS
    have hPI : pdWindowP2 zM hzM
        ((c.source : Set ↑(TopCat.of M))
          ∩ ⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) y).source)
        (hopx.inter hopS) :=
      pdWindowP2_of_chartOpen c.open_source c.open_target c.toHomeomorphSourceTarget
        zM hzM hcyc hloc (hopx.inter hopS) Set.inter_subset_left
    exact pdWindowP2_congr zM hzM
      (Finset.set_biUnion_insert x t
        (fun y => (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) y).source)).symm
      (hopx.union hopS) hop
      (pdWindowP2_union_charted zM hzM hopx hopS hPx hPS hPI)

open SKEFTHawking.SingularChartBridge in
/-- **`P₂(univ)` — the full Layer-A/Layer-B conclusion**: on a CLOSED (compact, charted)
surface, the induction predicate holds on the whole space. -/
theorem pdWindowP2_univ {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) M]
    (zM : SingularChain (TopCat.of M) (0 + 1 + 0 + 1))
    (hzM : chainBoundary (TopCat.of M) (0 + 1 + 0) zM = 0)
    (hcyc : zM ∈ cycles (TopCat.of M) (0 + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (0 + 2) (Homology.mk (TopCat.of M) (0 + 2) ⟨zM, hcyc⟩)
      = (manifoldLocalIso x).symm 1)
    (hop : IsOpen (Set.univ : Set ↑(TopCat.of M))) :
    pdWindowP2 zM hzM Set.univ hop := by
  classical
  haveI : CompactSpace ↑(TopCat.of M) := inferInstanceAs (CompactSpace M)
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover (isCompact_univ (X := ↑(TopCat.of M)))
    (fun x : M => ((chartAt (EuclideanSpace ℝ (Fin (0 + 2))) x).source : Set ↑(TopCat.of M)))
    (fun x => (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) x).open_source)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x⟩)
  have huniv : (⋃ x ∈ t, ((chartAt (EuclideanSpace ℝ (Fin (0 + 2))) x).source
      : Set ↑(TopCat.of M))) = Set.univ :=
    Set.Subset.antisymm (Set.subset_univ _) ht
  have hopt : IsOpen (⋃ x ∈ t, ((chartAt (EuclideanSpace ℝ (Fin (0 + 2))) x).source
      : Set ↑(TopCat.of M))) :=
    isOpen_biUnion (fun y _ => (chartAt (EuclideanSpace ℝ (Fin (0 + 2))) y).open_source)
  exact pdWindowP2_congr zM hzM huniv hopt hop
    (pdWindowP2_finset_chartSources zM hzM hcyc hloc t hopt)

end SKEFTHawking.SingularPDWindow2
