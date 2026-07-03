import Mathlib
import SKEFTHawking.SingularPDWindow

/-!
# Phase 5q.G (G1 (1,2)-window extension, X3) — the FOUR-conjunct induction predicate `P₄(W)`
and its full Bott–Tu tower

`pdWindowP4 = pdWindowP ∧ Bij D@(1,2)` — the deg-4 window extended by the `(1,2)`-duality
`H¹_c → H₃` (the `PoincareDual4Lo` input). The fourth conjunct is spelled at the
`(N,p) = (0,1)` upper-engine presentation of the SAME master `zM` (the engine is applied
DIRECTLY at `zM` — never at a pre-cast copy, which would produce non-unifiable composite
`castChain`s). Its base case is X2 (`cscOpen_one_eq_zero_of_chartConvex`) + B5; its MV-step
consumes the `(2,1)`-conjunct cross-wise (the A1-free single-`castChain` junction). The whole
Layer-A/Layer-B tower is mirrored verbatim on the extended predicate.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularCompactlySupportedOpen
open SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularOpenDualityBot
open SKEFTHawking.SingularOpenDualityMVConnSquare SKEFTHawking.SingularBaseCaseUpper
open SKEFTHawking.SingularPDWindow

namespace SKEFTHawking.SingularPDWindow4

/-- **The four-conjunct deg-4 PD-induction predicate** `P₄(W) = P(W) ∧ Bij D@(1,2)` (the
`(0,1)`-upper-engine presentation of the master `zM`). -/
def pdWindowP4 {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    (W : Set ↑M) (hW : IsOpen W) : Prop :=
  pdWindowP zM hzM W hW
  ∧ Function.Bijective (openDuality (k := 0 + 1) (m := 1 + 1) hW
      (castChain (show (0 : ℕ) + 1 + 3 = 0 + 1 + (1 + 1) + 1 by omega) zM)
      (chainBoundary_castChain_eq_zero (by omega) (by omega) zM hzM))

/-- `P₄`-transport across a set identity. -/
theorem pdWindowP4_congr {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    {W W' : Set ↑M} (h : W = W') (hW : IsOpen W) (hW' : IsOpen W')
    (hP : pdWindowP4 zM hzM W hW) : pdWindowP4 zM hzM W' hW' := by
  subst h
  exact hP

/-- **`P₄(∅)`.** -/
theorem pdWindowP4_empty {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0) :
    pdWindowP4 zM hzM (∅ : Set ↑M) isOpen_empty :=
  ⟨pdWindowP_empty zM hzM,
    bijective_of_forall_eq_zero _
      (fun α => cscOpen_empty_eq_zero α) (fun b => homology_sub_empty_eq_zero _ b)⟩

open SKEFTHawking.SingularChartBridge in
/-- **The `P₄` base case** — chart-convex opens: the first three conjuncts are B6, the fourth is
X2 (`CSC¹ = 0`) against B5 (`H₃(sub W) = 0`), both sides trivial. -/
theorem pdWindowP4_of_chartConvex {M : Type} [TopologicalSpace M] [T2Space M]
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
    pdWindowP4 zM hzM W hWo := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  refine ⟨pdWindowP_of_chartConvex hU hV e hCconv hCopen hp₀ hCV hWo hWU hWe zM hzM hcyc hloc, ?_⟩
  exact bijective_of_forall_eq_zero _
    (fun α => SKEFTHawking.SingularCSCConvexChart.cscOpen_one_eq_zero_of_chartConvex
      hU hV e hCconv hCopen ⟨p₀, hp₀⟩ hCV hWU hWe α)
    (fun x => SKEFTHawking.SingularConvexSubAcyclic.homology_chartConvexSub_eq_zero
      e hCconv hp₀ hCV hWU hWe (1 + 1) x)

/-- **The `P₄` Mayer–Vietoris step** — the first three conjuncts by `pdWindowP_union`, the fourth
by the `(N,p) = (0,1)` upper engine (its `(2,1)`-inputs cross-consume conjunct 1). -/
theorem pdWindowP4_union {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    {U V : Set ↑M} (hU : IsOpen U) (hV : IsOpen V)
    (hvanI : ∀ α : CompactlySupportedCohomologyOpen (U ∩ V) (2 + 1 + 2), α = 0)
    (hvanU : ∀ α : CompactlySupportedCohomologyOpen U (2 + 1 + 2), α = 0)
    (hvanV : ∀ α : CompactlySupportedCohomologyOpen V (2 + 1 + 2), α = 0)
    (hP4U : pdWindowP4 zM hzM U hU) (hP4V : pdWindowP4 zM hzM V hV)
    (hP4I : pdWindowP4 zM hzM (U ∩ V) (hU.inter hV)) :
    pdWindowP4 zM hzM (U ∪ V) (hU.union hV) := by
  obtain ⟨hPU, hCU⟩ := hP4U
  obtain ⟨hPV, hCV4⟩ := hP4V
  obtain ⟨hPI, hCI⟩ := hP4I
  refine ⟨pdWindowP_union zM hzM hU hV hvanI hvanU hvanV hPU hPV hPI, ?_⟩
  exact SKEFTHawking.SingularConnSquareCloseNCBotApex.openDuality_union_bijective_upper
    (N := 0) (p := 1) hU hV zM hzM hCI.surjective hCU hCV4 hPI.1 hPU.1.injective hPV.1.injective

/-- **`P₄` monotone-union stability.** -/
theorem pdWindowP4_monotone_union {M : TopCat} [T2Space ↑M]
    (zM : SingularChain M (1 + 0 + 3))
    (hzM : chainBoundary M (1 + 0 + 2) zM = 0)
    {W : ℕ → Set ↑M} (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (hP : ∀ n, pdWindowP4 zM hzM (W n) (hopen n)) :
    pdWindowP4 zM hzM (⋃ n, W n) (isOpen_iUnion hopen) :=
  ⟨pdWindowP_monotone_union zM hzM hmono hopen (fun n => (hP n).1),
    SKEFTHawking.SingularOpenDualityMonotoneUnion.openDuality_monotone_union_bijective
      hmono hopen _ _ (fun n => (hP n).2)⟩

open SKEFTHawking.SingularChartBridge in
/-- **The charted-manifold `P₄` MV-step** (`csc⁵` auto-discharged). -/
theorem pdWindowP4_union_charted {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (zM : SingularChain (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    {U V : Set ↑(TopCat.of M)} (hU : IsOpen U) (hV : IsOpen V)
    (hPU : pdWindowP4 zM hzM U hU) (hPV : pdWindowP4 zM hzM V hV)
    (hPI : pdWindowP4 zM hzM (U ∩ V) (hU.inter hV)) :
    pdWindowP4 zM hzM (U ∪ V) (hU.union hV) := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  exact pdWindowP4_union zM hzM hU hV
    (fun α => SKEFTHawking.SingularCSCVanishAboveGeom.cscOpen_eq_zero_of_isOpen (m := 2)
      (hU.inter hV) (by omega) α)
    (fun α => SKEFTHawking.SingularCSCVanishAboveGeom.cscOpen_eq_zero_of_isOpen (m := 2)
      hU (by omega) α)
    (fun α => SKEFTHawking.SingularCSCVanishAboveGeom.cscOpen_eq_zero_of_isOpen (m := 2)
      hV (by omega) α)
    hPU hPV hPI


open SKEFTHawking.SingularChartBridge in
/-- **(A4b) Within-chart finite unions**: `P(⋃ i ∈ s, Wf i)` for a finite family of opens in a
COMMON chart, each carried to a convex (possibly empty) open image. Strong double induction:
`Finset.induction_on` with the family ∀-generalized — the MV intersection
`Wf j ∩ ⋃ᵢ Wf i = ⋃ᵢ (Wf j ∩ Wf i)` is again an `s`-indexed such family (convex ∩ convex);
empty images collapse to `P(∅)`, nonempty ones are B6. -/
theorem pdWindowP4_finset_biUnion {M : Type} [TopologicalSpace M] [T2Space M]
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
      pdWindowP4 zM hzM (⋃ i ∈ s, Wf i) hop := by
  induction s using Finset.induction_on with
  | empty =>
    intro Wf Cf _ _ _ _ _ _ hop
    exact pdWindowP4_congr zM hzM
      (show (∅ : Set ↑(TopCat.of M)) = ⋃ i ∈ (∅ : Finset ι), Wf i by simp)
      isOpen_empty hop (pdWindowP4_empty zM hzM)
  | insert j s hj ih =>
    intro Wf Cf hopen hconv hCopen hCV hWU hWe hop
    have hjmem : j ∈ insert j s := Finset.mem_insert_self j s
    have hmem : ∀ i ∈ s, i ∈ insert j s := fun i hi => Finset.mem_insert_of_mem hi
    have hopj : IsOpen (Wf j) := hopen j hjmem
    have hopS : IsOpen (⋃ i ∈ s, Wf i) :=
      isOpen_biUnion (fun i hi => hopen i (hmem i hi))
    have hPj : pdWindowP4 zM hzM (Wf j) hopj := by
      rcases (Cf j).eq_empty_or_nonempty with hCe | hCne
      · refine pdWindowP4_congr zM hzM ?_ isOpen_empty hopj (pdWindowP4_empty zM hzM)
        symm
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have h := (hWe j hjmem ⟨x, hWU j hjmem hx⟩).mp hx
        rw [hCe] at h
        exact h
      · obtain ⟨p₀, hp₀⟩ := hCne
        exact pdWindowP4_of_chartConvex hU hV e (hconv j hjmem) (hCopen j hjmem) hp₀
          (hCV j hjmem) hopj (hWU j hjmem) (hWe j hjmem) zM hzM hcyc hloc
    have hPS : pdWindowP4 zM hzM (⋃ i ∈ s, Wf i) hopS :=
      ih Wf Cf (fun i hi => hopen i (hmem i hi)) (fun i hi => hconv i (hmem i hi))
        (fun i hi => hCopen i (hmem i hi)) (fun i hi => hCV i (hmem i hi))
        (fun i hi => hWU i (hmem i hi)) (fun i hi => hWe i (hmem i hi)) hopS
    have hPI : pdWindowP4 zM hzM (Wf j ∩ ⋃ i ∈ s, Wf i) (hopj.inter hopS) := by
      have hidt : Wf j ∩ (⋃ i ∈ s, Wf i) = ⋃ i ∈ s, (Wf j ∩ Wf i) :=
        Set.inter_iUnion₂ _ _
      have hopI : IsOpen (⋃ i ∈ s, (Wf j ∩ Wf i)) :=
        isOpen_biUnion (fun i hi => hopj.inter (hopen i (hmem i hi)))
      refine pdWindowP4_congr zM hzM hidt.symm hopI (hopj.inter hopS) ?_
      exact ih (fun i => Wf j ∩ Wf i) (fun i => Cf j ∩ Cf i)
        (fun i hi => hopj.inter (hopen i (hmem i hi)))
        (fun i hi => (hconv j hjmem).inter (hconv i (hmem i hi)))
        (fun i hi => (hCopen j hjmem).inter (hCopen i (hmem i hi)))
        (fun i hi => Set.inter_subset_right.trans (hCV i (hmem i hi)))
        (fun i hi => Set.inter_subset_left.trans (hWU j hjmem))
        (fun i hi u => by
          simp only [Set.mem_inter_iff]
          exact and_congr (hWe j hjmem u) (hWe i (hmem i hi) u)) hopI
    exact pdWindowP4_congr zM hzM (Finset.set_biUnion_insert j s Wf).symm (hopj.union hopS) hop
      (pdWindowP4_union_charted zM hzM hopj hopS hPj hPS hPI)



open SKEFTHawking.SingularChartBridge in
/-- **(A4c) `P` holds on every chart-open**: an open `W ⊆ U` is the pullback of its (open)
Euclidean chart image, which a countable family of balls exhausts (second countability);
the ball-truncations are A4b families and the exhaustion is monotone. The full Layer-A
conclusion for a single chart. -/
theorem pdWindowP4_of_chartOpen {M : Type} [TopologicalSpace M] [T2Space M]
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
    pdWindowP4 zM hzM W hWo := by
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
    exact pdWindowP4_congr zM hzM hWempty.symm isOpen_empty hWo (pdWindowP4_empty zM hzM)
  · -- enumerate the countable subfamily
    obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    -- the monotone finite-truncation exhaustion, each an A4b family
    have hstage : ∀ n : ℕ, ∀ hop : IsOpen (⋃ k ∈ Finset.range (n + 1),
        chartPull e (Metric.ball ((f k : ↥O) : EuclideanSpace ℝ (Fin (2 + 2))) (ε (f k)))),
        pdWindowP4 zM hzM _ hop := by
      intro n hop
      exact pdWindowP4_finset_biUnion hU hV e zM hzM hcyc hloc (Finset.range (n + 1))
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
    have hPmono := pdWindowP4_monotone_union zM hzM hmono hopseq (fun n => hstage n (hopseq n))
    -- the union of the truncations is W
    refine pdWindowP4_congr zM hzM ?_ _ hWo hPmono
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



open SKEFTHawking.SingularChartBridge in
/-- **Layer-B core**: `P(⋃ x ∈ t, chartSource x)` for any finite family of chart sources —
plain `Finset` induction; each member is a full chart source (A4c at `W := U`), and each
MV intersection is an open subset of ONE chart (A4c again). -/
theorem pdWindowP4_finset_chartSources {M : Type} [TopologicalSpace M] [T2Space M]
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
    pdWindowP4 zM hzM
      (⋃ x ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x).source) hop := by
  induction t using Finset.induction_on with
  | empty =>
    intro hop
    exact pdWindowP4_congr zM hzM
      (show (∅ : Set ↑(TopCat.of M)) = _ by simp) isOpen_empty hop (pdWindowP4_empty zM hzM)
  | insert x t hx ih =>
    intro hop
    set c := chartAt (EuclideanSpace ℝ (Fin (2 + 2))) x with hcdef
    have hopx : IsOpen (c.source : Set ↑(TopCat.of M)) := c.open_source
    have hopS : IsOpen (⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source
        : Set ↑(TopCat.of M)) :=
      isOpen_biUnion (fun y _ => (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).open_source)
    have hPx : pdWindowP4 zM hzM (c.source : Set ↑(TopCat.of M)) hopx :=
      pdWindowP4_of_chartOpen c.open_source c.open_target c.toHomeomorphSourceTarget
        zM hzM hcyc hloc hopx (le_refl _)
    have hPS : pdWindowP4 zM hzM
        (⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source
          : Set ↑(TopCat.of M)) hopS := ih hopS
    have hPI : pdWindowP4 zM hzM
        ((c.source : Set ↑(TopCat.of M))
          ∩ ⋃ y ∈ t, (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source)
        (hopx.inter hopS) :=
      pdWindowP4_of_chartOpen c.open_source c.open_target c.toHomeomorphSourceTarget
        zM hzM hcyc hloc (hopx.inter hopS) Set.inter_subset_left
    exact pdWindowP4_congr zM hzM
      (Finset.set_biUnion_insert x t
        (fun y => (chartAt (EuclideanSpace ℝ (Fin (2 + 2))) y).source)).symm
      (hopx.union hopS) hop
      (pdWindowP4_union_charted zM hzM hopx hopS hPx hPS hPI)


open SKEFTHawking.SingularChartBridge in
/-- **`P(univ)` — the full Layer-A/Layer-B conclusion**: on a CLOSED (compact, charted)
4-manifold, the induction predicate holds on the whole space. -/
theorem pdWindowP4_univ {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
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
    pdWindowP4 zM hzM Set.univ hop := by
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
  exact pdWindowP4_congr zM hzM huniv hopt hop
    (pdWindowP4_finset_chartSources zM hzM hcyc hloc t hopt)


end SKEFTHawking.SingularPDWindow4
