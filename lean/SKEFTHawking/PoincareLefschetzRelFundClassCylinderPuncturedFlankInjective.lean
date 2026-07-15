/-
# Phase 5q.H (W-A arm 4) — the `puncU` flank INJECTS into the punctured-product target

Route-B δ-closer. The flank count (`…PuncturedFlankCount`) established
`dim H_{m'+3}(M×I,{x}ᶜ) ≤ dim H_{m'+2}(M) + dim range δ`; this module PROVES the flank inclusion
`ι_U : H_{m'+3}(M×I, puncU) → H_{m'+3}(M×I, puncU ∪ puncV)` is **injective**, so a class supported on
the `puncU` flank (like the prism class, whose endpoint slices land in `puncU`) survives into the
target `T = H_{m'+3}(M×I, {x}ᶜ)`. The two inputs:

* **the overlap TOP vanishes** `H_{m'+3}(M×I, (M∖σ)×(I∖t)) = 0` (`overlapPair_top_eq_zero`), from its
  OWN pair-LES: `H_{m'+2}(sub overlap) = 0` (interval split + open-base top vanishing
  `…OpenTopVanish.openManifold_top_homology_eq_zero`) squeezes `δ = 0`, and `H_{m'+3}(M×I) = 0`
  (interval collapse + `homology_vanish_above`) squeezes `j_* = 0`, so the pair is `0`;
* **the `puncV` flank TOP vanishes** `H_{m'+3}(M×I, (M∖σ)×I) = 0` (`…PuncturedTopVanish`).

The relative-MV middle exactness (`relMv_exact_middle'`: `ker(relMvHomSum) = im(relMvHomDiag)`), with
`relMvHomDiag`'s source `H_{m'+3}(M×I, overlap) = 0`, gives `relMvHomSum` INJECTIVE; and
`relMvHomSum (α, 0) = ι_U(α)` (coprod), so `ι_U` is injective.

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the overlap top vanishing** `overlapPair_top_eq_zero`: `H_{m'+3}(M×I, (M∖σ)×(I∖t)) = 0`.
* **§2 — the flank injectivity** `relMvHomSum_top_injective` (`relMvHomSum` injective at `m'+3`) and
  `puncU_flank_injective` (`ι_U = relIncl (puncU ⊆ puncU∪puncV)` injective).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedOverlap
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedTopVanish
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderOpenTopVanish
import SKEFTHawking.SingularFundamentalClass

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedOverlap
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderOpenTopVanish

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedFlankInjective

noncomputable section

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-! ## §1. The overlap TOP vanishing `H_{m'+3}(M×I, (M∖σ)×(I∖t)) = 0` -/

/-- **The overlap SUBSPACE top homology vanishes**: `H_{m'+2}(sub overlap) = 0`. The clopen interval
split (`overlapSubHomEquiv`) identifies it with `H_{m'+2}(M∖σ)²`, and the open base top vanishes
(`openManifold_top_homology_eq_zero`). -/
theorem overlapSub_top_eq_zero (x : ↑(cyl (TopCat.of M))) (ht0 : (0 : ℝ) < (x.2 : ℝ))
    (ht1 : (x.2 : ℝ) < 1)
    (w : Homology (sub (overlap x)) (m' + 2)) : w = 0 := by
  refine (overlapSubHomEquiv (N := TopCat.of M) x ht0 ht1 (m' + 1)).injective ?_
  rw [map_zero]
  refine Prod.ext ?_ ?_ <;>
    exact openManifold_top_homology_eq_zero (M := M) x.1 _

omit [PreconnectedSpace M] in
/-- **The cylinder above-dimension homology vanishes**: `H_{m'+3}(M×I) = 0`. Interval-factor collapse
`H_{m'+3}(M×I) ≅ H_{m'+3}(M)` (`prodContractibleHomologyEquiv`) and `homology_vanish_above`. -/
theorem cyl_homology_above_eq_zero (q : Homology (cyl (TopCat.of M)) (m' + 3)) : q = 0 := by
  refine (prodContractibleHomologyEquiv (TopCat.of M) (TopCat.of unitInterval) ⊥ iccContraction
    slice_iccContraction_zero slice_iccContraction_one (m' + 2)).injective ?_
  rw [map_zero]
  exact SKEFTHawking.SingularFundamentalClass.homology_vanish_above (m := m') (M := M)
    (m' + 3) (by omega) _

/-- **The overlap PAIR top vanishes**: `H_{m'+3}(M×I, (M∖σ)×(I∖t)) = 0`. Its own pair-LES
`H_{m'+3}(M×I) →[j_*] H_{m'+3}(M×I, overlap) →[δ] H_{m'+2}(sub overlap)`: `δ = 0` (target vanishes,
`overlapSub_top_eq_zero`) puts the pair in `im j_*`; `H_{m'+3}(M×I) = 0` (`cyl_homology_above_eq_zero`)
kills `im j_*`. So the overlap pair is `0`. -/
theorem overlapPair_top_eq_zero (x : ↑(cyl (TopCat.of M))) (ht0 : (0 : ℝ) < (x.2 : ℝ))
    (ht1 : (x.2 : ℝ) < 1)
    (p : RelativeHomology (overlap x) (m' + 3)) : p = 0 := by
  -- δ p = 0
  have hdelta : connecting (X := cyl (TopCat.of M)) (overlap x) (m' + 2) p = 0 :=
    overlapSub_top_eq_zero x ht0 ht1 _
  -- p ∈ ker δ = im j_*
  obtain ⟨q, hq⟩ :=
    (exact_homProj_connecting (X := cyl (TopCat.of M)) (overlap x) (m' + 2) p).mp hdelta
  rw [← hq, cyl_homology_above_eq_zero q, map_zero]

/-! ## §2. The `puncU` flank injectivity -/

/-- **`relMvHomSum` is injective at top degree**: `H_{m'+3}(M×I, puncU) ⊕ H_{m'+3}(M×I, puncV) →
H_{m'+3}(M×I, {x}ᶜ)`. MV middle exactness (`relMv_exact_middle'`) makes its kernel the image of
`relMvHomDiag`, whose source `H_{m'+3}(M×I, overlap) = 0` (`overlapPair_top_eq_zero`). -/
theorem relMvHomSum_top_injective (x : ↑(cyl (TopCat.of M))) (ht0 : (0 : ℝ) < (x.2 : ℝ))
    (ht1 : (x.2 : ℝ) < 1) :
    Function.Injective (relMvHomSum (puncU x) (puncV x) (m' + 3)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨w, hw⟩ := (relMv_exact_middle' (puncU x) (puncV x) (isOpen_puncU x) (isOpen_puncV x)
    (m' + 2) a).mp ha
  rw [← hw, overlapPair_top_eq_zero x ht0 ht1 w, map_zero]

/-- **The `puncU` flank inclusion is injective**: `ι_U = relIncl (puncU ⊆ puncU∪puncV) :
H_{m'+3}(M×I, puncU) → H_{m'+3}(M×I, {x}ᶜ)` is injective. A prism-type class supported on the `puncU`
flank survives into the punctured-product target — the detection's structural half. From
`relMvHomSum (α, 0) = ι_U(α)` (coprod) and `relMvHomSum` injectivity. -/
theorem puncU_flank_injective (x : ↑(cyl (TopCat.of M))) (ht0 : (0 : ℝ) < (x.2 : ℝ))
    (ht1 : (x.2 : ℝ) < 1) :
    Function.Injective
      (relIncl (Set.subset_union_left : puncU x ⊆ puncU x ∪ puncV x) (m' + 3)) := by
  intro a b hab
  have hsum : relMvHomSum (puncU x) (puncV x) (m' + 3) (a, 0)
      = relMvHomSum (puncU x) (puncV x) (m' + 3) (b, 0) := by
    show relIncl Set.subset_union_left (m' + 3) a + relIncl Set.subset_union_right (m' + 3) 0
      = relIncl Set.subset_union_left (m' + 3) b + relIncl Set.subset_union_right (m' + 3) 0
    rw [hab]
  have := relMvHomSum_top_injective x ht0 ht1 hsum
  exact (Prod.ext_iff.mp this).1

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedFlankInjective
