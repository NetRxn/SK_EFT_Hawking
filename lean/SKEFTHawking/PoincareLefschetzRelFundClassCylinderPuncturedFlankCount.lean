/-
# Phase 5q.H (W-A arm 4) — the assembled flank count of the punctured-product target (both flanks)

Route-B assembly. The relative-MV LES flank bound (`…PuncturedMVBookkeeping.puncMv_target_finrank_le`)
controls the punctured-product target `T = H_{m'+3}(M×I, {x}ᶜ)` by the two piece dimensions plus the
δ-image:

  `dim T ≤ dim H_{m'+3}(M×I, puncU) + dim H_{m'+3}(M×I, puncV) + dim range δ`.

With BOTH flank pieces now computed in the top target degree `m'+3`:

* **`puncU`** (`…PuncturedPieceU.cylinder_puncU_relHom_finrank`): `dim H_{m'+3}(M×I, M×(I∖t)) = dim H_{m'+2}(M)`,
* **`puncV`** (`…PuncturedTopVanish.finrank_puncV_localHom_above`): `dim H_{m'+3}(M×I, (M∖σ)×I) = 0`,

the flank contribution COLLAPSES to the base top Betti number, leaving

  `dim H_{m'+3}(M×I, {x}ᶜ) ≤ dim H_{m'+2}(M) + dim range δ`.

For `M` a closed connected `(m'+2)`-manifold (`dim H_{m'+2}(M) = 1`) this is `dim T ≤ 1 + dim range δ`;
since `T ≅ ℤ/2` is the interior top local homology, the δ-closer's SOLE remaining job is the prism-class
nonvanishing inside `range δ ⊆ H_{m'+2}(M×I, (M∖σ)×(I∖t))` (`…PuncturedOverlapPair`). This module is the
flank-count bookkeeping; the prism nonvanishing is the dedicated next block.

## What this banks (all kernel-pure, no `sorry`/axiom)

* **`crossTarget_finrank_flank_collapse`**: `dim H_{m'+3}(M×I, {x}ᶜ) ≤ dim H_{m'+2}(M) + dim range δ` —
  the two piece dimensions (`puncU` = base top Betti, `puncV` = 0) plugged into the MV flank bound.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPieceU
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedMVBookkeeping
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedTopVanish

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPieceU
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedMVBookkeeping
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedTopVanish

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedFlankCount

noncomputable section

/-- **The assembled flank count** `dim H_{m'+3}(M×I, {x}ᶜ) ≤ dim H_{m'+2}(M) + dim range δ`. Both MV
flank pieces of the top target degree are now known — `puncU` gives the base top Betti number
(`cylinder_puncU_relHom_finrank`), `puncV` VANISHES (`finrank_puncV_localHom_above`) — so the relative-MV
flank bound (`puncMv_target_finrank_le`) collapses to the base Betti number plus the δ-image. The δ-closer
is left only with the prism-class nonvanishing inside `range δ`. -/
theorem crossTarget_finrank_flank_collapse {m' : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]
    (x : ↑(cyl (TopCat.of M))) (ht0 : (0 : ℝ) < (x.2 : ℝ)) (ht1 : (x.2 : ℝ) < 1)
    [FiniteDimensional (ZMod 2) (Homology (TopCat.of M) (m' + 2))]
    [FiniteDimensional (ZMod 2)
      (RelativeHomology (X := cyl (TopCat.of M)) (puncU x ∪ puncV x) (m' + 3))]
    [FiniteDimensional (ZMod 2) (RelativeHomology (X := cyl (TopCat.of M)) (puncU x) (m' + 3))] :
    Module.finrank (ZMod 2)
        (RelativeHomology (X := cyl (TopCat.of M)) (puncU x ∪ puncV x) (m' + 3))
      ≤ Module.finrank (ZMod 2) (Homology (TopCat.of M) (m' + 2))
        + Module.finrank (ZMod 2) (LinearMap.range (puncMvDelta x (m' + 2))) := by
  haveI : T1Space ↑(TopCat.of M) := inferInstanceAs (T1Space M)
  haveI : Subsingleton (RelativeHomology (X := cyl (TopCat.of M)) (puncV x) (m' + 3)) :=
    ⟨fun a b => by rw [puncV_localHom_above_eq_zero x a, puncV_localHom_above_eq_zero x b]⟩
  have hpuncU : Module.finrank (ZMod 2)
      (RelativeHomology (X := cyl (TopCat.of M)) (puncU x) (m' + 3))
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) (m' + 2)) :=
    cylinder_puncU_relHom_finrank x ht0 ht1 (m' + 1)
  have hpuncV : Module.finrank (ZMod 2)
      (RelativeHomology (X := cyl (TopCat.of M)) (puncV x) (m' + 3)) = 0 :=
    finrank_puncV_localHom_above x
  have hle : Module.finrank (ZMod 2)
        (RelativeHomology (X := cyl (TopCat.of M)) (puncU x ∪ puncV x) (m' + 3))
      ≤ Module.finrank (ZMod 2) (RelativeHomology (X := cyl (TopCat.of M)) (puncU x) (m' + 3))
        + Module.finrank (ZMod 2) (RelativeHomology (X := cyl (TopCat.of M)) (puncV x) (m' + 3))
        + Module.finrank (ZMod 2) (LinearMap.range (puncMvDelta x (m' + 2))) :=
    puncMv_target_finrank_le x (m' + 2)
  omega

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedFlankCount
