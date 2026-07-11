/-
# Phase 5q.H (E1 CSC-PD tower) — `openDuality₀(legδ)` single-stage collapse (integral, bot conjunct)

Integral mirror of `SingularOpenDualityBotLegdeltaCollapse.openDuality₀_legδ_eq_legW₀` (and the bottom-degree
companion of `SingularOpenDualityConnLegdeltaCollapseInt.openDuality_legδ_eq_legWInt`). The RHS single-stage
collapse of the integral PD connecting square at homology degree `0`: `openDuality₀Int` applied to the
cohomology-connecting leg `legδInt K g` collapses to a single per-compact bottom leg `legW₀Int J (…)`, with
`J = infCompactInt (legSplitUInt K) (legSplitVInt K)` and the fed class the `relCohomMvConnectingInt`-image of
`g` (identical RHS chain to the upper collapse — same `N+2` cohomology class). Feeds the BOT conjunct of
`HcoreG` (`k=2+1, m=0`). Mechanical: `legδInt_eq_enlarge` → `rawLegInt_apply` → `openDuality₀Int_of`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityInt
import SKEFTHawking.SingularOpenDualityBotInt
import SKEFTHawking.SingularCSCMayerVietorisConnectingInt
import SKEFTHawking.SingularRelativeCohomologyMVConnectingInt
import SKEFTHawking.SingularRelativeCohomologyRestrictInt
import SKEFTHawking.SingularCSCMayerVietorisMiddleInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularOpenDualityBotInt (openDuality₀Int openDuality₀Int_of legW₀Int)
open SKEFTHawking.SingularCSCMayerVietorisConnectingInt
open SKEFTHawking.SingularRelativeCohomologyMVConnectingInt (relCohomMvConnectingInt)
open SKEFTHawking.SingularRelativeCohomologyRestrictInt (relCohomRestrictInt)
open SKEFTHawking.SingularCSCMayerVietorisMiddleInt (relCohomSetCongrInt)

namespace SKEFTHawking.SingularOpenDualityBotLegdeltaCollapseInt

variable {X : TopCat} [T2Space ↑X]

/-- **The RHS single-stage collapse of the integral PD connecting square at degree 0.** `openDuality₀Int
(legδInt K g)` collapses to the bottom per-compact leg `legW₀Int J (relCohomMvConnectingInt-image of g)`,
`J = infCompactInt`. Bottom-degree mirror of `openDuality_legδ_eq_legWInt`; feeds the `HcoreG` bot conjunct. -/
theorem openDuality₀_legδ_eq_legW₀Int {N : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z'' : SingularChainInt X (N + 1 + 0 + 1)) (hz'' : chainBoundary X (N + 1 + 0) z'' = 0)
    (K : CompactsIn (U ∪ V)) (g : cohomGWInt (U ∪ V) (N + 1) K) :
    openDuality₀Int (k := N + 1) (hU.inter hV) z'' hz'' (legδInt U V hU hV N K g)
      = legW₀Int (k := N + 1) (hU.inter hV) z'' hz''
          (infCompactInt U V (legSplitUInt U V hU hV K) (legSplitVInt U V hU hV K))
          (relCohomSetCongrInt
              (by rw [infCompactInt_coe, Set.compl_inter] :
                ((↑(legSplitUInt U V hU hV K).1 : Set ↑X)ᶜ ∪ (↑(legSplitVInt U V hU hV K).1 : Set ↑X)ᶜ)
                  = (↑(infCompactInt U V (legSplitUInt U V hU hV K) (legSplitVInt U V hU hV K)).1 :
                      Set ↑X)ᶜ)
              (N + 2)
            (relCohomMvConnectingInt ((↑(legSplitUInt U V hU hV K).1 : Set ↑X)ᶜ)
                ((↑(legSplitVInt U V hU hV K).1 : Set ↑X)ᶜ)
                (legSplitUInt U V hU hV K).1.isCompact'.isClosed.isOpen_compl
                (legSplitVInt U V hU hV K).1.isCompact'.isClosed.isOpen_compl N
              (relCohomRestrictInt (Set.inter_subset_inter subset_rfl subset_rfl) (N + 1)
                (relCohomSetCongrInt
                    (by rw [legSplit_coverInt U V hU hV K, Set.compl_union] :
                      ((↑K.1 : Set ↑X)ᶜ)
                        = (↑(legSplitUInt U V hU hV K).1 : Set ↑X)ᶜ
                          ∩ (↑(legSplitVInt U V hU hV K).1 : Set ↑X)ᶜ)
                    (N + 1) g)))) := by
  have hJL : ((↑(legSplitUInt U V hU hV K).1 : Set ↑X)ᶜ ∪ (↑(legSplitVInt U V hU hV K).1 : Set ↑X)ᶜ)
      = (↑(infCompactInt U V (legSplitUInt U V hU hV K) (legSplitVInt U V hU hV K)).1 : Set ↑X)ᶜ := by
    rw [infCompactInt_coe, Set.compl_inter]
  have hcongr : ((↑K.1 : Set ↑X)ᶜ)
      = (↑(legSplitUInt U V hU hV K).1 : Set ↑X)ᶜ ∩ (↑(legSplitVInt U V hU hV K).1 : Set ↑X)ᶜ := by
    rw [legSplit_coverInt U V hU hV K, Set.compl_union]
  rw [legδInt_eq_enlarge U V hU hV N K (legSplitUInt U V hU hV K) (legSplitVInt U V hU hV K)
      (le_refl _) (le_refl _) subset_rfl subset_rfl hJL hcongr, rawLegInt_apply, openDuality₀Int_of]

end SKEFTHawking.SingularOpenDualityBotLegdeltaCollapseInt
