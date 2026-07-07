/-
# Phase 5q.H (E1 CSC-PD tower) — `openDuality(legδ)` single-stage collapse (integral)

Integral mirror of `SingularOpenDualityConnLegdeltaCollapse`. The **RHS single-stage collapse** of the
integral Poincaré-duality connecting square: `openDuality` applied to the cohomology-connecting leg
`legδInt K g` collapses (via the colimit computation rules) to a single per-compact duality leg
`legW J (…)`, where `J = infCompactInt (legSplitUInt K) (legSplitVInt K)` and the fed class is the
`relCohomMvConnectingInt`-image of `g`.

Mechanical — chains the three integral computation rules `legδInt_eq_enlarge` → `rawLegInt_apply` →
`openDuality_of`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityInt
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
open SKEFTHawking.SingularCSCMayerVietorisConnectingInt
open SKEFTHawking.SingularRelativeCohomologyMVConnectingInt (relCohomMvConnectingInt)
open SKEFTHawking.SingularRelativeCohomologyRestrictInt (relCohomRestrictInt)
open SKEFTHawking.SingularCSCMayerVietorisMiddleInt (relCohomSetCongrInt)

namespace SKEFTHawking.SingularOpenDualityConnLegdeltaCollapseInt

variable {X : TopCat} [T2Space ↑X]

/-- **The RHS single-stage collapse of the integral PD connecting square.** `openDuality (legδInt K g)`
collapses to the per-compact leg `legW J (relCohomMvConnectingInt-image of g)`, with `J = infCompactInt`.
Mirror of `SingularOpenDualityConnLegdeltaCollapse.openDuality_legδ_eq_legW`. -/
theorem openDuality_legδ_eq_legWInt {N p : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z'' : SingularChainInt X (N + 2 + p + 1)) (hz'' : chainBoundary X (N + 2 + p) z'' = 0)
    (K : CompactsIn (U ∪ V)) (g : cohomGWInt (U ∪ V) (N + 1) K) :
    openDuality (k := N + 2) (m := p) (hU.inter hV) z'' hz'' (legδInt U V hU hV N K g)
      = legW (k := N + 2) (m := p) (hU.inter hV) z'' hz''
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
      (le_refl _) (le_refl _) subset_rfl subset_rfl hJL hcongr, rawLegInt_apply, openDuality_of]

end SKEFTHawking.SingularOpenDualityConnLegdeltaCollapseInt
