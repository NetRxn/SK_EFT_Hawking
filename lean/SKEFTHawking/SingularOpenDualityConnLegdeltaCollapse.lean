import Mathlib
import SKEFTHawking.SingularOpenDualityMVConnSquare

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-c4-RHS) — `openDuality(legδ)` single-stage collapse

The **RHS single-stage collapse** of the Poincaré-duality connecting square: `openDuality`
applied to the cohomology-connecting leg `legδ K g` collapses (via the colimit computation
rules) to a single per-compact duality leg `legW J (…)`, where
`J = infCompact (legSplitU K) (legSplitV K)` and the fed class is the
`relCohomMvConnecting`-image of `g`.

Mechanical — chains the three existing computation rules
`legδ_eq_enlarge` → `rawLeg_apply` → `openDuality_of`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularCSCMayerVietorisConnecting
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularSubsetHomology SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.SingularOpenDualityConnLegdeltaCollapse

variable {X : TopCat} [T2Space ↑X]

theorem openDuality_legδ_eq_legW {N p : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z'' : SingularChain X (N + 2 + p + 1)) (hz'' : chainBoundary X (N + 2 + p) z'' = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K) :
    openDuality (k := N + 2) (m := p) (hU.inter hV) z'' hz''
        (SKEFTHawking.SingularCSCMayerVietorisConnecting.legδ U V hU hV N K g)
      = legW (k := N + 2) (m := p) (hU.inter hV) z'' hz''
          (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
          (SKEFTHawking.SingularCompactlySupportedTop.relCohomSetCongr
              (by rw [infCompact_coe, Set.compl_inter] :
                ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ ∪ (↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
                  = (↑(infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)).1 : Set ↑X)ᶜ)
              (N + 2)
            (SKEFTHawking.SingularRelativeCohomologyMVConnecting.relCohomMvConnecting
                ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ) ((↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
                (legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
                (legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl N
              (SKEFTHawking.SingularRelativeCohomologyRestrict.relCohomRestrict
                  (Set.inter_subset_inter subset_rfl subset_rfl) (N + 1)
                (SKEFTHawking.SingularCompactlySupportedTop.relCohomSetCongr
                    (by rw [legSplit_cover U V hU hV K, Set.compl_union] :
                      ((↑K.1 : Set ↑X)ᶜ)
                        = (↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ
                          ∩ (↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
                    (N + 1) g)))) := by
  have hJL : ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ ∪ (↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
      = (↑(infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)).1 : Set ↑X)ᶜ := by
    rw [infCompact_coe, Set.compl_inter]
  have hcongr : ((↑K.1 : Set ↑X)ᶜ)
      = (↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ ∩ (↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ := by
    rw [legSplit_cover U V hU hV K, Set.compl_union]
  rw [legδ_eq_enlarge U V hU hV N K (legSplitU U V hU hV K) (legSplitV U V hU hV K)
      (le_refl _) (le_refl _) subset_rfl subset_rfl hJL hcongr, rawLeg_apply, openDuality_of]

end SKEFTHawking.SingularOpenDualityConnLegdeltaCollapse
