import Mathlib
import SKEFTHawking.SingularOpenDualityBot

/-!
# Phase 5q.G (G1 PD-induction, brick B1a) — `openDuality₀(legδ)` single-stage collapse

The bottom (`H₀`-valued) mirror of `SingularOpenDualityConnLegdeltaCollapse.openDuality_legδ_eq_legW`:
`openDuality₀` applied to the cohomology-connecting leg `legδ K g` collapses (via the colimit
computation rules) to the single bottom per-compact duality leg `legW₀ J (…)`, with
`J = infCompact (legSplitU K) (legSplitV K)` and the fed class the `relCohomMvConnecting`-image
of `g`. The cohomology side (cochain degree `N+2`) is UNCHANGED from the main-family collapse —
only the duality-side maps are the ₀-family's (`k := N+1`, so `k+1 = N+2` cochains, `H₀` target).

Mechanical — the same three computation rules: `legδ_eq_enlarge` → `rawLeg_apply` →
`openDuality₀_of`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularCSCMayerVietorisConnecting
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularSubsetHomology SKEFTHawking.SingularHomologyMod2
  SKEFTHawking.SingularOpenDualityBot

namespace SKEFTHawking.SingularOpenDualityBotLegdeltaCollapse

variable {X : TopCat} [T2Space ↑X]

theorem openDuality₀_legδ_eq_legW₀ {N : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z'' : SingularChain X (N + 1 + 0 + 1)) (hz'' : chainBoundary X (N + 1 + 0) z'' = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K) :
    openDuality₀ (k := N + 1) (hU.inter hV) z'' hz''
        (SKEFTHawking.SingularCSCMayerVietorisConnecting.legδ U V hU hV N K g)
      = legW₀ (k := N + 1) (hU.inter hV) z'' hz''
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
      (le_refl _) (le_refl _) subset_rfl subset_rfl hJL hcongr, rawLeg_apply, openDuality₀_of]

end SKEFTHawking.SingularOpenDualityBotLegdeltaCollapse
