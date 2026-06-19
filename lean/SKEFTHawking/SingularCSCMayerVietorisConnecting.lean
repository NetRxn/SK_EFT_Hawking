import Mathlib
import SKEFTHawking.SingularRelativeCohomologyMVConnecting
import SKEFTHawking.SingularCSCMayerVietoris
import SKEFTHawking.SingularCSCMayerVietorisMiddle
import SKEFTHawking.SingularCompactlySupportedTop

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-b3) — the compactly-supported cohomology MV connecting map

The connecting map of the compactly-supported-cohomology Mayer–Vietoris sequence for opens `U`, `V`,
  `δ_csc : Hᵏ_c(U∪V) → Hᵏ⁺¹_c(U∩V)`,
the colimit (over compacts `K ⊆ U∪V`) of the per-`K` relative cohomology MV connecting map
`SingularRelativeCohomologyMVConnecting.relCohomMvConnecting` at the split subspaces `(↑LU)ᶜ`, `(↑LV)ᶜ`.

Index correspondence (the same as the middle exactness `SingularCSCMayerVietorisMiddle`): for compacts
`LU ⊆ U`, `LV ⊆ V`, the subspaces `A := (↑LU)ᶜ`, `B := (↑LV)ᶜ` satisfy `A∩B = (↑(LU∪LV))ᶜ` and
`A∪B = (↑(LU⊓LV))ᶜ`, so `relCohomMvConnecting A B : Hᵏ(M|LU∪LV) → Hᵏ⁺¹(M|LU⊓LV)` is exactly the connecting
map from the `(LU∪LV)`-stage of `Hᵏ_c(U∪V)` to the `(LU⊓LV)`-stage of `Hᵏ⁺¹_c(U∩V)`.

This module builds the **split-explicit raw leg** `rawLeg LU LV` (no choice yet); the per-`K` leg (binary
split of `K` across the cover) and the colimit assembly `δ_csc := DirectLimit.lift` — whose leg
compatibility is the `dualMap`-transfer of the homology MV connecting naturality
(`SingularRelativeMVNaturality.relMvDelta_naturality`) — follow.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMVConnecting
  SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularCompactlySupportedTop SKEFTHawking.SingularCSCMayerVietoris

namespace SKEFTHawking.SingularCSCMayerVietorisConnecting

variable {M : TopCat} [T2Space ↑M]

/-- The `U∩V`-compact `LU ⊓ LV` carrying the connecting map's target stage. -/
def infCompact (U V : Set ↑M) (LU : CompactsIn U) (LV : CompactsIn V) : CompactsIn (U ∩ V) :=
  ⟨LU.1 ⊓ LV.1, by
    rw [TopologicalSpace.Compacts.coe_inf]; exact Set.inter_subset_inter LU.2 LV.2⟩

theorem infCompact_coe (U V : Set ↑M) (LU : CompactsIn U) (LV : CompactsIn V) :
    (↑(infCompact U V LU LV).1 : Set ↑M) = ↑LU.1 ∩ ↑LV.1 :=
  TopologicalSpace.Compacts.coe_inf _ _

/-- **The split-explicit raw leg** `rawLeg LU LV : Hᵏ(M | LU∪LV) → Hᵏ⁺¹_c(U∩V)`: the per-`(LU,LV)`
relative MV connecting map at the split subspaces `(↑LU)ᶜ`, `(↑LV)ᶜ`, landing in the `(LU⊓LV)`-stage of
`Hᵏ⁺¹_c(U∩V)`. Source `Hᵏ(M, (↑LU)ᶜ ∩ (↑LV)ᶜ) = Hᵏ(M | LU∪LV)`. -/
noncomputable def rawLeg (U V : Set ↑M) (N : ℕ) (LU : CompactsIn U) (LV : CompactsIn V) :
    RelativeCohomology ((↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ) (N + 1)
      →ₗ[ZMod 2] CompactlySupportedCohomologyOpen (U ∩ V) (N + 2) :=
  (Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∩ V)) (cohomGW (U ∩ V) (N + 2))
        (cohomFW (U ∩ V) (N + 2)) (infCompact U V LU LV)).comp
    ((relCohomSetCongr (show ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ)
            = (↑(infCompact U V LU LV).1 : Set ↑M)ᶜ from by
          rw [infCompact_coe, Set.compl_inter]) (N + 2)).toLinearMap.comp
      (relCohomMvConnecting ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
        LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl N))

/-! ## The per-compact leg (binary split of `K ⊆ U∪V` across the cover) -/

/-- The chosen `U`-part of the binary split of `K ⊆ U∪V` (`compactsIn_binary_cover`, `Classical.choose`). -/
noncomputable def legSplitU (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (K : CompactsIn (U ∪ V)) :
    CompactsIn U :=
  (compactsIn_binary_cover hU hV K).choose

/-- The chosen `V`-part of the binary split of `K ⊆ U∪V`. -/
noncomputable def legSplitV (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (K : CompactsIn (U ∪ V)) :
    CompactsIn V :=
  (compactsIn_binary_cover hU hV K).choose_spec.choose

theorem legSplit_cover (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (K : CompactsIn (U ∪ V)) :
    (↑K.1 : Set ↑M) = ↑(legSplitU U V hU hV K).1 ∪ ↑(legSplitV U V hU hV K).1 :=
  (compactsIn_binary_cover hU hV K).choose_spec.choose_spec

/-- **The per-compact connecting leg** `legδ K : Hᵏ(M | K) → Hᵏ⁺¹_c(U∩V)` (`k = N+1`): transport the
`K`-stage class along `(↑K)ᶜ = (↑LU)ᶜ ∩ (↑LV)ᶜ` (the chosen split) into the `rawLeg` source, then apply
`rawLeg LU LV`. The cocone of the colimit `δ_csc`. -/
noncomputable def legδ (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ)
    (K : CompactsIn (U ∪ V)) :
    cohomGW (U ∪ V) (N + 1) K →ₗ[ZMod 2] CompactlySupportedCohomologyOpen (U ∩ V) (N + 2) :=
  (rawLeg U V N (legSplitU U V hU hV K) (legSplitV U V hU hV K)).comp
    (relCohomSetCongr (show ((↑K.1 : Set ↑M)ᶜ)
          = (↑(legSplitU U V hU hV K).1 : Set ↑M)ᶜ ∩ (↑(legSplitV U V hU hV K).1 : Set ↑M)ᶜ from by
        rw [legSplit_cover, Set.compl_union]) (N + 1)).toLinearMap

end SKEFTHawking.SingularCSCMayerVietorisConnecting
