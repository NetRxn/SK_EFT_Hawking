import Mathlib
import SKEFTHawking.SingularRelativeCohomologyMVConnecting
import SKEFTHawking.SingularCSCMayerVietoris
import SKEFTHawking.SingularCSCMayerVietorisMiddle
import SKEFTHawking.SingularCompactlySupportedTop
import SKEFTHawking.SingularRelativeMVNaturality

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
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyRestrict
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularRelativeMV
  SKEFTHawking.SingularDualityAdjoint SKEFTHawking.SingularRelativeUC

namespace SKEFTHawking.SingularCSCMayerVietorisConnecting

variable {M : TopCat} [T2Space ↑M]

/-- The `U∩V`-compact `LU ⊓ LV` carrying the connecting map's target stage. -/
def infCompact (U V : Set ↑M) (LU : CompactsIn U) (LV : CompactsIn V) : CompactsIn (U ∩ V) :=
  ⟨LU.1 ⊓ LV.1, by
    rw [TopologicalSpace.Compacts.coe_inf]; exact Set.inter_subset_inter LU.2 LV.2⟩

theorem infCompact_coe (U V : Set ↑M) (LU : CompactsIn U) (LV : CompactsIn V) :
    (↑(infCompact U V LU LV).1 : Set ↑M) = ↑LU.1 ∩ ↑LV.1 :=
  TopologicalSpace.Compacts.coe_inf _ _

/-- **The split-explicit raw leg** `rawLeg LU LV J hJ : Hᵏ(M | LU∪LV) → Hᵏ⁺¹_c(U∩V)`: the per-`(LU,LV)`
relative MV connecting map at the split subspaces `(↑LU)ᶜ`, `(↑LV)ᶜ`, landing at the `U∩V`-compact stage
`J` (with `(↑LU)ᶜ∪(↑LV)ᶜ = (↑J)ᶜ`; in use `J = LU⊓LV`). The target stage `J` is an **explicit argument**
(not `infCompact U V LU LV`) so that `Module.DirectLimit.of J` stays unreduced — keeping the
`Compacts.coe_inf` whnf out of `rawLeg`'s composition, which `infCompact`-baked-in would stall. Source
`Hᵏ(M, (↑LU)ᶜ ∩ (↑LV)ᶜ) = Hᵏ(M | LU∪LV)`. -/
noncomputable def rawLeg (U V : Set ↑M) (N : ℕ) (LU : CompactsIn U) (LV : CompactsIn V)
    (J : CompactsIn (U ∩ V))
    (hJ : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑J.1 : Set ↑M)ᶜ) :
    RelativeCohomology ((↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ) (N + 1)
      →ₗ[ZMod 2] CompactlySupportedCohomologyOpen (U ∩ V) (N + 2) :=
  (Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∩ V)) (cohomGW (U ∩ V) (N + 2))
        (cohomFW (U ∩ V) (N + 2)) J).comp
    ((relCohomSetCongr hJ (N + 2)).toLinearMap.comp
      (relCohomMvConnecting ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
        LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl N))

/-- **Computation rule for `rawLeg`** on `y` — the nested application (bypasses the `∘ₗ`/`∘ₛₗ`
`comp_apply` matcher friction; `J` explicit keeps `of J` unreduced, no `infCompact` whnf). -/
theorem rawLeg_apply (U V : Set ↑M) (N : ℕ) (LU : CompactsIn U) (LV : CompactsIn V)
    (J : CompactsIn (U ∩ V))
    (hJ : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑J.1 : Set ↑M)ᶜ)
    (y : RelativeCohomology ((↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ) (N + 1)) :
    rawLeg U V N LU LV J hJ y
      = Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∩ V)) (cohomGW (U ∩ V) (N + 2))
          (cohomFW (U ∩ V) (N + 2)) J
          (relCohomSetCongr hJ (N + 2)
            (relCohomMvConnecting ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
              LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl N y)) :=
  rfl

omit [T2Space ↑M] in
/-- **`relCohomSetCongr` absorbs into the source of `relCohomRestrict`** (the dual order to
`relCohomRestrict_relCohomSetCongr`): renaming the restriction target `S = S'` is restricting along the
transported inclusion. (`subst` the set equality.) -/
theorem relCohomSetCongr_relCohomRestrict {S S' T : Set ↑M} (hSS' : S = S') (h : S ⊆ T) (n : ℕ)
    (x : RelativeCohomology T n) :
    relCohomSetCongr hSS' n (relCohomRestrict h n x) = relCohomRestrict (hSS' ▸ h) n x := by
  subst hSS'; rfl

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
  (rawLeg U V N (legSplitU U V hU hV K) (legSplitV U V hU hV K)
      (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
      (by rw [infCompact_coe, Set.compl_inter])).comp
    (relCohomSetCongr (show ((↑K.1 : Set ↑M)ᶜ)
          = (↑(legSplitU U V hU hV K).1 : Set ↑M)ᶜ ∩ (↑(legSplitV U V hU hV K).1 : Set ↑M)ᶜ from by
        rw [legSplit_cover, Set.compl_union]) (N + 1)).toLinearMap

/-! ## Cohomology MV connecting-map naturality (the `dualMap`-transfer of homology naturality)

The leg compatibility of `δ_csc` needs that the per-pair connecting map `relCohomMvConnecting` commutes
with shrinking the complement subspaces `A ⊇ A'`, `B ⊇ B'` (i.e. enlarging the compacts). This is the
`dualMap`-transfer (through the perfect Kronecker pairing) of the **homology** MV connecting naturality
`relMvDelta_naturality` — supplied here as the hypothesis `homNat` (discharged downstream by
`SingularRelativeMVNaturality.relMvDelta_naturality`). -/

omit [T2Space ↑M] in
/-- **Cohomology MV connecting naturality** (given the homology naturality `homNat`): for `A' ⊆ A`,
`B' ⊆ B`, the connecting map commutes with the restrictions `relCohomRestrict` on the `∩` (source) and `∪`
(target),
  `δ_{A',B'} ∘ restrict_∩ = restrict_∪ ∘ δ_{A,B}`.
The `dualMap`-transfer of `relMvDelta_naturality`: pair both sides against any `w` and use the connecting
adjunction `relKroneckerH_relCohomMvConnecting` + the restriction adjunction `relKroneckerH_relCohomRestrict'`. -/
theorem relCohomMvConnecting_naturality (A B A' B' : Set ↑M)
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B')
    (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (N : ℕ)
    (homNat : ∀ w : RelativeHomology (A' ∪ B') (N + 2),
      relIncl (Set.inter_subset_inter hAA' hBB') (N + 1) (relMvDelta A' B' hA' hB' (N + 1) w)
        = relMvDelta A B hA hB (N + 1) (relIncl (Set.union_subset_union hAA' hBB') (N + 2) w))
    (ω : RelativeCohomology (A ∩ B) (N + 1)) :
    relCohomMvConnecting A' B' hA' hB' N
        (relCohomRestrict (Set.inter_subset_inter hAA' hBB') (N + 1) ω)
      = relCohomRestrict (Set.union_subset_union hAA' hBB') (N + 2)
        (relCohomMvConnecting A B hA hB N ω) := by
  refine sub_eq_zero.mp (relCohomology_eq_zero_of_relKroneckerH (A' ∪ B') _ (fun w => ?_))
  rw [map_sub, LinearMap.sub_apply, relKroneckerH_relCohomMvConnecting,
    relKroneckerH_relCohomRestrict', relKroneckerH_relCohomRestrict',
    relKroneckerH_relCohomMvConnecting, homNat, sub_self]

omit [T2Space ↑M] in
/-- **Cohomology MV connecting naturality** (unconditional): `relCohomMvConnecting_naturality` with the
homology naturality hypothesis discharged by `SingularRelativeMVNaturality.relMvDelta_naturality`. -/
theorem relCohomMvConnecting_naturality' (A B A' B' : Set ↑M)
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B')
    (hAA' : A' ⊆ A) (hBB' : B' ⊆ B) (N : ℕ) (ω : RelativeCohomology (A ∩ B) (N + 1)) :
    relCohomMvConnecting A' B' hA' hB' N
        (relCohomRestrict (Set.inter_subset_inter hAA' hBB') (N + 1) ω)
      = relCohomRestrict (Set.union_subset_union hAA' hBB') (N + 2)
        (relCohomMvConnecting A B hA hB N ω) :=
  relCohomMvConnecting_naturality A B A' B' hA hB hA' hB' hAA' hBB' N
    (fun w => SingularRelativeMVNaturality.relMvDelta_naturality A B A' B' hA hB hA' hB' hAA' hBB' (N + 1) w)
    ω

/-! ## `rawLeg` compatibility under enlarging the split compacts -/

/-- **`rawLeg` enlargement compatibility**: for `(LU,LV) ≤ (LU',LV')` (`hAA':(↑LU')ᶜ⊆(↑LU)ᶜ` etc.) at
target stages `J ≤ J'`, the smaller-compact leg equals the larger-compact leg of the restricted class.
By the cohomology MV connecting naturality (`relCohomMvConnecting_naturality'`) then the colimit `of_f`. -/
theorem rawLeg_enlarge (U V : Set ↑M) (N : ℕ)
    (LU LU' : CompactsIn U) (LV LV' : CompactsIn V) (J J' : CompactsIn (U ∩ V))
    (hJ : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑J.1 : Set ↑M)ᶜ)
    (hJ' : ((↑LU'.1 : Set ↑M)ᶜ ∪ (↑LV'.1 : Set ↑M)ᶜ) = (↑J'.1 : Set ↑M)ᶜ)
    (hJJ' : J ≤ J') (hAA' : (↑LU'.1 : Set ↑M)ᶜ ⊆ (↑LU.1 : Set ↑M)ᶜ)
    (hBB' : (↑LV'.1 : Set ↑M)ᶜ ⊆ (↑LV.1 : Set ↑M)ᶜ)
    (x : RelativeCohomology ((↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ) (N + 1)) :
    rawLeg U V N LU LV J hJ x
      = rawLeg U V N LU' LV' J' hJ' (relCohomRestrict (Set.inter_subset_inter hAA' hBB') (N + 1) x) := by
  rw [rawLeg_apply, rawLeg_apply,
    relCohomMvConnecting_naturality' ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ) ((↑LU'.1 : Set ↑M)ᶜ)
      ((↑LV'.1 : Set ↑M)ᶜ) LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl
      LU'.1.isCompact'.isClosed.isOpen_compl LV'.1.isCompact'.isClosed.isOpen_compl hAA' hBB' N x]
  set z := relCohomMvConnecting ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
    LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl N x with hz
  have heq : relCohomSetCongr hJ' (N + 2) (relCohomRestrict (Set.union_subset_union hAA' hBB') (N + 2) z)
      = cohomFW (U ∩ V) (N + 2) J J' hJJ' (relCohomSetCongr hJ (N + 2) z) := by
    rw [cohomFW, SingularCohomologyColimit.cohomF, relCohomSetCongr_relCohomRestrict]
    exact (SingularCSCMayerVietorisMiddle.relCohomRestrict_relCohomSetCongr hJ _ (N + 2) z).symm
  rw [heq]
  exact (Module.DirectLimit.of_f).symm

/-! ## The colimit assembly `δ_csc := DirectLimit.lift (legδ)` -/

/-- **`legδ` as a `rawLeg` at any enlarged split** `(LU,LV) ≥ (legSplitU K, legSplitV K)`: transport
`g` along the chosen-split complement-congruence, then restrict to the enlarged complements, then
apply the `(LU,LV)`-`rawLeg`. The bridge for `legδ_compat` — two different `K`-splits share a common
enlargement, so both per-`K` legs collapse to the same `(LU,LV)`-`rawLeg` of a single class. Unfolds
`legδ` (`rfl`) then `rawLeg_enlarge`. -/
theorem legδ_eq_enlarge (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ)
    (K : CompactsIn (U ∪ V)) (LU : CompactsIn U) (LV : CompactsIn V)
    (hKULU : (legSplitU U V hU hV K).1 ≤ LU.1) (hKVLV : (legSplitV U V hU hV K).1 ≤ LV.1)
    (hLUKU : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑(legSplitU U V hU hV K).1)ᶜ)
    (hLVKV : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑(legSplitV U V hU hV K).1)ᶜ)
    (hJL : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑(infCompact U V LU LV).1 : Set ↑M)ᶜ)
    (hcongr : ((↑K.1 : Set ↑M)ᶜ)
        = (↑(legSplitU U V hU hV K).1 : Set ↑M)ᶜ ∩ (↑(legSplitV U V hU hV K).1 : Set ↑M)ᶜ)
    (g : cohomGW (U ∪ V) (N + 1) K) :
    legδ U V hU hV N K g
      = rawLeg U V N LU LV (infCompact U V LU LV) hJL
          (relCohomRestrict (Set.inter_subset_inter hLUKU hLVKV) (N + 1)
            (relCohomSetCongr hcongr (N + 1) g)) := by
  have hbase : legδ U V hU hV N K g
      = rawLeg U V N (legSplitU U V hU hV K) (legSplitV U V hU hV K)
          (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
          (by rw [infCompact_coe, Set.compl_inter])
          (relCohomSetCongr hcongr (N + 1) g) := rfl
  rw [hbase]
  exact rawLeg_enlarge U V N (legSplitU U V hU hV K) LU (legSplitV U V hU hV K) LV
    (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)) (infCompact U V LU LV)
    (by rw [infCompact_coe, Set.compl_inter]) hJL
    (Subtype.coe_le_coe.mp (inf_le_inf hKULU hKVLV)) hLUKU hLVKV
    (relCohomSetCongr hcongr (N + 1) g)

theorem legδ_compat (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ)
    (K K' : CompactsIn (U ∪ V)) (hKK' : K ≤ K') (g : cohomGW (U ∪ V) (N + 1) K) :
    legδ U V hU hV N K' (cohomFW (U ∪ V) (N + 1) K K' hKK' g) = legδ U V hU hV N K g := by
  set KU := legSplitU U V hU hV K with hKU
  set KV := legSplitV U V hU hV K with hKV
  set KU' := legSplitU U V hU hV K' with hKU'
  set KV' := legSplitV U V hU hV K' with hKV'
  set LU := CompactsIn.sup KU KU' with hLU
  set LV := CompactsIn.sup KV KV' with hLV
  have hcoeLU : (↑LU.1 : Set ↑M) = ↑KU.1 ∪ ↑KU'.1 := by
    rw [hLU, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]
  have hcoeLV : (↑LV.1 : Set ↑M) = ↑KV.1 ∪ ↑KV'.1 := by
    rw [hLV, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]
  have hLUKU : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑KU.1)ᶜ :=
    Set.compl_subset_compl.mpr (by rw [hcoeLU]; exact Set.subset_union_left)
  have hLVKV : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑KV.1)ᶜ :=
    Set.compl_subset_compl.mpr (by rw [hcoeLV]; exact Set.subset_union_left)
  have hLUKU' : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑KU'.1)ᶜ :=
    Set.compl_subset_compl.mpr (by rw [hcoeLU]; exact Set.subset_union_right)
  have hLVKV' : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑KV'.1)ᶜ :=
    Set.compl_subset_compl.mpr (by rw [hcoeLV]; exact Set.subset_union_right)
  have hJL : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑(infCompact U V LU LV).1 : Set ↑M)ᶜ := by
    rw [infCompact_coe, Set.compl_inter]
  have hcongrK : ((↑K.1 : Set ↑M)ᶜ) = (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ := by
    rw [hKU, hKV, legSplit_cover, Set.compl_union]
  have hcongrK' : ((↑K'.1 : Set ↑M)ᶜ) = (↑KU'.1 : Set ↑M)ᶜ ∩ (↑KV'.1 : Set ↑M)ᶜ := by
    rw [hKU', hKV', legSplit_cover, Set.compl_union]
  rw [legδ_eq_enlarge U V hU hV N K' LU LV (le_sup_right) (le_sup_right) hLUKU' hLVKV' hJL hcongrK',
    legδ_eq_enlarge U V hU hV N K LU LV (le_sup_left) (le_sup_left) hLUKU hLVKV hJL hcongrK]
  congr 1
  have hKKc : (↑K'.1 : Set ↑M)ᶜ ⊆ (↑K.1 : Set ↑M)ᶜ :=
    Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hKK')
  have hLcollapse :
      relCohomSetCongr hcongrK' (N + 1) (cohomFW (U ∪ V) (N + 1) K K' hKK' g)
        = relCohomRestrict (hcongrK' ▸ hKKc) (N + 1) g := by
    rw [cohomFW, SingularCohomologyColimit.cohomF]
    exact relCohomSetCongr_relCohomRestrict hcongrK' hKKc (N + 1) g
  rw [SingularCSCMayerVietorisMiddle.relCohomRestrict_relCohomSetCongr hcongrK,
    hLcollapse, relCohomRestrict_trans]

/-- **The compactly-supported-cohomology MV connecting map** `δ_csc : Hᵏ_c(U∪V) → Hᵏ⁺¹_c(U∩V)`
(`k = N+1`): the `DirectLimit.lift` of the per-compact legs `legδ K` along the cocone compatibility
`legδ_compat`. The colimit assembly of the relative-cohomology MV connecting map. -/
noncomputable def cscMvConnecting (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ) :
    CompactlySupportedCohomologyOpen (U ∪ V) (N + 1) →ₗ[ZMod 2]
      CompactlySupportedCohomologyOpen (U ∩ V) (N + 2) :=
  Module.DirectLimit.lift (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
    (cohomFW (U ∪ V) (N + 1)) (legδ U V hU hV N)
    (fun K K' h x => legδ_compat U V hU hV N K K' h x)

@[simp] theorem cscMvConnecting_of (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ)
    (K : CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K) :
    cscMvConnecting U V hU hV N
        (Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) (N + 1))
          (cohomFW (U ∪ V) (N + 1)) K g)
      = legδ U V hU hV N K g :=
  Module.DirectLimit.lift_of _ _ g

end SKEFTHawking.SingularCSCMayerVietorisConnecting
