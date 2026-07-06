/-
# Phase 5q.H (E1 CSC-PD tower) — the integral compactly-supported cohomology MV connecting map

Integral (`ZMod 2 → ℤ`) mirror of `SingularCSCMayerVietorisConnecting`. The connecting map
  `δ_csc : Hᵏ_c(U∪V;ℤ) → Hᵏ⁺¹_c(U∩V;ℤ)`,
the colimit (over compacts `K ⊆ U∪V`) of the per-`K` relative-cohomology MV connecting map
`relCohomMvConnectingInt` at the split subspaces `(↑LU)ᶜ`, `(↑LV)ᶜ`.

For compacts `LU ⊆ U`, `LV ⊆ V`, the subspaces `A := (↑LU)ᶜ`, `B := (↑LV)ᶜ` satisfy `A∩B = (↑(LU∪LV))ᶜ`
and `A∪B = (↑(LU⊓LV))ᶜ`, so `relCohomMvConnectingInt A B : Hᵏ(M|LU∪LV) → Hᵏ⁺¹(M|LU⊓LV)` is the connecting
map from the `(LU∪LV)`-stage of `Hᵏ_c(U∪V)` to the `(LU⊓LV)`-stage of `Hᵏ⁺¹_c(U∩V)`. The leg
compatibility of `δ_csc` uses the **torsion-safe** connecting naturality `relCohomMvConnecting_naturalityInt`
(proven concretely from `δ = dualExcision⁻¹ ∘ midCohom`, NOT the field-only perfect Kronecker pairing).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomologyMVConnectingInt
import SKEFTHawking.SingularCSCMayerVietorisMiddleInt

open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeCohomologyRestrictInt
open SKEFTHawking.SingularRelativeCohomologyMVConnectingInt
open SKEFTHawking.SingularCohomologyColimitInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCSCMayerVietorisMiddleInt

namespace SKEFTHawking.SingularCSCMayerVietorisConnectingInt

variable {M : TopCat} [T2Space ↑M]

/-- The `U∩V`-compact `LU ⊓ LV` carrying the connecting map's target stage. -/
def infCompactInt (U V : Set ↑M) (LU : CompactsIn U) (LV : CompactsIn V) : CompactsIn (U ∩ V) :=
  ⟨LU.1 ⊓ LV.1, by
    rw [TopologicalSpace.Compacts.coe_inf]; exact Set.inter_subset_inter LU.2 LV.2⟩

theorem infCompactInt_coe (U V : Set ↑M) (LU : CompactsIn U) (LV : CompactsIn V) :
    (↑(infCompactInt U V LU LV).1 : Set ↑M) = ↑LU.1 ∩ ↑LV.1 :=
  TopologicalSpace.Compacts.coe_inf _ _

omit [T2Space ↑M] in
/-- **`relCohomSetCongrInt` absorbs into the source of `relCohomRestrictInt`** (dual order to
`relCohomRestrict_relCohomSetCongrInt`). -/
theorem relCohomSetCongr_relCohomRestrictInt {S S' T : Set ↑M} (hSS' : S = S') (h : S ⊆ T) (n : ℕ)
    (x : RelativeCohomologyInt T n) :
    relCohomSetCongrInt hSS' n (relCohomRestrictInt h n x) = relCohomRestrictInt (hSS' ▸ h) n x := by
  subst hSS'; rfl

/-- **The split-explicit raw leg** `rawLegInt LU LV J hJ : Hᵏ(M | LU∪LV;ℤ) → Hᵏ⁺¹_c(U∩V;ℤ)`. -/
noncomputable def rawLegInt (U V : Set ↑M) (N : ℕ) (LU : CompactsIn U) (LV : CompactsIn V)
    (J : CompactsIn (U ∩ V))
    (hJ : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑J.1 : Set ↑M)ᶜ) :
    RelativeCohomologyInt ((↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ) (N + 1)
      →ₗ[ℤ] CompactlySupportedCohomologyOpenInt (U ∩ V) (N + 2) :=
  (Module.DirectLimit.of ℤ (CompactsIn (U ∩ V)) (cohomGWInt (U ∩ V) (N + 2))
        (cohomFWInt (U ∩ V) (N + 2)) J).comp
    ((relCohomSetCongrInt hJ (N + 2)).toLinearMap.comp
      (relCohomMvConnectingInt ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
        LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl N))

theorem rawLegInt_apply (U V : Set ↑M) (N : ℕ) (LU : CompactsIn U) (LV : CompactsIn V)
    (J : CompactsIn (U ∩ V))
    (hJ : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑J.1 : Set ↑M)ᶜ)
    (y : RelativeCohomologyInt ((↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ) (N + 1)) :
    rawLegInt U V N LU LV J hJ y
      = Module.DirectLimit.of ℤ (CompactsIn (U ∩ V)) (cohomGWInt (U ∩ V) (N + 2))
          (cohomFWInt (U ∩ V) (N + 2)) J
          (relCohomSetCongrInt hJ (N + 2)
            (relCohomMvConnectingInt ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
              LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl N y)) :=
  rfl

/-! ## The per-compact leg (binary split of `K ⊆ U∪V` across the cover) -/

noncomputable def legSplitUInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (K : CompactsIn (U ∪ V)) :
    CompactsIn U :=
  (compactsIn_binary_cover hU hV K).choose

noncomputable def legSplitVInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (K : CompactsIn (U ∪ V)) :
    CompactsIn V :=
  (compactsIn_binary_cover hU hV K).choose_spec.choose

theorem legSplit_coverInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (K : CompactsIn (U ∪ V)) :
    (↑K.1 : Set ↑M) = ↑(legSplitUInt U V hU hV K).1 ∪ ↑(legSplitVInt U V hU hV K).1 :=
  (compactsIn_binary_cover hU hV K).choose_spec.choose_spec

/-- **The per-compact connecting leg** `legδInt K : Hᵏ(M | K;ℤ) → Hᵏ⁺¹_c(U∩V;ℤ)` (`k = N+1`). -/
noncomputable def legδInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ)
    (K : CompactsIn (U ∪ V)) :
    cohomGWInt (U ∪ V) (N + 1) K →ₗ[ℤ] CompactlySupportedCohomologyOpenInt (U ∩ V) (N + 2) :=
  (rawLegInt U V N (legSplitUInt U V hU hV K) (legSplitVInt U V hU hV K)
      (infCompactInt U V (legSplitUInt U V hU hV K) (legSplitVInt U V hU hV K))
      (by rw [infCompactInt_coe, Set.compl_inter])).comp
    (relCohomSetCongrInt (show ((↑K.1 : Set ↑M)ᶜ)
          = (↑(legSplitUInt U V hU hV K).1 : Set ↑M)ᶜ ∩ (↑(legSplitVInt U V hU hV K).1 : Set ↑M)ᶜ from by
        rw [legSplit_coverInt, Set.compl_union]) (N + 1)).toLinearMap

/-! ## `rawLegInt` compatibility under enlarging the split compacts -/

/-- **`rawLegInt` enlargement compatibility** via the torsion-safe connecting naturality
`relCohomMvConnecting_naturalityInt` then the colimit `of_f`. -/
theorem rawLegInt_enlarge (U V : Set ↑M) (N : ℕ)
    (LU LU' : CompactsIn U) (LV LV' : CompactsIn V) (J J' : CompactsIn (U ∩ V))
    (hJ : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑J.1 : Set ↑M)ᶜ)
    (hJ' : ((↑LU'.1 : Set ↑M)ᶜ ∪ (↑LV'.1 : Set ↑M)ᶜ) = (↑J'.1 : Set ↑M)ᶜ)
    (hJJ' : J ≤ J') (hAA' : (↑LU'.1 : Set ↑M)ᶜ ⊆ (↑LU.1 : Set ↑M)ᶜ)
    (hBB' : (↑LV'.1 : Set ↑M)ᶜ ⊆ (↑LV.1 : Set ↑M)ᶜ)
    (x : RelativeCohomologyInt ((↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ) (N + 1)) :
    rawLegInt U V N LU LV J hJ x
      = rawLegInt U V N LU' LV' J' hJ' (relCohomRestrictInt (Set.inter_subset_inter hAA' hBB') (N + 1) x) := by
  rw [rawLegInt_apply, rawLegInt_apply,
    relCohomMvConnecting_naturalityInt ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ) ((↑LU'.1 : Set ↑M)ᶜ)
      ((↑LV'.1 : Set ↑M)ᶜ) LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl
      LU'.1.isCompact'.isClosed.isOpen_compl LV'.1.isCompact'.isClosed.isOpen_compl hAA' hBB' N x]
  set z := relCohomMvConnectingInt ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ)
    LU.1.isCompact'.isClosed.isOpen_compl LV.1.isCompact'.isClosed.isOpen_compl N x with hz
  have heq : relCohomSetCongrInt hJ' (N + 2) (relCohomRestrictInt (Set.union_subset_union hAA' hBB') (N + 2) z)
      = cohomFWInt (U ∩ V) (N + 2) J J' hJJ' (relCohomSetCongrInt hJ (N + 2) z) := by
    rw [cohomFWInt, cohomFInt, relCohomSetCongr_relCohomRestrictInt]
    exact (relCohomRestrict_relCohomSetCongrInt hJ _ (N + 2) z).symm
  rw [heq]
  exact (Module.DirectLimit.of_f).symm

/-! ## The colimit assembly `δ_csc := DirectLimit.lift (legδInt)` -/

theorem legδInt_eq_enlarge (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ)
    (K : CompactsIn (U ∪ V)) (LU : CompactsIn U) (LV : CompactsIn V)
    (hKULU : (legSplitUInt U V hU hV K).1 ≤ LU.1) (hKVLV : (legSplitVInt U V hU hV K).1 ≤ LV.1)
    (hLUKU : (↑LU.1 : Set ↑M)ᶜ ⊆ (↑(legSplitUInt U V hU hV K).1)ᶜ)
    (hLVKV : (↑LV.1 : Set ↑M)ᶜ ⊆ (↑(legSplitVInt U V hU hV K).1)ᶜ)
    (hJL : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑(infCompactInt U V LU LV).1 : Set ↑M)ᶜ)
    (hcongr : ((↑K.1 : Set ↑M)ᶜ)
        = (↑(legSplitUInt U V hU hV K).1 : Set ↑M)ᶜ ∩ (↑(legSplitVInt U V hU hV K).1 : Set ↑M)ᶜ)
    (g : cohomGWInt (U ∪ V) (N + 1) K) :
    legδInt U V hU hV N K g
      = rawLegInt U V N LU LV (infCompactInt U V LU LV) hJL
          (relCohomRestrictInt (Set.inter_subset_inter hLUKU hLVKV) (N + 1)
            (relCohomSetCongrInt hcongr (N + 1) g)) := by
  have hbase : legδInt U V hU hV N K g
      = rawLegInt U V N (legSplitUInt U V hU hV K) (legSplitVInt U V hU hV K)
          (infCompactInt U V (legSplitUInt U V hU hV K) (legSplitVInt U V hU hV K))
          (by rw [infCompactInt_coe, Set.compl_inter])
          (relCohomSetCongrInt hcongr (N + 1) g) := rfl
  rw [hbase]
  exact rawLegInt_enlarge U V N (legSplitUInt U V hU hV K) LU (legSplitVInt U V hU hV K) LV
    (infCompactInt U V (legSplitUInt U V hU hV K) (legSplitVInt U V hU hV K)) (infCompactInt U V LU LV)
    (by rw [infCompactInt_coe, Set.compl_inter]) hJL
    (Subtype.coe_le_coe.mp (inf_le_inf hKULU hKVLV)) hLUKU hLVKV
    (relCohomSetCongrInt hcongr (N + 1) g)

theorem legδInt_compat (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ)
    (K K' : CompactsIn (U ∪ V)) (hKK' : K ≤ K') (g : cohomGWInt (U ∪ V) (N + 1) K) :
    legδInt U V hU hV N K' (cohomFWInt (U ∪ V) (N + 1) K K' hKK' g) = legδInt U V hU hV N K g := by
  set KU := legSplitUInt U V hU hV K with hKU
  set KV := legSplitVInt U V hU hV K with hKV
  set KU' := legSplitUInt U V hU hV K' with hKU'
  set KV' := legSplitVInt U V hU hV K' with hKV'
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
  have hJL : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑(infCompactInt U V LU LV).1 : Set ↑M)ᶜ := by
    rw [infCompactInt_coe, Set.compl_inter]
  have hcongrK : ((↑K.1 : Set ↑M)ᶜ) = (↑KU.1 : Set ↑M)ᶜ ∩ (↑KV.1 : Set ↑M)ᶜ := by
    rw [hKU, hKV, legSplit_coverInt, Set.compl_union]
  have hcongrK' : ((↑K'.1 : Set ↑M)ᶜ) = (↑KU'.1 : Set ↑M)ᶜ ∩ (↑KV'.1 : Set ↑M)ᶜ := by
    rw [hKU', hKV', legSplit_coverInt, Set.compl_union]
  rw [legδInt_eq_enlarge U V hU hV N K' LU LV (le_sup_right) (le_sup_right) hLUKU' hLVKV' hJL hcongrK',
    legδInt_eq_enlarge U V hU hV N K LU LV (le_sup_left) (le_sup_left) hLUKU hLVKV hJL hcongrK]
  congr 1
  have hKKc : (↑K'.1 : Set ↑M)ᶜ ⊆ (↑K.1 : Set ↑M)ᶜ :=
    Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hKK')
  have hLcollapse :
      relCohomSetCongrInt hcongrK' (N + 1) (cohomFWInt (U ∪ V) (N + 1) K K' hKK' g)
        = relCohomRestrictInt (hcongrK' ▸ hKKc) (N + 1) g := by
    rw [cohomFWInt, cohomFInt]
    exact relCohomSetCongr_relCohomRestrictInt hcongrK' hKKc (N + 1) g
  rw [relCohomRestrict_relCohomSetCongrInt hcongrK, hLcollapse, relCohomRestrictInt_trans]

/-- **The integral compactly-supported-cohomology MV connecting map** `δ_csc : Hᵏ_c(U∪V;ℤ) → Hᵏ⁺¹_c(U∩V;ℤ)`
(`k = N+1`): the `DirectLimit.lift` of the per-compact legs `legδInt K` along `legδInt_compat`. -/
noncomputable def cscMvConnectingInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ) :
    CompactlySupportedCohomologyOpenInt (U ∪ V) (N + 1) →ₗ[ℤ]
      CompactlySupportedCohomologyOpenInt (U ∩ V) (N + 2) :=
  Module.DirectLimit.lift ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
    (cohomFWInt (U ∪ V) (N + 1)) (legδInt U V hU hV N)
    (fun K K' h x => legδInt_compat U V hU hV N K K' h x)

@[simp] theorem cscMvConnectingInt_of (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (N : ℕ)
    (K : CompactsIn (U ∪ V)) (g : cohomGWInt (U ∪ V) (N + 1) K) :
    cscMvConnectingInt U V hU hV N
        (Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) (N + 1))
          (cohomFWInt (U ∪ V) (N + 1)) K g)
      = legδInt U V hU hV N K g :=
  Module.DirectLimit.lift_of _ _ g

end SKEFTHawking.SingularCSCMayerVietorisConnectingInt
