/-
# Phase 5q.H (W-A arm 4) — the LOCAL cross detection reduced to the ABSOLUTE `puncU` cross class

Route-B δ-closer assembly. The terminal detection needs `crossHloc([M]|σ) ≠ 0` in the punctured-product
local homology `T = H_{m'+3}(M×I, {x}ᶜ)`. Both `crossHloc` (the LOCAL prism, source `H(M, M∖σ)`) and the
GENERAL absolute cross `crossH` (source `H(M)`, for any subspace `S ⊇ M×∂I`-endpoints) are built from the
SAME prism chain `prismOp graphHom z`. So, taking `S = puncU x = M×(I∖t)` (which contains the endpoint
slices `M×{0,1}` since `0,1 ≠ t`), the prism class rel `puncU`

  `αU := crossH_puncU([M]) ∈ H_{m'+3}(M×I, puncU)`

satisfies, chain-for-chain, `crossHloc([M]|σ) = ι_U(αU)` where `ι_U = relIncl (puncU ⊆ {x}ᶜ)`. Since
`ι_U` is INJECTIVE (`…PuncturedFlankInjective.puncU_flank_injective`, transported across
`puncU ∪ puncV = {x}ᶜ`), the terminal nonvanishing collapses to the ABSOLUTE, flank-local statement

  `αU = crossH_puncU([M]) ≠ 0`,

the honest interior local-Künneth on the split-computable `puncU` piece. This module banks that
collapse; the `αU ≠ 0` detection is the dedicated `…CrossLocalDetect` block.

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — endpoint slices land in `puncU`** and the interior real bounds `interior_real_bounds`.
* **§2 — the absolute `puncU` cross class** `alphaU` and the chain-for-chain bridge
  `crossHloc_eq_relIncl_alphaU`: `crossHloc([M]|σ) = ι_U(αU)`.
* **§3 — `ι_U` injective** (`relIncl_puncU_compl_injective`) and the collapse
  `crossHloc_ne_zero_of_alphaU_ne_zero`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalReduce
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedFlankInjective
import SKEFTHawking.SingularConvexStageIso
import SKEFTHawking.SingularFundamentalClassExist

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocal
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalReduce
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedFlankInjective

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalBridge

noncomputable section

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-! ## §1. Endpoint slices land in `puncU`; the interior real bounds -/

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] in
/-- **Interior real bounds** from `x ∉ ∂W`: `0 < x.2 < 1` (real). -/
theorem interior_real_bounds (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) : (0 : ℝ) < (x.2 : ℝ) ∧ (x.2 : ℝ) < 1 := by
  obtain ⟨h0, h1⟩ := interior_snd_ne x hx
  refine ⟨lt_of_le_of_ne (unitInterval.nonneg x.2) ?_, lt_of_le_of_ne (unitInterval.le_one x.2) ?_⟩
  · exact fun h => h0 (Subtype.ext (h.symm.trans (Set.Icc.coe_bot 0 1).symm))
  · exact fun h => h1 (Subtype.ext (h.trans (Set.Icc.coe_top 0 1).symm))

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] in
/-- **The endpoint slice `M × {1}` lands in `puncU x`** (`1 ≠ x.2`, from `x.2 < 1`). -/
theorem slice_one_maps_puncU (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)) :
    Set.MapsTo (slice (graphHom (TopCat.of M)) 1) (Set.univ : Set ↑(TopCat.of M))
      (puncU (N := TopCat.of M) x) := by
  intro a _
  show (slice (graphHom (TopCat.of M)) 1 a).2 ≠ x.2
  rw [slice_graphHom]
  intro h
  exact absurd (congrArg (fun y : unitInterval => (y : ℝ)) h.symm)
    (by simpa using ne_of_lt (interior_real_bounds x hx).2)

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] in
/-- **The endpoint slice `M × {0}` lands in `puncU x`** (`0 ≠ x.2`, from `0 < x.2`). -/
theorem slice_zero_maps_puncU (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)) :
    Set.MapsTo (slice (graphHom (TopCat.of M)) 0) (Set.univ : Set ↑(TopCat.of M))
      (puncU (N := TopCat.of M) x) := by
  intro a _
  show (slice (graphHom (TopCat.of M)) 0 a).2 ≠ x.2
  rw [slice_graphHom]
  intro h
  exact absurd (congrArg (fun y : unitInterval => (y : ℝ)) h.symm)
    (by simpa using ne_of_gt (interior_real_bounds x hx).1)

/-! ## §2. The absolute `puncU` cross class and the chain-for-chain bridge -/

/-- **The absolute `puncU` cross class** `αU = [M] × [I,∂I] ∈ H_{m'+3}(M×I, M×(I∖t))`, the prism of the
fundamental class rel the `I`-punctured piece — the flank-local incarnation of the terminal prism. -/
noncomputable def alphaU (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)) :
    RelativeHomology (puncU (N := TopCat.of M) x) (m' + 3) :=
  crossH (M := TopCat.of M) (slice_one_maps_puncU x hx) (slice_zero_maps_puncU x hx) (m' + 1)
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M))

omit [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M] in
/-- **`puncU x ⊆ {x}ᶜ`**: a point differing from `x` in the interval coordinate differs from `x`. -/
theorem puncU_subset_compl (x : ↑(cyl (TopCat.of M))) :
    puncU x ⊆ ({x}ᶜ : Set ↑(cyl (TopCat.of M))) :=
  fun _p hp hpx => hp (hpx ▸ rfl)

/-- **`relIncl` on a `mk` class** is the `mk` of the identity-pushed relative cycle (same chain, bigger
subspace). The `RelativeHomology.mk`-form of `RelativeHomology.map_mk`. -/
theorem relIncl_mk {X : TopCat} {S T : Set ↑X} (h : S ⊆ T) (n : ℕ) (z : relCycles S n) :
    relIncl h n (RelativeHomology.mk S n z)
      = RelativeHomology.mk T n
          (relCyclesMap (ContinuousMap.id ↑X) (fun _a ha => h ha) n z) := by
  show RelativeHomology.map (ContinuousMap.id ↑X) (fun _a ha => h ha) n (Submodule.Quotient.mk z)
    = Submodule.Quotient.mk (relCyclesMap (ContinuousMap.id ↑X) (fun _a ha => h ha) n z)
  rw [RelativeHomology.map_mk]

omit [PreconnectedSpace M] in
/-- **The chain-for-chain bridge** `crossHloc([M]|σ) = ι_U(αU)`. Both sides are the class of the SAME
prism chain `prismOp graphHom z` (`z` a fundamental cycle rep): the LHS rel `{x}ᶜ` (via `crossHloc_mk`
on `mLocalClass = [z] rel {σ}ᶜ`), the RHS the `puncU`-class `crossH([M])` re-included to `{x}ᶜ` (via
`crossH_mk` + `relIncl` = same chain under `mapChain id`). -/
theorem crossHloc_eq_relIncl_alphaU (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    crossHloc (M := TopCat.of M) (interior_slice_one x hx) (interior_slice_zero x hx)
        (interior_punc x) (m' + 1) (mLocalClass x z)
      = relIncl (puncU_subset_compl (x : ↑(cyl (TopCat.of M)))) (m' + 3) (alphaU x hx) := by
  simp only [alphaU]
  rw [hz, crossH_mk]
  simp only [mLocalClass]
  rw [crossHloc_mk, relIncl_mk]
  refine congrArg (RelativeHomology.mk ({x}ᶜ : Set ↑(cyl (TopCat.of M))) (m' + 3)) (Subtype.ext ?_)
  rw [relCyclesMap_coe]
  show crossRelChainLM (interior_punc x) (m' + 1)
      (RelativeChain.mk ({x.1}ᶜ : Set ↑(TopCat.of M)) (m' + 2)
        (z : SingularChain (TopCat.of M) (m' + 2)))
    = relMapChain (ContinuousMap.id ↑(cyl (TopCat.of M))) _ (m' + 3)
        (RelativeChain.mk (puncU (N := TopCat.of M) x) (m' + 3)
          (crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2))))
  rw [crossRelChainLM_mk, relMapChain_mk, SKEFTHawking.SingularFunctoriality.mapChain_id]
  rfl

/-! ## §3. `ι_U` injective and the collapse to `αU ≠ 0` -/

/-- **`ι_U = relIncl (puncU ⊆ {x}ᶜ)` is injective** at top degree — a `puncU`-flank class survives into
the punctured-product target. Transported from `puncU_flank_injective` (`relIncl (puncU ⊆ puncU∪puncV)`)
across the set congruence `puncU ∪ puncV = {x}ᶜ` (`puncU_union_puncV`, a `LinearEquiv`). -/
theorem relIncl_puncU_compl_injective (x : ↑(cyl (TopCat.of M))) (ht0 : (0 : ℝ) < (x.2 : ℝ))
    (ht1 : (x.2 : ℝ) < 1) :
    Function.Injective (relIncl (puncU_subset_compl x) (m' + 3)) := by
  have hUV : puncU x ∪ puncV x = ({x}ᶜ : Set ↑(cyl (TopCat.of M))) := puncU_union_puncV x
  intro a b hab
  apply puncU_flank_injective x ht0 ht1
  apply (SKEFTHawking.SingularConvexStageIso.relHomologySetCongr hUV.subset hUV.symm.subset
    (m' + 3)).injective
  show relIncl hUV.subset (m' + 3) (relIncl Set.subset_union_left (m' + 3) a)
    = relIncl hUV.subset (m' + 3) (relIncl Set.subset_union_left (m' + 3) b)
  rw [relIncl_trans, relIncl_trans]
  exact hab

/-- **The terminal collapse**: `crossHloc([M]|σ) ≠ 0` if the absolute `puncU` cross class `αU ≠ 0`. From
the chain-for-chain bridge `crossHloc([M]|σ) = ι_U(αU)` and `ι_U` injective (injective maps send
nonzero to nonzero). The interior local-Künneth is now the ABSOLUTE, split-computable
`crossH_puncU([M]) ≠ 0`. -/
theorem crossHloc_ne_zero_of_alphaU_ne_zero (x : ↑(TopCat.of (cylW M)))
    (hx : x ∉ (cylModel m').boundary (cylW M)) (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z)
    (hαU : alphaU x hx ≠ 0) :
    crossHloc (M := TopCat.of M) (interior_slice_one x hx) (interior_slice_zero x hx)
        (interior_punc x) (m' + 1) (mLocalClass x z) ≠ 0 := by
  rw [crossHloc_eq_relIncl_alphaU x hx z hz]
  intro h
  obtain ⟨ht0, ht1⟩ := interior_real_bounds x hx
  exact hαU (relIncl_puncU_compl_injective (x : ↑(cyl (TopCat.of M))) ht0 ht1
    (by rw [map_zero]; exact h))

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalBridge
