/-
# Phase 5q.H — K6′b Leg 25: **`KummerK3` IS A SMOOTH 4-MANIFOLD**

The capstone of the weld atlas. `KummerK3Chart` made `K3` a charted space on the boundaryless flat
model `𝓔³ × ℝ` with the three weld chart families; Legs 15–24 closed the nine ordered transition
classes of the `3 × 3` dispatch:

| | 1 = E-interior | 2 = Q-interior | 3 = seam |
|---|---|---|---|
| **1** | §1 here (lift + `isManifold_interiorE`) | `KummerInteriorManifold` (vacuous) | `KummerSeamTransE` |
| **2** | `KummerSeamTransition` | §1 here (lift + `isManifold_interiorQ`) | `KummerSeamTransQClass` |
| **3** | `KummerSeamTransE` | `KummerSeamTransQClass` | `KummerSeamTransition` |

**What §1 adds.** `KummerInteriorManifold` proved the two *pieces* `↥interiorE` and `↥interiorQ` are
`C^k` manifolds on `𝓔³ × ℝ`. The `K3`-level diagonal classes are those transitions pushed forward
along the two open embeddings, and `OpenPartialHomeomorph.lift_openEmbedding_trans` cancels the
embedding on the nose — leaving exactly the piece-level coordinate change. The one genuinely new
ingredient is the *off-diagonal E* case `c ≠ c′`: two distinct copies of the resolution piece are
disjoint in `K3` because the weld glues an `inr` only to an `inl` (`weldMk_inr_injective`).

**§2 — the assembly**, and **§3 — the mission's model transport**:

    IsManifold 𝓘(ℝ, 𝓔³ × ℝ) k KummerK3        (§2)
    IsManifold (𝓡 4) k KummerK3                (§3, via `ManifoldModelTransport`)

for every regularity `k : WithTop ℕ∞` — in particular `k = ⊤`, the smooth category.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamTransQClass

namespace SKEFTHawking.KummerK3Manifold

open Set Topology
open scoped Manifold
open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerResolutionPiece (RP3)
open SKEFTHawking.KummerWeld (KummerK3 EIndex weldMk weldMk_inr_injective)
open SKEFTHawking.KummerWeldOpenPieces (interiorE eInteriorCopy isOpenEmbedding_eInteriorCopy)
open SKEFTHawking.KummerWeldQInterior (interiorQ)
open SKEFTHawking.HalfSpaceInteriorFlatten (FModel)
open SKEFTHawking.KummerSeamChart (seamChart)
open SKEFTHawking.KummerK3Chart

noncomputable section

variable {k : WithTop ℕ∞}

/-! ## §1. The two diagonal interior classes, at the `K3` level -/

/-- **CLASS (1,1), same copy.** The lift along `eInteriorCopy c` cancels
(`lift_openEmbedding_trans`), leaving the `↥interiorE` coordinate change. -/
theorem mem_contDiffGroupoid_eFam_same (c : EIndex) (y y' : ↥interiorE) :
    ((eFamChart c y).symm.trans (eFamChart c y')) ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  haveI : IsManifold 𝓘(ℝ, FModel) k (↥interiorE) :=
    SKEFTHawking.KummerInteriorManifold.isManifold_interiorE
  rw [eFamChart, eFamChart, OpenPartialHomeomorph.lift_openEmbedding_trans]
  exact StructureGroupoid.compatible _ (chart_mem_atlas FModel y) (chart_mem_atlas FModel y')

/-- **CLASS (1,1), distinct copies — vacuous.** The weld glues an `inr` only to an `inl`, so two
distinct copies of the resolution piece are disjoint in `K3`. -/
theorem source_empty_eFam_ne {c c' : EIndex} (h : c ≠ c') (y y' : ↥interiorE) :
    ((eFamChart c y).symm.trans (eFamChart c' y')).source = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage] at hp
  obtain ⟨-, hp2⟩ := hp
  rw [eFamChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hp2
  obtain ⟨e', -, he'⟩ := hp2
  have hsy : (eFamChart c y).symm p = eInteriorCopy c ((chartAt FModel y).symm p) := rfl
  rw [hsy] at he'
  have hpair : (c', (e' : SKEFTHawking.KummerResolutionPiece.ResE))
      = (c, (((chartAt FModel y).symm p : ↥interiorE) : SKEFTHawking.KummerResolutionPiece.ResE)) :=
    weldMk_inr_injective he'
  exact h (congrArg Prod.fst hpair).symm

/-- **CLASS (1,1) CLOSED at the `K3` level.** -/
theorem mem_contDiffGroupoid_eFam (c c' : EIndex) (y y' : ↥interiorE) :
    ((eFamChart c y).symm.trans (eFamChart c' y')) ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  by_cases h : c = c'
  · subst h; exact mem_contDiffGroupoid_eFam_same c y y'
  · exact SKEFTHawking.KummerInteriorManifold.mem_groupoid_of_source_empty
      (source_empty_eFam_ne h y y')

/-- **CLASS (2,2) CLOSED at the `K3` level.** There is only one Q-interior copy, so the lift
cancels outright. -/
theorem mem_contDiffGroupoid_qFam (y y' : ↥interiorQ) :
    ((qFamChart y).symm.trans (qFamChart y')) ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  haveI : IsManifold 𝓘(ℝ, FModel) k (↥interiorQ) :=
    SKEFTHawking.KummerInteriorManifold.isManifold_interiorQ
  rw [qFamChart, qFamChart, OpenPartialHomeomorph.lift_openEmbedding_trans]
  exact StructureGroupoid.compatible _ (chart_mem_atlas FModel y) (chart_mem_atlas FModel y')

/-! ## §2. The nine-class dispatch, and the flat-model manifold -/

/-- **EVERY WELD-ATLAS COORDINATE CHANGE IS `C^k`** — the `3 × 3` dispatch, one entry per closed
transition class. -/
theorem mem_contDiffGroupoid_atlasK3 {f f' : OpenPartialHomeomorph KummerK3 FModel}
    (hf : f ∈ atlasK3) (hf' : f' ∈ atlasK3) :
    (f.symm.trans f') ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  rcases hf with (hf | hf) | hf
  · obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hf
    obtain ⟨y, rfl⟩ := hc
    rcases hf' with (hf' | hf') | hf'
    · obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp hf'
      obtain ⟨y', rfl⟩ := hc'
      exact mem_contDiffGroupoid_eFam c c' y y'
    · obtain ⟨y', rfl⟩ := hf'
      exact SKEFTHawking.KummerInteriorManifold.mem_contDiffGroupoid_eFam_trans_qFam c y y'
    · obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp hf'
      obtain ⟨r₀, rfl⟩ := hc'
      exact SKEFTHawking.KummerSeamTransE.mem_contDiffGroupoid_eFam_trans_seamFam c c' y r₀
  · obtain ⟨y, rfl⟩ := hf
    rcases hf' with (hf' | hf') | hf'
    · obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp hf'
      obtain ⟨y', rfl⟩ := hc'
      exact SKEFTHawking.KummerSeamTransition.mem_contDiffGroupoid_qFam_trans_eFam c' y' y
    · obtain ⟨y', rfl⟩ := hf'
      exact mem_contDiffGroupoid_qFam y y'
    · obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp hf'
      obtain ⟨r₀, rfl⟩ := hc'
      exact SKEFTHawking.KummerSeamTransQClass.mem_contDiffGroupoid_qFam_trans_seamFam y c' r₀
  · obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hf
    obtain ⟨r₀, rfl⟩ := hc
    rcases hf' with (hf' | hf') | hf'
    · obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp hf'
      obtain ⟨y', rfl⟩ := hc'
      exact SKEFTHawking.KummerSeamTransE.mem_contDiffGroupoid_seamFam_trans_eFam c' c y' r₀
    · obtain ⟨y', rfl⟩ := hf'
      exact SKEFTHawking.KummerSeamTransQClass.mem_contDiffGroupoid_seamFam_trans_qFam y' c r₀
    · obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp hf'
      obtain ⟨r₀', rfl⟩ := hc'
      exact SKEFTHawking.KummerSeamTransition.mem_contDiffGroupoid_seamFam c c' r₀ r₀'

instance hasGroupoid_kummerK3 :
    HasGroupoid KummerK3 (contDiffGroupoid k 𝓘(ℝ, FModel)) :=
  ⟨fun hf hf' => mem_contDiffGroupoid_atlasK3 hf hf'⟩

/-- **`KummerK3` IS A `C^k` MANIFOLD ON THE FLAT MODEL `𝓔³ × ℝ`** — the weld atlas is a smooth
atlas, for every regularity `k` (in particular `k = ⊤`, the smooth category). -/
instance isManifold_kummerK3 : IsManifold 𝓘(ℝ, FModel) k KummerK3 :=
  IsManifold.mk' _ _ _

/-! ## §3. The mission's model transport -/

/-- **`KummerK3` IS A `C^k` MANIFOLD ON `𝓡 4`** — the Kummer K3 surface, built as the 16-fold weld
of the resolution pieces onto the free quotient `T⁴°/τ`, is a smooth 4-manifold on the flat model
`𝓡 4` that downstream consumers demand. The charted space is the weld atlas transported along the
continuous linear reshape `𝓔³ × ℝ ≃L 𝓔⁴`. -/
theorem isManifold_R4_kummerK3 :
    letI := SKEFTHawking.ManifoldModelTransport.transportedChartedSpace
      (SKEFTHawking.ManifoldModelTransport.prodRealEquivEuclidean 3) KummerK3
    IsManifold (𝓡 4) k KummerK3 :=
  SKEFTHawking.ManifoldModelTransport.isManifold_R4_of_prodReal KummerK3

/-- The smooth-category specialisation. -/
theorem isManifold_R4_kummerK3_smooth :
    letI := SKEFTHawking.ManifoldModelTransport.transportedChartedSpace
      (SKEFTHawking.ManifoldModelTransport.prodRealEquivEuclidean 3) KummerK3
    IsManifold (𝓡 4) ⊤ KummerK3 :=
  isManifold_R4_kummerK3

end

end SKEFTHawking.KummerK3Manifold
