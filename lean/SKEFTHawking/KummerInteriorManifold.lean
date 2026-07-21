/-
# Phase 5q.H — K6′b Leg 13: the two INTERIOR pieces are boundaryless `C^k` manifolds on `𝓔³ × ℝ`

Step 5 of the weld atlas is a 3×3 transition dispatch. This module closes its two **interior
diagonal** classes — (1,1) `E-int ↔ E-int` and (2,2) `Q-int ↔ Q-int` — at the level of the pieces
themselves:

* `isManifold_interiorE : IsManifold 𝓘(ℝ, 𝓔³ × ℝ) k ↥interiorE`
* `isManifold_interiorQ : IsManifold 𝓘(ℝ, 𝓔³ × ℝ) k ↥interiorQ`

**The chain.** Each flat interior chart is *literally* the flattening of a `subtypeRestr` of a
half-space chart of the ambient piece:

    eIntChart c = flatChart (c.subtypeRestr _)          (`eIntChart_eq_flatChart_subtypeRestr`)

so its transition is, by `OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr`, `EqOnSource`
to an open **restriction** of the ambient transition — which lies in `contDiffGroupoid k
((𝓡 3).prod (𝓡∂ 1))` by `instIsManifoldResE` / `isManifold_freeQuotient` plus
`ClosedUnderRestriction` — and `HalfSpaceInteriorSmooth.mem_contDiffGroupoid_flatChart` carries it
across the flattening.

§4 also closes the off-diagonal class (1,2), which is **vacuous**: the two interior families have
disjoint sources in `K3` (`KummerWeldQInterior.disjoint_qInterior_eInterior`), so their transition
has empty source and lies in every structure groupoid.

**What remains of step 5** (named precisely, not hand-waved): the three **seam** classes (1,3),
(2,3) and (3,3). Each needs the smoothness of the double-collar parametrization
`dblCollar c : ℝP³ × (−1/8, 1/2) → K3` *as a map into the E and Q pieces* — i.e. the `v ≠ 0`
thickening of `KummerSeamSmooth.contMDiff_bdryMapRP3`, which is only the boundary (`v = 0`) case.
Nothing in this module is blocked on them; they are a separate brick.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.HalfSpaceInteriorSmooth
import SKEFTHawking.KummerEInteriorChart
import SKEFTHawking.KummerQInteriorChart
import SKEFTHawking.KummerResolutionPieceManifold
import SKEFTHawking.KummerQuotientManifold
import SKEFTHawking.KummerK3Chart

namespace SKEFTHawking.KummerInteriorManifold

open Set Topology
open scoped Manifold
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerWeldOpenPieces (interiorE isOpen_interiorE)
open SKEFTHawking.KummerWeldQInterior (interiorQ isOpen_interiorQ)
open SKEFTHawking.HalfSpaceInteriorFlatten
open SKEFTHawking.HalfSpaceInteriorSmooth
open SKEFTHawking.KummerEInteriorChart
open SKEFTHawking.KummerQInteriorChart
open SKEFTHawking.KummerK3Chart

noncomputable section

variable {k : WithTop ℕ∞}

/-! ## §1. The generic step: a flattened `subtypeRestr` transition is in the flat groupoid -/

/-- **THE GENERIC INTERIOR-DIAGONAL STEP.** For an open subset `s` of a manifold-with-boundary `M`
on the half-space model, the flattening of the `s`-restrictions of two ambient charts has a `C^k`
transition on the flat model — provided the ambient transition is `C^k`. -/
theorem mem_contDiffGroupoid_flatChart_subtypeRestr {M : Type*} [TopologicalSpace M]
    {s : TopologicalSpace.Opens M} (hs : Nonempty ↥s)
    {c c' : OpenPartialHomeomorph M HModel}
    (h : (c.symm.trans c') ∈ contDiffGroupoid k IH) :
    ((flatChart (c.subtypeRestr hs)).symm.trans (flatChart (c'.subtypeRestr hs)))
      ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  refine mem_contDiffGroupoid_flatChart ?_
  refine (contDiffGroupoid k IH).mem_of_eqOnSource
    (closedUnderRestriction' h (c.isOpen_inter_preimage_symm s.2)) ?_
  exact OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr hs c c'

/-! ## §2. Class (1,1) — the E-piece interior -/

/-- The E-interior as an `Opens ResE`. -/
def interiorEOpens : TopologicalSpace.Opens ResE := ⟨interiorE, isOpen_interiorE⟩

/-- **The flat E-interior chart IS the flattening of a `subtypeRestr`** — the associativity that
puts `eIntChart` in range of the generic step. -/
theorem eIntChart_eq_flatChart_subtypeRestr (c : OpenPartialHomeomorph ResE HModel) :
    eIntChart c = flatChart (c.subtypeRestr (s := interiorEOpens) instNonemptyInteriorE) :=
  (OpenPartialHomeomorph.trans_assoc _ _ _).symm

theorem atlasEInt_subset_atlasE : atlasEInt ⊆ SKEFTHawking.KummerResolutionPieceBoundary.atlasE := by
  rintro c (rfl | rfl | rfl)
  · exact Or.inl (Or.inl (Or.inl (Set.mem_insert _ _)))
  · exact Or.inl (Or.inl (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  · exact Or.inl (Or.inl (Or.inl
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))

/-- **CLASS (1,1) CLOSED — `↥interiorE` is a boundaryless `C^k` manifold on `𝓔³ × ℝ`.** -/
theorem isManifold_interiorE : IsManifold 𝓘(ℝ, FModel) k (↥interiorE) := by
  haveI : HasGroupoid (↥interiorE) (contDiffGroupoid k 𝓘(ℝ, FModel)) := by
    refine ⟨?_⟩
    rintro f f' ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    rw [eIntChart_eq_flatChart_subtypeRestr, eIntChart_eq_flatChart_subtypeRestr]
    refine mem_contDiffGroupoid_flatChart_subtypeRestr _ ?_
    exact StructureGroupoid.compatible (contDiffGroupoid k IH)
      (atlasEInt_subset_atlasE hc) (atlasEInt_subset_atlasE hc')
  exact IsManifold.mk' _ _ _

/-! ## §3. Class (2,2) — the Q-piece interior -/

/-- The Q-interior as an `Opens FreeQuotient`. -/
def interiorQOpens : TopologicalSpace.Opens FreeQuotient := ⟨interiorQ, isOpen_interiorQ⟩

theorem qIntChart_eq_flatChart_subtypeRestr (y : ↥interiorQ) :
    qIntChart y
      = flatChart ((chartAt HModel (y : FreeQuotient)).subtypeRestr
          (s := interiorQOpens) ⟨y⟩) :=
  (OpenPartialHomeomorph.trans_assoc _ _ _).symm

/-- **CLASS (2,2) CLOSED — `↥interiorQ` is a boundaryless `C^k` manifold on `𝓔³ × ℝ`.** -/
theorem isManifold_interiorQ : IsManifold 𝓘(ℝ, FModel) k (↥interiorQ) := by
  haveI : IsManifold ((𝓡 3).prod (𝓡∂ 1)) k FreeQuotient :=
    SKEFTHawking.KummerQuotientManifold.isManifold_freeQuotient
  haveI : HasGroupoid (↥interiorQ) (contDiffGroupoid k 𝓘(ℝ, FModel)) := by
    refine ⟨?_⟩
    rintro f f' ⟨y, rfl⟩ ⟨y', rfl⟩
    rw [qIntChart_eq_flatChart_subtypeRestr, qIntChart_eq_flatChart_subtypeRestr]
    refine mem_contDiffGroupoid_flatChart_subtypeRestr _ ?_
    exact StructureGroupoid.compatible (contDiffGroupoid k IH)
      (chart_mem_atlas HModel (y : FreeQuotient)) (chart_mem_atlas HModel (y' : FreeQuotient))
  exact IsManifold.mk' _ _ _

/-! ## §4. Class (1,2) — vacuous: the two interior families are disjoint in `K3` -/

/-- A coordinate change with empty source lies in **every** structure groupoid — locality has
nothing to check. -/
theorem mem_groupoid_of_source_empty {H : Type*} [TopologicalSpace H] {G : StructureGroupoid H}
    {e : OpenPartialHomeomorph H H} (he : e.source = ∅) : e ∈ G :=
  G.locality fun x hx => absurd (he ▸ hx) (Set.notMem_empty x)

/-- **CLASS (1,2) IS VACUOUS.** An E-interior chart of `K3` and a Q-interior chart of `K3` have
disjoint sources (`KummerWeldQInterior.disjoint_qInterior_eInterior`), so their transition has empty
source. -/
theorem source_empty_eFam_trans_qFam (c : SKEFTHawking.KummerWeld.EIndex) (y : ↥interiorE)
    (y' : ↥interiorQ) :
    ((eFamChart c y).symm.trans (qFamChart y')).source = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hE : (eFamChart c y).symm p ∈ (eFamChart c y).source :=
    (eFamChart c y).map_target hp1
  rw [eFamChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hE
  obtain ⟨e, -, heq⟩ := hE
  rw [qFamChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hp2
  obtain ⟨q, -, hqeq⟩ := hp2
  refine Set.disjoint_left.mp SKEFTHawking.KummerWeldQInterior.disjoint_qInterior_eInterior
    ⟨q, hqeq⟩ ?_
  exact ⟨Sum.inr (c, (e : ResE)), ⟨(c, (e : ResE)), ⟨Set.mem_univ _, e.2⟩, rfl⟩, heq⟩

/-- **CLASS (1,2) CLOSED** — the transition lies in the flat groupoid because it is empty. -/
theorem mem_contDiffGroupoid_eFam_trans_qFam (c : SKEFTHawking.KummerWeld.EIndex)
    (y : ↥interiorE) (y' : ↥interiorQ) :
    ((eFamChart c y).symm.trans (qFamChart y')) ∈ contDiffGroupoid k 𝓘(ℝ, FModel) :=
  mem_groupoid_of_source_empty (source_empty_eFam_trans_qFam c y y')

end

end SKEFTHawking.KummerInteriorManifold
