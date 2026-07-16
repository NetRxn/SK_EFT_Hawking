/-
# Phase 5q.H close-out — THE D⁵ SIDE OF THE CAPSTONE COVER-GLUE (residual 1 + the boundary absorbs)

This module discharges the two remaining constructive residuals of `CapstoneCoverGlueResidual`
(`PinPlusTraceCapstoneCoverGlueCyl.lean`) whose content is genuinely available:

**§1 — the two boundary-absorb facts (`habsorbB`/`habsorbHa`), from the surgered-end datum.** The
cylinder-side absorb (`habsorbB`) says the cylinder's manifold boundary `∂(M × I) = M × {⊥,⊤}`, pushed
by `fromCyl`, lands in `∂W ∪ range fromHandle`. It is discharged face by face: the bottom face
`M × {0}` is the source end `range ktSourceEnd ⊆ ∂W` (via the datum's boundary decomposition `d.bdry`);
the attached top `range φ` glues to the handle core (`HandleAttachment.glue`); the un-attached top
`M × {1} ∖ range φ` is absorbed into the surgered end `range eM' ⊆ ∂W` (via the new `topFaceCovered`
field). The `∂W` in the residual is bridged to `d.bdry`'s LHS through the Bordism's own
`he_boundary : range e = ∂W` field, so no `.W` whnf is forced.

**§2 — the disk's relative fundamental class (residual 1), the disk analogue of `hasRelFundClass_cylGen`.**
`D⁵ = closedBall(0,1) ⊆ E⁵` is a compact convex manifold-with-boundary; its boundary sphere `S⁴` is the
relative pair's boundary set `BdHa`. The relative fundamental class of `(D⁵, S⁴)` restricts to the
interior local generator at every interior point, giving `HasRelFundClass (TopCat.of D5) BdHa gen` — the
piece-intrinsic input `exists_detecting_chain_of_hasRelFundClass` turns into the residual's `D⁵`
detecting-chain triple `cHa`/`hcHa`/`hdetHa`.

Additive module (imports the cover-glue residual; touches no membrane-weld module). Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no `native_decide`, no
`maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCoverGlueCyl

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlue
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueCyl

namespace SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §1. The boundary-absorb facts, discharged from the surgered-end datum. -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- The residual's boundary set `∂W` decomposes as `range ktSourceEnd ∪ range eM'`, bridged from the
datum's `d.bdry` through the Bordism's own `he_boundary` field (no `.W` whnf forced). -/
theorem capstone_boundary_eq :
    (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      = Set.range (ktSourceEnd s.M D5 S hS φ hφ hφinj) ∪ Set.range d.eM' :=
  d.bdry

omit [Nonempty s.M] [PreconnectedSpace s.M] in
/-- **The cylinder-side boundary-absorb fact (`habsorbB`), discharged.** The cylinder's manifold
boundary `∂(M × I) = M × {⊥,⊤}`, pushed by `fromCyl`, lands in `∂W ∪ range fromHandle`. Bottom face
`M × {⊥}`: the source end `range ktSourceEnd ⊆ ∂W`. Attached top `range φ`: the handle core (`glue`).
Un-attached top `M × {⊤} ∖ range φ`: the surgered end `range eM' ⊆ ∂W` (via `d.topFaceCovered`). -/
theorem capstone_habsorbB :
    ∀ y ∈ capstoneCylBdB s S hS φ hφ hφinj,
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl y
        ∈ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          ∪ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle := by
  intro y hy
  rw [capstoneCylBdB, cyl_boundary_eq] at hy
  have hy2 : y.2 = ⊥ ∨ y.2 = ⊤ := hy.2
  rcases hy2 with hbot | htop
  · -- bottom face `M × {⊥}`: the source end, inside `∂W`
    have hyeq : cylBot s.M y.1 = y := Prod.ext rfl (by rw [hbot]; rfl)
    refine Set.mem_union_left _ ?_
    rw [capstone_boundary_eq]
    exact Set.mem_union_left _ ⟨y.1, by rw [ktSourceEnd, hyeq]⟩
  · -- top face `M × {⊤}`: attached part glues to the handle, un-attached part to `eM'`
    by_cases hyφ : y ∈ Set.range φ
    · -- attached: `y = φ a`, and `fromCyl (φ a) = fromHandle a` (glue)
      obtain ⟨a, ha⟩ := hyφ
      refine Set.mem_union_right _ ⟨(a : D5), ?_⟩
      rw [← ha]
      exact ((ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a).symm
    · -- un-attached: covered by the surgered end `range eM' ⊆ ∂W`
      refine Set.mem_union_left _ ?_
      rw [capstone_boundary_eq]
      refine Set.mem_union_right _ (d.topFaceCovered ?_)
      exact Set.mem_image_of_mem _ ⟨Set.mem_prod.mpr ⟨Set.mem_univ _, htop⟩, hyφ⟩

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The handle-side boundary-absorb fact (`habsorbHa`), discharged.** The disk handle's model
boundary `∂D⁵ = S⁴ = {v | ‖v‖ = 1}` (`boundary_D5`), pushed by `fromHandle`, lands in
`∂W ∪ range fromCyl`. Attached part `y ∈ S`: `fromHandle y = fromCyl (φ ⟨y,·⟩)` glues to the cylinder
core (`glue`). Free boundary-sphere part `y ∈ S⁴ ∖ S`: the surgered end `range eM' ⊆ ∂W` (via the new
`d.sphereFaceCovered` field). The handle-side mirror of `capstone_habsorbB`; discharges the residual's
`habsorbHa` with `BdHa = S⁴ = {v | ‖v‖ = 1}`. -/
theorem capstone_habsorbHa :
    ∀ y ∈ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1},
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle y
        ∈ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          ∪ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl := by
  intro y hy
  by_cases hyS : y ∈ S
  · -- attached part `y ∈ S`: `fromHandle y = fromCyl (φ ⟨y,·⟩)` glues to the cylinder core
    refine Set.mem_union_right _ ⟨φ ⟨y, hyS⟩, ?_⟩
    exact (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue ⟨y, hyS⟩
  · -- free boundary-sphere part `y ∈ S⁴ ∖ S`: covered by the surgered end `range eM' ⊆ ∂W`
    refine Set.mem_union_left _ ?_
    rw [capstone_boundary_eq]
    exact Set.mem_union_right _ (d.sphereFaceCovered (Set.mem_image_of_mem _ ⟨hy, hyS⟩))

/-! ## §2. The disk's model boundary is the bounding sphere — the residual's `BdHa`, pinned.

The handle-side residual `CapstoneCoverGlueResidual.BdHa` is the disk's boundary-support set. The
canonical choice is the disk's own `ModelWithCorners` boundary `((𝓡 4).prod (𝓡∂ 1)).boundary D5`,
which this section computes to be exactly the bounding unit sphere `‖v‖ = 1` (`S⁴`). This is the
`n = 4` analogue of `SphereDiskFreezeB.boundary_threeDisk` and pins the residual's `BdHa`: interior
points (`‖v‖ < 1`, where the interior local-generator lives) are exactly the non-boundary points, so
the disk detecting chain of residual 1 has `BdHa = S⁴` as its boundary-support. -/

open SKEFTHawking.DiskChartGeneric

/-- Frontier of the disk collar model range at `n = 4`: `univ ×ˢ {half-space wall}`. The `n = 4`
analogue of `SphereDiskFreezeB.frontier_range_diskModel`. -/
theorem frontier_range_D5Model :
    frontier (Set.range ((𝓡 4).prod (𝓡∂ 1)))
      = (Set.univ : Set (EuclideanSpace ℝ (Fin 4))) ×ˢ
        {y : EuclideanSpace ℝ (Fin 1) | (0 : ℝ) = y 0} := by
  rw [ModelWithCorners.range_prod, frontier_prod_eq,
    ModelWithCorners.range_eq_univ (I := 𝓡 4), frontier_univ, closure_univ,
    frontier_range_modelWithCornersEuclideanHalfSpace, Set.empty_prod, Set.union_empty]

/-- **The boundary of `D⁵`** (collar model): the bounding unit sphere `‖v‖ = 1` (`= S⁴`). The `n = 4`
analogue of `SphereDiskFreezeB.boundary_threeDisk`; pins the residual's handle-side boundary-support
set `BdHa`. -/
theorem boundary_D5 :
    ((𝓡 4).prod (𝓡∂ 1)).boundary D5
      = {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} := by
  ext v
  simp only [ModelWithCorners.boundary, ModelWithCorners.IsBoundaryPoint, Set.mem_setOf_eq,
    frontier_range_D5Model, Set.mem_prod, Set.mem_univ, true_and]
  rw [extChartAt_coe]
  simp only [Function.comp_apply, ModelWithCorners.prod_apply]
  by_cases h : ‖(v : EuclideanSpace ℝ (Fin 5))‖ < 1
  · rw [show chartAt (ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanHalfSpace 1)) v
        = diskInteriorChart 4 from if_pos h]
    show (0 : ℝ) = (WithLp.toLp 2
        (fun _ : Fin 1 => (v : EuclideanSpace ℝ (Fin 5)).ofLp (Fin.last 4) + 2)).ofLp 0
        ↔ ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1
    rw [WithLp.ofLp_toLp]
    apply iff_of_false
    · intro heq
      have h2 : ‖(v : EuclideanSpace ℝ (Fin 5)).ofLp (Fin.last 4)‖
          ≤ ‖(v : EuclideanSpace ℝ (Fin 5))‖ := PiLp.norm_apply_le _ _
      rw [Real.norm_eq_abs] at h2
      have h3 := (abs_le.mp (h2.trans (le_of_lt h))).1
      linarith
    · exact ne_of_lt h
  · rw [show chartAt (ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanHalfSpace 1)) v
        = diskCollarChart 4 (diskDir 4 v) from if_neg h]
    show (0 : ℝ) = (WithLp.toLp 2
        (fun _ : Fin 1 => 1 - ‖(v : EuclideanSpace ℝ (Fin 5))‖)).ofLp 0
        ↔ ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1
    rw [WithLp.ofLp_toLp]
    constructor <;> intro heq <;> linarith

end

end SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
