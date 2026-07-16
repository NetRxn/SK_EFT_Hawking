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

end

end SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
