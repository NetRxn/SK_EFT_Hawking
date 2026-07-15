/-
# Phase 5q.H W-D — SURGERY WAVE 8 (stage 4): THE TRACE CAPSTONE — source end wired into the b-row

Wave 8 stage 1 closed the seam collar; stage 3 (`SingularSurgeryBoundaryFloor.lean`) constructed the
source-end inclusion `s.M ↪ W` and the boundary-map combinators. This capstone wires them together:
the Pin⁺ trace bordism `Bordism ((𝓡 4).prod (𝓡∂ 1)) s t` produced with the boundary map
`e = Sum.elim (ktSourceEnd) eM'` — the **source half constructed** (`ktSourceEnd`, a closed embedding),
its continuity and its half of `he_inj` DISCHARGED, so only the surgered-end map `eM'` (with its own
continuity/injectivity and its disjointness from the source end) remains a geometric input.

## The residual row, after this wave (the FINAL b-row)

`Bordism ((𝓡 4).prod (𝓡∂ 1)) s t` is produced from **only**:

* the source closed 4-manifold `s` (Hausdorff), the target `t`;
* the attaching data `S ⊆ D⁵` / `φ : S → s.M × I` (+ the top-face fact `hφtop : φ` lands in `M × {1}`);
* the **seam collar datum** `cd` + `hseam` (wave 8 stage 1 — the collar homeomorphism, the seam chart
  CONSTRUCTED);
* the **surgered end** `eM' : t.M → W` continuous, injective, and range-disjoint from the source end
  (the `M'` cap embedding — the one genuinely-geometric boundary input left);
* `he_boundary : Set.range (Sum.elim (ktSourceEnd) eM') = J.boundary W` — the deep boundary
  identification (chart-choice-dependent at `k = 0`; the residual the smooth weld / `M'` packaging rides).

The handle atlas (wave 7), the seam-collar chart (wave 8 stage 1), and the source-end half of the
boundary map (wave 8 stage 3) are all discharged. What remains is exactly the attaching data + top-face
fact, the collar homeomorphism, the surgered-end cap embedding, and the boundary-range identification —
the irreducible geometric core of a surgery trace.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSurgerySeamCollarD5
import SKEFTHawking.SingularSurgeryBoundaryFloor

namespace SKEFTHawking.SurgeryFoundation

open Topology TopologicalSpace Set
open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTSurgeryTraceConsumers
open SKEFTHawking.DiskChartGeneric (D5)

/-- **THE TRACE CAPSTONE — the Pin⁺ ambient trace bordism with source end + seam collar discharged.**
With the handle end `D⁵` (wave 7), the seam collar (wave 8 stage 1 — `cd`), and the source-end half of
the boundary map (`ktSourceEnd`, wave 8 stage 3) all constructed, `Bordism ((𝓡 4).prod (𝓡∂ 1)) s t` is
produced from exactly: the attaching data `S`/`φ` + top-face fact `hφtop`; the seam collar datum `cd` +
`hseam`; the surgered-end cap `eM' : t.M → W` (continuous, injective, disjoint from the source end); and
the boundary-range identification `he_boundary`. The boundary map is `e = Sum.elim (ktSourceEnd) eM'`,
whose continuity and injectivity are discharged from the source-end structure + `eM'`'s. -/
noncomputable def ambientTraceBordism_capstone
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (eM' : t.M → (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (heM'_cont : Continuous eM')
    (heM'_inj : Function.Injective eM')
    (hdisj : Disjoint (Set.range (ktSourceEnd s.M D5 S hS φ hφ hφinj)) (Set.range eM'))
    (he_boundary :
      letI := cd.chartSeam
      letI : ChartedSpace KTModel (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier :=
        (ktSurgeryChartDatum s.M D5 S hS φ hφ hφinj cd.seamNbhd hseam).carrierChartedSpace
      Set.range (Sum.elim (ktSourceEnd s.M D5 S hS φ hφ hφinj) eM') =
        ((𝓡 4).prod (𝓡∂ 1)).boundary (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) :
    Bordism ((𝓡 4).prod (𝓡∂ 1)) s t :=
  ambientTraceBordism_concrete_D5_ofCollar s t S hS φ hφ hφinj cd hseam
    (Sum.elim (ktSourceEnd s.M D5 S hS φ hφ hφinj) eM')
    ((continuous_ktSourceEnd s.M D5 S hS φ hφ hφinj).sumElim heM'_cont)
    (injective_sumElim_ktSourceEnd s.M D5 S hS φ hφ hφinj eM' heM'_inj hdisj)
    he_boundary

end SKEFTHawking.SurgeryFoundation
