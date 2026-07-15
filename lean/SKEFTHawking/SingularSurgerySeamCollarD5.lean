/-
# Phase 5q.H W-D — SURGERY WAVE 8 (stage 2): THE D⁵ b-ROW WITH THE SEAM COLLAR CLOSED

Wave 8 stage 1 (`SingularSurgerySeamCollar.lean`) closed the seam: the raw
`[chartSeam : ChartedSpace KTModel ↥seamNbhd]` typeclass input is now CONSTRUCTED from a
`SeamCollarDatum` (the collar homeomorphism onto a welded-collar model). This module pins that at the
concrete handle end `Ha = D⁵` (wave 7) and restates the FINAL residual row of
`ambientTraceBordism_concrete_D5`.

## The residual row, after this wave

The Pin⁺ ambient trace bordism `Bordism ((𝓡 4).prod (𝓡∂ 1)) s t` is now produced from **only**:

* the source closed 4-manifold `s` (Hausdorff) and target `t`;
* the attaching region `S ⊆ D⁵` (closed) and attaching map `φ : S → s.M × I` (continuous, injective);
* the **seam collar datum** `cd : SeamCollarDatum W` — the attaching base `A` (a 4-manifold charted on
  `E⁴`, the tubular presentation of `φ(S)`) and the collar homeomorphism `↥seamNbhd ≃ₜ WeldedCollarModel A`
  (the collar-neighborhood-theorem output) — plus the containment `hseam`;
* the boundary identification `e` — continuous, injective, with range exactly `∂W`.

The seam collar's chart — Wave-6's opaque `[chartSeam]` typeclass — is now CONSTRUCTED from the collar
datum; only {attaching map, collar homeomorphism, boundary injectivity + range} carry genuine geometric
content. Both the handle-atlas (wave 7) and the seam-collar chart (wave 8) are discharged.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSurgerySeamCollar
import SKEFTHawking.SingularSurgeryHandleD5

namespace SKEFTHawking.SurgeryFoundation

open Topology TopologicalSpace Set
open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTSurgeryTraceConsumers
open SKEFTHawking.DiskChartGeneric (D5)

/-- **The concrete ambient trace bordism with the `D⁵` handle AND the seam collar closed (the restated
residual row).** With the handle end fixed to `D⁵` (wave 7) and the seam collar supplied by a
`SeamCollarDatum` (wave 8 stage 1), the Pin⁺ surgery-trace `Bordism ((𝓡 4).prod (𝓡∂ 1)) s t` is
produced from exactly the sharply-named residuals: the attaching region `S ⊆ D⁵`/map `φ`, the **seam
collar datum** `cd` (the attaching base `A` charted on `E⁴` + the collar homeomorphism) with containment
`hseam`, and a boundary identification `e` that is continuous, injective, and hits exactly `∂W`. Both
the handle-atlas AND the seam-collar chart — the two largest of wave 6's four named inputs — are no
longer opaque hypotheses. -/
noncomputable def ambientTraceBordism_concrete_D5_ofCollar
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (e : s.M ⊕ t.M → (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (he_cont : Continuous e)
    (he_inj : Function.Injective e)
    (he_boundary :
      letI := cd.chartSeam
      letI : ChartedSpace KTModel (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier :=
        (ktSurgeryChartDatum s.M D5 S hS φ hφ hφinj cd.seamNbhd hseam).carrierChartedSpace
      Set.range e =
        ((𝓡 4).prod (𝓡∂ 1)).boundary (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) :
    Bordism ((𝓡 4).prod (𝓡∂ 1)) s t :=
  ambientTraceBordism_concrete_ofCollar s t D5 S hS φ hφ hφinj cd hseam e he_cont he_inj he_boundary

end SKEFTHawking.SurgeryFoundation
