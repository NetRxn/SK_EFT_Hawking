/-
# Phase 5q.H W-D — SURGERY WAVE 7 (stage 2): D⁵ PLUGGED INTO THE WAVE-6 CONSTRUCTORS

Wave 6 (`SingularSurgeryChartsConcrete.lean`) left the Pin⁺ surgery-trace consumer's handle end `Ha`
as a `[ChartedSpace KTModel Ha]` typeclass INPUT (the header's design of record: `Ha = D⁵`, NO corner,
NO re-association). Wave 7 stage 1 (`DiskChartGeneric.lean`) built the dimension-generic closed-ball
atlas and its `n = 4` instantiation `instChartedSpaceKTModelD5 : ChartedSpace KTModel D⁵`.

This module **discharges the handle-atlas input**: it feeds `D⁵` (with its concrete `KTModel`-atlas,
its `CompactSpace`/`T2Space` free — `EuclideanSpace ℝ (Fin 5)` is a proper space, so
`CompactSpace (closedBall 0 1)` is a global instance) into wave 6's constructors, and **restates the
residual row** of `ambientTraceBordism_concrete` with `Ha = D⁵` fixed.

## The residual row, after this wave

The Pin⁺ ambient trace bordism `Bordism ((𝓡 4).prod (𝓡∂ 1)) s t` is now produced from **only**:

* the source closed 4-manifold `s` (Hausdorff) and target `t` — its cylinder end `s.M × I` and chart
  are baked in (wave 6 §1);
* the attaching region `S ⊆ D⁵` (closed) and attaching map `φ : S → s.M × I` (continuous, injective);
* the welded seam collar `seamNbhd`/`chartSeam`;
* the boundary identification `e` — continuous (smoothness free at `k = 0`, wave 6 §2), injective, with
  range exactly `∂W`.

The handle end and its atlas — the largest of wave 6's four named inputs — are now **concrete** (`D⁵`
+ `instChartedSpaceKTModelD5`), no longer a hypothesis. Only {attaching map, seam collar, boundary
injectivity + range} carry genuine geometric content.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.DiskChartGeneric

namespace SKEFTHawking.SurgeryFoundation

open Topology TopologicalSpace
open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTSurgeryTraceConsumers
open SKEFTHawking.DiskChartGeneric (D5)

/-! ## §1. The KT surgery-trace handle attachment with the concrete `D⁵` handle end. -/

/-- **The KT surgery-trace handle-attachment with handle end `Ha = D⁵`.** The cylinder end
`B = s.M × I` and the handle end `D⁵` are both concrete now; only the attaching region `S ⊆ D⁵` and
attaching map `φ : S → s.M × I` are geometric inputs. `D⁵`'s compactness/Hausdorffness are free
(proper-space closed ball; subtype of a metric space). -/
def ktHandleAttachmentD5
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ) : HandleAttachment :=
  ktHandleAttachment M D5 S hS φ hφ hφinj

/-! ## §2. The KT surgery-trace smooth chart datum with the concrete `D⁵` handle end. -/

/-- **The KT surgery-trace `SmoothSurgeryChartDatum` with handle end `D⁵`**, at the Pin⁺ tangent
model `J = (𝓡 4).prod (𝓡∂ 1)`, smoothness order `k = 0`. The handle atlas is now
`instChartedSpaceKTModelD5` (concrete), not a hypothesis; the cylinder-end chart and the whole
`k = 0` smoothness/weld stack are free (wave 6 §1–§3). The remaining inputs are the attaching data,
the seam collar, and their closure/subset side conditions. -/
noncomputable def ktSmoothSurgeryChartDatumD5
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (seamNbhd : Opens (ktHandleAttachment M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment M D5 S hS φ hφ hφinj).seamRegion ⊆ seamNbhd)
    [chartSeam : ChartedSpace KTModel seamNbhd] : SmoothSurgeryChartDatum :=
  ktSmoothSurgeryChartDatum M D5 S hS φ hφ hφinj seamNbhd hseam

/-! ## §3. The residual row, restated — the concrete ambient trace bordism with the `D⁵` handle. -/

/-- **The concrete ambient trace bordism with the `D⁵` handle (the restated residual row).** With the
handle end fixed to `D⁵` and its atlas discharged by `instChartedSpaceKTModelD5`, the Pin⁺
surgery-trace `Bordism ((𝓡 4).prod (𝓡∂ 1)) s t` is produced from exactly the sharply-named residuals:
the attaching region `S ⊆ D⁵`/map `φ`, the welded seam collar `seamNbhd`/`chartSeam`, and a boundary
identification `e` that is continuous, injective, and hits exactly `∂W`. The handle-atlas input — the
largest of wave 6's four named inputs — is no longer a hypothesis. -/
noncomputable def ambientTraceBordism_concrete_D5
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (seamNbhd : Opens (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ seamNbhd)
    [chartSeam : ChartedSpace KTModel seamNbhd]
    (e : s.M ⊕ t.M → (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (he_cont : Continuous e)
    (he_inj : Function.Injective e)
    (he_boundary :
      letI : ChartedSpace KTModel (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier :=
        (ktSurgeryChartDatum s.M D5 S hS φ hφ hφinj seamNbhd hseam).carrierChartedSpace
      Set.range e =
        ((𝓡 4).prod (𝓡∂ 1)).boundary (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) :
    Bordism ((𝓡 4).prod (𝓡∂ 1)) s t :=
  ambientTraceBordism_concrete s t D5 S hS φ hφ hφinj seamNbhd hseam e he_cont he_inj he_boundary

end SKEFTHawking.SurgeryFoundation
