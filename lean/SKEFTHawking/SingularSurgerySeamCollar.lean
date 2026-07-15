/-
# Phase 5q.H W-D — SURGERY WAVE 8 (stage 1): THE WELDED SEAM COLLAR (closing the seam)

Wave 7 (`SingularSurgeryHandleD5.lean`) made the handle end concrete (`Ha = D⁵` +
`instChartedSpaceKTModelD5`), leaving `ambientTraceBordism_concrete_D5` conditional on exactly:
the attaching data `S`/`φ`, the **welded seam collar** (`seamNbhd`/`hseam`/`chartSeam` — a raw
`ChartedSpace KTModel ↥seamNbhd` typeclass input), and the boundary inputs `e`/`he_inj`/`he_boundary`.

This module **closes the seam**: it converts the opaque `[chartSeam]` typeclass input into a
constructed chart, built from the genuinely-geometric collar DATA — a homeomorphism presenting the
seam neighborhood as a welded-collar model. That is the honest reduction the mission asks for:
"parameterize what genuinely needs φ-input; construct everything else."

## The welded collar — geometry (document of record)

The seam `q(S)` is the glued attaching region. Near it, the carrier `W = B ⊔_φ Ha` is the union of the
two half-collars:

* the **B-side** half-collar — `φ(S)`'s neighborhood in `B = M × I`, whose collar direction is the
  canonical interval second factor (points `(m, t)` with `t ↗ 1`, glued at `t = 1`);
* the **Ha-side** half-collar — `S`'s radial neighborhood in `D⁵`, whose collar direction is the
  radial `1 − ‖v‖` of `DiskChartGeneric.diskCollarChart` (points at radius `‖v‖ ↗ 1`, glued at the
  boundary sphere).

The gluing identifies the two attaching faces; the welded collar coordinate `w` runs `w < 0`
(B-side interior) → `w = 0` (seam face) → `w > 0` (Ha-side interior). Over the interior of the
attaching region the weld **heals the boundary**: the seam face becomes an INTERIOR slice, so the
welded collar there is `(attaching-region chart) × (welded interval)` and charts into the INTERIOR of
the `KTModel` half-space (`t > 0`). This §-1/§-2 delivers exactly that interior model, concretely and
for free, and the §-3 datum names the collar homeomorphism as the genuine input.

## §-map
* **§1 — the generic seam-chart constructor** `chartSeamOfHomeo`: transport a `KTModel` chart across a
  homeomorphism onto any `KTModel`-charted model. The mechanism `chartSeam` is discharged by.
* **§2 — the concrete interior welded-collar model** `WeldedCollarModel A = A × (welded interval)`:
  charted on `KTModel` for FREE (product of the attaching base's `E⁴` charts and the welded interval's
  interior-landing half-space charts), with the welded interval = the open interior of `Icc(-1,1)`.
* **§3 — the seam-collar datum** `SeamCollarDatum`: bundles the open seam neighborhood, the attaching
  base `A` (a 4-manifold charted on `E⁴` — the tubular presentation of `φ(S)`), and the collar
  homeomorphism (the collar-neighborhood-theorem output — the genuine φ-input). From it `chartSeam` is
  CONSTRUCTED, retiring the raw typeclass.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryChartsConcrete

namespace SKEFTHawking.SurgeryFoundation

open Topology TopologicalSpace Set
open scoped Manifold

/-! ## §1. The generic seam-chart constructor — transport across a homeomorphism onto a model. -/

/-- **The generic seam-chart constructor.** Given a homeomorphism `e : SN ≃ₜ C` from the seam
neighborhood `SN` onto a type `C` that is itself charted on `KTModel`, transport the chart structure
back to `SN` (`chartedSpaceOfHomeo` then `ChartedSpace.comp`). This is the mechanism that discharges
the raw `chartSeam` typeclass input of `ktSurgeryChartDatum`: supply the collar model `C` + the
homeomorphism, and the `KTModel`-atlas on the seam collar is constructed. -/
@[reducible] noncomputable def chartSeamOfHomeo {C : Type*} [TopologicalSpace C]
    [ChartedSpace KTModel C] {SN : Type*} [TopologicalSpace SN] (e : SN ≃ₜ C) :
    ChartedSpace KTModel SN :=
  letI := chartedSpaceOfHomeo e
  ChartedSpace.comp KTModel C SN

/-! ## §2. The concrete interior welded-collar model. -/

/-- **The welded interval** `(-1, 1)` — the OPEN interior of the closed interval `Icc(-1,1)`, presented
as an `Opens` of the boundary-charted `↥(Set.Icc (-1) 1)`. Its inherited charts (`Opens.instChartedSpace`
over `instIccChartedSpace`) land in the INTERIOR of the half-space (`t > 0`, since `IccLeftChart` sends
an interior point `z` to `z − (−1) = z + 1 > 0`), so the welded interval is a boundaryless collar
direction — the healed seam coordinate. -/
def weldedInterval : Opens ↥(Set.Icc (-1 : ℝ) 1) :=
  ⟨{z | (-1 : ℝ) < z.val ∧ z.val < 1}, by
    have : {z : ↥(Set.Icc (-1 : ℝ) 1) | (-1 : ℝ) < z.val ∧ z.val < 1}
        = Subtype.val ⁻¹' Set.Ioo (-1 : ℝ) 1 := by
      ext z; simp [Set.mem_Ioo]
    rw [this]; exact isOpen_Ioo.preimage continuous_subtype_val⟩

/-- **A welded-collar model over an attaching base `A`** — `A × (welded interval)`. For `A` a 4-manifold
charted on `E⁴` (the tubular presentation of the attaching region `φ(S)`), this is the interior slice of
the welded collar. -/
@[reducible] def WeldedCollarModel (A : Type*) [TopologicalSpace A] : Type _ :=
  A × ↥weldedInterval

/-- **The welded-collar model is `KTModel`-charted, for free** — the product of the attaching base's
`E⁴` charts and the welded interval's interior-landing half-space charts. All charts land in the
interior of the `KTModel` half-space, so the model is a boundaryless collar slice. This is the "construct
everything else" of the seam-collar reduction; only the collar homeomorphism (§3) is a genuine input. -/
noncomputable instance instChartedSpaceWeldedCollarModel (A : Type*) [TopologicalSpace A]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) A] :
    ChartedSpace KTModel (WeldedCollarModel A) := by
  letI : Fact ((-1 : ℝ) < 1) := ⟨by norm_num⟩
  letI : ChartedSpace (EuclideanHalfSpace 1) ↥weldedInterval :=
    TopologicalSpace.Opens.instChartedSpace weldedInterval
  exact prodChartedSpace (EuclideanSpace ℝ (Fin 4)) A (EuclideanHalfSpace 1) ↥weldedInterval

/-! ## §3. The seam-collar datum — the genuine φ-input, parameterized. -/

/-- **The seam-collar datum** — the genuinely-geometric seam-collar input, parameterized. For a carrier
`W`, bundles: the open seam neighborhood `seamNbhd`; the attaching base `A` (a 4-manifold charted on
`E⁴` — the tubular-neighborhood presentation of `φ(S)`); and the collar homeomorphism
`hHomeo : ↥seamNbhd ≃ₜ WeldedCollarModel A` (the collar-neighborhood-theorem output). From it
`chartSeam` is CONSTRUCTED (`chartSeam`), discharging the raw `ChartedSpace KTModel ↥seamNbhd` typeclass
that `ktSurgeryChartDatum` previously demanded. -/
structure SeamCollarDatum (W : Type) [TopologicalSpace W] where
  /-- the open seam neighborhood in the carrier. -/
  seamNbhd : Opens W
  /-- the attaching-region base — a 4-manifold, the tubular presentation of `φ(S)`. -/
  A : Type
  [topA : TopologicalSpace A]
  [chartA : ChartedSpace (EuclideanSpace ℝ (Fin 4)) A]
  /-- **the collar homeomorphism** — the seam neighborhood presented as a welded-collar model. The
  collar-neighborhood-theorem output; the genuine φ-input. -/
  hHomeo : ↥seamNbhd ≃ₜ WeldedCollarModel A

namespace SeamCollarDatum

variable {W : Type} [TopologicalSpace W] (cd : SeamCollarDatum W)

attribute [instance] SeamCollarDatum.topA SeamCollarDatum.chartA

/-- **The constructed seam-collar chart** — `KTModel` charts on the seam neighborhood, built from the
collar datum by transporting the welded-collar model's charts across the collar homeomorphism (§1).
This is the constructed replacement for the raw `chartSeam` typeclass input. -/
@[reducible] noncomputable def chartSeam : ChartedSpace KTModel ↥cd.seamNbhd :=
  chartSeamOfHomeo cd.hHomeo

end SeamCollarDatum

/-! ## §4b. The boundary verdict — the welded interval is boundaryless (the weld heals the boundary).

The geometric content of the welded collar: over the interior of the attaching region the surgery weld
HEALS the boundary — the attaching face becomes an interior slice. Concretely, the welded interval
`(-1,1)` is boundaryless as a `(𝓡∂ 1)`-manifold: its only would-be boundary points are the two `Icc`
endpoints `⊥, ⊤`, which the open interior excludes. This is the "the weld heals the boundary" verdict. -/

/-- **The welded interval is boundaryless — the weld heals the boundary.** Every point of the welded
interval `(-1,1)` is an INTERIOR point of the half-space model: the only boundary points of `Icc(-1,1)`
are its endpoints `⊥, ⊤` (`boundary_Icc`), which the open interior excludes. So
`(𝓡∂ 1).boundary ↥weldedInterval = ∅`: the seam slice is interior — the geometric statement that the
surgery weld heals the attaching-face boundary. -/
theorem boundary_weldedInterval [Fact ((-1 : ℝ) < 1)] :
    (𝓡∂ 1).boundary ↥weldedInterval = ∅ := by
  haveI : Fact ((-1 : ℝ) ≤ 1) := ⟨by norm_num⟩
  rw [← ModelWithCorners.compl_interior, Set.compl_empty_iff, ModelWithCorners.interior_open,
    ← ModelWithCorners.compl_boundary, boundary_Icc]
  ext w
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_univ, iff_true, not_or]
  obtain ⟨h1, h2⟩ := w.2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at h1; simp at h1
  · rw [h] at h2; simp at h2

/-! ## §4. The b-row restated — the seam collar discharged by the collar datum.

The Wave-6 `ktSurgeryChartDatum` and Wave-6 `ambientTraceBordism_concrete` took the seam collar as a
raw `[chartSeam : ChartedSpace KTModel ↥seamNbhd]` typeclass input. Here we restate both with the seam
collar supplied by a `SeamCollarDatum` (the collar homeomorphism), so `chartSeam` is CONSTRUCTED, not
assumed. The residual for the seam collar is now exactly the named geometric datum {`A`, `hHomeo`} plus
the containment `hseam` — the honest φ-input, no opaque atlas. -/

open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTSurgeryTraceConsumers

/-- **The KT surgery-trace `SurgeryChartDatum` with the seam collar supplied by a collar datum.**
Identical to Wave-6's `ktSurgeryChartDatum` except the raw `[chartSeam]` typeclass is replaced by the
`SeamCollarDatum`'s constructed chart (`cd.chartSeam`). The seam collar is now discharged from named
geometric data. -/
noncomputable def ktSurgeryChartDatum_ofCollar
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (Ha : Type) [TopologicalSpace Ha] [CompactSpace Ha] [T2Space Ha]
    [ChartedSpace KTModel Ha]
    (S : Set Ha) (hS : IsClosed S) (φ : ↥S → M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment M Ha S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment M Ha S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd) :
    SurgeryChartDatum :=
  letI := cd.chartSeam
  ktSurgeryChartDatum M Ha S hS φ hφ hφinj cd.seamNbhd hseam

/-- **The concrete ambient trace bordism with the seam collar supplied by a collar datum.** The Wave-6
`ambientTraceBordism_concrete` with its raw `[chartSeam]` typeclass discharged by a `SeamCollarDatum`
(`cd`). The Pin⁺ surgery-trace `Bordism ((𝓡 4).prod (𝓡∂ 1)) s t` is now produced from: the attaching
data `S`/`φ`, the **collar datum** `cd` (the collar homeomorphism onto a welded-collar model — the seam
collar CONSTRUCTED, not assumed), the containment `hseam`, and the boundary identification
`e`/`he_inj`/`he_boundary`. The seam-collar residual is retired to the named φ-input. -/
noncomputable def ambientTraceBordism_concrete_ofCollar
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (Ha : Type) [TopologicalSpace Ha] [CompactSpace Ha] [T2Space Ha]
    [ChartedSpace KTModel Ha]
    (S : Set Ha) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment s.M Ha S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M Ha S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (e : s.M ⊕ t.M → (ktHandleAttachment s.M Ha S hS φ hφ hφinj).carrier)
    (he_cont : Continuous e)
    (he_inj : Function.Injective e)
    (he_boundary :
      letI := cd.chartSeam
      letI : ChartedSpace KTModel (ktHandleAttachment s.M Ha S hS φ hφ hφinj).carrier :=
        (ktSurgeryChartDatum s.M Ha S hS φ hφ hφinj cd.seamNbhd hseam).carrierChartedSpace
      Set.range e =
        ((𝓡 4).prod (𝓡∂ 1)).boundary (ktHandleAttachment s.M Ha S hS φ hφ hφinj).carrier) :
    Bordism ((𝓡 4).prod (𝓡∂ 1)) s t :=
  letI := cd.chartSeam
  ambientTraceBordism_concrete s t Ha S hS φ hφ hφinj cd.seamNbhd hseam e he_cont he_inj he_boundary

end SKEFTHawking.SurgeryFoundation
