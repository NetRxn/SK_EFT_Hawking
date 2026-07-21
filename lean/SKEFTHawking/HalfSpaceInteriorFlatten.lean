/-
# Phase 5q.H — K6′b Leg 10: FLATTENING the half-space model on its interior

Every chart family of the Kummer weld's two *interior* pieces (`ResE ∖ ∂E` on the E side,
`Q ∖ ∂Q` on the Q side) is inherited from a manifold-**with-boundary** atlas modelled on
`Model = ModelProd 𝓔³ (EuclideanHalfSpace 1)`. The weld's boundaryless target model is the untagged
product `𝓔³ × ℝ` (the one `ManifoldModelTransport.prodRealEquivEuclidean` carries to `𝓡 4`). This
module supplies the missing **interior-of-half-space ≅ ℝ** step that converts the former into the
latter:

* `flatten : OpenPartialHomeomorph Model (𝓔³ × ℝ)` — source the strictly-positive-height region
  `interiorRegion = {q | 0 < height q}`, target `{p | 0 < p.2}`, acting by `(a, h) ↦ (a, h₀)`.
  Junk-clamped off-source by `max · 0`, so the inverse is total.
* `flatChart c := c.trans flatten` — the flattened form of a half-space chart `c`, whose source is
  exactly the part of `c.source` that `c` sends into the half-space interior.
* the **positive-height propagation toolkit** (`PosHt`): the property "this chart sends its whole
  source into the half-space interior", which propagates through `trans` (from the outer factor),
  through `lift_openEmbedding`, and out of any chart whose target is already inside
  `interiorRegion`. That toolkit is what lets each concrete interior chart family be flattened
  without re-deriving its coordinate formula.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib

namespace SKEFTHawking.HalfSpaceInteriorFlatten

open Set Topology
open scoped Manifold

noncomputable section

/-! ## §1. The half-space model, its height coordinate, and its interior region -/

/-- The half-space boundary model `ModelProd 𝓔³ (EuclideanHalfSpace 1)` shared by
`KummerBoundaryChart.Model`, `KummerResolutionPieceBoundary.Model` and `KummerShellChart.Model`. -/
abbrev HModel : Type := ModelProd (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 1)

/-- The boundaryless target model — the **untagged** product `𝓔³ × ℝ`. Untagged is load-bearing:
`ModelProd` is a semireducible type tag, and the tagged form blocks the ordinary `NormedSpace`
instance resolution that `ManifoldModelTransport.isManifold_R4_of_prodReal` needs. -/
abbrev FModel : Type := EuclideanSpace ℝ (Fin 3) × ℝ

/-- **The half-space height coordinate** — the single real coordinate of the `EuclideanHalfSpace 1`
factor. The manifold boundary is `height = 0`; the interior is `height > 0`. -/
def height (q : HModel) : ℝ := q.2.val.ofLp 0

@[simp] theorem height_mk (a : EuclideanSpace ℝ (Fin 3)) (h : EuclideanHalfSpace 1) :
    height (a, h) = h.val.ofLp 0 := rfl

theorem height_nonneg (q : HModel) : 0 ≤ height q := q.2.2

theorem continuous_height : Continuous height :=
  (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
    (continuous_subtype_val.comp continuous_snd)

/-- **The interior region of the half-space model** — the strictly-positive-height part. -/
def interiorRegion : Set HModel := {q : HModel | 0 < height q}

theorem isOpen_interiorRegion : IsOpen interiorRegion :=
  isOpen_lt continuous_const continuous_height

/-! ## §2. The flattening chart -/

/-- Rebuilding a `EuclideanHalfSpace 1` point from a nonnegative real. -/
def ofHeight (t : ℝ) : EuclideanHalfSpace 1 :=
  ⟨WithLp.toLp 2 (fun _ : Fin 1 => max t 0), by simp⟩

@[simp] theorem ofHeight_coord (t : ℝ) : (ofHeight t).val.ofLp 0 = max t 0 := by
  simp [ofHeight]

/-- On `𝓔¹`, reassembling the single coordinate recovers the vector (the local copy of
`DiskChartGeneric.toLp_ofLp_fin_one`, kept here so this module stays import-light). -/
theorem toLp_ofLp_one (x : EuclideanSpace ℝ (Fin 1)) :
    WithLp.toLp 2 (fun _ : Fin 1 => x.ofLp 0) = x := by
  apply WithLp.ofLp_injective
  funext i
  rw [Subsingleton.elim i 0]

theorem continuous_ofHeight : Continuous ofHeight := by
  apply Continuous.subtype_mk
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_id.max continuous_const)

/-- **THE INTERIOR-OF-HALF-SPACE FLATTENING** `Model → 𝓔³ × ℝ`, an `OpenPartialHomeomorph` with
source the interior region `{0 < height}` and target `{p | 0 < p.2}`: keep the `𝓔³` factor, replace
the `EuclideanHalfSpace 1` factor by its single real coordinate. Junk-clamped off-source
(`max · 0`), so `invFun` is total and continuous everywhere. -/
def flatten : OpenPartialHomeomorph HModel FModel where
  source := interiorRegion
  target := {p : FModel | 0 < p.2}
  toFun q := (q.1, height q)
  invFun p := (p.1, ofHeight p.2)
  map_source' q hq := hq
  map_target' p hp := by
    show (0 : ℝ) < height (p.1, ofHeight p.2)
    rw [height_mk, ofHeight_coord, max_eq_left (le_of_lt hp)]
    exact hp
  left_inv' q hq := by
    refine Prod.ext rfl ?_
    apply Subtype.ext
    show WithLp.toLp 2 (fun _ : Fin 1 => max (height q) 0) = q.2.val
    rw [max_eq_left (le_of_lt hq)]
    exact toLp_ofLp_one _
  right_inv' p hp := by
    refine Prod.ext rfl ?_
    show height (p.1, ofHeight p.2) = p.2
    rw [height_mk, ofHeight_coord, max_eq_left (le_of_lt hp)]
  open_source := isOpen_interiorRegion
  open_target := isOpen_lt continuous_const continuous_snd
  continuousOn_toFun := (continuous_fst.prodMk continuous_height).continuousOn
  continuousOn_invFun := (continuous_fst.prodMk (continuous_ofHeight.comp continuous_snd)).continuousOn

@[simp] theorem flatten_source : flatten.source = interiorRegion := rfl

@[simp] theorem flatten_apply (q : HModel) : flatten q = (q.1, height q) := rfl

/-! ## §3. Positive height on a chart's source — the propagation toolkit -/

variable {M : Type*} [TopologicalSpace M]

/-- **The positive-height property of a half-space chart**: the chart sends its whole source into
the interior of the half-space model. This is the hypothesis `flatChart` needs in order to keep the
chart's source intact; it is what distinguishes an *interior* chart family from a collar family. -/
def PosHt (c : OpenPartialHomeomorph M HModel) : Prop := ∀ x ∈ c.source, 0 < height (c x)

/-- A chart whose target already lies in the interior region has positive height on its source. -/
theorem posHt_of_target_subset {c : OpenPartialHomeomorph M HModel}
    (h : c.target ⊆ interiorRegion) : PosHt c := fun _ hx => h (c.map_source hx)

/-- Positive height propagates through `trans` from the **outer** factor. -/
theorem posHt_trans {N : Type*} [TopologicalSpace N] (e : OpenPartialHomeomorph M N)
    {c : OpenPartialHomeomorph N HModel} (hc : PosHt c) : PosHt (e.trans c) := by
  intro x hx
  rw [OpenPartialHomeomorph.trans_source] at hx
  exact hc (e x) hx.2

/-- Positive height propagates through `lift_openEmbedding` along an open embedding. -/
theorem posHt_lift {N : Type*} [TopologicalSpace N] {f : M → N}
    (hf : IsOpenEmbedding f) {c : OpenPartialHomeomorph M HModel} (hc : PosHt c) :
    PosHt (c.lift_openEmbedding hf) := by
  intro y hy
  rw [OpenPartialHomeomorph.lift_openEmbedding_source] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [c.lift_openEmbedding_apply hf]
  exact hc x hx

/-! ## §4. Flattening a half-space chart -/

/-- **The flattened chart** — a half-space chart post-composed with `flatten`. Its source is the
part of `c.source` that `c` maps into the half-space interior; under `PosHt c` that is all of
`c.source` (`flatChart_source_of_posHt`). -/
def flatChart (c : OpenPartialHomeomorph M HModel) : OpenPartialHomeomorph M FModel :=
  c.trans flatten

@[simp] theorem flatChart_apply {c : OpenPartialHomeomorph M HModel} (y : M) :
    flatChart c y = ((c y).1, height (c y)) := rfl

/-- Membership in the flattened chart's source: be in the original source **and** land in the
half-space interior. -/
theorem mem_flatChart_source {c : OpenPartialHomeomorph M HModel} {x : M} (hx : x ∈ c.source)
    (hpos : 0 < height (c x)) : x ∈ (flatChart c).source := by
  rw [flatChart, OpenPartialHomeomorph.trans_source]
  exact ⟨hx, hpos⟩

/-- **Under `PosHt`, flattening preserves the source exactly.** -/
theorem flatChart_source_of_posHt {c : OpenPartialHomeomorph M HModel} (hc : PosHt c) :
    (flatChart c).source = c.source := by
  refine Set.Subset.antisymm ?_ (fun x hx => mem_flatChart_source hx (hc x hx))
  rw [flatChart, OpenPartialHomeomorph.trans_source]
  exact fun _ hx => hx.1

end

end SKEFTHawking.HalfSpaceInteriorFlatten
