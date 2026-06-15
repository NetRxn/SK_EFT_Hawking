/-
# Phase 5q.F — the regular-value theorem on a general manifold (the manifold-valued PD foundation)

The genuine geometric Smith map `[M] ↦ [PD(a) = N]` of the Smith long exact sequence (TY §3.4,
DDDKLPT Def 3.7) needs the Poincaré-dual submanifold `N = {section = 0}` to be a genuine
`SingularManifold` — a codim-1 submanifold of the *manifold* `M`, not just a level set in a model space.
The W5 placeholder (`[M] ↦ [emptySM]`) is forced precisely because the project's existing
`SmithRegularValueGeneral.levelSetIsManifold` lives on the model space `E` (`f : E → ℝ`), and Mathlib has
no regular-value / preimage-submanifold theorem for a general manifold (searched: `IsSmoothEmbedding` is a
property of a map, with `proof_wanted` stubs; no level-set manifold structure).

This module builds the manifold version, brick by brick, by composing `M`'s atlas charts with the
model-space construction (`SmithRegularValueGeneral`): in each chart `φ` around a point `p` of the zero
locus, `f ∘ φ.symm : E → ℝ` is the local representative, whose zero locus is a model-space submanifold
(`levelSetIsManifold`); the `M`-chart transitions are smooth (`M` is a manifold), so the composite charts
gives `N = {f = 0}` a `C^∞` codim-1 manifold structure, with a compact, boundaryless representative
packageable as `SingularManifold`.

Kernel-pure; no axioms beyond Mathlib's core.
-/
import Mathlib
import SKEFTHawking.SmithRegularValueGeneral

namespace SKEFTHawking.ManifoldRegularValue

open scoped Manifold
open SKEFTHawking.SmithRegularValueGeneral

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-! ## §1. The zero locus of `f : M → ℝ` on the manifold, and its point-set topology -/

/-- The **zero locus** of `f : M → ℝ` in the manifold `M` (the candidate Poincaré-dual submanifold). -/
def mZeroLocus (f : M → ℝ) : Set M := {x | f x = 0}

omit [TopologicalSpace M] [ChartedSpace H M] in
@[simp] theorem mem_mZeroLocus {f : M → ℝ} {x : M} : x ∈ mZeroLocus f ↔ f x = 0 := Iff.rfl

/-- The zero locus is **closed** — the preimage of `{0}` under the continuous `f`. -/
theorem isClosed_mZeroLocus {f : M → ℝ} (hf : Continuous f) : IsClosed (mZeroLocus f) :=
  isClosed_eq hf continuous_const

/-- In a **compact** manifold, the zero locus is compact (a closed subset of a compact space). -/
theorem isCompact_mZeroLocus [CompactSpace M] {f : M → ℝ} (hf : Continuous f) :
    IsCompact (mZeroLocus f) :=
  (isClosed_mZeroLocus hf).isCompact

/-- The zero locus, as a subtype, is a **compact space** when `M` is compact. -/
instance instCompactSpace_mZeroLocus [CompactSpace M] {f : M → ℝ} (hf : Continuous f) :
    CompactSpace (mZeroLocus f) :=
  isCompact_iff_compactSpace.mp (isCompact_mZeroLocus hf)

/-! ## §2. The local representative of `f` in an extended chart

In the extended chart `extChartAt I p` (a `PartialEquiv M E`), `f` is represented by
`localRep f p := f ∘ (extChartAt I p).symm : E → ℝ`. Smoothness of `f` on the manifold transfers to
`ContDiffOn` of `localRep` on the chart target, the link to the model-space construction
(`SmithRegularValueGeneral.levelSetIsManifold`, which works with `g : E → ℝ`). -/

variable [IsManifold I ⊤ M]

/-- The **local representative** of `f : M → ℝ` in the extended chart at `p`:
`localRep f p = f ∘ (extChartAt I p).symm : E → ℝ`. (The target chart on `ℝ` is the identity, so this
is exactly `writtenInExtChartAt 𝓘(ℝ,ℝ) I p f`.) -/
noncomputable def localRep (f : M → ℝ) (p : M) : E → ℝ := f ∘ (extChartAt I p).symm

omit [FiniteDimensional ℝ E] [IsManifold I ⊤ M] in
@[simp] theorem localRep_apply (f : M → ℝ) (p : M) (x : E) :
    localRep (I := I) f p x = f ((extChartAt I p).symm x) := rfl

omit [FiniteDimensional ℝ E] in
/-- The local representative is **`ContDiffOn`** on the chart target: `f` smooth on `M` composed with the
smooth chart-inverse `(extChartAt I p).symm` is `ContMDiffOn` as a model-space map `E → ℝ`, which is
`ContDiffOn` (`contMDiffOn_iff_contDiffOn`). The link from manifold smoothness of `f` to the model-space
regular-value machinery (`SmithRegularValueGeneral`). -/
theorem localRep_contDiffOn {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ⊤ f) (p : M) :
    ContDiffOn ℝ ⊤ (localRep (I := I) f p) (extChartAt I p).target :=
  contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm p))

/-! ## §3. The local representative is `ContDiffAt`/`HasStrictFDerivAt` at the chart point

At the chart image `extChartAt I p p`, the chart target is a neighborhood (boundaryless manifold,
`extChartAt_target_mem_nhds`), so the `ContDiffOn` of §2 upgrades to `ContDiffAt`, hence (for `C^⊤ ≥ C¹`)
a `HasStrictFDerivAt` — the hypothesis the model-space IFT chart (`SmithRegularValue`) consumes. -/

variable [I.Boundaryless]

omit [FiniteDimensional ℝ E] in
/-- The local representative is `ContDiffAt` at the chart point (target ∈ 𝓝, boundaryless). -/
theorem localRep_contDiffAt {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ⊤ f) (p : M) :
    ContDiffAt ℝ ⊤ (localRep (I := I) f p) (extChartAt I p p) :=
  (localRep_contDiffOn hf p).contDiffAt (extChartAt_target_mem_nhds (I := I) p)

omit [FiniteDimensional ℝ E] in
/-- The local representative has a **`HasStrictFDerivAt`** at the chart point, with derivative
`fderiv ℝ (localRep f p) (extChartAt I p p)` — the regular-value IFT input. -/
theorem localRep_hasStrictFDerivAt {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ⊤ f) (p : M) :
    HasStrictFDerivAt (localRep (I := I) f p)
      (fderiv ℝ (localRep (I := I) f p) (extChartAt I p p)) (extChartAt I p p) :=
  (localRep_contDiffAt hf p).hasStrictFDerivAt (by norm_num)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ⊤ M] in
/-- At a zero-locus point `p`, the local representative vanishes at the chart point:
`localRep f p (extChartAt I p p) = f p = 0` — the `h0` input the level-set chart needs. -/
theorem localRep_chartPt_eq_zero {f : M → ℝ} {p : M} (hp : p ∈ mZeroLocus f) :
    localRep (I := I) f p (extChartAt I p p) = 0 := by
  rw [localRep_apply, extChartAt_to_inv]
  exact hp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ⊤ M] in
/-- On the chart source, `localRep f p ∘ extChartAt I p = f`: so `extChartAt I p` maps
`mZeroLocus f ∩ source` into the model-space zero locus `zeroLocus (localRep f p)` — the
subtype correspondence the §5 chart is built on. -/
theorem localRep_extChartAt_eq {f : M → ℝ} {p q : M} (hq : q ∈ (extChartAt I p).source) :
    localRep (I := I) f p (extChartAt I p q) = f q := by
  rw [localRep_apply, (extChartAt I p).left_inv hq]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ⊤ M] in
/-- `extChartAt I p` carries a zero-locus point in its source into the model-space zero locus
`SmithRegularValue.zeroLocus (localRep f p)`. -/
theorem extChartAt_mem_zeroLocus {f : M → ℝ} {p q : M} (hq : q ∈ (extChartAt I p).source)
    (hqz : q ∈ mZeroLocus f) :
    extChartAt I p q ∈ SmithRegularValue.zeroLocus (localRep (I := I) f p) := by
  rw [SmithRegularValue.mem_zeroLocus, localRep_extChartAt_eq hq]
  exact hqz

/-! ## §5. The per-point Euclidean chart of the manifold level set, and the smooth-manifold structure

At each `p ∈ mZeroLocus f`, the local representative `localRep f p` is a `C^∞` real submersion at the
chart point `extChartAt I p p` (regular-value hypothesis `hsub`). Its model-space level-set chart
(`SmithRegularValue.levelSetChart`) is transported to a chart on `mZeroLocus f` by pre-composing with
the subtype-restricted extended chart `extChartAt I p` (which maps `mZeroLocus f ∩ source` to
`zeroLocus (localRep f p)`, by `extChartAt_mem_zeroLocus`) and post-composing with the fixed Euclidean
identification `kerEquivEuclidean`. The chart transitions are `C^∞`: they factor through the
model-space level-set transitions (`SmithRegularValueGeneral`) composed with the `M`-chart transitions
(`contDiffWithinAt_ext_coord_change`, `C^∞` as `M` is a smooth manifold) — giving `IsManifold`. -/

section Chart

open SmithRegularValue
open scoped Classical

variable (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ⊤ f)
  (hsub : ∀ p ∈ mZeroLocus f,
    LinearMap.range (fderiv ℝ (localRep (I := I) f p) (extChartAt I p p) : E →ₗ[ℝ] ℝ) = ⊤)

/-- The model-space level-set chart of the local representative `localRep f p` at the chart point
`extChartAt I p p` (a `C^∞` submersion there, by `hsub`), valued in the per-point kernel
`ker (fderiv (localRep f p) (extChartAt I p p))` — the local model of `mZeroLocus f` in the chart. -/
noncomputable def mLevelSetChart (p : mZeroLocus f) :
    OpenPartialHomeomorph (zeroLocus (localRep (I := I) f p.1))
      (kerModel (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))) :=
  levelSetChart (localRep (I := I) f p.1)
    (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (extChartAt I p.1 p.1)
    (localRep_hasStrictFDerivAt hf p.1) (hsub p.1 p.2) (localRep_chartPt_eq_zero p.2)

/-- The IFT chart `Φ : E ≈ ℝ × ker(fderiv …)` of the local representative `localRep f p` at the chart
point, with `(Φ x).1 = localRep f p x`. The model-space implicit-function chart underlying the level-set
chart, exposed so the manifold chart can thread the extended chart `extChartAt I p` through it. -/
noncomputable def mIftChart (p : mZeroLocus f) :
    OpenPartialHomeomorph E (ℝ × kerModel (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))) :=
  iftChart (localRep (I := I) f p.1)
    (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (extChartAt I p.1 p.1)
    (localRep_hasStrictFDerivAt hf p.1) (hsub p.1 p.2)

/-- The first IFT-chart coordinate is the local representative: `(mIftChart p x).1 = localRep f p x`. -/
theorem mIftChart_fst (p : mZeroLocus f) (x : E) :
    (mIftChart f hf hsub p x).1 = localRep (I := I) f p.1 x :=
  iftChart_fst (localRep (I := I) f p.1) _ _ _ _ x

/-- The IFT-chart inverse of a `{first = 0}` point lands in the zero locus of the local representative. -/
theorem mIftChart_symm_fst_eq_zero (p : mZeroLocus f)
    {k : kerModel (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))}
    (hk : (0, k) ∈ (mIftChart f hf hsub p).target) :
    localRep (I := I) f p.1 ((mIftChart f hf hsub p).symm (0, k)) = 0 :=
  iftChart_symm_fst_eq_zero (localRep (I := I) f p.1) _ _ _ _ hk

/-- **The extended chart `extChartAt I p`, restricted to a homeomorphism between the manifold zero
locus `mZeroLocus f` and the model-space zero locus `zeroLocus (localRep f p)`.** Source/target are the
extended-chart source/target (pulled back to the subtypes); `toFun = extChartAt I p`, `invFun =
(extChartAt I p).symm`. Pre-composing the model-space level-set chart (`mLevelSetChart`) with this via
`OpenPartialHomeomorph.trans` automatically keeps the composite within `extChartAt`'s domain (where the
local representative is `C^∞`), giving the manifold level-set chart. -/
noncomputable def extChartSubtype (p : mZeroLocus f) :
    OpenPartialHomeomorph (mZeroLocus f) (zeroLocus (localRep (I := I) f p.1)) where
  toFun := fun q =>
    if h : q.1 ∈ (extChartAt I p.1).source then ⟨extChartAt I p.1 q.1, extChartAt_mem_zeroLocus h q.2⟩
    else ⟨extChartAt I p.1 p.1, by rw [mem_zeroLocus]; exact localRep_chartPt_eq_zero p.2⟩
  invFun := fun y =>
    if h : y.1 ∈ (extChartAt I p.1).target then
      ⟨(extChartAt I p.1).symm y.1, by rw [mem_mZeroLocus, ← localRep_apply f p.1 y.1]; exact y.2⟩
    else p
  source := Subtype.val ⁻¹' (extChartAt I p.1).source
  target := Subtype.val ⁻¹' (extChartAt I p.1).target
  map_source' := by
    intro q hq
    rw [Set.mem_preimage] at hq ⊢
    simp only [dif_pos hq]
    exact (extChartAt I p.1).map_source hq
  map_target' := by
    intro y hy
    rw [Set.mem_preimage] at hy ⊢
    simp only [dif_pos hy]
    exact (extChartAt I p.1).map_target hy
  left_inv' := by
    intro q hq
    rw [Set.mem_preimage] at hq
    have hmap := (extChartAt I p.1).map_source hq
    simp only [dif_pos hq, dif_pos hmap]
    exact Subtype.ext ((extChartAt I p.1).left_inv hq)
  right_inv' := by
    intro y hy
    rw [Set.mem_preimage] at hy
    have hmap := (extChartAt I p.1).map_target hy
    simp only [dif_pos hy, dif_pos hmap]
    exact Subtype.ext ((extChartAt I p.1).right_inv hy)
  open_source := (isOpen_extChartAt_source p.1).preimage continuous_subtype_val
  open_target := (isOpen_extChartAt_target p.1).preimage continuous_subtype_val
  continuousOn_toFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr ((continuousOn_extChartAt p.1).comp
      continuous_subtype_val.continuousOn (fun q hq => hq)) ?_
    intro q hq
    rw [Set.mem_preimage] at hq
    simp only [Function.comp_apply, dif_pos hq]
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr ((continuousOn_extChartAt_symm p.1).comp
      continuous_subtype_val.continuousOn (fun y hy => hy)) ?_
    intro y hy
    rw [Set.mem_preimage] at hy
    simp only [Function.comp_apply, dif_pos hy]

/-- **The per-point level-set chart of the manifold zero locus, valued in the kernel model.** The
model-space level-set chart of `localRep f p` (`mLevelSetChart`), pre-composed with the
subtype-restricted extended chart (`extChartSubtype`): the composite carries `mZeroLocus f` (near `p`)
to `ker (fderiv (localRep f p) (extChartAt I p p))`. `OpenPartialHomeomorph.trans` discharges
source/target/inverse/continuity and keeps the composite within `extChartAt`'s domain. -/
noncomputable def mLevelChartKer (p : mZeroLocus f) :
    OpenPartialHomeomorph (mZeroLocus f)
      (kerModel (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))) :=
  (extChartSubtype f p).trans (mLevelSetChart f hf hsub p)

end Chart

end SKEFTHawking.ManifoldRegularValue
