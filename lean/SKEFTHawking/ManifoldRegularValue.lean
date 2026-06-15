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

/-! ### Smoothness of the per-point chart transitions

The model-space level-set chart `mLevelSetChart` (of the *local* representative `localRep f p`, which is
only `ContDiffOn` the extended chart target — not a global submersion) has a `C^∞` inverse only on the
**regular set**: chart points whose IFT-preimage lies in `extChartAt`'s target (where `localRep` is `C^∞`)
and has an invertible forward derivative. We adapt `SmithRegularValueGeneral`'s machinery to this
`ContDiffAt`-on-target setting. -/

/-- The forward IFT chart of the local representative is `ContDiffAt` at each point of the extended
chart target (where `localRep f p` is `C^∞`): its first coordinate is `localRep f p` (`ContDiffAt`
there), its second is the affine `chartProj (· - a)`. -/
theorem mIftChart_contDiffAt (p : mZeroLocus f) {x : E} (hx : x ∈ (extChartAt I p.1).target) :
    ContDiffAt ℝ ⊤ (mIftChart f hf hsub p) x := by
  have hloc : ContDiffAt ℝ ⊤ (localRep (I := I) f p.1) x :=
    (localRep_contDiffOn hf p.1).contDiffAt ((isOpen_extChartAt_target p.1).mem_nhds hx)
  have hcoe : (⇑(mIftChart f hf hsub p)) = fun y => (localRep (I := I) f p.1 y,
      chartProj (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (hsub p.1 p.2)
        (y - extChartAt I p.1 p.1)) :=
    iftChart_coe (localRep (I := I) f p.1) _ _ (localRep_hasStrictFDerivAt hf p.1) (hsub p.1 p.2)
  rw [hcoe]
  exact hloc.prodMk
    (((chartProj _ (hsub p.1 p.2)).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt)

/-- **The IFT chart inverse of the local representative is `ContDiffAt`** at a chart point `y` whose
preimage `(mIftChart p).symm y` lies in `extChartAt`'s target (so `localRep f p` is `C^∞` there) and
where the forward derivative `(fderiv (localRep f p) ·).prod P` is invertible. Adapts
`SmithRegularValueGeneral.iftChart_symm_contDiffAt` to the `ContDiffAt`-on-target setting. -/
theorem mIftChart_symm_contDiffAt (p : mZeroLocus f)
    {y : ℝ × kerModel (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))}
    (hy : y ∈ (mIftChart f hf hsub p).target)
    (hpre : (mIftChart f hf hsub p).symm y ∈ (extChartAt I p.1).target)
    (hinv : ((fderiv ℝ (localRep (I := I) f p.1) ((mIftChart f hf hsub p).symm y)).prod
      (chartProj (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (hsub p.1 p.2))).IsInvertible) :
    ContDiffAt ℝ ⊤ (mIftChart f hf hsub p).symm y := by
  obtain ⟨g, hg⟩ := hinv
  refine (mIftChart f hf hsub p).contDiffAt_symm (f₀' := g) hy ?_ ?_
  · have hd : HasFDerivAt (⇑(mIftChart f hf hsub p))
        ((fderiv ℝ (localRep (I := I) f p.1) ((mIftChart f hf hsub p).symm y)).prod
          (chartProj (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (hsub p.1 p.2)))
        ((mIftChart f hf hsub p).symm y) :=
      iftChart_hasFDerivAt (localRep (I := I) f p.1) _ _ (localRep_hasStrictFDerivAt hf p.1)
        (hsub p.1 p.2) (((localRep_contDiffOn hf p.1).contDiffAt
          ((isOpen_extChartAt_target p.1).mem_nhds hpre)).differentiableAt (by norm_num))
    rw [← hg] at hd
    exact hd
  · exact mIftChart_contDiffAt f hf hsub p hpre

include hf in
/-- The derivative-with-projection map `x ↦ (fderiv (localRep f p) x).prod P` is `ContinuousOn` the
extended chart target (where `localRep f p` is `C^∞`, so its `fderiv` is continuous). -/
theorem mContinuousOn_fderiv_prod (p : mZeroLocus f) :
    ContinuousOn (fun x => (fderiv ℝ (localRep (I := I) f p.1) x).prod
      (chartProj (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (hsub p.1 p.2)))
      (extChartAt I p.1).target := by
  have hd : ContinuousOn (fderiv ℝ (localRep (I := I) f p.1)) (extChartAt I p.1).target :=
    (localRep_contDiffOn hf p.1).continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target p.1)
      (by norm_num)
  have hcomp : ContinuousOn (fun x => (ContinuousLinearMap.prodL ℝ)
      (fderiv ℝ (localRep (I := I) f p.1) x,
        chartProj (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (hsub p.1 p.2)))
      (extChartAt I p.1).target :=
    (ContinuousLinearMap.prodL ℝ).continuous.comp_continuousOn (hd.prodMk continuousOn_const)
  simpa only [ContinuousLinearMap.prodL_apply] using hcomp

/-- The **regular target set** of the local-rep chart at `p` (in kernel coordinates): chart points `(0,k)`
whose IFT-preimage lies in `extChartAt`'s target (so `localRep f p` is `C^∞` there) and has invertible
forward derivative — the open set on which the inverse chart is `C^∞`. Adds the `target`-membership
condition to `SmithRegularValueGeneral.regularKerTarget`. -/
def mRegularKerTarget (p : mZeroLocus f) :
    Set (kerModel (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))) :=
  {k | (0, k) ∈ (mIftChart f hf hsub p).target ∧
    (mIftChart f hf hsub p).symm (0, k) ∈ (extChartAt I p.1).target ∧
    ((fderiv ℝ (localRep (I := I) f p.1) ((mIftChart f hf hsub p).symm (0, k))).prod
      (chartProj (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (hsub p.1 p.2))).IsInvertible}

theorem isOpen_mRegularKerTarget (p : mZeroLocus f) : IsOpen (mRegularKerTarget f hf hsub p) := by
  have hcont0 : Continuous (fun k : kerModel (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) =>
      ((0 : ℝ), k)) := continuous_const.prodMk continuous_id
  set A := (fun k : kerModel (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) => ((0 : ℝ), k)) ⁻¹'
    (mIftChart f hf hsub p).target with hA
  have hAopen : IsOpen A := (mIftChart f hf hsub p).open_target.preimage hcont0
  have hscont : ContinuousOn (fun k => (mIftChart f hf hsub p).symm (0, k)) A :=
    (mIftChart f hf hsub p).continuousOn_symm.comp hcont0.continuousOn (fun _ hk => hk)
  have hTopen : IsOpen ((extChartAt I p.1).target ∩
      {x : E | ((fderiv ℝ (localRep (I := I) f p.1) x).prod
        (chartProj (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (hsub p.1 p.2))).IsInvertible}) :=
    (mContinuousOn_fderiv_prod f hf hsub p).isOpen_inter_preimage (isOpen_extChartAt_target p.1)
      (isOpen_isInvertible _)
  have heq : mRegularKerTarget f hf hsub p = A ∩ (fun k => (mIftChart f hf hsub p).symm (0, k)) ⁻¹'
      ((extChartAt I p.1).target ∩
        {x : E | ((fderiv ℝ (localRep (I := I) f p.1) x).prod
          (chartProj (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (hsub p.1 p.2))).IsInvertible}) := by
    ext k
    simp only [mRegularKerTarget, hA, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  rw [heq]
  exact hscont.isOpen_inter_preimage hAopen hTopen

/-- **The inverse local-rep chart is `C^∞` on the regular set.** In kernel coordinates,
`k ↦ (mIftChart p).symm (0, k)` is `ContDiffOn ℝ ⊤` on `mRegularKerTarget`. The load-bearing
inverse-smoothness for the chart transitions. -/
theorem mContDiffOn_iftChart_symm (p : mZeroLocus f) :
    ContDiffOn ℝ ⊤ (fun k => (mIftChart f hf hsub p).symm (0, k)) (mRegularKerTarget f hf hsub p) := by
  rw [(isOpen_mRegularKerTarget f hf hsub p).contDiffOn_iff]
  intro k hk
  obtain ⟨hkt, hpre, hinv⟩ := hk
  exact (mIftChart_symm_contDiffAt f hf hsub p hkt hpre hinv).comp k
    (contDiffAt_const.prodMk contDiffAt_id)

/-- The **regular-set restriction** of the per-point kernel chart: its source intersected with the
(open) preimage of the regular kernel target, where the inverse chart is `C^∞` (so the chart
transitions will be `C^∞`). -/
noncomputable def mLevelChartKerR (p : mZeroLocus f) :
    OpenPartialHomeomorph (mZeroLocus f)
      (kerModel (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))) :=
  (mLevelChartKer f hf hsub p).restrOpen
    ((mLevelChartKer f hf hsub p).source ∩
      ⇑(mLevelChartKer f hf hsub p) ⁻¹' (mRegularKerTarget f hf hsub p))
    ((mLevelChartKer f hf hsub p).continuousOn_toFun.isOpen_inter_preimage
      (mLevelChartKer f hf hsub p).open_source (isOpen_mRegularKerTarget f hf hsub p))

/-- **The per-point chart of the manifold level set, valued in the fixed Euclidean model**
`EuclideanSpace ℝ (Fin (finrank E - 1))`: the regular-restricted kernel chart composed with the
continuous-linear identification `kerEquivEuclidean : ker (fderiv (localRep f p) …) ≃L euclideanModel E`. -/
noncomputable def mLevelChartE (p : mZeroLocus f) :
    OpenPartialHomeomorph (mZeroLocus f) (euclideanModel E) :=
  (mLevelChartKerR f hf hsub p).transHomeomorph
    (kerEquivEuclidean (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))
      (hsub p.1 p.2)).toHomeomorph

/-- The IFT chart of the local representative sends its base point `extChartAt I p p` to `(0, 0)`
(the first coordinate is `localRep f p (extChartAt I p p) = 0`, the second is `0` by the
implicit-function self-identity). -/
theorem mIftChart_self (p : mZeroLocus f) :
    mIftChart f hf hsub p (extChartAt I p.1 p.1) = (0, 0) := by
  have h := (localRep_hasStrictFDerivAt hf p.1).implicitToOpenPartialHomeomorph_self (hsub p.1 p.2)
  rw [show mIftChart f hf hsub p (extChartAt I p.1 p.1)
      = (localRep_hasStrictFDerivAt hf p.1).implicitToOpenPartialHomeomorph (localRep (I := I) f p.1)
        (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (hsub p.1 p.2)
        (extChartAt I p.1 p.1) from rfl, h, localRep_chartPt_eq_zero p.2]

/-- The base point `extChartAt I p p` lies in the source of the IFT chart of `localRep f p`. -/
theorem mem_mIftChart_source_self (p : mZeroLocus f) :
    extChartAt I p.1 p.1 ∈ (mIftChart f hf hsub p).source :=
  mem_iftChart_source (localRep (I := I) f p.1) _ _ (localRep_hasStrictFDerivAt hf p.1)
    (hsub p.1 p.2)

/-- The IFT-chart inverse sends `(0, 0)` back to the base point `extChartAt I p p`. -/
theorem mIftChart_symm_zero (p : mZeroLocus f) :
    (mIftChart f hf hsub p).symm (0, 0) = extChartAt I p.1 p.1 := by
  rw [← mIftChart_self f hf hsub p,
    (mIftChart f hf hsub p).left_inv (mem_mIftChart_source_self f hf hsub p)]

/-- The kernel origin `0` lies in the regular target set: the base point is regular. -/
theorem zero_mem_mRegularKerTarget (p : mZeroLocus f) :
    (0 : kerModel (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))) ∈
      mRegularKerTarget f hf hsub p := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← mIftChart_self f hf hsub p]
    exact (mIftChart f hf hsub p).map_source (mem_mIftChart_source_self f hf hsub p)
  · rw [mIftChart_symm_zero f hf hsub p]
    exact (extChartAt I p.1).map_source (mem_extChartAt_source p.1)
  · rw [mIftChart_symm_zero f hf hsub p]
    exact prod_chartProj_isInvertible _ (hsub p.1 p.2)

omit [FiniteDimensional ℝ E] [IsManifold I ⊤ M] in
/-- On the extended-chart source, the subtype-restricted extended chart is `extChartAt I p`. -/
theorem extChartSubtype_apply_of_mem (p : mZeroLocus f) {q : mZeroLocus f}
    (hq : q.1 ∈ (extChartAt I p.1).source) :
    (extChartSubtype f p) q = ⟨extChartAt I p.1 q.1, extChartAt_mem_zeroLocus hq q.2⟩ := by
  apply Subtype.ext
  show (dite (q.1 ∈ (extChartAt I p.1).source) _ _ : zeroLocus (localRep (I := I) f p.1)).1 =
    extChartAt I p.1 q.1
  rw [dif_pos hq]

/-- The manifold level-set chart sends the base point `p` to the kernel origin `0`. -/
theorem mLevelChartKer_self (p : mZeroLocus f) : (mLevelChartKer f hf hsub p) p = 0 := by
  rw [mLevelChartKer, OpenPartialHomeomorph.trans_apply,
    extChartSubtype_apply_of_mem f p (mem_extChartAt_source p.1)]
  show (mIftChart f hf hsub p (extChartAt I p.1 p.1)).2 = 0
  rw [mIftChart_self]

/-- The base point `p` lies in the source of the (unrestricted) kernel chart. -/
theorem mem_mLevelChartKer_source_self (p : mZeroLocus f) :
    p ∈ (mLevelChartKer f hf hsub p).source := by
  rw [mLevelChartKer, OpenPartialHomeomorph.trans_source]
  refine ⟨mem_extChartAt_source p.1, ?_⟩
  rw [Set.mem_preimage, extChartSubtype_apply_of_mem f p (mem_extChartAt_source p.1)]
  exact mem_mIftChart_source_self f hf hsub p

/-- **Every point of the manifold level set lies in the source of its own Euclidean chart** — the
charted-space covering condition. -/
theorem mem_mLevelChartE_source (p : mZeroLocus f) : p ∈ (mLevelChartE f hf hsub p).source := by
  rw [mLevelChartE, OpenPartialHomeomorph.transHomeomorph_source, mLevelChartKerR,
    OpenPartialHomeomorph.restrOpen_source]
  refine ⟨mem_mLevelChartKer_source_self f hf hsub p,
    mem_mLevelChartKer_source_self f hf hsub p, ?_⟩
  rw [Set.mem_preimage, mLevelChartKer_self f hf hsub p]
  exact zero_mem_mRegularKerTarget f hf hsub p

/-- **The level set of a `C^∞` real submersion `f : M → ℝ` on a (boundaryless) manifold is a charted
space over the fixed Euclidean model** `EuclideanSpace ℝ (Fin (finrank E - 1))`. -/
@[reducible] noncomputable def mLevelSetChartedSpace :
    ChartedSpace (euclideanModel E) (mZeroLocus f) where
  atlas := Set.range (mLevelChartE f hf hsub)
  chartAt p := mLevelChartE f hf hsub p
  mem_chart_source p := mem_mLevelChartE_source f hf hsub p
  chart_mem_atlas p := Set.mem_range_self p

/-! ### The chart transitions are `C^∞` (the structure-groupoid compatibility)

The transition between the charts at `p` and `q`, in kernel coordinates, is the composite
`(forward q-chart) ∘ (M-coordinate change `extChartAt q ∘ extChartAt p⁻¹`) ∘ (inverse p-chart)`, each
`C^∞`: the inverse p-chart on `mRegularKerTarget` (`mContDiffOn_iftChart_symm`), the M-coordinate
change by `contDiffOn_ext_coord_change`, the forward q-chart `(mIftChart q ·).2` affine. -/

/-- The forward q-chart second coordinate `w ↦ (mIftChart q w).2 = P_q (w - a_q)` is globally `C^∞`. -/
theorem mContDiff_forwardChart (q : mZeroLocus f) :
    ContDiff ℝ ⊤ (fun w => (mIftChart f hf hsub q w).2) := by
  have : (fun w => (mIftChart f hf hsub q w).2) =
      fun w => chartProj (fderiv ℝ (localRep (I := I) f q.1) (extChartAt I q.1 q.1)) (hsub q.1 q.2)
        (w - extChartAt I q.1 q.1) := by
    funext w; rw [show mIftChart f hf hsub q w = iftChart (localRep (I := I) f q.1) _ _
      (localRep_hasStrictFDerivAt hf q.1) (hsub q.1 q.2) w from rfl, iftChart_eq]
  rw [this]
  exact (chartProj _ (hsub q.1 q.2)).contDiff.comp (contDiff_id.sub contDiff_const)

/-- **The chart transition in kernel coordinates is `C^∞`** on the regular set (intersected with the
preimage of the M-coordinate-change domain): the composite of the `C^∞` inverse p-chart, the `C^∞`
M-coordinate change, and the `C^∞` forward q-chart. -/
theorem mContDiffOn_transition (p q : mZeroLocus f) :
    ContDiffOn ℝ ⊤
      (fun k => (mIftChart f hf hsub q
        (extChartAt I q.1 ((extChartAt I p.1).symm ((mIftChart f hf hsub p).symm (0, k))))).2)
      (mRegularKerTarget f hf hsub p ∩ (fun k => (mIftChart f hf hsub p).symm (0, k)) ⁻¹'
        ((extChartAt I p.1).symm.trans (extChartAt I q.1)).source) := by
  have hg2 : ContDiffOn ℝ ⊤ (fun k => (mIftChart f hf hsub p).symm (0, k))
      (mRegularKerTarget f hf hsub p ∩ (fun k => (mIftChart f hf hsub p).symm (0, k)) ⁻¹'
        ((extChartAt I p.1).symm.trans (extChartAt I q.1)).source) :=
    (mContDiffOn_iftChart_symm f hf hsub p).mono Set.inter_subset_left
  have hmaps : Set.MapsTo (fun k => (mIftChart f hf hsub p).symm (0, k))
      (mRegularKerTarget f hf hsub p ∩ (fun k => (mIftChart f hf hsub p).symm (0, k)) ⁻¹'
        ((extChartAt I p.1).symm.trans (extChartAt I q.1)).source)
      ((extChartAt I p.1).symm.trans (extChartAt I q.1)).source := fun k hk => hk.2
  have hg3 := (contDiffOn_ext_coord_change (I := I) q.1 p.1).comp hg2 hmaps
  exact (mContDiff_forwardChart f hf hsub q).comp_contDiffOn hg3

/-- **The chart transition in Euclidean coordinates is `C^∞`** — the kernel transition conjugated by
the two Euclidean identifications `kerEquivEuclidean`. -/
theorem mContDiffOn_transitionE (p q : mZeroLocus f) :
    ContDiffOn ℝ ⊤
      (fun v : euclideanModel E =>
        (kerEquivEuclidean (fderiv ℝ (localRep (I := I) f q.1) (extChartAt I q.1 q.1)) (hsub q.1 q.2))
          ((mIftChart f hf hsub q (extChartAt I q.1 ((extChartAt I p.1).symm
            ((mIftChart f hf hsub p).symm (0,
              (kerEquivEuclidean (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))
                (hsub p.1 p.2)).symm v))))).2))
      ((kerEquivEuclidean (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))
          (hsub p.1 p.2)).symm ⁻¹'
        (mRegularKerTarget f hf hsub p ∩ (fun k => (mIftChart f hf hsub p).symm (0, k)) ⁻¹'
          ((extChartAt I p.1).symm.trans (extChartAt I q.1)).source)) := by
  have hp : ContDiff ℝ ⊤ ⇑(kerEquivEuclidean (fderiv ℝ (localRep (I := I) f p.1)
      (extChartAt I p.1 p.1)) (hsub p.1 p.2)).symm :=
    (kerEquivEuclidean (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))
      (hsub p.1 p.2)).symm.contDiff
  have hq : ContDiff ℝ ⊤ ⇑(kerEquivEuclidean (fderiv ℝ (localRep (I := I) f q.1)
      (extChartAt I q.1 q.1)) (hsub q.1 q.2)) :=
    (kerEquivEuclidean (fderiv ℝ (localRep (I := I) f q.1) (extChartAt I q.1 q.1))
      (hsub q.1 q.2)).contDiff
  exact (hq.comp_contDiffOn (mContDiffOn_transition f hf hsub p q)).comp hp.contDiffOn
    (Set.mapsTo_preimage _ _)

/-- The Euclidean chart at `q`, on a point in the extended-chart source, reads
`x ↦ e_q ((mIftChart q (extChartAt q x)).2)`. -/
theorem mLevelChartE_apply (q x : mZeroLocus f) (hx : x.1 ∈ (extChartAt I q.1).source) :
    (mLevelChartE f hf hsub q) x =
      (kerEquivEuclidean (fderiv ℝ (localRep (I := I) f q.1) (extChartAt I q.1 q.1)) (hsub q.1 q.2))
        ((mIftChart f hf hsub q (extChartAt I q.1 x.1)).2) := by
  rw [mLevelChartE, OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
    ContinuousLinearEquiv.coe_toHomeomorph]
  congr 1
  rw [show (mLevelChartKerR f hf hsub q) x = (mLevelChartKer f hf hsub q) x from rfl,
    mLevelChartKer, OpenPartialHomeomorph.trans_apply, extChartSubtype_apply_of_mem f q hx]
  rfl

/-- The inverse model-space level-set chart, on a kernel point in its target, is the IFT-chart
inverse: `(mLevelSetChart p).symm k = (mIftChart p).symm (0, k)` in ambient coordinates. -/
theorem mLevelSetChart_symm_apply (p : mZeroLocus f)
    {k : kerModel (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))}
    (hk : (0, k) ∈ (mIftChart f hf hsub p).target) :
    ((mLevelSetChart f hf hsub p).symm k : E) = (mIftChart f hf hsub p).symm (0, k) := by
  have hk' : (0, k) ∈ (iftChart (localRep (I := I) f p.1)
      (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1)) (extChartAt I p.1 p.1)
      (localRep_hasStrictFDerivAt hf p.1) (hsub p.1 p.2)).target := hk
  rw [mLevelSetChart, levelSetChart]
  simp only [OpenPartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk, dif_pos hk']
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ⊤ M] in
/-- The inverse subtype-restricted extended chart, on a target point, is `(extChartAt I p).symm`. -/
theorem extChartSubtype_symm_apply_of_mem (p : mZeroLocus f)
    {y : zeroLocus (localRep (I := I) f p.1)} (hy : y.1 ∈ (extChartAt I p.1).target) :
    ((extChartSubtype f p).symm y : M) = (extChartAt I p.1).symm y.1 := by
  rw [extChartSubtype]
  simp only [OpenPartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk, dif_pos hy]

/-- The Euclidean chart inverse at `p`, in ambient `M`-coordinates: `v ↦ (extChartAt I p).symm` of the
IFT-chart inverse of `e_p.symm v`. Holds where the IFT-preimage stays in `extChartAt`'s target. -/
theorem mLevelChartE_symm_apply (p : mZeroLocus f) (v : euclideanModel E)
    (hv : (0, (kerEquivEuclidean (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))
      (hsub p.1 p.2)).symm v) ∈ (mIftChart f hf hsub p).target)
    (hw : (mIftChart f hf hsub p).symm (0, (kerEquivEuclidean (fderiv ℝ (localRep (I := I) f p.1)
      (extChartAt I p.1 p.1)) (hsub p.1 p.2)).symm v) ∈ (extChartAt I p.1).target) :
    ((mLevelChartE f hf hsub p).symm v : M) =
      (extChartAt I p.1).symm ((mIftChart f hf hsub p).symm
        (0, (kerEquivEuclidean (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))
          (hsub p.1 p.2)).symm v)) := by
  have hy : ((mLevelSetChart f hf hsub p).symm
      ((kerEquivEuclidean (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))
        (hsub p.1 p.2)).symm v) : E) ∈ (extChartAt I p.1).target := by
    rw [mLevelSetChart_symm_apply f hf hsub p hv]; exact hw
  rw [mLevelChartE, OpenPartialHomeomorph.transHomeomorph_symm_apply, Function.comp_apply,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, mLevelChartKerR,
    OpenPartialHomeomorph.coe_restrOpen_symm, mLevelChartKer,
    OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
    extChartSubtype_symm_apply_of_mem f p hy, mLevelSetChart_symm_apply f hf hsub p hv]

/-- The (regular-restricted) kernel chart's target lands in the regular kernel target. -/
theorem mLevelChartKerR_target_subset (p : mZeroLocus f) :
    (mLevelChartKerR f hf hsub p).target ⊆ mRegularKerTarget f hf hsub p := by
  intro w hw
  have hsource := (mLevelChartKerR f hf hsub p).map_target hw
  rw [mLevelChartKerR, OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.coe_restrOpen_symm,
    Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_preimage] at hsource
  have hri := (mLevelChartKerR f hf hsub p).right_inv hw
  rw [mLevelChartKerR, OpenPartialHomeomorph.coe_restrOpen,
    OpenPartialHomeomorph.coe_restrOpen_symm] at hri
  rw [hri] at hsource
  exact hsource.2.2

/-- From `v ∈ (mLevelChartE p).target`, the inverse Euclidean coordinate is regular. -/
theorem mLevelChartE_target_regular (p : mZeroLocus f) {v : euclideanModel E}
    (hv : v ∈ (mLevelChartE f hf hsub p).target) :
    (kerEquivEuclidean (fderiv ℝ (localRep (I := I) f p.1) (extChartAt I p.1 p.1))
      (hsub p.1 p.2)).symm v ∈ mRegularKerTarget f hf hsub p := by
  rw [mLevelChartE, OpenPartialHomeomorph.transHomeomorph_target,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, Set.mem_preimage] at hv
  exact mLevelChartKerR_target_subset f hf hsub p hv

/-- A point in a Euclidean chart's source has its `M`-coordinate in the corresponding extended chart's
source. -/
theorem mLevelChartE_source_mem_extChart (q : mZeroLocus f) {x : mZeroLocus f}
    (hx : x ∈ (mLevelChartE f hf hsub q).source) : x.1 ∈ (extChartAt I q.1).source := by
  rw [mLevelChartE, OpenPartialHomeomorph.transHomeomorph_source, mLevelChartKerR,
    OpenPartialHomeomorph.restrOpen_source, mLevelChartKer, OpenPartialHomeomorph.trans_source] at hx
  exact hx.1.1

/-- **The chart transition `(mLevelChartE p).symm ≫ₕ (mLevelChartE q)` is `C^∞`** — it equals the
explicit Euclidean transition composite (`mContDiffOn_transitionE`) on its source, which lands in the
composite's regular domain. The structure-groupoid compatibility of the level-set atlas. -/
theorem mContDiffOn_chart_trans (p q : mZeroLocus f) :
    ContDiffOn ℝ ⊤ (↑((mLevelChartE f hf hsub p).symm ≫ₕ mLevelChartE f hf hsub q))
      ((mLevelChartE f hf hsub p).symm ≫ₕ mLevelChartE f hf hsub q).source := by
  refine (mContDiffOn_transitionE f hf hsub p q).congr_mono ?_ ?_
  · intro v hv
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, Set.mem_inter_iff,
      Set.mem_preimage] at hv
    obtain ⟨hvtgt, hvsrc⟩ := hv
    have hreg := mLevelChartE_target_regular f hf hsub p hvtgt
    have hq_src := mLevelChartE_source_mem_extChart f hf hsub q hvsrc
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      mLevelChartE_apply f hf hsub q _ hq_src,
      mLevelChartE_symm_apply f hf hsub p v hreg.1 hreg.2.1]
  · intro v hv
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, Set.mem_inter_iff,
      Set.mem_preimage] at hv
    obtain ⟨hvtgt, hvsrc⟩ := hv
    have hreg := mLevelChartE_target_regular f hf hsub p hvtgt
    have hq_src := mLevelChartE_source_mem_extChart f hf hsub q hvsrc
    rw [mLevelChartE_symm_apply f hf hsub p v hreg.1 hreg.2.1] at hq_src
    rw [Set.mem_preimage]
    refine ⟨hreg, ?_⟩
    rw [Set.mem_preimage, PartialEquiv.trans_source, PartialEquiv.symm_source, Set.mem_inter_iff,
      Set.mem_preimage]
    exact ⟨hreg.2.1, hq_src⟩

/-- **The manifold level set has a `C^∞` structure groupoid.** Every atlas chart transition is a `C^∞`
diffeomorphism of the Euclidean model (`mContDiffOn_chart_trans`). -/
theorem mLevelSetHasGroupoid :
    @HasGroupoid (euclideanModel E) _ (mZeroLocus f) _ (mLevelSetChartedSpace f hf hsub)
      (contDiffGroupoid ⊤ (modelWithCornersSelf ℝ (euclideanModel E))) := by
  letI := mLevelSetChartedSpace f hf hsub
  apply hasGroupoid_of_pregroupoid
  intro e e' he he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨q, rfl⟩ := he'
  rw [contDiffPregroupoid]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.inter_univ, Set.preimage_id, Function.id_comp, Function.comp_id]
  exact mContDiffOn_chart_trans f hf hsub p q

/-- **The level set of a `C^∞` real submersion `f : M → ℝ` on a boundaryless manifold is a `C^∞`
manifold** modelled on `EuclideanSpace ℝ (Fin (finrank E - 1))` — the manifold regular-value theorem. -/
theorem mLevelSetIsManifold :
    @IsManifold ℝ _ (euclideanModel E) _ _ (euclideanModel E) _
      (modelWithCornersSelf ℝ (euclideanModel E)) ⊤ (mZeroLocus f) _ (mLevelSetChartedSpace f hf hsub) :=
  letI := mLevelSetChartedSpace f hf hsub
  { compatible := fun he he' => (mLevelSetHasGroupoid f hf hsub).compatible he he' }

/-- **The manifold level set as a `SingularManifold`** (over `PUnit`): the compact, boundaryless
`C^∞` manifold `mZeroLocus f`, packaged for the bordism group `DataBordismGrp`. This is the form the
geometric Smith map's Poincaré-dual `[M] ↦ [PD(a) = N]` consumes — `mZeroLocus f` is compact (closed
in the compact `M`), boundaryless (modelled on a boundaryless self-model), and `C^∞`
(`mLevelSetIsManifold`). -/
noncomputable def mLevelSetSingularManifold [CompactSpace M] :
    SingularManifold PUnit ⊤ (modelWithCornersSelf ℝ (euclideanModel E)) :=
  letI := mLevelSetChartedSpace f hf hsub
  letI := mLevelSetIsManifold f hf hsub
  haveI : CompactSpace (mZeroLocus f) := instCompactSpace_mZeroLocus hf.continuous
  SingularManifold.toPUnit (mZeroLocus f) (modelWithCornersSelf ℝ (euclideanModel E))

end Chart

end SKEFTHawking.ManifoldRegularValue
