/-
Copyright (c) 2026 SK-EFT Hawking project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SKEFTHawking.CollarNeighbourhood
import SKEFTHawking.ContMDiffPartitionOfUnity
import SKEFTHawking.InwardFlow

/-!
# A `C^n` boundary-defining function on a bordism-model manifold

This is the first consumer of `SKEFTHawking.ContMDiffPartitionOfUnity`, and the second collar
prerequisite in usable form. For `W` a `C^n` manifold modelled on `I.prod (𝓡∂ 1)` (`I`
boundaryless), it patches the *local heights* — the last model coordinate of each boundary chart —
into a single global `C^n` function `ρ : W → ℝ` with `ρ ≥ 0` everywhere and `ρ⁻¹(0) = ∂W` on a
neighbourhood of the boundary.

`ρ` is the scalar avatar of the inward-pointing vector field the collar neighbourhood theorem
needs: near `∂W` it is a submersion onto `[0, ∞)` transverse to the boundary, and the collar
coordinate is built from its flow. Producing it at *finite* `n` is exactly what the finite-
regularity partition of unity buys — Mathlib's `SmoothPartitionOfUnity` would force `n = ∞`.

## Main definitions

* `SKEFTHawking.Collar.localHeight`: the last model coordinate of the extended chart at `y`.
* `SKEFTHawking.Collar.lastCoord`: that coordinate as a continuous linear functional.
* `SKEFTHawking.Collar.boundaryHeight`: the global patched function.

## Main results

* `localHeight_nonneg`: unconditional — the chart lands in the half space by construction.
* `localHeight_eq_zero_iff` / `localHeight_pos_iff`: the local height detects boundary/interior
  points, in *any* chart (chart-independence comes from `CollarNeighbourhood`).
* `contMDiffOn_localHeight`: `C^n` on its chart domain.
* `contMDiff_boundaryHeight`: **the patched function is `C^n` on all of `W`**.
* `boundaryHeight_nonneg`, `boundaryHeight_eq_zero_of_mem_boundary`,
  `boundaryHeight_pos_of_notMem_boundary`, `boundaryHeight_eq_zero_iff`.
* `exists_contMDiff_boundaryDefiningFunction`: **the packaged existence statement.**
* `prodIcc_exists_contMDiff_boundaryDefiningFunction`: **non-vacuity with a non-degenerate
  conclusion** — on `ℝ × [0,1]` the boundary is nonempty and the `ρ` produced is provably not the
  zero function on its own neighbourhood.

It also transports `SKEFTHawking.Collar.exists_forward_flow_halfSpace` (prerequisite (3), model
form) onto this model's range:

* `exists_forward_flow_prodHalf`: an inward-pointing field's forward trajectory from any point of
  `range (I.prod (𝓡∂ 1))` stays in it, and lies in `interior (range (I.prod (𝓡∂ 1)))` for every
  `t > 0`.
* `exists_inward_field_prodHalf`, `exists_forward_flow_prodHalf_from_boundary`: non-vacuity — the
  hypotheses are satisfied by the constant unit half-line field, and the origin is a genuine
  boundary point of the model range from which the trajectory does leave the boundary.
-/

open Set Function Filter
open scoped Topology Manifold ContDiff NNReal

namespace SKEFTHawking.Collar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {W : Type*} [TopologicalSpace W] [ChartedSpace (ModelProd H (EuclideanHalfSpace 1)) W]

variable (I) in
/-- The **local height** of `x` in the chart at `y`: the last model coordinate of the preferred
extended chart at `y`. -/
noncomputable def localHeight (y : W) (x : W) : ℝ :=
  (extChartAt (I.prod (𝓡∂ 1)) y x).2 0

/-- The continuous linear functional "last coordinate" on the ambient model space. -/
noncomputable def lastCoord (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 1)).comp (ContinuousLinearMap.snd ℝ E (EuclideanSpace ℝ (Fin 1)))

@[simp] theorem lastCoord_apply (p : E × EuclideanSpace ℝ (Fin 1)) : lastCoord E p = p.2 0 := rfl

omit [I.Boundaryless] in
theorem localHeight_eq_comp (y : W) :
    localHeight I y = lastCoord E ∘ extChartAt (I.prod (𝓡∂ 1)) y := rfl

omit [I.Boundaryless] in
/-- In the chart, the local height is the last coordinate of the half-space factor. -/
theorem localHeight_eq_chart (y x : W) :
    localHeight I y x = ((chartAt (ModelProd H (EuclideanHalfSpace 1)) y) x).2.1 0 := rfl

omit [I.Boundaryless] in
/-- **The local height is never negative** — the chart lands in the half space by construction, so
no hypothesis on `x` is needed. -/
theorem localHeight_nonneg (y x : W) : 0 ≤ localHeight I y x :=
  ((chartAt (ModelProd H (EuclideanHalfSpace 1)) y) x).2.2

omit [I.Boundaryless] in
/-- The local height is `C^n` on the chart domain: it is the last coordinate of the extended
chart, i.e. a continuous linear functional applied to it. -/
theorem contMDiffOn_localHeight {n : ℕ∞} [IsManifold (I.prod (𝓡∂ 1)) (n : WithTop ℕ∞) W]
    (y : W) :
    ContMDiffOn (I.prod (𝓡∂ 1)) 𝓘(ℝ) n (localHeight I y)
      (chartAt (ModelProd H (EuclideanHalfSpace 1)) y).source :=
  (lastCoord E).contMDiff.comp_contMDiffOn contMDiffOn_extChartAt

/-- **The local height detects the boundary.** In any chart containing `x`, the last coordinate of
`x` vanishes exactly when `x` is a boundary point — the chart-independence supplied by
`isBoundaryPoint_prodHalf_iff_of_mem_atlas`. -/
theorem localHeight_eq_zero_iff {m : WithTop ℕ∞} [IsManifold (I.prod (𝓡∂ 1)) m W] (hm : m ≠ 0)
    {y x : W} (hx : x ∈ (chartAt (ModelProd H (EuclideanHalfSpace 1)) y).source) :
    localHeight I y x = 0 ↔ (I.prod (𝓡∂ 1)).IsBoundaryPoint x :=
  (isBoundaryPoint_prodHalf_iff_of_mem_atlas hm (chart_mem_atlas _ y) hx).symm

/-- The companion of `localHeight_eq_zero_iff`: a strictly positive local height detects an
interior point. -/
theorem localHeight_pos_iff {m : WithTop ℕ∞} [IsManifold (I.prod (𝓡∂ 1)) m W] (hm : m ≠ 0)
    {y x : W} (hx : x ∈ (chartAt (ModelProd H (EuclideanHalfSpace 1)) y).source) :
    0 < localHeight I y x ↔ (I.prod (𝓡∂ 1)).IsInteriorPoint x :=
  (isInteriorPoint_prodHalf_iff_of_mem_atlas hm (chart_mem_atlas _ y) hx).symm

/-! ### The global boundary-defining function -/

section Global

variable {n : ℕ∞} [IsManifold (I.prod (𝓡∂ 1)) (n : WithTop ℕ∞) W]

variable (I) in
/-- **The boundary-defining function** of a `C^n` partition of unity `f` on `W`, indexed by the
boundary and subordinate to the chart cover: patch the local heights together. -/
noncomputable def boundaryHeight
    (f : ContMDiffPartitionOfUnity ↥((I.prod (𝓡∂ 1)).boundary W) (I.prod (𝓡∂ 1)) W n
      ((I.prod (𝓡∂ 1)).boundary W)) (x : W) : ℝ :=
  ∑ᶠ y, f y x • localHeight I (y : W) x

variable (f : ContMDiffPartitionOfUnity ↥((I.prod (𝓡∂ 1)).boundary W) (I.prod (𝓡∂ 1)) W n
  ((I.prod (𝓡∂ 1)).boundary W))

omit [I.Boundaryless] in
/-- **The boundary-defining function is `C^n` on all of `W`** — the point of using a partition of
unity: each local height is only defined on its own chart, and the partition kills it elsewhere. -/
theorem contMDiff_boundaryHeight
    (hf : ContMDiffPartitionOfUnity.IsSubordinate f
      fun y => (chartAt (ModelProd H (EuclideanHalfSpace 1)) (y : W)).source) :
    ContMDiff (I.prod (𝓡∂ 1)) 𝓘(ℝ) n (boundaryHeight I f) := by
  refine ContMDiffPartitionOfUnity.contMDiff_finsum_smul f fun y x hx => ?_
  have hxs : x ∈ (chartAt (ModelProd H (EuclideanHalfSpace 1)) (y : W)).source := hf y hx
  exact (contMDiffOn_localHeight (n := n) (y : W)).contMDiffAt
    ((chartAt (ModelProd H (EuclideanHalfSpace 1)) (y : W)).open_source.mem_nhds hxs)

omit [I.Boundaryless] [IsManifold (I.prod (𝓡∂ 1)) (n : WithTop ℕ∞) W] in
theorem boundaryHeight_nonneg (x : W) : 0 ≤ boundaryHeight I f x :=
  finsum_nonneg fun y => by
    simpa only [smul_eq_mul] using
      mul_nonneg (ContMDiffPartitionOfUnity.nonneg f y x) (localHeight_nonneg (y : W) x)

/-- **The boundary-defining function vanishes on the boundary.** -/
theorem boundaryHeight_eq_zero_of_mem_boundary (hn : (n : WithTop ℕ∞) ≠ 0)
    (hf : ContMDiffPartitionOfUnity.IsSubordinate f
      fun y => (chartAt (ModelProd H (EuclideanHalfSpace 1)) (y : W)).source)
    {x : W} (hx : x ∈ (I.prod (𝓡∂ 1)).boundary W) : boundaryHeight I f x = 0 := by
  have hterm : ∀ y, f y x • localHeight I (y : W) x = 0 := by
    intro y
    by_cases h : f y x = 0
    · simp [h]
    · have hxs : x ∈ (chartAt (ModelProd H (EuclideanHalfSpace 1)) (y : W)).source :=
        hf y (subset_closure h)
      simp [(localHeight_eq_zero_iff hn hxs).mpr hx]
  simp only [boundaryHeight, hterm, finsum_zero]

omit [I.Boundaryless] [IsManifold (I.prod (𝓡∂ 1)) (n : WithTop ℕ∞) W] in
/-- The supports of a partition of unity indexed by the boundary have finite trace at each point,
so the defining sum is a finite sum. -/
theorem finite_support_boundaryHeight (x : W) :
    (support fun y => f y x • localHeight I (y : W) x).Finite :=
  ((ContMDiffPartitionOfUnity.locallyFinite f).point_finite x).subset fun y hy => by
    simpa using fun h => hy (by simp [h])

/-- **Off the boundary, the defining function is strictly positive** wherever the partition of
unity is supported. -/
theorem boundaryHeight_pos_of_notMem_boundary (hn : (n : WithTop ℕ∞) ≠ 0)
    (hf : ContMDiffPartitionOfUnity.IsSubordinate f
      fun y => (chartAt (ModelProd H (EuclideanHalfSpace 1)) (y : W)).source)
    {x : W} (hx : x ∉ (I.prod (𝓡∂ 1)).boundary W) {y₀ : ↥((I.prod (𝓡∂ 1)).boundary W)}
    (hy₀ : f y₀ x ≠ 0) : 0 < boundaryHeight I f x := by
  have hxs : x ∈ (chartAt (ModelProd H (EuclideanHalfSpace 1)) (y₀ : W)).source :=
    hf y₀ (subset_closure hy₀)
  have hint : (I.prod (𝓡∂ 1)).IsInteriorPoint x :=
    ((I.prod (𝓡∂ 1)).isInteriorPoint_or_isBoundaryPoint x).resolve_right hx
  have hpos : 0 < localHeight I (y₀ : W) x := (localHeight_pos_iff hn hxs).mpr hint
  have hfpos : 0 < f y₀ x := lt_of_le_of_ne (ContMDiffPartitionOfUnity.nonneg f y₀ x) (Ne.symm hy₀)
  refine lt_of_lt_of_le ?_ (single_le_finsum y₀ (finite_support_boundaryHeight f x) fun y => ?_)
  · simpa only [smul_eq_mul] using mul_pos hfpos hpos
  · simpa only [smul_eq_mul] using
      mul_nonneg (ContMDiffPartitionOfUnity.nonneg f y x) (localHeight_nonneg (y : W) x)

/-- **The defining property.** On the open set where the partition of unity is supported — an open
neighbourhood of `∂W` — the function `boundaryHeight` vanishes exactly on the boundary. -/
theorem boundaryHeight_eq_zero_iff (hn : (n : WithTop ℕ∞) ≠ 0)
    (hf : ContMDiffPartitionOfUnity.IsSubordinate f
      fun y => (chartAt (ModelProd H (EuclideanHalfSpace 1)) (y : W)).source)
    {x : W} (hx : ∃ y, f y x ≠ 0) :
    boundaryHeight I f x = 0 ↔ x ∈ (I.prod (𝓡∂ 1)).boundary W := by
  obtain ⟨y₀, hy₀⟩ := hx
  refine ⟨fun h => by_contra fun hb => ?_,
    boundaryHeight_eq_zero_of_mem_boundary f hn hf⟩
  exact absurd h (boundaryHeight_pos_of_notMem_boundary f hn hf hb hy₀).ne'

end Global

/-! ### Flow out of a boundary point, in the ambient model space -/

/-- **The forward flow of an inward-pointing field never leaves the bordism model's range, and
enters its interior immediately.**

This is `exists_forward_flow_halfSpace` transported to the model range of `I.prod (𝓡∂ 1)` via
`range_prodHalf` / `interior_range_prodHalf`. Stated in the *model space* `E × ℝ¹`, it is the
half of Mathlib's "integral curve venturing to the boundary" TODO that does not need a new
manifold-level notion: starting at any point of the closed half space (in particular at a
boundary point, where the last coordinate vanishes), the trajectory of a field whose last
component is bounded below by `c > 0` remains admissible for all `t ∈ [0, ε]` and is strictly
interior for all `t ∈ (0, ε]`. -/
theorem exists_forward_flow_prodHalf [CompleteSpace E]
    {v : E × EuclideanSpace ℝ (Fin 1) → E × EuclideanSpace ℝ (Fin 1)} {K L : ℝ≥0}
    (hlip : LipschitzWith K v) (hbdd : ∀ x, ‖v x‖ ≤ L) {c : ℝ} (hc : 0 < c)
    (hv : ∀ x, c ≤ (v x).2 0) {x₀ : E × EuclideanSpace ℝ (Fin 1)}
    (hx₀ : x₀ ∈ range (I.prod (𝓡∂ 1))) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ → E × EuclideanSpace ℝ (Fin 1), α 0 = x₀ ∧
      (∀ t ∈ Icc (0 : ℝ) ε, HasDerivWithinAt α (v (α t)) (Icc (0 : ℝ) ε) t) ∧
      (∀ t ∈ Icc (0 : ℝ) ε, α t ∈ range (I.prod (𝓡∂ 1))) ∧
      ∀ t ∈ Ioc (0 : ℝ) ε, α t ∈ interior (range (I.prod (𝓡∂ 1))) := by
  rw [range_prodHalf I] at hx₀
  obtain ⟨α, hα0, hα, hcl, hop⟩ :=
    exists_forward_flow_halfSpace (φ := lastCoord E) hlip hbdd hc hv hx₀ hε
  refine ⟨α, hα0, hα, fun t ht => ?_, fun t ht => ?_⟩
  · rw [range_prodHalf I]; exact hcl t ht
  · rw [interior_range_prodHalf I]; exact hop t ht

omit [NormedSpace ℝ E] [I.Boundaryless] in
/-- The constant unit field in the half-line direction is globally Lipschitz, bounded, and
inward-pointing with `c = 1`: the hypotheses of `exists_forward_flow_prodHalf` are satisfiable. -/
theorem exists_inward_field_prodHalf :
    ∃ v : E × EuclideanSpace ℝ (Fin 1) → E × EuclideanSpace ℝ (Fin 1),
      LipschitzWith 0 v ∧ (∀ x, ‖v x‖ ≤ 1) ∧ ∀ x, (1 : ℝ) ≤ (v x).2 0 := by
  refine ⟨fun _ => (0, EuclideanSpace.single (0 : Fin 1) 1), LipschitzWith.const _,
    fun x => ?_, fun x => ?_⟩
  · simp [Prod.norm_def]
  · simp

/-- **Non-vacuity of the flow-out-of-the-boundary statement.** The origin is a genuine *boundary*
point of the model range — it is not interior — and yet the forward trajectory of the constant
inward field starts there, stays admissible, and is strictly interior at every positive time.

So `exists_forward_flow_prodHalf` is not vacuous on two counts: its hypothesis bundle is
satisfiable (`exists_inward_field_prodHalf`), and its conclusion is non-degenerate — the curve
genuinely leaves the boundary, which is precisely what a collar needs. -/
theorem exists_forward_flow_prodHalf_from_boundary [CompleteSpace E] {ε : ℝ} (hε : 0 < ε) :
    (0 : E × EuclideanSpace ℝ (Fin 1)) ∉ interior (range (I.prod (𝓡∂ 1))) ∧
      ∃ α : ℝ → E × EuclideanSpace ℝ (Fin 1), α 0 = 0 ∧
        (∀ t ∈ Icc (0 : ℝ) ε, α t ∈ range (I.prod (𝓡∂ 1))) ∧
        ∀ t ∈ Ioc (0 : ℝ) ε, α t ∈ interior (range (I.prod (𝓡∂ 1))) := by
  obtain ⟨v, hlip, hbdd, hv⟩ := exists_inward_field_prodHalf (E := E)
  have h0 : (0 : E × EuclideanSpace ℝ (Fin 1)) ∈ range (I.prod (𝓡∂ 1)) := by
    rw [range_prodHalf I]; simp
  obtain ⟨α, hα0, -, hcl, hop⟩ :=
    exists_forward_flow_prodHalf (I := I) (L := 1) hlip (by simpa using hbdd) zero_lt_one hv h0 hε
  refine ⟨?_, α, hα0, hcl, hop⟩
  rw [interior_range_prodHalf I]
  simp

/-! ### Existence -/

/-- **A `C^n` boundary-defining function exists on a neighbourhood of the boundary.**

For a Hausdorff, σ-compact `C^n` manifold `W` modelled on `I.prod (𝓡∂ 1)` (`I` boundaryless,
finite-dimensional), there is an open `V ⊇ ∂W` and a globally `C^n`, everywhere-nonnegative
`ρ : W → ℝ` whose zero set inside `V` is exactly `∂W`.

This is the scalar avatar of the inward-pointing vector field the collar neighbourhood theorem
needs, and it is exactly what a finite-regularity partition of unity buys: the local heights (the
last coordinate of each boundary chart) are patched into one global `C^n` function. At `n = ∞` it
is available from Mathlib's `SmoothPartitionOfUnity`; at finite `n` it needs
`SKEFTHawking.Collar.ContMDiffPartitionOfUnity.exists_isSubordinate_chartAt_source_of_isClosed`. -/
theorem exists_contMDiff_boundaryDefiningFunction {n : ℕ∞} [FiniteDimensional ℝ E] [T2Space W]
    [SigmaCompactSpace W] [IsManifold (I.prod (𝓡∂ 1)) (n : WithTop ℕ∞) W]
    (hn : (n : WithTop ℕ∞) ≠ 0) :
    ∃ (V : Set W) (ρ : W → ℝ), IsOpen V ∧ (I.prod (𝓡∂ 1)).boundary W ⊆ V ∧
      ContMDiff (I.prod (𝓡∂ 1)) 𝓘(ℝ) n ρ ∧ (∀ x, 0 ≤ ρ x) ∧
      ∀ x ∈ V, (ρ x = 0 ↔ x ∈ (I.prod (𝓡∂ 1)).boundary W) := by
  obtain ⟨f, hf⟩ :=
    ContMDiffPartitionOfUnity.exists_isSubordinate_chartAt_source_of_isClosed
      (I := I.prod (𝓡∂ 1)) (n := n) (isClosed_boundary_prodHalf (I := I) (W := W) hn)
  refine ⟨⋃ y, support (f y), boundaryHeight I f, isOpen_iUnion fun y =>
    (f y).continuous.isOpen_preimage _ isOpen_ne, fun x hx => ?_,
    contMDiff_boundaryHeight f hf, boundaryHeight_nonneg f, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := (ContMDiffPartitionOfUnity.toPartitionOfUnity f).exists_pos hx
    exact mem_iUnion_of_mem y hy.ne'
  · obtain ⟨y, hy⟩ := mem_iUnion.1 hx
    exact boundaryHeight_eq_zero_iff f hn hf ⟨y, hy⟩

/-- **Non-vacuity, with a non-degenerate conclusion.** `ℝ × [0,1]` satisfies the whole hypothesis
bundle of `exists_contMDiff_boundaryDefiningFunction`, its boundary `ℝ × {⊥, ⊤}` is nonempty, and
— crucially — the `ρ` produced is *not* the zero function on its neighbourhood `V`: it vanishes
somewhere (on `∂W`) and is nonzero somewhere else (inside `V`).

The last conjunct is what rules out the degenerate reading of
`exists_contMDiff_boundaryDefiningFunction` in which `∂W = ∅`, `V = ∅` and `ρ = 0`. It is forced by
connectedness: if `ρ` vanished on all of `V`, the defining property would make `V = ∂W` clopen,
nonempty and proper in the connected space `ℝ × [0,1]`. -/
theorem prodIcc_exists_contMDiff_boundaryDefiningFunction {n : ℕ∞} (hn : (n : WithTop ℕ∞) ≠ 0) :
    letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
    ((𝓘(ℝ, ℝ).prod (𝓡∂ 1)).boundary (ℝ × Icc (0 : ℝ) 1)).Nonempty ∧
      ∃ (V : Set (ℝ × Icc (0 : ℝ) 1)) (ρ : ℝ × Icc (0 : ℝ) 1 → ℝ), IsOpen V ∧
        (𝓘(ℝ, ℝ).prod (𝓡∂ 1)).boundary (ℝ × Icc (0 : ℝ) 1) ⊆ V ∧
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 1)) 𝓘(ℝ) n ρ ∧ (∀ x, 0 ≤ ρ x) ∧
        (∀ x ∈ V, (ρ x = 0 ↔ x ∈ (𝓘(ℝ, ℝ).prod (𝓡∂ 1)).boundary (ℝ × Icc (0 : ℝ) 1))) ∧
        ∃ x ∈ V, ρ x ≠ 0 := by
  letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hbot : ((0 : ℝ), (⊥ : Icc (0 : ℝ) 1)) ∈
      (𝓘(ℝ, ℝ).prod (𝓡∂ 1)).boundary (ℝ × Icc (0 : ℝ) 1) := by
    rw [boundary_product]; exact ⟨mem_univ _, mem_insert _ _⟩
  have hmid : ((0 : ℝ), (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1)) ∉
      (𝓘(ℝ, ℝ).prod (𝓡∂ 1)).boundary (ℝ × Icc (0 : ℝ) 1) := by
    rw [boundary_product]
    rintro ⟨-, h | h⟩ <;>
      exact absurd (congrArg Subtype.val h) (by norm_num)
  obtain ⟨V, ρ, hVo, hVsub, hρ, hρ0, hiff⟩ :=
    exists_contMDiff_boundaryDefiningFunction (I := 𝓘(ℝ, ℝ)) (W := ℝ × Icc (0 : ℝ) 1) hn
  refine ⟨⟨_, hbot⟩, V, ρ, hVo, hVsub, hρ, hρ0, hiff, ?_⟩
  by_contra hall
  push Not at hall
  have hVeq : V = (𝓘(ℝ, ℝ).prod (𝓡∂ 1)).boundary (ℝ × Icc (0 : ℝ) 1) :=
    subset_antisymm (fun x hx => (hiff x hx).1 (hall x hx)) hVsub
  have hclopen : IsClopen V :=
    ⟨hVeq ▸ isClosed_boundary_prodHalf (I := 𝓘(ℝ, ℝ)) (W := ℝ × Icc (0 : ℝ) 1) hn, hVo⟩
  exact hmid (hVeq ▸ (hclopen.eq_univ ⟨_, hVsub hbot⟩ ▸ mem_univ _))

end SKEFTHawking.Collar
